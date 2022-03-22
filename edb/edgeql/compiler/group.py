#
# This source file is part of the EdgeDB open source project.
#
# Copyright 2008-present MagicStack Inc. and the EdgeDB authors.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#


from __future__ import annotations

from typing import *

from edb.common import ast as ast_visitor

from edb.edgeql import qltypes
from edb.ir import ast as irast

from . import context


class FindAggregatingUses(ast_visitor.NodeVisitor):
    """
    XXX: track visibility, and only look at shapes when visible??
    """
    skip_hidden = True
    extra_skips = frozenset(['materialized_sets'])

    def __init__(
        self, target: irast.PathId, to_skip: AbstractSet[irast.PathId],
        ctx: context.ContextLevel,
    ) -> None:
        super().__init__()
        self.target = target
        self.to_skip = to_skip
        self.aggregate: Optional[irast.Set] = None
        self.sightings: Set[Optional[irast.Set]] = set()
        self.ctx = ctx
        self.counts: Dict[irast.PathId, int] = {}
        self.count_logs: Dict[
            Optional[irast.Set], FrozenSet[irast.PathId]] = {}
        self.scope_tree = ctx.path_scope

    def visit_Stmt(self, stmt: irast.Stmt) -> Any:
        # XXX???
        # Sometimes there is sharing, so we want the official scope
        # for a node to be based on its appearance in the result,
        # not in a subquery.
        # I think it might not actually matter, though.

        # XXX: make sure stuff like
        # WITH X := g.x, (count(X), X)
        # gets flagged
        # SHOULD WE SKIP THE BINDINGS???

        old = self.aggregate

        # Can't handle ORDER/LIMIT/OFFSET which operate on the whole
        # set
        # XXX: but often we probably could with arguments to the
        # aggregates, as long as the argument to the aggregate is just
        # a reference
        if isinstance(stmt, irast.SelectStmt) and (
            stmt.orderby or stmt.limit or stmt.offset or stmt.materialized_sets
        ):
            self.aggregate = None

        self.visit(stmt.bindings)
        if stmt.iterator_stmt:
            self.visit(stmt.iterator_stmt)
        if isinstance(stmt, irast.MutatingStmt):
            self.visit(stmt.subject)
        self.visit(stmt.result)

        # XXX: AS D F THIS obviously fucks the counting thing
        # but the counting thing is fucked anyway
        res = self.generic_visit(stmt)

        self.aggregate = old

        return res

    def repeated_node_visit(self, node: irast.Base) -> None:
        if isinstance(node, irast.Set):
            self.counts[node.path_id] = self.counts.get(node.path_id, 0) + 1

    # XXX: can we just /always/ skip rptrs?
    # and expr, if there is a shape??

    def visit_Set(self, node: irast.Set, skip_rptr: bool=False) -> None:
        # XXX: or just the node??
        self.counts[node.path_id] = self.counts.get(node.path_id, 0) + 1

        if node.path_id in self.to_skip:
            return

        if node.path_id == self.target:
            self.sightings.add(self.aggregate)
            return

        old_scope = self.scope_tree
        if node.path_scope_id is not None:
            self.scope_tree = self.ctx.env.scope_tree_nodes[node.path_scope_id]

        # We also can't handle references inside of a semi-join,
        # because the bodies are executed one at a time, and so the
        # semi-join deduplication doesn't work.
        is_semijoin = (
            node.rptr
            and node.path_id.is_objtype_path()
            and not self.scope_tree.is_visible(node.rptr.source.path_id)
        )

        old = self.aggregate
        if is_semijoin:
            # XXX: do we want this around .shape? around .expr??
            self.aggregate = None

        self.visit(node.shape)

        if not node.expr and node.rptr:
            self.visit(node.rptr.source)
        elif node.rptr:
            self.counts[node.rptr.source.path_id] = self.counts.get(
                node.rptr.source.path_id, 0)

        # XXX: maybe need to still look for the target in the skipped rptrs?
        if not node.shape:
            if isinstance(node.expr, irast.Call):
                self.process_call(node.expr, node)
            else:
                self.visit(node.expr)

        self.aggregate = old
        self.scope_tree = old_scope

    def process_call(self, node: irast.Call, ir_set: irast.Set) -> None:
        # It needs to be backed by an actual SQL function and must
        # not return SET OF
        returns_set = node.typemod == qltypes.TypeModifier.SetOfType
        calls_sql_func = (
            isinstance(node, irast.FunctionCall)
            and node.func_sql_function
        )
        for arg, typemod in zip(node.args, node.params_typemods):
            old = self.aggregate
            # If this *returns* a set, it is going to mess things up since
            # the operation can't actually run on multiple things...

            old_counts = None

            # TODO: we would like to do better in some cases with
            # DISTINCT and the like where there are built in features
            # to do it in a GROUP
            if returns_set:
                self.aggregate = None
            # XXX: disabling this optimization breaks some things and
            # fixes others... sigh!
            elif (
                calls_sql_func
                and typemod == qltypes.TypeModifier.SetOfType
            ):
                old_counts = self.counts
                self.counts = {}
                self.aggregate = ir_set
            self.visit(arg)
            self.aggregate = old

            if old_counts is not None:
                self.count_logs[ir_set] = frozenset({
                    k for k, v in self.counts.items() if v == 0
                    and self.scope_tree.is_visible(k)
                })
                for k, n in self.counts.items():
                    # If we referred to some visible set and also
                    # spotted the target, we can't actually compile
                    # the target separately, so ditch it.
                    if (
                        n > 0
                        and self.scope_tree.is_visible(k)
                        and ir_set in self.sightings
                    ):
                        self.sightings.discard(ir_set)
                        self.sightings.add(None)
                    old_counts[k] = self.counts.get(k, 0) + n

                self.counts = old_counts


def infer_group_aggregates(
    ir: irast.Base,
    *,
    ctx: context.ContextLevel,
) -> None:
    # XXX: scope scope scope???
    flt = lambda n: isinstance(n, irast.GroupStmt)
    groups: List[irast.GroupStmt] = ast_visitor.find_children(ir, flt)
    for stmt in groups:
        visitor = FindAggregatingUses(
            stmt.group_binding.path_id,
            {x.path_id for x, _ in stmt.using.values()},
            ctx=ctx,
        )
        visitor.visit(stmt.result)
        # XXX: I think there are potentially issues with overlapping...
        stmt.group_aggregate_sets = {
            k: visitor.count_logs.get(k, frozenset())
            for k in visitor.sightings
        }
