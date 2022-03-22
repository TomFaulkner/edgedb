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

from edb.edgeql import ast as qlast
from edb.edgeql import desugar_group
from edb.edgeql import qltypes
from edb.ir import ast as irast
from edb.pgsql import ast as pgast

from . import astutils
from . import clauses
from . import context
from . import dispatch
from . import output
from . import pathctx
from . import relctx
from . import relgen


class FindAggregatingUses(ast_visitor.NodeVisitor):
    """
    XXX: track visibility, and only look at shapes when visible??
    """
    skip_hidden = True
    extra_skips = frozenset(['materialized_sets'])

    def __init__(
        self, target: irast.PathId, to_skip: AbstractSet[irast.PathId],
        ctx: context.CompilerContextLevel,
    ) -> None:
        super().__init__()
        self.target = target
        self.to_skip = to_skip
        self.aggregate: Optional[irast.Set] = None
        self.sightings: Set[Optional[irast.Set]] = set()
        self.ctx = ctx
        self.counts: Dict[irast.PathId, int] = {}
        self.count_logs: Dict[irast.Set, Set[irast.PathId]] = {}
        self.scope_tree = ctx.scope_tree

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
        if new_scope := relctx.get_scope(node, ctx=self.ctx):
            self.scope_tree = new_scope

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
                self.count_logs[ir_set] = {
                    k for k, v in self.counts.items() if v == 0
                    and self.scope_tree.is_visible(k)
                }
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


def compile_grouping_atom(
    el: qlast.GroupingAtom,
    stmt: irast.GroupStmt, *, ctx: context.CompilerContextLevel
) -> pgast.Base:
    if isinstance(el, qlast.GroupingIdentList):
        return pgast.GroupingOperation(
            args=[
                compile_grouping_atom(at, stmt, ctx=ctx) for at in el.elements
            ],
        )

    assert isinstance(el, qlast.ObjectRef)
    alias_set, _ = stmt.using[el.name]
    return pathctx.get_path_value_var(
        ctx.rel, alias_set.path_id, env=ctx.env)


def compile_grouping_el(
    el: qlast.GroupingElement,
    stmt: irast.GroupStmt, *, ctx: context.CompilerContextLevel
) -> pgast.Base:
    if isinstance(el, qlast.GroupingSets):
        return pgast.GroupingOperation(
            operation='GROUPING SETS',
            args=[compile_grouping_el(sub, stmt, ctx=ctx) for sub in el.sets],
        )
    elif isinstance(el, qlast.GroupingOperation):
        return pgast.GroupingOperation(
            operation=el.oper,
            args=[
                compile_grouping_atom(at, stmt, ctx=ctx) for at in el.elements
            ],
        )
    elif isinstance(el, qlast.GroupingSimple):
        return compile_grouping_atom(el.element, stmt, ctx=ctx)
    raise AssertionError('Unknown GroupingElement')


def _compile_grouping_value(
        stmt: irast.GroupStmt, used_args: AbstractSet[str], *,
        ctx: context.CompilerContextLevel) -> pgast.BaseExpr:
    assert stmt.grouping_binding
    grouprel = ctx.rel

    # XXX: omit the ones that aren't really grouped on
    if len(used_args) == 1:
        return pgast.ArrayExpr(
            elements=[
                pgast.StringConstant(val=list(used_args)[0].split('~')[0])]
        )

    # XXX: or do we want to sort this?
    using = {k: stmt.using[k] for k in used_args}

    args = [
        pathctx.get_path_var(
            grouprel, alias_set.path_id, aspect='value', env=ctx.env)
        for alias_set, _ in using.values()
    ]

    grouping_alias = ctx.env.aliases.get('g')
    grouping_call = pgast.FuncCall(name=('grouping',), args=args)
    subq = pgast.SelectStmt(
        target_list=[
            pgast.ResTarget(name=grouping_alias, val=grouping_call),
        ]
    )
    q = pgast.SelectStmt(
        from_clause=[pgast.RangeSubselect(
            subquery=subq,
            alias=pgast.Alias(aliasname=ctx.env.aliases.get())
        )]
    )

    grouping_ref = pgast.ColumnRef(name=(grouping_alias,))

    els: List[pgast.BaseExpr] = []
    for i, name in enumerate(using):
        name = name.split('~')[0]  # ...
        mask = 1 << (len(using) - i - 1)
        # (CASE (e & 2) WHEN 0 THEN 'a' ELSE NULL END)

        els.append(pgast.CaseExpr(
            arg=pgast.Expr(
                kind=pgast.ExprKind.OP,
                name='&',
                lexpr=grouping_ref,
                rexpr=pgast.LiteralExpr(expr=str(mask))
            ),
            args=[
                pgast.CaseWhen(
                    expr=pgast.LiteralExpr(expr='0'),
                    result=pgast.StringConstant(val=name)
                )
            ],
            defresult=pgast.NullConstant()
        ))

    val = pgast.FuncCall(
        name=('array_remove',),
        args=[pgast.ArrayExpr(elements=els), pgast.NullConstant()]
    )

    q.target_list.append(pgast.ResTarget(val=val))

    return q


def _compile_grouping_binding(
        stmt: irast.GroupStmt, *, used_args: AbstractSet[str],
        ctx: context.CompilerContextLevel) -> None:
    assert stmt.grouping_binding
    pathctx.put_path_var(
        ctx.rel, stmt.grouping_binding.path_id,
        _compile_grouping_value(stmt, used_args=used_args, ctx=ctx),
        aspect='value', env=ctx.env)


def _compile_group(
        stmt: irast.GroupStmt, *,
        ctx: context.CompilerContextLevel,
        parent_ctx: context.CompilerContextLevel) -> pgast.BaseExpr:

    # XXX: or should we do this analysis on the IR side???
    visitor = FindAggregatingUses(
        stmt.group_binding.path_id,
        {x.path_id for x, _ in stmt.using.values()},
        ctx=ctx,
    )
    visitor.visit(stmt.result)
    # XXX: I think there are potentially issues with overlapping...
    group_uses = visitor.sightings

    # OK Actually compile now
    query = ctx.stmt

    # Compile a GROUP BY into a subquery, along with all the aggregations
    with ctx.subrel() as groupctx:
        grouprel = groupctx.rel

        # First compile the actual subject
        # subrel *solely* for path id map reasons
        with groupctx.subrel() as subjctx:
            subjctx.path_scope = subjctx.path_scope.new_child()
            # ???
            # MAYBE WE SHOULD SWIZZLE AROUND SUBREL
            subjctx.path_scope[stmt.subject.path_id] = None
            subjctx.expr_exposed = False

            dispatch.visit(stmt.subject, ctx=subjctx)
            if stmt.subject.path_id.is_objtype_path():
                # This shouldn't technically be needed but we generate
                # better code with it.
                relgen.ensure_source_rvar(
                    stmt.subject, subjctx.rel, ctx=subjctx)

        # XXX: aspects?
        subj_rvar = relctx.rvar_for_rel(
            subjctx.rel, ctx=groupctx, lateral=True)
        aspects = pathctx.list_path_aspects(
            subjctx.rel, stmt.subject.path_id, env=ctx.env)
        # update_mask=False because we are doing this solely to remap
        # elements individually and don't want to affect the mask.
        # ugh, this is hacking around the OH MY thing below
        # print("YEAAAAAH", aspects)
        ctx.env.shutup += 1
        relctx.include_rvar(
            grouprel, subj_rvar, stmt.group_binding.path_id,
            aspects=aspects,
            update_mask=False, ctx=groupctx)
        ctx.env.shutup -= 1
        relctx.include_rvar(
            grouprel, subj_rvar, stmt.subject.path_id,
            aspects=aspects,
            update_mask=False, ctx=groupctx)

        # OH MY.
        # We set up this mapping *after* compiling and including the rvar
        # under both names, because we need materialized things under
        # both paths to make it out.
        pathctx.put_path_id_map(
            subjctx.rel,
            stmt.group_binding.path_id, stmt.subject.path_id)

        # Now we compile the bindings
        groupctx.path_scope = subjctx.path_scope.new_child()
        # XXX: wait why
        groupctx.path_scope[stmt.group_binding.path_id] = None

        for _alias, (value, using_card) in stmt.using.items():
            # If the using bit is nullable, we need to compile it
            # as optional, or we'll get in trouble.
            # TODO: Can we do better here and not do this
            # in obvious cases like directly referencing an optional
            # property.
            if using_card.can_be_zero():
                groupctx.force_optional = ctx.force_optional | {value.path_id}
            # assert groupctx.path_scope[value.path_id] == ctx.rel
            # OK THIS IS WILDLY FUCKED
            for m in groupctx.path_scope.maps:
                if value.path_id in m:
                    del m[value.path_id]

            # groupctx.path_scope[value.path_id] = None  # ???
            dispatch.visit(value, ctx=groupctx)
            groupctx.force_optional = ctx.force_optional

        # XXX: OK there are some scary bits about this whole scheme....
        # Which is that... the source fields in these aggregates
        # can be any fucking thing
        groupctx.materializing |= {None}

        for group_use in group_uses:
            if not group_use:
                continue
            with groupctx.subrel() as hoistctx:
                # XXX: are there are other checks that need to be done
                # for this to be safe? Some sort of visibility check?
                hoistctx.skippable_sources |= (
                    visitor.count_logs.get(group_use, frozenset()))

                # XXX: do we need the rvars??
                relgen.process_set_as_agg_expr_inner(
                    group_use, hoistctx.rel,
                    aspect='value', wrapper=None, for_group_by=True,
                    ctx=hoistctx)
                pathctx.get_path_value_output(
                    rel=hoistctx.rel, path_id=group_use.path_id, env=ctx.env)
                pathctx.put_path_value_var(
                    grouprel, group_use.path_id, hoistctx.rel, env=ctx.env
                )

        groupctx.materializing -= {None}

        packed = False
        if None in group_uses:
            packed = True
            # OK WE NEED TO DO THE HARD THING
            # XXX: dupe with materialized stuff
            # XXX: Also, when all we do is serialize, we'd like to *just*
            # serialize...
            with context.output_format(ctx, context.OutputFormat.NATIVE), (
                    ctx.new()) as matctx:
                matctx.materializing |= {stmt}  # ...
                matctx.expr_exposed = True

                mat_qry = relgen.set_as_subquery(
                    stmt.group_binding, as_value=True, ctx=matctx)
                mat_qry = relctx.set_to_array(
                    path_id=stmt.group_binding.path_id,
                    for_group_by=True,
                    query=mat_qry,
                    ctx=matctx)
                if not mat_qry.target_list[0].name:
                    mat_qry.target_list[0].name = ctx.env.aliases.get('v')

                ref = pgast.ColumnRef(
                    name=[mat_qry.target_list[0].name],
                    is_packed_multi=True,
                )
                pathctx.put_path_packed_output(
                    mat_qry, stmt.group_binding.path_id, ref)

                pathctx.put_path_var(
                    grouprel, stmt.group_binding.path_id, mat_qry,
                    aspect='value',
                    flavor='packed', env=ctx.env
                )

        used_args = desugar_group.collect_grouping_atoms(stmt.by)

        if stmt.grouping_binding:
            _compile_grouping_binding(stmt, used_args=used_args, ctx=groupctx)

        # XXX: Is there a better way here? We want to make sure that every
        # grouping key is associated with exactly one output from
        # the query. The means that tuples must be packed up and
        # keys must not have an extra serialized output.
        #
        # We do this by manually packing up any TupleVarBases and
        # copying value aspects to serialized.
        # of the grouping keys get an extra serialized output from
        # grouprel, so we just copy all their value aspects to their
        # serialized aspects.
        using = {k: stmt.using[k] for k in used_args}
        for using_val, _ in using.values():
            uvar = pathctx.get_path_var(
                grouprel, using_val.path_id, aspect='value', env=ctx.env)
            if isinstance(uvar, pgast.TupleVarBase):
                uvar = output.output_as_value(uvar, env=ctx.env)
                pathctx.put_path_var(
                    grouprel, using_val.path_id, uvar,
                    aspect='value', force=True, env=ctx.env)

            uout = pathctx.get_path_output(
                grouprel, using_val.path_id, aspect='value', env=ctx.env)
            pathctx._put_path_output_var(
                grouprel, using_val.path_id, 'serialized', uout, env=ctx.env)

        grouprel.group_clause = [
            compile_grouping_el(el, stmt, ctx=groupctx) for el in stmt.by
        ]

    group_rvar = relctx.rvar_for_rel(grouprel, ctx=ctx, lateral=True)
    # ???
    if packed:
        relctx.include_rvar(
            query, group_rvar, path_id=stmt.group_binding.path_id,
            flavor='packed', update_mask=False, pull_namespace=False,
            aspects=('value',),  # maybe?
            ctx=ctx)
    # XXX: mask, aspects??
    else:
        # Not include_rvar because we don't actually provide the path id!
        relctx.rel_join(query, group_rvar, ctx=ctx)

    # Set up the hoisted aggregates and bindings to be found
    # in the group subquery.
    for group_use in [
        *group_uses,
        *[x for x, _ in stmt.using.values()],
        stmt.grouping_binding,
    ]:
        if group_use:
            pathctx.put_path_rvar(
                query, group_use.path_id,
                group_rvar, aspect='value', env=ctx.env)

    vol_ref = None

    def _get_volatility_ref() -> Optional[pgast.BaseExpr]:
        nonlocal vol_ref
        if vol_ref:
            return vol_ref

        name = ctx.env.aliases.get('key')
        grouprel.target_list.append(
            pgast.ResTarget(
                name=name,
                val=pgast.FuncCall(name=('row_number',), args=[],
                                   over=pgast.WindowDef())
            )
        )
        vol_ref = pgast.ColumnRef(name=[group_rvar.alias.aliasname, name])
        return vol_ref

    with ctx.new() as outctx:

        outctx.volatility_ref += (lambda stmt, xctx: _get_volatility_ref(),)

        # Process materialized sets
        clauses.compile_materialized_exprs(query, stmt, ctx=outctx)

        # ... right? It's that simple?
        clauses.compile_output(stmt.result, ctx=outctx)

    # XXX: duped from select?
    with ctx.new() as ictx:
        # FILTER and ORDER BY need to have the base result as a
        # volatility ref.
        clauses.setup_iterator_volatility(stmt.result, ctx=ictx)

        # The FILTER clause.
        if stmt.where is not None:
            query.where_clause = astutils.extend_binop(
                query.where_clause,
                clauses.compile_filter_clause(
                    stmt.where, stmt.where_card, ctx=ctx))

        # The ORDER BY clause
        if stmt.orderby is not None:
            with ctx.new() as ictx:
                query.sort_clause = clauses.compile_orderby_clause(
                    stmt.orderby, ctx=ictx)

    # XXX: bindings?

    return query


def compile_group(
        stmt: irast.GroupStmt, *,
        ctx: context.CompilerContextLevel) -> pgast.BaseExpr:
    with ctx.substmt() as sctx:
        return _compile_group(stmt, ctx=sctx, parent_ctx=ctx)
