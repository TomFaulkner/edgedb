#
# This source file is part of the EdgeDB open source project.
#
# Copyright 2012-present MagicStack Inc. and the EdgeDB authors.
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

import os.path

from edb.testbase import server as tb
from edb.tools import test


class TestEdgeQLGroup(tb.QueryTestCase):
    '''These tests are focused on using the internal GROUP statement.'''

    SCHEMA = os.path.join(os.path.dirname(__file__), 'schemas',
                          'issues.esdl')

    SCHEMA_CARDS = os.path.join(os.path.dirname(__file__), 'schemas',
                                'cards.esdl')

    SETUP = [
        os.path.join(os.path.dirname(__file__), 'schemas',
                     'issues_setup.edgeql'),
        'SET MODULE cards;',
        os.path.join(os.path.dirname(__file__), 'schemas',
                     'cards_setup.edgeql'),
    ]

    async def test_edgeql_group_simple_01(self):
        # XXX: key, also
        await self.assert_query_result(
            r'''
            GROUP cards::Card {name} BY .element
            ''',
            tb.bag([
                {
                    "elements": tb.bag(
                        [{"name": "Bog monster"}, {"name": "Giant turtle"}]),
                    "key": {"element": "Water"}
                },
                {
                    "elements": tb.bag([{"name": "Imp"}, {"name": "Dragon"}]),
                    "key": {"element": "Fire"}
                },
                {
                    "elements": tb.bag([{"name": "Dwarf"}, {"name": "Golem"}]),
                    "key": {"element": "Earth"}
                },
                {
                    "elements": tb.bag([
                        {"name": "Sprite"},
                        {"name": "Giant eagle"},
                        {"name": "Djinn"}
                    ]),
                    "key": {"element": "Air"}
                }
            ])
        )

    async def test_edgeql_group_simple_02(self):
        # XXX: key, also
        await self.assert_query_result(
            r'''
            SELECT (GROUP cards::Card {name} BY .element)
            ''',
            tb.bag([
                {
                    "elements": tb.bag(
                        [{"name": "Bog monster"}, {"name": "Giant turtle"}]),
                    "key": {"element": "Water"}
                },
                {
                    "elements": tb.bag([{"name": "Imp"}, {"name": "Dragon"}]),
                    "key": {"element": "Fire"}
                },
                {
                    "elements": tb.bag([{"name": "Dwarf"}, {"name": "Golem"}]),
                    "key": {"element": "Earth"}
                },
                {
                    "elements": tb.bag([
                        {"name": "Sprite"},
                        {"name": "Giant eagle"},
                        {"name": "Djinn"}
                    ]),
                    "key": {"element": "Air"}
                }
            ])
        )

    async def test_edgeql_group_simple_03(self):
        # XXX: key, also
        # the compilation here is kind of a bummer; could we avoid an
        # unnest?
        await self.assert_query_result(
            r'''
            SELECT (GROUP cards::Card {name} BY .element)
            FILTER .key.element != 'Air';
            ''',
            tb.bag([
                {
                    "elements": tb.bag(
                        [{"name": "Bog monster"}, {"name": "Giant turtle"}]),
                    "key": {"element": "Water"}
                },
                {
                    "elements": tb.bag([{"name": "Imp"}, {"name": "Dragon"}]),
                    "key": {"element": "Fire"}
                },
                {
                    "elements": tb.bag([{"name": "Dwarf"}, {"name": "Golem"}]),
                    "key": {"element": "Earth"}
                },
            ])
        )

    async def test_edgeql_group_process_01(self):
        await self.assert_query_result(
            r'''
            WITH MODULE cards
            SELECT (GROUP Card BY .element) {
                element := .key.element,
                cnt := count(.elements),
            };
            ''',
            tb.bag([
                {"cnt": 2, "element": "Water"},
                {"cnt": 2, "element": "Fire"},
                {"cnt": 2, "element": "Earth"},
                {"cnt": 3, "element": "Air"}
            ])
        )

    async def test_edgeql_group_process_02a(self):
        await self.assert_query_result(
            r'''
            WITH MODULE cards
            FOR g IN (GROUP Card BY .element) UNION (
                element := g.key.element,
                cnt := count(g.elements),
            );
            ''',
            tb.bag([
                {"cnt": 2, "element": "Water"},
                {"cnt": 2, "element": "Fire"},
                {"cnt": 2, "element": "Earth"},
                {"cnt": 3, "element": "Air"}
            ])
        )

    async def test_edgeql_group_process_02b(self):
        await self.assert_query_result(
            r'''
            WITH MODULE cards
            FOR g IN (SELECT (GROUP Card BY .element)) UNION (
                element := g.key.element,
                cnt := count(g.elements),
            );
            ''',
            tb.bag([
                {"cnt": 2, "element": "Water"},
                {"cnt": 2, "element": "Fire"},
                {"cnt": 2, "element": "Earth"},
                {"cnt": 3, "element": "Air"}
            ])
        )
