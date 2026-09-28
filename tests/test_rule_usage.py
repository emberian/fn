"""tools/rule_usage.py: what dependents use, and include rewires simulated on the graph."""
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))

import rule_usage                                             # noqa: E402

LOG = """Summary
Form:  ( DEFTHM FN-B-KEEPS ...)
Rules: ((:DEFINITION FN-A-DEF)
        (:REWRITE FN-BASE-LEMMA)
        (:EXECUTABLE-COUNTERPART TAU-SYSTEM))
Hint-events: ((:USE FN-BASE-OTHER))
Time:  0.00 seconds
"""


class Stub(rule_usage.Map):
    """A Map over a hand-written graph, sources and logs (no tree, no run)."""

    def __init__(self, graph, sources, logs):
        self.root = Path("/nonexistent")
        self.graph = graph
        self.included_by = {}
        for book, includes in graph.items():
            for dependency in includes:
                self.included_by.setdefault(dependency, set()).add(book)
        self.logs = {}
        self._sources = sources
        self._logs = logs
        self._used, self._tokens, self._exports = {}, {}, {}
        self._external = set()

    def used(self, book):
        return self._logs.get(book)

    def source_text(self, book):
        return self._sources.get(book, "")

    def tokens(self, book):
        return set(self._sources.get(book, "").split())

    def exports(self, book):
        if book == "books/top":                 # top defines nothing; its source is its uses
            return [], []
        names = self._sources.get(book, "").split()
        return ([n for n in names if n.endswith("-lemma")], [n for n in names if n.endswith("-def")])


# base <- mid <- top; top also includes side, which includes base.
GRAPH = {"books/base": [], "books/mid": ["books/base"], "books/side": ["books/base"],
         "books/top": ["books/mid", "books/side"], "books/leaf": []}


class LogTests(unittest.TestCase):
    def test_runes_and_hint_events_are_the_used_names(self):
        self.assertEqual(rule_usage.log_names(LOG),
                         {"fn-a-def", "fn-base-lemma", "tau-system", "fn-base-other"})

    def test_strings_comments_and_character_literals_name_nothing(self):
        with tempfile.NamedTemporaryFile("w", suffix=".lisp", delete=False) as handle:
            handle.write('(defun fn-x (a) "uses fn-in-doc" (list #\\" a)) ; fn-in-comment\n'
                         '#| fn-in-block |# (fn-real a)\n')
        tokens = rule_usage.source_tokens(Path(handle.name))
        self.assertIn("fn-real", tokens)
        self.assertIn("fn-x", tokens)
        for hidden in ("fn-in-doc", "fn-in-comment", "fn-in-block"):
            self.assertNotIn(hidden, tokens)


class GraphTests(unittest.TestCase):
    def test_chain_position_counts_levels_below_and_above(self):
        position = rule_usage.chain_position(GRAPH)
        self.assertEqual(position["books/base"], (1, 3))
        self.assertEqual(position["books/top"], (3, 1))
        self.assertEqual(position["books/leaf"], (1, 1))

    def test_a_rewire_is_two_graph_keys_and_never_a_self_include(self):
        self.assertEqual(rule_usage.parse_rewire("books/cbor.lisp:-./books/defrecord"),
                         ("books/cbor", "-", "books/defrecord"))
        with self.assertRaises(SystemExit):
            rule_usage.parse_rewire("books/cbor:+books/cbor")
        with self.assertRaises(SystemExit):
            rule_usage.parse_rewire("books/cbor")


class SimulateTests(unittest.TestCase):
    def usage(self, top_source):
        sources = {"books/base": "fn-base-def fn-base-lemma", "books/mid": "fn-mid-def",
                   "books/side": "fn-side-def", "books/top": top_source}
        return Stub(GRAPH, sources, {"books/top": {"fn-base-lemma"}})

    def test_a_dead_include_drops_the_book_from_the_includers_closure(self):
        usage = self.usage("fn-side-def")
        result = rule_usage.simulate(usage, ["books/top:-books/mid"], ["books/mid"])
        self.assertEqual(result["before"]["books"]["books/mid"]["dependents"], 1)
        self.assertEqual(result["after"]["books"]["books/mid"]["dependents"], 0)
        self.assertEqual(result["lost_uses"]["books/top"]["uses"], {})

    def test_a_used_name_is_reported_and_fixup_restores_its_book(self):
        usage = self.usage("fn-mid-def")
        result = rule_usage.simulate(usage, ["books/top:-books/mid"], ["books/mid"])
        self.assertEqual(result["lost_uses"]["books/top"]["uses"], {"fn-mid-def": ["books/mid"]})
        fixed = rule_usage.simulate(usage, ["books/top:-books/mid"], ["books/mid"], fixup=True)
        self.assertEqual(fixed["fixups"], ["books/top:+books/mid"])
        self.assertEqual(fixed["after"]["books"]["books/mid"]["dependents"], 1)

    def test_a_name_still_reached_another_way_is_not_lost(self):
        # top applied fn-base-lemma; base stays in its closure through side.
        usage = self.usage("fn-side-def")
        result = rule_usage.simulate(usage, ["books/top:-books/mid"], [])
        self.assertNotIn("fn-base-lemma", result["lost_uses"]["books/top"]["uses"])

    def test_weighted_chain_follows_the_seconds(self):
        usage = self.usage("fn-side-def")
        walls = {"books/base": 1.0, "books/mid": 5.0, "books/side": 2.0, "books/top": 1.0,
                 "books/leaf": 0.5}
        result = rule_usage.simulate(usage, ["books/top:-books/mid"], [], walls)
        self.assertEqual(result["before"]["weighted_chain"], ["books/top", "books/mid", "books/base"])
        self.assertEqual(result["before"]["weighted_chain_seconds"], 7.0)
        # mid (5 s) still ends a chain of its own: mid, base.
        self.assertEqual(result["after"]["weighted_chain"], ["books/mid", "books/base"])
        self.assertEqual(result["after"]["weighted_chain_seconds"], 6.0)


if __name__ == "__main__":
    unittest.main()
