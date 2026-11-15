"""Actual cold DFS source-boundary controls; these do not run ACL2 or hashes."""
import sys
import unittest
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
from lisp_source import forms, read_sexp
ROOT = Path(__file__).resolve().parents[1]


def definitions(path):
    return {node[1]: node for text in forms((ROOT / path).read_text())
            if isinstance((node := read_sexp(text)), list) and node and node[0] == "defun"}


def walk(node):
    if isinstance(node, list):
        yield node
        for child in node:
            yield from walk(child)


def calls(node):
    return [n[0] for n in walk(node) if n and isinstance(n[0], str)]


def closed_identity_complete(source):
    names = calls(source)
    return all("fn2-checkpoint-restore-semantic-work-" + field in names
               for field in ("unit", "epoch", "allocation", "page-kind", "schema", "run", "level",
                             "expected-known", "expected-count", "directory", "source", "filter")) \
        and "fn2-checkpoint-restore-semantic-hash-equal" in names


class SemanticDfsSource(unittest.TestCase):
    def setUp(self):
        self.work = definitions("books/checkpoint-restore-semantic-work.lisp")
        self.page = definitions("books/checkpoint-restore-semantic.lisp")

    def test_closed_alias_requires_full_identity_and_gray_cycle_precedes_mutation(self):
        enqueue = self.work["fn2-checkpoint-restore-semantic-enqueue"]
        self.assertTrue(closed_identity_complete(enqueue))
        # Remove the actual equality helper, rather than declaring a caller flag.
        def damage(node):
            if not isinstance(node, list):
                return node
            return [] if node and node[0] == "fn2-checkpoint-restore-semantic-hash-equal" else [damage(n) for n in node]
        damaged = damage(enqueue)
        self.assertFalse(closed_identity_complete(damaged))
        body = next(n for n in walk(enqueue[3:]) if n and n[0] == "b*")
        cycle = next(i for i, binding in enumerate(body[1]) if ":cycle" in str(binding))
        write = next(i for i, binding in enumerate(body[1]) if "fn2-checkpoint-restore-semantic-work-put" in calls(binding))
        self.assertLess(cycle, write)

    def test_parent_close_and_pop_depend_on_actual_descendant_closure(self):
        consume = self.work["fn2-checkpoint-restore-semantic-consume"]
        end = next(n for n in walk(consume) if n and n[0] == ["when", ["eq", "code", ":page-end"]])
        self.assertIn("fn2-checkpoint-restore-semantic-seen", calls(end))
        self.assertIn("fn2-checkpoint-restore-semantic-expected-count", calls(end))
        self.assertIn("fn2-checkpoint-restore-semantic-track", calls(consume))
        track = self.work["fn2-checkpoint-restore-semantic-track"]
        self.assertIn("fn2-checkpoint-restore-semantic-work-waiting", calls(track))
        find = self.work["fn2-checkpoint-restore-semantic-find"]
        text = str(find)
        self.assertIn("*fn2-checkpoint-restore-semantic-work-state-closed*", text)
        self.assertIn("*fn2-checkpoint-restore-semantic-work-state-gray*", text)
        self.assertIn("fn2-checkpoint-restore-semantic-work-child", calls(find))
        self.assertNotIn("fn2-block-read-children", calls(find))

    def test_one_window_parent_resume_reauthenticates_before_saved_cursor(self):
        find = self.work["fn2-checkpoint-restore-semantic-find"]
        self.assertIn("fn2-pool-reset", calls(find))
        self.assertIn("fn2-checkpoint-restore-semantic-work-hash-copy", calls(find))
        self.assertIn("fn2-checkpoint-restore-semantic-work-cursor", calls(find))
        page = self.page["fn2-checkpoint-restore-semantic-page"]
        self.assertIn("fn2-format-run", calls(page))
        self.assertIn("fn2-checkpoint-semantic-page-read-header", calls(page))
        self.assertIn("fn2-checkpoint-restore-semantic-resume", calls(page))
        self.assertIn("fn2-checkpoint-restore-semantic-entries", calls(page))
        self.assertIn("*fn2-run-max-levels*", str(page))
        self.assertIn("fn2-ribbon-read-header", calls(page))
        state = (ROOT / "books/checkpoint-restore-semantic-state.lisp").read_text()
        self.assertNotIn("pending-head", state)
        self.assertIn("(:empty :gray :closed)", state)

    def test_root_filter_and_payload_remain_separate_actual_closures(self):
        consume = self.work["fn2-checkpoint-restore-semantic-consume"]
        text = str(consume)
        self.assertIn(":payload-required", text)
        self.assertIn("fn2-checkpoint-restore-semantic-entry-stage", calls(consume))
        self.assertIn("*page-kind-partitioned-filter*", text)
        self.assertIn("*fn2-manifest-entry-field-filter-hash*", text)
        self.assertIn("fn2-checkpoint-semantic-page-child-p", calls(consume))
        self.assertIn("fn2-run-layout-page-kind", calls(consume))

    def test_cost_bound_comes_from_registered_entry_and_index_codecs(self):
        assembly = definitions("books/runs-assemble.lisp")
        sizes = assembly["fn2-ra-layout-max-sizes"]
        self.assertEqual(calls(sizes).count("fn2-codec-constant"), 2)
        source = (ROOT / "books/checkpoint-restore-semantic-work.lisp").read_text()
        self.assertIn("*fn2-run-restart-interval* *fn2-run-layout-max-entry-bytes*", source)
        reach = (ROOT / "books/checkpoint-restore-semantic-reach.lisp").read_text()
        self.assertIn("*fn2-checkpoint-restore-reach-role-semantic-source*", reach)


if __name__ == "__main__":
    unittest.main()
