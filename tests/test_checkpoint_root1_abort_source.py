"""Source-only controls for exact root1 cancellation; no ACL2/IO execution."""
import sys
import unittest
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
from lisp_source import forms, read_sexp
BOOK = Path(__file__).resolve().parents[1] / "books/checkpoint-metadata-abort.lisp"


def trees(source):
    return [read_sexp(text) for text in forms(source)]


def nodes(tree):
    if isinstance(tree, list):
        yield tree
        for child in tree:
            yield from nodes(child)


def definitions(source):
    return {tree[1]: tree for tree in trees(source)
            if isinstance(tree, list) and tree and tree[0] == "defun"}


def names(tree):
    return [n[0] for n in nodes(tree) if n and isinstance(n[0], str)]


def has_reset_authority(source):
    body = definitions(source)["fn2-checkpoint-root1-abort-reset"]
    calls = names(body)
    return all(name in calls for name in ("fn2-checkpoint-build-abort-ownerp", "fn2-checkpoint-build-abort-row",
                                          "fn2-checkpoint-root1-abort-windows-p", "fn2-checkpoint-root1-abort-future-p",
                                          "fn2-checkpoint-page-pending", "fn2-checkpoint-page-transferred",
                                          "fn2-checkpoint-semantic-pending", "fn2-checkpoint-payload-pending")) \
        and "*fn2-checkpoint-build-phase-cancelled*" in str(body)


class Root1AbortSource(unittest.TestCase):
    def test_actual_cancel_and_operation_quiescence_are_required(self):
        source = BOOK.read_text()
        self.assertTrue(has_reset_authority(source))
        self.assertFalse(has_reset_authority(source.replace("fn2-checkpoint-build-abort-ownerp", "missing-cancel-authority")))
        reset = definitions(source)["fn2-checkpoint-root1-abort-reset"]
        self.assertEqual(reset[2][:5], ["budget", "token", "kind", "owner", "gen"])
        self.assertNotIn("fn2-pool-release", names(reset))
        self.assertNotIn("fn2-core-release-children", names(reset))

    def test_all_named_windows_are_owned_and_future_borrows_returned(self):
        defs = definitions(BOOK.read_text())
        own = defs["fn2-checkpoint-root1-abort-windows-p"]
        future = defs["fn2-checkpoint-root1-abort-future-p"]
        self.assertIn("fn2-pool-workspace-code", names(own))
        self.assertIn("*fn2-checkpoint-window-count*", str(own))
        self.assertIn("fn2-pool-workspace-code", names(future))
        self.assertIn("fn2-checkpoint-future-windows-borrowed", names(future))
        self.assertIn("*fn2-checkpoint-future-window-count*", str(future))

    def test_parent_authorities_and_hash_bytes_are_not_modified(self):
        reset = definitions(BOOK.read_text())["fn2-checkpoint-root1-abort-reset"]
        for name in names(reset[4:]):
            self.assertFalse(any(name.startswith(prefix) for prefix in
                             ("fn2-checkpoint-build-set-", "fn2-checkpoint-build-put", "fn2-checkpoint-planning-set-",
                              "fn2-checkpoints-set-", "fn2-extents-set-", "fn2-alloc-", "fn2-b3-init", "fn2-digest-set-")), name)
        self.assertIn("fn2-csnapshot-set-complete", names(reset))
        self.assertNotIn("fn2-csnapshot-set-phase", names(reset))
        self.assertNotIn("fn2-csnapshot-set-token", names(reset))
        self.assertNotIn("fn2-checkpoint-retained-entry-set-serial", names(reset))

    def test_all_changed_carriers_survive_and_result_width_is_supported(self):
        source = BOOK.read_text()
        macro = next(tree for tree in trees(source)
                     if isinstance(tree, list) and tree[:2] == ["defmacro", "fn2-checkpoint-root1-abort-mv"])
        mv = next(n for n in nodes(macro) if n and n[0] == "mv")
        outputs = {n for n in mv[2:] if isinstance(n, str) and n.startswith("fn2-")}
        reset = definitions(source)["fn2-checkpoint-root1-abort-reset"]
        assigned = set()
        for node in nodes(reset[3:]):
            if node and node[0] in ("b*", "let", "let*") and isinstance(node[1], list):
                for binding in node[1]:
                    if isinstance(binding, list) and binding and isinstance(binding[0], str) and binding[0].startswith("fn2-"):
                        assigned.add(binding[0])
        self.assertEqual(outputs, assigned)
        self.assertEqual(len(outputs) + 1, 16)
        self.assertLessEqual(len(outputs) + 1, 32)
        terminal = definitions(source)["fn2-checkpoint-root1-abort-reset-p"]
        self.assertIn("fn2-checkpoint-root1-abort-row", names(terminal))
        self.assertIn("*fn2-checkpoint-root1-abort-phase-complete*", str(terminal))

    def test_prepared_interleaving_uses_actual_io_and_cancel_methods(self):
        fixture = BOOK.parent.parent / "tests/checkpoint-root1-abort-unit.lisp"
        defs = definitions(fixture.read_text())
        body = defs["fn2-cra-body"]
        calls = names(body)
        self.assertIn("fn2-block-read", calls)
        self.assertIn("fn2-cra-clean-loop", calls)
        self.assertEqual(calls.count("fn2-harvest-one"), 2)
        self.assertEqual(calls.count("fn2-cra-reset-step"), 2)
        self.assertLess(calls.index("fn2-cra-clean-loop"), calls.index("fn2-cra-reset-step"))
        self.assertLess(calls.index("fn2-harvest-one"), calls.index("fn2-cra-reset-loop"))
        self.assertIn("fn2-checkpoint-planning-cancel-step", names(defs["fn2-cra-cancel-step"]))
        self.assertIn("fn2-checkpoint-build-abort-step", names(defs["fn2-cra-clean-step"]))
        self.assertIn("fn2-post-result", names(defs["fn2-cra-post"]))
        self.assertIn("fn2-outbox-ack", names(defs["fn2-cra-ack"]))
        observe = defs["fn2-cra-observe"]
        for field in ("fn2-extents-outstanding-io", "fn2-checkpoint-semantic-pending", "fn2-checkpoint-payload-pending",
                      "fn2-alloc-freeze-phase", "fn2-csnapshot-complete"):
            self.assertIn(field, names(observe))


if __name__ == "__main__":
    unittest.main()
