"""tools/hot_path_check.py on a fake tree: what it finds, and what it must not."""

from __future__ import annotations

import importlib.util
import json
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("hot_path_check",
                                              ROOT / "tools" / "hot_path_check.py")
hot_path_check = importlib.util.module_from_spec(SPEC)
sys.modules.setdefault("hot_path_check", hot_path_check)
SPEC.loader.exec_module(hot_path_check)

DIMENSIONS = {
    "seeds": {"fk-records": "N", "fk-jobs": "J"},
    "host_dispatchers": {"names": ["fnn-core"]},
    "cold_entries": {"words": ["open"], "served_words": ["connection"]},
    "resumable": {"note": "", "fk-bounded-walk recursion N": "at most 64 records per step"},
    "formal_seeds": {"fk-contact": {"offered": "J"}},
    "cuts": {"fk-shortcut": "the session carries the live state itself"},
}

BOOK = """
(defun fk-records (s) (declare (xargs :guard t)) (car s))
(defun fk-jobs (s) (declare (xargs :guard t)) (cdr s))

; A seeded list walked by len.
(defun fk-count (s) (declare (xargs :guard t)) (len (fk-records s)))

; A recursive walk of a formal bound to the seeded list.
(defun fk-sum (xs) (declare (xargs :guard t))
  (if (consp xs) (+ 1 (fk-sum (cdr xs))) 0))
(defun fk-total (s) (declare (xargs :guard t)) (fk-sum (fk-records s)))

; The logic branch walks, the executed branch does not.
(defun fk-last-count (s)
  (declare (xargs :guard t))
  (mbe :logic (len (fk-records s)) :exec (cdr (car s))))

; A guard that walks: evaluated when the host calls through a counterpart.
(defun fk-all-natp (xs) (declare (xargs :guard t))
  (if (consp xs) (and (natp (car xs)) (fk-all-natp (cdr xs))) (null xs)))
(defun fk-guarded (s)
  (declare (xargs :guard (fk-all-natp (fk-records s))))
  (car s))

; Called only at open.
(defun fk-rebuild (s) (declare (xargs :guard t)) (reverse (fk-records s)))

; Bounded by a quantum (named in the dimensions file).
(defun fk-bounded-walk (xs) (declare (xargs :guard t))
  (if (consp xs) (fk-bounded-walk (cdr xs)) nil))
(defun fk-step (s) (declare (xargs :guard t)) (fk-bounded-walk (fk-records s)))

; A formal seed: the host threads OFFERED.
(defun fk-contact (s offered) (declare (xargs :guard t))
  (if (member-equal (car s) offered) nil s))

; A cut: the walk under it is not descended.
(defun fk-shortcut (s live) (declare (xargs :guard t))
  (or (equal s live) (fk-total s)))

; Reached by no host line.
(defun fk-model-only (s) (declare (xargs :guard t)) (len (fk-jobs s)))
"""

HOST = """
(defun fk-host-count (state)
  (declare (xargs :stobjs state :mode :program))
  (fk-count (f-get-global 'fk-store state)))
(defun fk-host-total (state)
  (declare (xargs :stobjs state :mode :program))
  (fk-total (f-get-global 'fk-store state)))
(defun fk-host-last (state)
  (declare (xargs :stobjs state :mode :program))
  (fk-last-count (f-get-global 'fk-store state)))
(defun fk-host-open (state)
  (declare (xargs :stobjs state :mode :program))
  (fk-rebuild (f-get-global 'fk-store state)))
(defun fk-host-step (state)
  (declare (xargs :stobjs state :mode :program))
  (fk-step (f-get-global 'fk-store state)))
(defun fk-host-shortcut (state)
  (declare (xargs :stobjs state :mode :program))
  (fk-shortcut (f-get-global 'fk-store state) (f-get-global 'fk-live state)))
"""

NATIVE = """
(defun fnn-fk-guarded (store)
  (fnn-core 'fk-guarded store))
(defun fnn-fk-contact (store offered)
  (fnn-core 'fk-contact store offered))
"""

DRIVER = "fk-host-count fk-host-total fk-host-last fk-host-open fk-host-step " \
         "fk-host-shortcut fnn-fk-guarded fnn-fk-contact\n"


class FakeTree(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.directory = tempfile.TemporaryDirectory()
        root = Path(cls.directory.name)
        for relative, text in (("books/fk.lisp", BOOK), ("host/fk-host.lisp", HOST),
                               ("host/native/fk.lisp", NATIVE),
                               ("tests/drive.py", "# " + DRIVER),
                               ("tools/dims.json", json.dumps(DIMENSIONS))):
            (root / relative).parent.mkdir(parents=True, exist_ok=True)
            (root / relative).write_text(text)
        cls.root = root
        cls.analysis = hot_path_check.analyze(root, root / "tools" / "dims.json")
        cls.finds = cls.analysis.finds

    @classmethod
    def tearDownClass(cls) -> None:
        cls.directory.cleanup()

    def test_a_seeded_list_walked_by_len_is_found_with_its_host_line(self) -> None:
        find = self.finds["fk-count len N"]
        self.assertEqual(find.klass, "unexpected")
        self.assertEqual(set(find.entries), {"fk-host-count"})
        self.assertEqual(find.entries["fk-host-count"][0], "host/fk-host.lisp")

    def test_a_recursive_walk_of_a_bound_formal_is_found(self) -> None:
        find = self.finds["fk-sum recursion N"]
        self.assertIn("fk-host-total", find.entries)
        self.assertIn("fk-total", hot_path_check.path_text(find))

    def test_the_exec_branch_is_what_runs(self) -> None:
        # fk-last-count's :logic walks; its :exec does not; it is verified.
        self.assertFalse([key for key, find in self.finds.items()
                          if "fk-host-last" in find.entries])

    def test_a_guard_evaluated_by_a_counterpart_call_is_a_walk(self) -> None:
        find = self.finds["fk-all-natp recursion N"]
        self.assertEqual(set(find.entries), {"fnn-fk-guarded"})
        self.assertIn("fk-guarded#guard", find.via)

    def test_a_cold_entry_makes_a_cold_find(self) -> None:
        self.assertEqual(self.finds["fk-rebuild reverse N"].klass, "cold")

    def test_a_named_bound_makes_a_resumable_find(self) -> None:
        find = self.finds["fk-bounded-walk recursion N"]
        self.assertEqual(find.klass, "resumable")
        self.assertEqual(find.bound, "at most 64 records per step")

    def test_a_formal_seed_carries_its_dimension(self) -> None:
        self.assertEqual(set(self.finds["fk-contact member-equal J"].entries),
                         {"fnn-fk-contact"})

    def test_a_cut_is_not_descended_and_is_reported(self) -> None:
        self.assertFalse([key for key, find in self.finds.items()
                          if "fk-host-shortcut" in find.entries])
        self.assertIn("fk-shortcut", self.analysis.cuts)

    def test_an_unreached_walk_is_not_a_find(self) -> None:
        self.assertNotIn("fk-model-only len J", self.finds)

    def test_strict_names_new_and_stale_finds(self) -> None:
        listed = {key: {"packet": "PKT-0"} for key in self.finds}
        self.assertEqual(hot_path_check.compare(self.analysis, listed), ([], []))
        del listed["fk-count len N"]
        listed["fk-gone len N"] = {"packet": "PKT-0"}
        fresh, stale = hot_path_check.compare(self.analysis, listed)
        self.assertEqual(fresh, ["fk-count len N"])
        self.assertEqual(stale, ["fk-gone len N"])


class RealTree(unittest.TestCase):
    def test_every_find_on_the_tree_is_listed_with_a_packet(self) -> None:
        analysis = hot_path_check.analyze()
        listed = hot_path_check.load_findings()
        self.assertEqual(hot_path_check.compare(analysis, listed), ([], []))
        for key, row in listed.items():
            self.assertTrue(row.get("packet"), key)


if __name__ == "__main__":
    unittest.main()
