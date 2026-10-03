"""tools/lock_discipline_check.py: positive and negative structural fixtures.

Each fixture is a small host source read with the real contracts file
(tools/lock_discipline_contracts.json), so a fixture exercises the same lock
table, leaves, borrows and wrappers the tree is checked against.  The
negative fixtures are the shapes of this week's defects (r31 F1/F2, the
committer catch, the publisher's early deregistration, the adopt push, r67
F2's I/O under the owner); each positive twin is the repaired shape.
"""
import os
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import lock_discipline_check as ldc  # noqa: E402

CONTRACTS = ldc.load_contracts(ROOT / "tools" / "lock_discipline_contracts.json")

PRELUDE = """
(define-condition fnn-store-error (error) ())
(define-condition fnn-store-fault (fnn-store-error) ())
(define-condition fnn-store-indeterminate (fnn-store-error) ())
(defvar *fnn-extent-lock* (sb-thread:make-mutex :name "x"))
(defvar *fnn-extent-fds* (make-hash-table)) ; guarded-by: *fnn-extent-lock* (fds)
(defun fnn-fault (control) (error 'fnn-store-fault :message control))
(defun fnn-owner-stop-service-locked (service code) (setf (fnn-owner-service-stopping service) code))
(defun fnn-live-arena () *fnn-arena*)
(defun fnn-close (fd) (sb-posix:close fd))
"""


def run(source, rules=None, reach=None):
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        (root / "host" / "native").mkdir(parents=True)
        (root / "host" / "native" / "fixture.lisp").write_text(PRELUDE + source)
        an, model, checker = ldc.analyze_tree(root, CONTRACTS, ["host/native/fixture.lisp"], reach or {})
        found = checker.run(set(rules) if rules else None)
        return [f for f in found if f.category != "exception"]


def keys(findings, rule):
    return [(f.function, f.key) for f in findings if f.rule == rule]


class R3Reads(unittest.TestCase):
    NAKED = """
(defun fnn-extent-prefetch-direct (file eoff)
  (let ((fd nil) (octets (make-array 10)))
    (sb-thread:with-mutex (*fnn-extent-lock* :wait-p t)
      (setq fd (gethash file *fnn-extent-fds*)))
    (fnn-extent-pread fd octets eoff)))
(defun fnn-owner-cold-line-direct (entry)
  (sb-thread:make-thread (lambda () (apply #'fnn-extent-prefetch-direct entry)) :name "fn cold extent"))
"""

    def test_r31_f1_naked_offlock_pread_is_refused(self):
        found = run(self.NAKED, ["R3"])
        self.assertIn(("fnn-extent-prefetch-direct", "naked:fnn-extent-pread"), keys(found, "R3"))

    def test_r31_f2_per_miss_thread_is_undeclared(self):
        found = run(self.NAKED, ["R4"])
        self.assertTrue(any(k[1].startswith("undeclared:") for k in keys(found, "R4")))

    def test_read_inside_the_lock_that_found_the_descriptor_passes(self):
        src = """
(defun fnn-extent-read-locked (file eoff)
  (sb-thread:with-mutex (*fnn-extent-lock* :wait-p t)
    (fnn-extent-pread (gethash file *fnn-extent-fds*) (make-array 10) eoff)))
"""
        self.assertEqual(keys(run(src, ["R3"]), "R3"), [])

    ISSUED = """
(defun fnn-extent-issue-direct (file)
  (sb-thread:with-mutex (*fnn-extent-lock* :wait-p t)
    (fnn-core 'fn-pio-direct-admit file)))
(defun fnn-extent-prefetch (token)
  (let ((fd nil))
    (sb-thread:with-mutex (*fnn-extent-lock* :wait-p t)
      (setq fd (gethash (first token) *fnn-extent-fds*)))
    (fnn-extent-pread fd (make-array 10) 0)))
(defun fnn-extent-executor-actual-return (worker) worker)
(defun fnn-extent-executor-job (worker)
  (handler-case (fnn-extent-prefetch worker)
    (serious-condition (c) c)))
(defun fnn-extent-executor-loop (worker)
  (loop
    (fnn-extent-executor-job worker)
    (sb-thread:with-mutex (*fnn-extent-lock*)
      (fnn-extent-executor-actual-return worker))))
"""

    def test_issued_row_protocol_passes(self):
        self.assertEqual([k for k in keys(run(self.ISSUED, ["R3"]), "R3") if k[0] == "fnn-extent-prefetch"], [])

    def test_removing_the_hold_fails(self):
        src = self.ISSUED.replace("      (fnn-extent-executor-actual-return worker))))", "      worker)))")
        self.assertIn(("fnn-extent-prefetch", "borrow:fnn-extent-pread"), keys(run(src, ["R3"]), "R3"))

    def test_release_before_return_fails(self):
        src = self.ISSUED.replace(
            "    (fnn-extent-executor-job worker)\n    (sb-thread:with-mutex (*fnn-extent-lock*)\n"
            "      (fnn-extent-executor-actual-return worker))))",
            "    (sb-thread:with-mutex (*fnn-extent-lock*)\n      (fnn-extent-executor-actual-return worker))\n"
            "    (fnn-extent-executor-job worker)))")
        self.assertIn(("fnn-extent-prefetch", "borrow:fnn-extent-pread"), keys(run(src, ["R3"]), "R3"))

    def test_a_new_caller_of_the_borrow_fails(self):
        src = self.ISSUED + "(defun fnn-elsewhere (tok) (fnn-extent-prefetch tok))\n"
        self.assertIn(("fnn-extent-prefetch", "borrow:fnn-extent-pread"), keys(run(src, ["R3"]), "R3"))

    LEASE = """
(defun fnn-extent-discovery-release (token) token)
(defun fnn-snapshot-source-read-page (root request)
  (let ((fd nil) (token nil) (handed-off nil))
    (sb-thread:with-mutex (*fnn-extent-lock*)
      (setq token (fnn-core-page-read-pool 'fn-owner-page-file-pin-read root request)
            fd (gethash (second token) *fnn-extent-fds*)))
    (unwind-protect
         (progn (fnn-extent-pread fd (make-array 10) 0) (setq handed-off t))
      (unless handed-off
        (sb-thread:with-mutex (*fnn-extent-lock*) (fnn-extent-discovery-release token))))))
"""

    def test_snapshot_file_pin_passes(self):
        self.assertEqual(keys(run(self.LEASE, ["R3"]), "R3"), [])

    def test_file_pin_released_before_the_read_fails(self):
        src = self.LEASE.replace("    (unwind-protect\n",
                                 "    (fnn-extent-discovery-release token)\n    (unwind-protect\n")
        self.assertIn(("fnn-snapshot-source-read-page", "borrow:fnn-extent-pread"), keys(run(src, ["R3"]), "R3"))


class R2Blocking(unittest.TestCase):
    def test_io_under_the_owner_is_refused_and_the_no_io_branch_is_followed(self):
        src = """
(defvar *fnn-extent-no-io* nil)
(defun fnn-extent-entry (f)
  (if *fnn-extent-no-io* (throw 'cold f) (fnn-extent-pread f (make-array 1) 0)))
(defun fnn-quantum (service f)
  (sb-thread:with-mutex ((fnn-owner-service-lock service)) (fnn-extent-entry f)))
(defun fnn-quantum-no-io (service f)
  (sb-thread:with-mutex ((fnn-owner-service-lock service))
    (let ((*fnn-extent-no-io* t)) (fnn-extent-entry f))))
"""
        found = [f for f in run(src, ["R2"]) if f.rule == "R2"]
        self.assertEqual(len(found), 1)
        self.assertIn("fnn-quantum ", found[0].message + " ")
        self.assertEqual(found[0].weight, 1)

    def test_condition_wait_releases_only_its_own_mutex(self):
        src = """
(defun fnn-wait-alone (service)
  (sb-thread:with-mutex ((fnn-owner-service-commit-lock service))
    (sb-thread:condition-wait (fnn-owner-service-commit-ready service) (fnn-owner-service-commit-lock service))))
(defun fnn-wait-under-owner (service)
  (sb-thread:with-mutex ((fnn-owner-service-lock service)) (fnn-wait-alone service)))
"""
        found = [f for f in run(src, ["R2"]) if f.rule == "R2"]
        self.assertEqual([f.key for f in found], ["O:sb-thread:condition-wait"])

    def test_a_core_call_reaching_a_realizer_through_acl2(self):
        src = """
(defun fn-durable-realize-octets (f)
  (sb-thread:with-mutex (*fnn-extent-lock*) (fnn-extent-pread f (make-array 1) 0)))
(defun fnn-owner-cursor-step (service plan)
  (sb-thread:with-mutex ((fnn-owner-service-lock service)) (fnn-call 'fn-splan-cursor-step plan)))
"""
        reach = {"fn-splan-cursor-step": {"fn-durable-realize-octets": "fn-arena-get"},
                 "fn-arena-get": {"fn-durable-realize-octets": "fn-durable-realize-octets"},
                 "fn-durable-realize-octets": {"fn-durable-realize-octets": "fn-durable-realize-octets"}}
        found = [f for f in run(src, ["R2"], reach) if f.rule == "R2" and f.key == "O:fnn-extent-pread"]
        self.assertEqual(len(found), 1)
        self.assertIn("fn-splan-cursor-step -> fn-arena-get", "\n".join(found[0].trail))


class R1State(unittest.TestCase):
    def test_a_thread_reading_owner_state_off_the_mutex_is_refused(self):
        src = """
(defun fnn-reader (service) (fnn-live-arena))
(defun fnn-spawn (service) (sb-thread:make-thread (lambda () (fnn-reader service)) :name "t"))
"""
        found = run(src, ["R1"])
        self.assertTrue(any("fnn-live-arena" in f.key for f in found if f.rule == "R1"))

    def test_the_serialized_thunk_holds_the_owner(self):
        src = """
(defun fnn-owner-shared-action-locked (service cid thunk) (funcall thunk))
(defun fnn-owner-serialized (service cid thunk &optional (class :control))
  (sb-thread:with-mutex ((fnn-owner-service-lock service))
    (fnn-owner-shared-action-locked service cid thunk)))
(defun fnn-spawn (service)
  (sb-thread:make-thread
   (lambda () (fnn-owner-serialized service nil (lambda () (fnn-live-arena)))) :name "t"))
"""
        self.assertEqual([f for f in run(src, ["R1"]) if f.rule == "R1"], [])

    def test_a_stored_callback_does_not_inherit_its_creators_lock(self):
        src = """
(defvar *hooks* nil)
(defun fnn-register (service)
  (sb-thread:with-mutex ((fnn-owner-service-lock service))
    (push (lambda () (fnn-live-arena)) *hooks*)))
"""
        # the stored lambda is its own root with a fresh lockset: the owner
        # lock its creator held does not cover the later call
        found = [f for f in run(src, ["R1"]) if f.rule == "R1"]
        self.assertTrue(any(f.function.startswith("lambda@") and "fnn-live-arena" in f.key for f in found))


class R7Failure(unittest.TestCase):
    COMMITTER = """
(defun fnn-pipeline (service) (fnn-core 'fn-otb-issue service))
(defun fnn-committer-loop (service)
  (handler-case (fnn-pipeline service)
    (fnn-store-error () nil)
    (serious-condition (e) (fnn-owner-fault-service service nil e))))
(defun fnn-owner-fault-service (service cid e) (fnn-owner-stop-service-locked service 4))
(defun fnn-start (service) (sb-thread:make-thread (lambda () (fnn-committer-loop service)) :name "c"))
"""

    def test_a_parent_catch_that_swallows_fault_and_indeterminate(self):
        found = run(self.COMMITTER, ["R7"])
        self.assertTrue(any(f.function == "fnn-committer-loop" and f.key.startswith("swallow:fnn-store-error")
                            for f in found))

    def test_routing_the_core_classes_first_passes(self):
        src = self.COMMITTER.replace(
            "    (fnn-store-error () nil)",
            "    (fnn-store-indeterminate (e) (fnn-owner-stop-service-locked service 3) (error e))\n"
            "    (fnn-store-fault (e) (fnn-owner-fault-service service nil e))\n"
            "    (fnn-store-error () nil)")
        found = [f for f in run(src, ["R7"]) if f.function == "fnn-committer-loop"]
        self.assertEqual(found, [])


class R4Threads(unittest.TestCase):
    def test_deregistration_before_terminal_shared_work(self):
        src = """
(defun fnn-arena-unpin (pin) (sb-thread:with-mutex (*fnn-arena-pins-lock*) pin))
(defun fnn-publish (service pin)
  (sb-thread:with-mutex ((fnn-owner-service-roster service))
    (setf (fnn-owner-service-workers service)
          (delete sb-thread:*current-thread* (fnn-owner-service-workers service))))
  (fnn-arena-unpin pin))
"""
        found = run(src, ["R4"])
        self.assertTrue(any(f.key.startswith("dereg-before-cleanup") for f in found))

    def test_a_nil_registered_worker(self):
        src = """
(defun fnn-owner-maybe-publish-quantum (service ok)
  (sb-thread:with-mutex ((fnn-owner-service-roster service))
    (let ((thread (and ok (sb-thread:make-thread (lambda () (handler-case 1 (serious-condition () 2))) :name "p"))))
      (push thread (fnn-owner-service-workers service)))))
"""
        found = run(src, ["R4"])
        self.assertTrue(any(f.key.startswith("nil-registered") for f in found))


class R5R6R8R10(unittest.TestCase):
    def test_an_inverted_edge(self):
        src = """
(defun fnn-inverted (service)
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (sb-thread:with-mutex ((fnn-owner-service-lock service)) 1)))
"""
        found = run(src, ["R5"])
        self.assertTrue(any(f.key == "E->O" and "INVERTS" in f.message for f in found))

    def test_dispatch_administration_takes_no_lock(self):
        src = """
(defvar *specs* (make-hash-table :synchronized t))
(defun fnn-entry-guard (name) (sb-thread:with-mutex (*fnn-extent-lock*) name))
(defun fnn-call (name &rest args) (fnn-entry-guard name) (apply name args))
"""
        found = run(src, ["R6"])
        self.assertTrue(any(f.function == "fnn-entry-guard" for f in found))

    def test_push_into_an_inbox_without_a_lifecycle_check(self):
        src = """
(defstruct (fnn-mux-loop) lock inbox)
(defun fnn-mux-adopt (loop socket)
  (sb-thread:with-mutex ((fnn-mux-loop-lock loop))
    (push socket (fnn-mux-loop-inbox loop))))
"""
        self.assertTrue(any(f.rule == "R8" for f in run(src, ["R8"])))

    def test_a_swallowed_close(self):
        src = """
(defvar *fnn-owner-log-fd* nil)
(defun fnn-log-swap-fd (fd)
  (let ((old *fnn-owner-log-fd*))
    (setq *fnn-owner-log-fd* fd)
    (when old (ignore-errors (fnn-close old)))))
"""
        found = run(src, ["R10"])
        self.assertTrue(any(f.key == "ignored-close:fnn-close" for f in found))


class Realization(unittest.TestCase):
    CLOSE = """
(defun fnn-extent-close (ids)
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (dolist (id ids)
      (when (fnn-core 'fn-pio-file-clear-p id)
        (fnn-close (gethash id *fnn-extent-fds*))))))
"""
    ROW = {"label": ":close", "layer": "C", "enabled": [], "sites": [
        {"function": "fnn-extent-close", "file": "host/native/fixture.lisp", "primitive": "fnn-close",
         "core": None, "locks_held": ["E"], "requires_before": ["fn-pio-file-clear-p"]}]}

    def realize(self, src, row):
        raw = dict(CONTRACTS.raw, realization=[row])
        contracts = ldc.Contracts(raw)
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "host" / "native").mkdir(parents=True)
            (root / "host" / "native" / "fixture.lisp").write_text(PRELUDE + src)
            an, model, checker = ldc.analyze_tree(root, contracts, ["host/native/fixture.lisp"], {})
            ldc.check_realization(checker)
            return [f.key for f in checker.findings]

    def test_the_close_label_holds_its_guard_and_lock(self):
        self.assertEqual(self.realize(self.CLOSE, self.ROW), [])

    def test_a_close_that_skips_the_clear_check_fails(self):
        src = self.CLOSE.replace("(when (fnn-core 'fn-pio-file-clear-p id)", "(progn")
        self.assertIn("realization-before::close", self.realize(src, self.ROW))

    def test_a_close_outside_the_extent_lock_fails(self):
        src = self.CLOSE.replace("(sb-thread:with-mutex (*fnn-extent-lock*)", "(progn")
        self.assertIn("realization-locks::close", self.realize(src, self.ROW))

    def test_a_p_label_names_its_assumption(self):
        row = dict(self.ROW, layer="P")
        self.assertIn("realization-shape::close", self.realize(self.CLOSE, row))


class Baseline(unittest.TestCase):
    def test_comment_and_blank_line_shifts_preserve_callback_keys(self):
        source = "(defun fnn-start () (push (lambda () (fnn-live-arena)) *hooks*))"
        before = run(source, ["R1"])
        after = run("; inserted comment\n\n" + source.replace("(lambda", "\n; callback comment\n(lambda"), ["R1"])
        self.assertTrue(before)
        self.assertTrue([f.baseline_key() for f in before] == [f.baseline_key() for f in after],
                        "callback identities must survive comments and blank lines")
        self.assertNotEqual([f.line for f in before], [f.line for f in after])

    def test_identical_callbacks_on_one_line_are_distinct_and_new_one_is_new(self):
        one = "(defun fnn-start () (push (lambda () (fnn-live-arena)) *hooks*))"
        two = "(defun fnn-start () (push (lambda () (fnn-live-arena)) *hooks*) (push (lambda () (fnn-live-arena)) *hooks*))"
        before, after = run(one, ["R1"]), run(two, ["R1"])
        self.assertEqual(len(before), 1)
        self.assertEqual(len(after), 2)
        self.assertEqual(len({f.baseline_key() for f in after}), 2)
        baseline = {f.baseline_key(): {"count": f.weight} for f in before}
        self.assertEqual(len(ldc.judge(after, baseline, set())["new"]), 1)

    def test_migration_preserves_counts_and_refuses_ambiguous_callbacks(self):
        from lock_baseline_migrate import migrate_keys
        old = "lambda@host/native/x.lisp:10"
        new = "lambda@host/native/x.lisp:fnn-start#lambda1"
        data = {"findings": [{"key": "R1|" + old + "|O:fnn-live-arena", "count": 3}]}
        migrated = migrate_keys(data, {old: {new}}, "revision", "digest")
        self.assertEqual(migrated["findings"][0]["count"], 3)
        self.assertIn(new, migrated["findings"][0]["key"])
        self.assertIn(old, data["findings"][0]["key"])
        for candidates in (set(), {new, new + "other"}):
            with self.assertRaises(ValueError):
                migrate_keys(data, {old: candidates}, "revision", "digest")

    def test_the_baseline_only_shrinks_and_the_enclave_is_strict(self):
        f = ldc.Finding("R3", "violation", "fn-a", "x.lisp", 1, "m", "naked:p")
        g = ldc.Finding("R2", "violation", "fn-b", "x.lisp", 2, "m", "O:leaf", weight=3)
        base = {f.baseline_key(): {"count": 1}, g.baseline_key(): {"count": 3}}
        self.assertEqual(ldc.judge([f, g], base, set())["new"], [])
        g.weight = 4
        self.assertEqual(len(ldc.judge([f, g], base, set())["new"]), 1)
        self.assertEqual(ldc.judge([f], base, set())["stale"], [g.baseline_key()])
        self.assertEqual(len(ldc.judge([f], {f.baseline_key(): {"count": 1}}, {"fn-a"})["new"]), 1)


if __name__ == "__main__":
    unittest.main()
