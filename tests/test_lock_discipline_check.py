"""tools/lock_discipline_check.py: positive and negative structural fixtures.

Each fixture is a small host source read with the real contracts file
(tools/lock_discipline_contracts.json), so a fixture exercises the same lock
table, leaves, borrows and wrappers the tree is checked against.  The
negative fixtures are the shapes of this week's defects (r31 F1/F2, the
committer catch, the publisher's early deregistration, the adopt push, r67
F2's I/O under the owner); each positive twin is the repaired shape.
"""
import contextlib
import io
import os
import sys
import tempfile
import unittest
import json
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


def analyzed(source):
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        (root / "host" / "native").mkdir(parents=True)
        (root / "host" / "native" / "fixture.lisp").write_text(PRELUDE + source)
        an, _, _ = ldc.analyze_tree(root, CONTRACTS, ["host/native/fixture.lisp"], {})
        return an


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

    def test_a_lambda_an_flet_funcalls_is_not_its_own_root(self):
        # the cleanup shape: the lambda runs at the funcall, on this call.
        # Spawning it as an async root invents a second actor.
        src = """
(defvar *fnn-box* nil)
(defun fnn-touch () (setq *fnn-box* t))
(defun fnn-command-box ()
  (flet ((cleanup (operation)
           (handler-case (funcall operation)
             (serious-condition () nil))))
    (cleanup (lambda () (fnn-touch)))))
"""
        self.assertFalse(any(f.rule == "R1b" and "*fnn-box*" in f.key for f in run(src, ["R1b"])))
        self.assertFalse(any(name.startswith("lambda@") for name in analyzed(src).infos))

    def test_a_lambda_funcalled_inside_the_flets_lock_holds_it(self):
        src = """
(defun fnn-run (service)
  (flet ((call (operation) (funcall operation)))
    (sb-thread:with-mutex ((fnn-owner-service-lock service))
      (call (lambda () (fnn-live-arena))))))
"""
        self.assertEqual([f for f in run(src, ["R1"]) if f.rule == "R1"], [])

    def test_a_lambda_an_flet_stores_stays_async(self):
        src = """
(defvar *fnn-hooks* nil)
(defun fnn-register (service)
  (flet ((save (operation) (setq *fnn-hooks* operation)))
    (sb-thread:with-mutex ((fnn-owner-service-lock service))
      (save (lambda () (fnn-live-arena))))))
"""
        found = [f for f in run(src, ["R1"]) if f.rule == "R1"]
        self.assertTrue(any(f.function.startswith("lambda@") and "fnn-live-arena" in f.key for f in found))

    def test_a_close_in_a_funcalled_flet_lambda_stays_with_the_opener(self):
        src = """
(defun fnn-command-close ()
  (let ((fd (fnn-open "x" 0)))
    (flet ((cleanup (thunk) (funcall thunk)))
      (cleanup (lambda () (fnn-close fd))))))
"""
        self.assertFalse(any(f.key.startswith("foreign-close") for f in run(src, ["R10"])))


class ParamRoutePruning(unittest.TestCase):
    """628df3a0a: a conditional run route is dropped only for a call site
    passing a SELF-EVALUATING literal that contradicts the arm's test."""
    CALLEE = """
(defun fnn-maybe-locked (service thunk locked)
  (if locked
      (sb-thread:with-mutex ((fnn-owner-service-lock service)) (funcall thunk))
      (funcall thunk)))
"""

    SPAWN = """
(defun fnn-spawn (s) (sb-thread:make-thread (lambda () (fnn-a s t)) :name "t"))
"""

    def r1(self, caller):
        # R1 judges thread roots only: the caller runs on a spawned thread
        return [f for f in run(self.CALLEE + caller + self.SPAWN, ["R1"])
                if f.rule == "R1" and "fnn-live-arena" in f.key]

    def test_literal_t_selects_the_locked_arm_and_prunes_the_bare_route(self):
        self.assertEqual(self.r1("(defun fnn-a (s &optional x) (fnn-maybe-locked s (lambda () (fnn-live-arena)) t))"), [])

    def test_literal_nil_selects_the_bare_arm_and_the_finding_fires(self):
        self.assertTrue(self.r1("(defun fnn-a (s &optional x) (fnn-maybe-locked s (lambda () (fnn-live-arena)) nil))"))

    def test_a_variable_discriminator_is_not_pruned(self):
        self.assertTrue(self.r1("(defun fnn-a (s flag) (fnn-maybe-locked s (lambda () (fnn-live-arena)) flag))"))

    def test_a_call_result_discriminator_is_not_pruned(self):
        self.assertTrue(self.r1("(defun fnn-a (s &optional x) (fnn-maybe-locked s (lambda () (fnn-live-arena)) (fnn-decide s)))"))

    def test_a_written_parameter_is_not_tagged(self):
        src = """
(defun fnn-maybe-locked (service thunk locked)
  (setq locked (fnn-decide service))
  (if locked
      (sb-thread:with-mutex ((fnn-owner-service-lock service)) (funcall thunk))
      (funcall thunk)))
(defun fnn-a (s &optional x) (fnn-maybe-locked s (lambda () (fnn-live-arena)) t))
(defun fnn-spawn (s) (sb-thread:make-thread (lambda () (fnn-a s)) :name "t"))
"""
        found = [f for f in run(src, ["R1"]) if f.rule == "R1" and "fnn-live-arena" in f.key]
        self.assertTrue(found)

    def test_a_parameter_written_by_pop_or_mvsetq_is_not_tagged(self):
        # setq/setf with a value rebind the env entry; these heads rely on the write scan
        for write in ("(pop locked)", "(multiple-value-setq (locked) (fnn-decide service))"):
            src = """
(defun fnn-maybe-locked (service thunk locked)
  %s
  (if locked
      (sb-thread:with-mutex ((fnn-owner-service-lock service)) (funcall thunk))
      (funcall thunk)))
(defun fnn-a (s &optional x) (fnn-maybe-locked s (lambda () (fnn-live-arena)) t))
(defun fnn-spawn (s) (sb-thread:make-thread (lambda () (fnn-a s)) :name "t"))
""" % write
            found = [f for f in run(src, ["R1"]) if f.rule == "R1" and "fnn-live-arena" in f.key]
            self.assertTrue(found, write)

    def test_a_shadowing_let_is_not_tagged(self):
        src = """
(defun fnn-maybe-locked (service thunk locked)
  (let ((locked (fnn-decide service)))
    (if locked
        (sb-thread:with-mutex ((fnn-owner-service-lock service)) (funcall thunk))
        (funcall thunk))))
(defun fnn-a (s &optional x) (fnn-maybe-locked s (lambda () (fnn-live-arena)) t))
(defun fnn-spawn (s) (sb-thread:make-thread (lambda () (fnn-a s)) :name "t"))
"""
        found = [f for f in run(src, ["R1"]) if f.rule == "R1" and "fnn-live-arena" in f.key]
        self.assertTrue(found)


class FletLambdaInlining(unittest.TestCase):
    """84a4d8dd6 / 628df3a0a: a closure run synchronously under a lock is
    inlined into that context; a stored one stays a fresh async root; the
    inlining never invents a lock."""
    SECTION = """
(defvar *fnn-hooks* nil)
(defstruct fnn-box slot)
(defun fnn-section (service thunk)
  (sb-thread:with-mutex ((fnn-owner-service-lock service)) (funcall thunk)))
"""

    def r1(self, body):
        src = self.SECTION + "(defun fnn-a (s) %s)\n" % body + \
            '(defun fnn-spawn (s) (sb-thread:make-thread (lambda () (fnn-a s)) :name "t"))\n'
        return [f for f in run(src, ["R1"]) if f.rule == "R1" and "fnn-live-arena" in f.key]

    def test_flet_ref_funcalled_by_a_section_runs_under_its_lock(self):
        self.assertEqual(self.r1("(flet ((call () (fnn-live-arena))) (fnn-section s #'call))"), [])

    def test_flet_lambda_funcalled_immediately_under_the_callers_lock(self):
        self.assertEqual(self.r1(
            "(flet ((run1 (op) (funcall op))) (fnn-section s (lambda () (run1 (lambda () (fnn-live-arena))))))"), [])

    def test_flet_lambda_funcalled_without_a_lock_still_fires(self):
        self.assertTrue(self.r1("(flet ((run1 (op) (funcall op))) (run1 (lambda () (fnn-live-arena))))"))

    def test_flet_ref_called_without_a_lock_still_fires(self):
        self.assertTrue(self.r1("(flet ((call () (fnn-live-arena))) (call))"))

    def test_flet_ref_stored_instead_of_run_does_not_inherit_the_lock(self):
        self.assertTrue(self.r1(
            "(flet ((call () (fnn-live-arena))) (sb-thread:with-mutex ((fnn-owner-service-lock s)) (push #'call *fnn-hooks*)))"))

    def test_flet_called_under_a_lock_and_also_stored_keeps_its_own_walk(self):
        # one locked call must not hide the stored #'call, which runs later with no lock
        self.assertTrue(self.r1(
            "(flet ((call () (fnn-live-arena))) (push #'call *fnn-hooks*) (sb-thread:with-mutex ((fnn-owner-service-lock s)) (call)))"))

    def test_lambda_pushed_by_the_flet_stays_an_async_root(self):
        self.assertTrue(self.r1(
            "(flet ((keep (op) (push op *fnn-hooks*))) (sb-thread:with-mutex ((fnn-owner-service-lock s)) (keep (lambda () (fnn-live-arena)))))"))

    def test_lambda_setf_into_a_slot_by_the_flet_stays_an_async_root(self):
        self.assertTrue(self.r1(
            "(flet ((keep (op) (setf (fnn-box-slot (make-fnn-box)) op))) (sb-thread:with-mutex ((fnn-owner-service-lock s)) (keep (lambda () (fnn-live-arena)))))"))

    def test_lambda_handed_to_a_thread_by_the_flet_stays_an_async_root(self):
        self.assertTrue(self.r1(
            "(flet ((go1 (op) (sb-thread:make-thread op :name \"w\"))) (sb-thread:with-mutex ((fnn-owner-service-lock s)) (go1 (lambda () (fnn-live-arena)))))"))

    def test_lambda_funcalled_and_also_stored_stays_an_async_root(self):
        self.assertTrue(self.r1(
            "(flet ((both (op) (funcall op) (push op *fnn-hooks*))) (sb-thread:with-mutex ((fnn-owner-service-lock s)) (both (lambda () (fnn-live-arena)))))"))


class R7DeferredRethrow(unittest.TestCase):
    """capture into a let variable in the handler, re-signal it on EVERY exit path"""
    def swallow(self, let_body_tail, extra="", pre=""):
        src = """
(defun fnn-actor (s flag other)
  (let ((failure nil) (spare nil))
    %s
    (flet ((release (thunk)
             (handler-case (funcall thunk)
               (serious-condition (c) (unless failure (setq failure c))))))
      (release (lambda () (fnn-fault "x"))))
    %s
    %s))
(defun fnn-spawn (s) (sb-thread:make-thread (lambda () (fnn-actor s nil nil)) :name "t"))
""" % (pre, extra, let_body_tail)
        return [f for f in run(src, ["R7"]) if f.rule == "R7" and f.key.startswith("swallow")]

    def test_tail_rethrow_of_the_captured_variable_is_recognised(self):
        self.assertEqual(self.swallow("(when failure (error failure))"), [])

    def test_if_with_a_quiet_else_is_recognised(self):
        self.assertEqual(self.swallow("(if failure (error failure) nil)"), [])

    def test_rethrow_gated_on_another_flag_is_not(self):
        self.assertTrue(self.swallow("(when flag (error failure))"))

    def test_conjunction_test_is_not(self):
        self.assertTrue(self.swallow("(when (and failure flag) (error failure))"))

    def test_rethrow_of_a_different_variable_is_not(self):
        self.assertTrue(self.swallow("(when spare (error spare))"))

    def test_a_non_signalling_arm_is_not(self):
        self.assertTrue(self.swallow('(when failure (fnn-out "x"))'))

    def test_rethrow_on_one_branch_of_the_arm_is_not(self):
        self.assertTrue(self.swallow("(when failure (if flag (error failure) (fnn-out \"x\")))"))

    def test_a_nested_conditional_rethrow_is_not_the_tail(self):
        self.assertTrue(self.swallow('(fnn-out "x")', extra="(when flag (when failure (error failure)))"))

    def test_an_early_return_between_capture_and_tail_is_not(self):
        self.assertTrue(self.swallow("(when failure (error failure))",
                                     extra="(when flag (return-from fnn-actor nil))"))

    def test_a_throw_between_capture_and_tail_is_not(self):
        self.assertTrue(self.swallow("(when failure (error failure))", extra="(when flag (throw :out nil))"))

    def test_a_reset_between_capture_and_tail_is_not(self):
        self.assertTrue(self.swallow("(when failure (error failure))", extra="(setq failure nil)"))

    def test_a_capture_inside_a_thread_lambda_is_not(self):
        src = """
(defun fnn-actor (s)
  (let ((failure nil))
    (sb-thread:make-thread
     (lambda () (handler-case (fnn-fault "x") (serious-condition (c) (setq failure c)))) :name "w")
    (when failure (error failure))))
(defun fnn-spawn (s) (sb-thread:make-thread (lambda () (fnn-actor s)) :name "t"))
"""
        self.assertTrue([f for f in run(src, ["R7"]) if f.key.startswith("swallow")])

    def test_unwind_protect_cleanup_tail_is_recognised(self):
        src = """
(defun fnn-actor (s)
  (let ((failure nil))
    (unwind-protect (fnn-out "x")
      (handler-case (fnn-fault "x") (serious-condition (c) (push c failure)))
      (when failure (error (car failure))))))
(defun fnn-spawn (s) (sb-thread:make-thread (lambda () (fnn-actor s)) :name "t"))
"""
        self.assertEqual([f for f in run(src, ["R7"]) if f.key.startswith("swallow")], [])

    def test_a_declared_dominated_escape_call_is_a_terminal_arm(self):
        src = """
(defun fnn-actor (s)
  (let ((completed nil) (failures nil) (primary nil))
    (unwind-protect (fnn-out "x")
      (handler-case (fnn-fault "x") (serious-condition (c) (push c failures)))
      (when failures
        (if completed (error (car (last failures))) (fnn-x-escape primary (reverse failures)))))))
(defun fnn-spawn (s) (sb-thread:make-thread (lambda () (fnn-actor s)) :name "t"))
"""
        raw = CONTRACTS.raw
        self.assertTrue([f for f in run(src, ["R7"]) if f.key.startswith("swallow")])
        raw["dominated_escape_functions"] = {"fnn-x-escape": "test"}
        try:
            self.assertEqual([f for f in run(src, ["R7"]) if f.key.startswith("swallow")], [])
            # the declaration covers only that name
            other = src.replace("fnn-x-escape", "fnn-y-escape")
            self.assertTrue([f for f in run(other, ["R7"]) if f.key.startswith("swallow")])
        finally:
            del raw["dominated_escape_functions"]

    def test_a_lambda_walked_inside_the_let_does_not_lose_the_deferral(self):
        pre = "(handler-bind ((serious-condition (lambda (c) (setq spare c)))) (fnn-out \"x\"))"
        self.assertEqual(self.swallow("(when failure (error failure))", pre=pre), [])


class ActorBeforeStart(unittest.TestCase):
    """def-actor's starter funcalls its seventh argument (before-start) inside
    the roster section of fnn-owner-actor-start (owner.lisp:1778-1785), on the
    caller's thread: that lambda is not a stored callback."""
    ACTOR = """
(defun fnn-owner-actor-start (service custody thunk name rosterp escape &optional physical-callback before-start)
  (sb-thread:with-mutex ((fnn-owner-service-roster service))
    (when before-start (funcall before-start nil))))
(def-actor fnn-x-spawn :kind :publisher :thread-name "fn x" :roster t :join fnn-x-join :failure :service)
"""
    BARE = """
(defun fnn-owner-actor-start (service custody thunk name rosterp escape &optional physical-callback before-start)
  (when before-start (funcall before-start nil)))
(def-actor fnn-x-spawn :kind :publisher :thread-name "fn x" :roster t :join fnn-x-join :failure :service)
"""

    def r1(self, actor, args):
        src = actor + """
(defun fnn-start (service)
  (fnn-x-spawn service nil (lambda () nil) %s))
(defun fnn-go (s) (sb-thread:make-thread (lambda () (fnn-start s)) :name "t"))
""" % args
        return [f for f in run(src, ["R1"]) if f.rule == "R1" and "fnn-owner-service-publisher" in f.key]

    TOUCH = "(lambda (worker) (setf (fnn-owner-service-publisher service) worker))"

    def test_before_start_runs_under_the_roster(self):
        self.assertEqual(self.r1(self.ACTOR, "nil nil " + self.TOUCH), [])

    def test_the_starter_template_is_the_macro_s_expansion(self):
        owner = (ROOT / "host" / "native" / "owner.lisp").read_text(encoding="utf-8")
        macro = owner[owner.index("(defmacro def-actor"):]
        macro = macro[:macro.index("\n(def", 1)]
        self.assertIn("(defun ,name (service custody thunk &optional escape physical-callback before-start)", macro)
        self.assertIn("(fnn-owner-actor-start service custody thunk ,thread-name ,roster escape physical-callback before-start)", macro)
        self.assertEqual(ldc.ACTOR_RUNNER, "fnn-owner-actor-start")
        self.assertEqual(ldc.ACTOR_BEFORE_START_ARG, 5)

    def test_the_same_lambda_as_the_escape_stays_a_root(self):
        self.assertTrue(self.r1(self.ACTOR, self.TOUCH + " nil nil"))

    def test_the_same_lambda_as_the_physical_callback_stays_a_root(self):
        self.assertTrue(self.r1(self.ACTOR, "nil " + self.TOUCH + " nil"))

    def test_before_start_without_the_roster_still_fires(self):
        self.assertTrue(self.r1(self.BARE, "nil nil " + self.TOUCH))


class R7ClassifyingEscape(unittest.TestCase):
    """contract classifying_escape_functions: fault/indet handed to the named
    function reach the fence; it is not a fence for connection-local kinds."""
    SRC = """
(defun fnn-actor (s)
  (handler-case (fnn-fault "x")
    (serious-condition (e) (%s s e "label"))))
(defun fnn-spawn (s) (sb-thread:make-thread (lambda () (fnn-actor s)) :name "t"))
"""
    REFUSAL = """
(defun fnn-actor (s)
  (handler-case (error 'fnn-store-error)
    (serious-condition (e) (%s s e "label"))))
(defun fnn-spawn (s) (sb-thread:make-thread (lambda () (fnn-actor s)) :name "t"))
"""

    def keys(self, src, name):
        return [f.key for f in run(src % name, ["R7"]) if f.rule == "R7"]

    def test_declared_classifier_routes_fault_and_indet(self):
        raw = CONTRACTS.raw
        self.assertTrue([k for k in self.keys(self.SRC, "fnn-x-classify") if k.startswith("swallow")])
        raw["classifying_escape_functions"] = {"fnn-x-classify": "test"}
        try:
            self.assertEqual(self.keys(self.SRC, "fnn-x-classify"), [])
            self.assertTrue([k for k in self.keys(self.SRC, "fnn-y-classify") if k.startswith("swallow")])
        finally:
            del raw["classifying_escape_functions"]

    def test_declared_classifier_is_not_a_fence_for_a_refusal(self):
        raw = CONTRACTS.raw
        raw["classifying_escape_functions"] = {"fnn-x-classify": "test"}
        try:
            self.assertEqual([k for k in self.keys(self.REFUSAL, "fnn-x-classify") if k.startswith("overfence")], [])
        finally:
            del raw["classifying_escape_functions"]
        raw["fence_functions"].append("fnn-x-classify")
        try:
            self.assertTrue([k for k in self.keys(self.REFUSAL, "fnn-x-classify") if k.startswith("overfence")])
        finally:
            raw["fence_functions"].remove("fnn-x-classify")


class R7ConvertingClause(unittest.TestCase):
    """a clause that ends in a call signalling a fault or indeterminate
    condition on every path converts it; it does not consume it"""
    HELPERS = """
(defun fnn-indeterminate (control) (error 'fnn-store-indeterminate :message control))
(defun fnn-refuse-x (control) (error 'fnn-store-error :message control))
(defun fnn-die (control) (fnn-fault control))
(defun fnn-maybe-die (control flag) (when flag (fnn-fault control)))
"""

    def swallows(self, clause_body):
        src = self.HELPERS + """
(defun fnn-actor (s flag)
  (handler-case (fnn-fault "x")
    (serious-condition (e) %s)))
(defun fnn-spawn (s) (sb-thread:make-thread (lambda () (fnn-actor s nil)) :name "t"))
""" % clause_body
        return [f for f in run(src, ["R7"]) if f.key.startswith("swallow")]

    def test_a_clause_ending_in_fnn_indeterminate_converts(self):
        self.assertEqual(self.swallows('(fnn-out "x") (fnn-indeterminate "y")'), [])

    def test_a_clause_ending_in_fnn_fault_through_a_helper_converts(self):
        self.assertEqual(self.swallows('(fnn-die "y")'), [])

    def test_both_arms_of_an_if_converts(self):
        self.assertEqual(self.swallows('(if flag (fnn-fault "a") (fnn-indeterminate "b"))'), [])

    def test_a_conditional_signal_is_a_swallow(self):
        self.assertTrue(self.swallows('(when flag (fnn-fault "y"))'))

    def test_one_arm_of_an_if_is_a_swallow(self):
        self.assertTrue(self.swallows('(if flag (fnn-fault "a") (fnn-out "b"))'))

    def test_a_helper_that_signals_only_sometimes_is_a_swallow(self):
        self.assertTrue(self.swallows('(fnn-maybe-die "y" flag)'))

    def test_converting_to_a_refusal_is_a_swallow(self):
        self.assertTrue(self.swallows('(fnn-refuse-x "y")'))

    def test_an_early_return_before_the_signal_is_a_swallow(self):
        self.assertTrue(self.swallows('(when flag (return-from fnn-actor nil)) (fnn-fault "y")'))

    def test_a_signal_that_is_not_the_last_form_is_a_swallow(self):
        self.assertTrue(self.swallows('(fnn-fault "y") (fnn-out "z")'))


class CallbackContexts(unittest.TestCase):
    """contracts `callback_contexts': a stored callback declared to run in a
    command's own extent gets that command's context, and nothing else does."""
    SRC = """
(defstruct fnn-cbx-grant turn)
(defun fnn-cbx-loop (grant) (funcall (fnn-cbx-grant-turn grant)))
(defun fnn-cbx-begin (grant) (setf (fnn-cbx-grant-turn grant) (lambda () (fnn-live-arena))))
(defun fnn-command-cbx (grant) (fnn-cbx-begin grant) (fnn-cbx-loop grant))
(defun fnn-cbx-spawn (grant) (sb-thread:make-thread (lambda () (fnn-cbx-loop grant)) :name "t"))
"""
    LAMBDA = "lambda@host/native/fixture.lisp:fnn-cbx-begin#lambda1"

    def run_with(self, rows, src=SRC):
        raw = dict(CONTRACTS.raw, callback_contexts=rows)
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "host" / "native").mkdir(parents=True)
            (root / "host" / "native" / "fixture.lisp").write_text(PRELUDE + src)
            an, model, checker = ldc.analyze_tree(root, ldc.Contracts(raw), ["host/native/fixture.lisp"], {})
            return [f for f in checker.run({"R1"}) if f.rule == "R1"]

    def test_undeclared_stored_callback_is_unresolved(self):
        found = self.run_with({})
        self.assertTrue(any(f.function == self.LAMBDA and f.category == "unresolved" for f in found))

    def test_declared_callback_runs_in_its_command(self):
        src = self.SRC.replace('(defun fnn-cbx-spawn (grant) (sb-thread:make-thread (lambda () (fnn-cbx-loop grant)) :name "t"))', "")
        found = self.run_with({self.LAMBDA: {"runs_in": "fnn-command-cbx", "why": "w"}}, src)
        self.assertFalse(any(f.function == self.LAMBDA for f in found))

    def test_a_renumbered_declaration_is_refused(self):
        with self.assertRaises(ValueError):
            self.run_with({self.LAMBDA.replace("lambda1", "lambda2"): {"runs_in": "fnn-command-cbx", "why": "w"}})

    def test_an_entry_a_thread_reaches_is_refused(self):
        src = self.SRC + "(defun fnn-cbx-threaded (grant) (sb-thread:make-thread (lambda () (fnn-command-cbx grant)) :name \"u\"))\n"
        with self.assertRaises(ValueError):
            self.run_with({self.LAMBDA: {"runs_in": "fnn-command-cbx", "why": "w"}}, src)

    def test_an_entry_that_does_not_create_the_callback_is_refused(self):
        src = self.SRC + "(defun fnn-command-other (grant) (fnn-cbx-loop grant))\n"
        with self.assertRaises(ValueError):
            self.run_with({self.LAMBDA: {"runs_in": "fnn-command-other", "why": "w"}}, src)


class CallbackOrdinalAudit(unittest.TestCase):
    """--audit-callbacks: a why text's own-file file.lisp:NNN marker must name
    the line the declared ordinal resolves to (declare_callback_contexts
    refuses a MISSING ordinal, never a MOVED one); a row without a marker is
    not audited, and a marker naming another file is context, not a claim."""
    # the spawn-free source, so the declaration itself is accepted
    SRC = CallbackContexts.SRC.replace(
        '(defun fnn-cbx-spawn (grant) (sb-thread:make-thread (lambda () (fnn-cbx-loop grant)) :name "t"))',
        "")
    LAMBDA = CallbackContexts.LAMBDA

    def audit(self, why):
        raw = dict(CONTRACTS.raw, callback_contexts={self.LAMBDA: {"runs_in": "fnn-command-cbx", "why": why}})
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "host" / "native").mkdir(parents=True)
            (root / "host" / "native" / "fixture.lisp").write_text(PRELUDE + self.SRC)
            an, model, checker = ldc.analyze_tree(root, ldc.Contracts(raw), ["host/native/fixture.lisp"], {})
            return ldc.audit_callbacks(model, checker.c.raw), model.an.infos[self.LAMBDA].line

    def test_an_agreeing_marker_passes(self):
        _, line = self.audit("no marker yet")
        failures, _ = self.audit(f"the grant's turn callback (fixture.lisp:{line})")
        self.assertEqual(failures, [])

    def test_a_moved_marker_fails(self):
        _, line = self.audit("no marker yet")
        failures, _ = self.audit(f"the grant's turn callback (fixture.lisp:{line + 1})")
        self.assertEqual(len(failures), 1)
        self.assertIn(f"fixture.lisp:{line + 1}", failures[0])
        self.assertIn(f"fixture.lisp:{line}", failures[0])

    def test_a_markerless_row_and_other_file_markers_pass(self):
        failures, _ = self.audit("the grant's turn callback, funcalled by the loop "
                                 "(host/native/other.lisp:12); no line claimed here")
        self.assertEqual(failures, [])

    def check_main(self, why):
        """--check with no flag: the audit is part of the default verdict over
        a scratch tree whose single declaration carries this why text."""
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "host" / "native").mkdir(parents=True)
            (root / "host" / "native" / "fixture.lisp").write_text(PRELUDE + self.SRC)
            contracts = root / "contracts.json"
            contracts.write_text(json.dumps(dict(
                CONTRACTS.raw,
                enclave={"functions": [], "files": []},  # a scratch tree reads one fixture
                callback_contexts={
                    self.LAMBDA: {"runs_in": "fnn-command-cbx", "why": why}})))
            baseline = root / "baseline.json"
            baseline.write_text(json.dumps({"findings": []}))
            with contextlib.redirect_stdout(io.StringIO()) as out:
                code = ldc.main(["--root", str(root), "--contracts", str(contracts),
                                 "--baseline", str(baseline), "--rule", "R1",
                                 "--check", "--summary"])
            return code, out.getvalue()

    def test_the_wired_check_fails_on_a_moved_marker_without_the_flag(self):
        _, line = self.audit("no marker yet")  # the ordinal's true line
        code, out = self.check_main(f"the grant's turn callback (fixture.lisp:{line + 1})")
        self.assertEqual(code, 1)
        self.assertIn("CALLBACK-AUDIT", out)
        self.assertIn(f"fixture.lisp:{line}", out)

    def test_the_wired_check_passes_on_an_agreeing_marker(self):
        _, line = self.audit("no marker yet")
        code, out = self.check_main(f"the grant's turn callback (fixture.lisp:{line})")
        self.assertEqual(code, 0, out)
        self.assertIn("callback-ordinal audit: 1 declared row(s), 1 with an own-file "
                      "line marker, 0 disagreeing", out)


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
(defun fnn-control-launch-client (state ok)
  (sb-thread:with-mutex ((fnn-control-state-lock state))
    (let ((thread (and ok (sb-thread:make-thread (lambda () (handler-case 1 (serious-condition () 2))) :name "p"))))
      (push thread (fnn-control-state-workers state)))))
"""
        found = run(src, ["R4"])
        self.assertTrue(any(f.key.startswith("nil-registered") for f in found))

    # Lanes ACTORS / GENERATORS-2: a def-actor is the thread's declaration.
    # A starter call is walked as a make-thread of its thunk under the
    # declared name; R4 holds the declared join site and every starter call
    # to the declared failure policy, with no hand `threads' row.
    ACTORS = """
(defun fnn-owner-thread-escape (service condition label &optional jobp)
  (declare (ignore service condition label jobp)) nil)
(defun fnn-owner-actor-join (service worker) (declare (ignore service worker)) t)
(defun fnn-x-join (service w) (fnn-owner-actor-join service w))
(defun fnn-x-body (service) service)
(def-actor fnn-x-spawn-svc :kind :maintenance :thread-name "fn x svc" :roster t
  :join fnn-x-join :failure :service)
(def-actor fnn-x-spawn-job :kind :publisher :thread-name "fn x job" :roster t
  :join fnn-x-join :failure :job)
(def-actor fnn-x-spawn-res :kind :syncer :thread-name "fn x res" :roster t
  :join fnn-x-join :failure :result)
"""

    def test_a_def_actor_starter_is_a_thread_of_its_declaration(self):
        an = analyzed(self.ACTORS + """
(defun fnn-x-start (service)
  (fnn-x-spawn-svc service nil (lambda () (fnn-x-body service))
    (lambda (c) (fnn-owner-thread-escape service c "x"))))
""")
        self.assertEqual(an.tree.actors["fnn-x-spawn-svc"][2:],
                         (":maintenance", "fn x svc", "t", "fnn-x-join", ":service"))
        self.assertEqual([e.extra for e in an.infos["fnn-x-start"].events if e.kind == "thread"],
                         ["fn x svc"])

    def test_starters_that_keep_their_declared_policies(self):
        found = run(self.ACTORS + """
(defun fnn-x-start (service)
  (fnn-x-spawn-svc service nil (lambda () (fnn-x-body service))
    (lambda (c) (fnn-owner-thread-escape service c "x")))
  (fnn-x-spawn-job service nil (lambda () (fnn-x-body service))
    (lambda (c) (fnn-owner-thread-escape service c "x" t)))
  (fnn-x-spawn-res service nil
    (lambda () (handler-case (fnn-x-body service) (serious-condition (e) e)))))
""", ["R4"])
        self.assertEqual([f for f in found if "actor" in f.key], [])

    def test_a_starter_against_its_declared_policy(self):
        found = run(self.ACTORS + """
(defun fnn-x-start (service)
  (fnn-x-spawn-svc service nil (lambda () (fnn-x-body service))
    (lambda (c) (fnn-owner-thread-escape service c "x" t)))
  (fnn-x-spawn-job service nil (lambda () (fnn-x-body service)))
  (fnn-x-spawn-res service nil (lambda () (fnn-x-body service))
    (lambda (c) (fnn-owner-thread-escape service c "x"))))
""", ["R4"])
        self.assertEqual(sorted(f.key for f in found if "actor" in f.key),
                         ["actor-failure:fnn-x-spawn-job", "actor-failure:fnn-x-spawn-res",
                          "actor-failure:fnn-x-spawn-svc"])

    def test_a_lock_declares_only_its_own_nonblocking_leaves(self):
        # XWEB (the web face lock) names the wake pipe's write and close as its
        # non-blocking leaves: they pass under it; any other blocking leaf, and
        # the same leaves under another lock, are still R2 findings.
        found = run("""
(defun fnn-web-wake-x (face fd one)
  (sb-thread:with-mutex ((fnn-web-face-lock face))
    (sb-unix:unix-write fd one 0 1)
    (sb-posix:close fd)))
(defun fnn-web-slow-x (face fd)
  (sb-thread:with-mutex ((fnn-web-face-lock face))
    (sb-posix:fsync fd)))
(defun fnn-owner-wake-x (service fd)
  (sb-thread:with-mutex ((fnn-owner-service-lock service))
    (sb-posix:close fd)))
""", ["R2"])
        self.assertEqual(sorted(keys(found, "R2")),
                         [("fnn-owner-wake-x", "O:sb-posix:close"), ("fnn-web-slow-x", "XWEB:sb-posix:fsync")])

    def test_a_declared_delegation_realizes_the_core_call_with_its_locks(self):
        # A realization site that makes its ACL2 call through a declared helper
        # holds the locks at the call plus the helper's own; an undeclared helper
        # (or none) is "no longer calls".
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "host" / "native").mkdir(parents=True)
            (root / "host" / "native" / "fixture.lisp").write_text(PRELUDE + """
(defun fnn-x-step (event)
  (sb-thread:with-mutex (*fnn-arena-pins-lock*) (fnn-call 'fn-arpn-step nil event)))
(defun fnn-x-pin () (fnn-x-step '(:pin)))
(defun fnn-x-pin-owned (service)
  (sb-thread:with-mutex ((fnn-owner-service-lock service)) (fnn-x-pin)))
""")
            _, _, checker = ldc.analyze_tree(root, CONTRACTS, ["host/native/fixture.lisp"], {})
        via = {"fnn-x-pin-owned": ["fnn-x-pin"], "fnn-x-pin": ["fnn-x-step"]}
        sites = ldc.realized_core_sites(checker, "fnn-x-pin-owned", "fn-arpn-step", via)
        self.assertEqual([set(locks) for _, locks in sites], [{"O", "A"}])
        self.assertEqual(ldc.realized_core_sites(checker, "fnn-x-pin-owned", "fn-arpn-step", {}), [])
        self.assertEqual(ldc.realized_core_sites(
            checker, "fnn-x-pin-owned", "fn-arpn-step", {"fnn-x-pin-owned": ["fnn-x-pin"]}), [])

    def test_a_declared_thread_thunk_wrapper_is_the_threads_lambda(self):
        # fnn-native-observed-thread-thunk returns its thunk or a lambda that
        # funcalls it: the thread runs the lambda written inside the wrapper.
        src = """
(defun fnn-x-run (service) (sb-thread:with-mutex ((fnn-owner-service-lock service)) 1))
(defun fnn-x-spawn (service)
  (sb-thread:make-thread
   (fnn-native-observed-thread-thunk (lambda () (fnn-x-run service)))
   :name "fn x wrapped"))
"""
        an = analyzed(src)
        self.assertEqual([e.extra for e in an.infos["fnn-x-spawn"].events if e.kind == "thread"],
                         ["fn x wrapped"])
        self.assertFalse([f for f in run(src, ["R4"]) if "computed function" in f.message])
        # an undeclared computed maker stays unresolved
        other = src.replace("fnn-native-observed-thread-thunk", "fnn-x-some-maker")
        self.assertTrue([f for f in run(other, ["R4"]) if "computed function" in f.message])

    def test_a_declared_join_site_that_does_not_join(self):
        found = run(self.ACTORS.replace(":join fnn-x-join :failure :job", ":join fnn-x-body :failure :job"),
                    ["R4"])
        self.assertEqual([f.key for f in found if "actor" in f.key], ["actor-no-join:fnn-x-spawn-job"])


class R5R6R8R10(unittest.TestCase):
    def test_an_inverted_edge(self):
        src = """
(defun fnn-inverted (service)
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (sb-thread:with-mutex ((fnn-owner-service-lock service)) 1)))
"""
        found = run(src, ["R5"])
        self.assertTrue(any(f.key == "E->O" and "INVERTS" in f.message for f in found))

    @staticmethod
    def observed_mutex_template():
        # Consume the actual non-evaluated macro source: its gensym MUTEX,
        # LABEL and RELEASE bindings previously collapsed to one NIL alias.
        forms = ldc.read_forms((ROOT / "host/native/io.lisp").read_text())
        return ldc.render(next(f for f, _ in forms if ldc.head(f) == "defmacro"
                               and ldc.sym(f[1]) == "fnn-with-observed-mutex"), limit=100000)

    def test_observed_mutex_preserves_owner_and_real_unknown_inner_lock(self):
        src = self.observed_mutex_template() + """
(defun fnn-nested (service)
  (fnn-with-observed-mutex ((fnn-owner-service-lock service) :owner)
    (sb-thread:with-mutex ((fnn-owner-service-undeclared-ledger-lock service)) 1)))
"""
        found = run(src, ["R5"])
        self.assertIn("O->?(fnn-owner-service-undeclared-ledger-lock)", [f.key for f in found])
        self.assertFalse(any("?nil" in f.key for f in found))

    def test_unwind_cleanups_cleanup_forms_are_walked(self):
        # The actual macro source: its `,@(mapcar (lambda (cleanup) `(handler-case
        # ,cleanup ...)) cleanups)' splice must expand per cleanup, so a lock
        # edge inside a cleanup is seen and the macro is not opaque.
        forms = ldc.read_forms((ROOT / "host/native/io.lisp").read_text())
        macro = ldc.render(next(f for f, _ in forms if ldc.head(f) == "defmacro"
                                and ldc.sym(f[1]) == "fnn-unwind-cleanups"), limit=100000)
        src = macro + """
(defun fnn-cleanup-inverted (service)
  (fnn-unwind-cleanups ((fnn-close 1))
    (fnn-close 2)
    (sb-thread:with-mutex (*fnn-extent-lock*)
      (sb-thread:with-mutex ((fnn-owner-service-lock service)) 1))))
"""
        self.assertFalse([f for f in run(src, ["R1"]) if "hides" in f.message])
        found = run(src, ["R5"])
        self.assertTrue(any(f.key == "E->O" and "INVERTS" in f.message for f in found))

    def test_conditional_unquote_template_is_expanded(self):
        # The actual macro source: `,(if actor-p `(list ,label ID ,@args) `(list
        # ,label ,@args))' is a computed unquote.  The expander follows it on the
        # macro's own parameter: a literal T or NIL picks one arm, a computed
        # argument keeps both; a lock edge inside ARGS is seen on every path and
        # the macro is no longer an unresolved primitive-hider.
        forms = ldc.read_forms((ROOT / "host/native/extent.lisp").read_text())
        macro = ldc.render(next(f for f, _ in forms if ldc.head(f) == "defmacro"
                                and ldc.sym(f[1]) == "fnn-extent-native-observe"), limit=100000)
        for actor_p in ("t", "nil", "(fnn-actor-p)"):
            src = macro + """
(defun fnn-observe-inverted (service)
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (fnn-extent-native-observe :probe %s
      (sb-thread:with-mutex ((fnn-owner-service-lock service)) 1))))
""" % actor_p
            self.assertFalse([f for f in run(src, ["R1"]) if "hides" in f.message], actor_p)
            found = run(src, ["R5"])
            self.assertTrue(any(f.key == "E->O" and "INVERTS" in f.message for f in found), actor_p)

    def test_actual_section_envelope_keeps_owner_callback_lock(self):
        wanted = {"fnn-section-envelope", "fnn-with-observed-owner",
                  "fnn-owner-measured", "fnn-section-run", "fnn-owner-serialized"}
        forms = ldc.read_forms((ROOT / "host/native/owner.lisp").read_text())
        src = self.observed_mutex_template() + "\n" + "\n".join(
            ldc.render(f, limit=100000) for f, _ in forms
            if ldc.head(f) in ("defmacro", "defun") and ldc.sym(f[1]) in wanted)
        src += """
(defun fnn-owner-shared-action-locked (service cid thunk) (funcall thunk))
(defun fnn-budget (service)
  (fnn-owner-serialized service nil
    (lambda ()
      (sb-thread:with-mutex ((fnn-owner-service-undeclared-ledger-lock service)) 1))))
"""
        found = run(src, ["R5"])
        self.assertIn("O->?(fnn-owner-service-undeclared-ledger-lock)", [f.key for f in found])
        self.assertFalse(any("?nil" in f.key for f in found))

    def test_observed_mutex_still_refuses_reverse_order(self):
        src = self.observed_mutex_template() + """
(defun fnn-inverted (service)
  (fnn-with-observed-mutex (*fnn-extent-lock* :extent)
    (fnn-with-observed-mutex ((fnn-owner-service-lock service) :owner) 1)))
"""
        found = run(src, ["R5"])
        self.assertTrue(any(f.key == "E->O" and "INVERTS" in f.message for f in found))

    def test_observed_mutex_actual_nil_is_unresolved(self):
        src = self.observed_mutex_template() + """
(defun fnn-bad (service)
  (fnn-with-observed-mutex (nil :bad)
    (sb-thread:with-mutex ((fnn-owner-service-lock service)) 1)))
"""
        self.assertIn("?nil->O", [f.key for f in run(src, ["R5"])])

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

    @staticmethod
    def literal(value):
        if value is None:
            return "nil"
        if isinstance(value, dict):
            return "(" + " ".join(":" + k + " " + Realization.literal(v)
                                    for k, v in value.items()) + ")"
        if isinstance(value, list):
            return "(" + " ".join(Realization.literal(v) for v in value) + ")"
        return value if value.startswith(":") else json.dumps(value)

    def realize(self, src, row, seed=None, **extra):
        raw = dict(CONTRACTS.raw, realization=[seed or row], **extra)
        contracts = ldc.Contracts(raw)
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "host" / "native").mkdir(parents=True)
            (root / "host" / "native" / "fixture.lisp").write_text(PRELUDE + src)
            (root / "books").mkdir()
            (root / "books/host-model.lisp").write_text('(defconst *fn-hmc-realization* \''
                + self.literal([row]) + ')')
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

    STEP = """
(defun fnn-x-step (event)
  (sb-thread:with-mutex (*fnn-arena-pins-lock*) (fnn-call 'fn-arpn-step nil event)))
(defun fnn-x-pin () (fnn-x-step '(:pin)))
"""
    PIN = {"label": ":pin", "layer": "C", "enabled": [], "sites": [
        {"function": "fnn-x-pin", "file": "host/native/fixture.lisp", "primitive": None,
         "core": "fn-arpn-step", "locks_held": ["A"], "requires_before": []}]}

    def test_a_declared_delegate_realizes_the_site_s_core_call(self):
        self.assertEqual(self.realize(self.STEP, self.PIN,
                                      realization_via={"fnn-x-pin": ["fnn-x-step"]}), [])
        self.assertIn("realization::pin", self.realize(self.STEP, self.PIN))
        # the helper's own lock counts, and a lock it does not hold is still refused
        needs_o = {**self.PIN, "sites": [dict(self.PIN["sites"][0], locks_held=["O", "A"])]}
        self.assertIn("realization-locks::pin", self.realize(
            self.STEP, needs_o, realization_via={"fnn-x-pin": ["fnn-x-step"]}))

    ISSUED = """
(defun fnn-x-issue (cid) (fnn-call 'fn-pio-direct-admit cid))
(defun fnn-x-read (token fd octets) (fnn-extent-pread fd octets token))
(defun fnn-x-job (token fd octets) (fnn-x-read token fd octets))
(defun fnn-x-return (worker) worker)
(defun fnn-x-loop (worker token fd octets) (fnn-x-job token fd octets) (fnn-x-return worker))
"""
    BEGIN = {"label": ":io-begin", "layer": "P", "assumption": "A-PRIM-PREAD", "enabled": [], "sites": [
        {"function": "fnn-x-read", "file": "host/native/fixture.lisp", "primitive": "fnn-extent-pread",
         "core": None, "locks_held": [], "requires_before": ["fn-pio-direct-admit"],
         "capability": {"kind": "issued-row", "acquire": "fnn-x-issue", "release_site": "fnn-x-return"}}]}
    BORROW = {"fnn-x-read": {"kind": "issued-row", "callers": ["fnn-x-job"], "activation": "fnn-x-loop",
              "job": "fnn-x-job", "release": "fnn-x-return", "issue": "fnn-x-issue",
              "issue_core": "fn-pio-direct-admit", "why": "fixture"}}

    def test_a_typed_borrow_dominates_requires_before_across_functions(self):
        borrows = dict(CONTRACTS.raw["borrows"], **self.BORROW)
        self.assertEqual(self.realize(self.ISSUED, self.BEGIN, borrows=borrows), [])
        # no declared borrow: the straight-line rule applies
        self.assertIn("realization-before::io-begin", self.realize(self.ISSUED, self.BEGIN))
        # a borrow whose protocol is broken (the release never follows the job) does not dominate
        broken = self.ISSUED.replace("(fnn-x-return worker))\n", "nil)\n").replace(
            "(fnn-x-job token fd octets) nil)", "(fnn-x-job token fd octets) nil)")
        self.assertIn("realization-before::io-begin", self.realize(broken, self.BEGIN, borrows=borrows))

    def test_a_p_label_names_its_assumption(self):
        row = dict(self.ROW, layer="P")
        self.assertIn("realization-shape::close", self.realize(self.CLOSE, row))
        crash = dict(label=":crash", layer="P", assumption="A-CRASH-IMAGE", enabled=[], sites=[])
        self.assertEqual(self.realize(self.CLOSE, crash), [])

    def test_table_site_file_must_match_actual_host_graph(self):
        row = dict(self.ROW, sites=[dict(self.ROW["sites"][0], file="host/native/wrong.lisp")])
        self.assertIn("realization-file::close", self.realize(self.CLOSE, row))


    def test_model_literal_cannot_be_replaced_by_old_json_seed(self):
        seed = dict(self.ROW, sites=[dict(self.ROW["sites"][0], function="fnn-old-seed")])
        self.assertTrue(self.realize(self.CLOSE, self.ROW, seed=seed) == [],
                        "realization must check the model literal instead of its JSON seed")

    def table(self, model, machine=None):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "books").mkdir()
            (root / "books/host-model.lisp").write_text(model)
            if machine is not None:
                (root / "books/host-model-machine.lisp").write_text(machine)
            return ldc.realization_table(root)

    def test_machine_table_is_read_only_when_included_and_has_actual_provenance(self):
        constant = "(defconst *fn-hmc-realization* '" + self.literal([self.ROW]) + ")"
        table = self.table('(include-book "host-model-machine")', constant)
        self.assertEqual(table["source"]["file"], "books/host-model-machine.lisp")
        self.assertEqual(len(table["source"]["sha256"]), 64)
        self.assertEqual(table["rows"], [self.ROW])
        with self.assertRaisesRegex(ValueError, "exactly one"):
            self.table("(defun fn-model () nil)", constant)
        with self.assertRaisesRegex(ValueError, "exactly one"):
            self.table(constant + '(include-book "host-model-machine")', constant)

    def test_missing_computed_and_duplicate_property_tables_refuse(self):
        for source in ("(defun fn-model () nil)",
                       "(defconst *fn-hmc-realization* (append nil nil))",
                       "(defconst *fn-hmc-realization* '((:label :close :label :close)))",
                       "(defconst *fn-hmc-realization* '((:label :close :sites ((:function (evil))))))"):
            with self.subTest(source=source), self.assertRaises(ValueError):
                self.table(source)

    def test_enabled_scalar_and_nil_lists_are_normalized_without_evaluation(self):
        row = dict(self.ROW, enabled="fn-pio-file-clear-p")
        row["sites"] = [dict(self.ROW["sites"][0], requires_before=None)]
        table = self.table("(defconst *fn-hmc-realization* '" + self.literal([row]) + ")")
        self.assertEqual(table["rows"][0]["enabled"], ["fn-pio-file-clear-p"])
        self.assertEqual(table["rows"][0]["sites"][0]["requires_before"], [])


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

    # Lane WRAPPER: a def-section declares a generated owner entry; the check
    # analyzes the function the macro emits, so the template it writes and the
    # macro in host/native/owner.lisp must be the same shape.
    def test_the_def_section_template_is_the_macro_s_expansion(self):
        owner = (ROOT / "host" / "native" / "owner.lisp").read_text(encoding="utf-8")
        macro = owner[owner.index("(defmacro def-section"):]
        macro = macro[:macro.index("\n(def", 1)]
        self.assertIn("(defun ,name (service cid thunk &optional (class ,(first classes)))", macro)
        self.assertIn("(if (eq admits :live) 'fnn-section-run 'fnn-section-run-cleanup)", macro)
        self.assertIn("service class cid ',admits ',classes ',name thunk", macro)
        self.assertIn("(defun {name} (service cid thunk &optional (class {default}))",
                      ldc.SECTION_TEMPLATE)
        self.assertIn("({run} service class cid '{admits} '{classes} '{name} thunk)",
                      ldc.SECTION_TEMPLATE)

    def test_a_declared_section_is_an_analyzed_function(self):
        an = analyzed("""
(defun fnn-section-run (service class cid admits classes name thunk)
  (declare (ignore service class cid admits classes name)) (funcall thunk))
(defun fnn-section-run-cleanup (service class cid admits classes name thunk)
  (declare (ignore service class cid admits classes name)) (funcall thunk))
(def-section fnn-quantum-x :actors (:control) :classes (:control :inspect) :admits :live)
(def-section fnn-quantum-y :actors (:maintenance) :classes (:control) :admits (:cleanup :fault))
""")
        self.assertEqual(an.tree.sections["fnn-quantum-x"][2:], ([":control"], [":control", ":inspect"], ":live"))
        self.assertIn("fnn-section-run", [e.name for e in an.infos["fnn-quantum-x"].events if e.kind == "call"])
        self.assertIn("fnn-section-run-cleanup",
                      [e.name for e in an.infos["fnn-quantum-y"].events if e.kind == "call"])

    def test_a_lambda_is_named_by_its_definition_not_its_line(self):
        an = analyzed("""
(defun fn-a (x) (mapc (lambda (y) y) x) (mapc (lambda (z) z) x))
""")
        names = [n for n in an.infos if n.startswith("lambda@")]
        self.assertTrue(all(":fn-a#" in n for n in names), names)


class DurableLockRow(unittest.TestCase):
    """XDURABLE (fnn-log-durable-lock): io_ok because its one acquisition is the fsync pair."""
    SRC = """
(defun fnn-log-make-durable (log)
  (sb-thread:with-mutex ((fnn-log-durable-lock log))
    (fnn-fsync-file (fnn-log-fd log))
    (fnn-fsync-dir (fnn-log-dir-pending log))))
(defun fnn-fsync-file (fd) (sb-posix:fsync fd))
(defun fnn-fsync-dir (dir) (sb-posix:fsync (sb-posix:open dir 0)))
(defun fnn-inline-fence (service log)
  (sb-thread:with-mutex ((fnn-owner-service-lock service)) (fnn-log-make-durable log)))
"""

    def test_the_lock_itself_is_not_blocked_on_but_a_holder_of_the_owner_still_is(self):
        found = [f for f in run(self.SRC, ["R2"]) if f.rule == "R2"]
        keys_ = sorted({f.key for f in found})
        self.assertEqual(keys_, ["O:sb-posix:fsync", "O:sb-posix:open"])

    def test_the_declared_lock_is_acquired_in_one_place_only(self):
        hits = []
        for path in sorted((ROOT / "host" / "native").glob("*.lisp")):
            for n, line in enumerate(path.read_text().splitlines(), 1):
                if "fnn-log-durable-lock" in line and not line.lstrip().startswith(";"):
                    hits.append((path.name, line.strip()))
        self.assertEqual(len(hits), 1, hits)   # the struct slot is implicit; one with-mutex
        self.assertIn("with-mutex", hits[0][1])
        self.assertTrue(CONTRACTS.raw["locks"]["XDURABLE"]["io_ok"])
        self.assertEqual(CONTRACTS.raw["lock_order"]["XDURABLE"], ["K"])


class R3OwnedFd(unittest.TestCase):
    """borrows kind owned-fd (the catchup spool worker's private temp-file descriptor)."""
    GOOD = """
(defstruct (fnn-csp-worker (:constructor %make-fnn-csp-worker)) lease path fd created lock)
(defun fnn-csp-worker-perform (worker operation offset count)
  (case operation
    (:open (let ((fd (fnn-open (fnn-csp-worker-path worker) 66 384)))
             (setf (fnn-csp-worker-fd worker) fd (fnn-csp-worker-created worker) t)
             (values :ok 0)))
    ((:digest :replay)
     (fnn-extent-window-pread (fnn-csp-worker-fd worker) (make-array 2) offset count))))
(defun fnn-csp-worker-loop (worker)
  (unwind-protect (fnn-csp-worker-perform worker :open 0 0)
    (when (fnn-csp-worker-fd worker)
      (let ((fd (fnn-csp-worker-fd worker)))
        (setf (fnn-csp-worker-fd worker) nil)
        (fnn-close fd)))))
(defun fnn-csp-worker-start (path)
  (let ((worker (%make-fnn-csp-worker :path path)))
    (sb-thread:make-thread (lambda () (fnn-csp-worker-loop worker)) :name "fn catchup spool")
    worker))
"""
    ROOT_NAME = "lambda@host/native/fixture.lisp:fnn-csp-worker-start#lambda1"

    def r3(self, src, root=None):
        raw = dict(CONTRACTS.raw)
        borrows = dict(raw["borrows"])
        row = dict(borrows["fnn-csp-worker-perform"])
        row["thread_roots"] = [root or self.ROOT_NAME]
        borrows["fnn-csp-worker-perform"] = row
        raw["borrows"] = borrows
        with tempfile.TemporaryDirectory() as tmp:
            r = Path(tmp)
            (r / "host" / "native").mkdir(parents=True)
            (r / "host" / "native" / "fixture.lisp").write_text(PRELUDE + src)
            an, model, checker = ldc.analyze_tree(r, ldc.Contracts(raw), ["host/native/fixture.lisp"], {})
            return [f for f in checker.run({"R3"}) if f.category != "exception"]

    def test_the_declared_private_fd_is_accepted(self):
        self.assertEqual([(f.function, f.key, f.message) for f in self.r3(self.GOOD)], [])

    def test_without_the_row_the_pread_is_naked(self):
        raw = dict(CONTRACTS.raw)
        raw["borrows"] = {k: v for k, v in raw["borrows"].items() if k != "fnn-csp-worker-perform"}
        with tempfile.TemporaryDirectory() as tmp:
            r = Path(tmp)
            (r / "host" / "native").mkdir(parents=True)
            (r / "host" / "native" / "fixture.lisp").write_text(PRELUDE + self.GOOD)
            an, model, checker = ldc.analyze_tree(r, ldc.Contracts(raw), ["host/native/fixture.lisp"], {})
            found = checker.run({"R3"})
        self.assertIn("naked:fnn-extent-window-pread", [f.key for f in found])

    def broken(self, old, new, **kw):
        self.assertIn(old, self.GOOD)
        found = self.r3(self.GOOD.replace(old, new, 1), **kw)
        self.assertEqual([f.key for f in found], ["borrow:fnn-extent-window-pread"],
                         [(f.key, f.message) for f in found])
        return found[0].message

    def test_a_second_toucher_of_the_slot_breaks_the_row(self):
        src = self.GOOD + "(defun fnn-csp-peek (w) (fnn-csp-worker-fd w))\n"
        found = self.r3(src)
        self.assertEqual([f.key for f in found], ["borrow:fnn-extent-window-pread"])
        self.assertIn("referenced in fnn-csp-peek", found[0].message)

    def test_a_store_that_is_not_an_open_breaks_the_row(self):
        msg = self.broken("(setf (fnn-csp-worker-fd worker) fd (fnn-csp-worker-created worker) t)",
                          "(setf (fnn-csp-worker-fd worker) (gethash 1 *fnn-extent-fds*) (fnn-csp-worker-created worker) t)")
        self.assertIn("stored from something other", msg)

    def test_a_constructor_that_seeds_the_slot_breaks_the_row(self):
        msg = self.broken("(%make-fnn-csp-worker :path path)", "(%make-fnn-csp-worker :path path :fd 3)")
        self.assertIn("initialises", msg)

    def test_a_loop_that_never_closes_breaks_the_row(self):
        msg = self.broken("(fnn-close fd)", "fd")
        self.assertIn("does not fnn-close", msg)

    def test_a_pread_of_another_descriptor_breaks_the_row(self):
        msg = self.broken("(fnn-extent-window-pread (fnn-csp-worker-fd worker)",
                          "(fnn-extent-window-pread (gethash 1 *fnn-extent-fds*)")
        self.assertIn("is not passed", msg)

    def test_a_second_caller_of_the_perform_breaks_the_row(self):
        src = self.GOOD + "(defun fnn-csp-other (w) (fnn-csp-worker-perform w :digest 0 1))\n"
        found = self.r3(src)
        self.assertEqual([f.key for f in found], ["borrow:fnn-extent-window-pread"])
        self.assertIn("called from", found[0].message)

    def test_a_thread_root_that_is_not_declared_breaks_the_row(self):
        msg = self.broken("(lambda () (fnn-csp-worker-loop worker))",
                          "(lambda () (fnn-csp-worker-loop worker))", root="lambda@elsewhere#lambda9")
        self.assertIn("thread roots", msg)


class R2WaitWrapper(unittest.TestCase):
    """A declared condition-wait wrapper (contracts condition_wait_wrappers) releases the
    mutex its caller passes, exactly as sb-thread:condition-wait does."""
    WRAPPER = """
(defun fnn-observed-condition-wait (queue mutex label &key timeout)
  (if (null *obs*)
      (sb-thread:condition-wait queue mutex :timeout timeout)
    (progn (note label) (sb-thread:condition-wait queue mutex :timeout timeout))))
"""

    def test_a_wrapper_wait_on_the_held_extent_lock_is_not_a_blocking_leaf(self):
        src = self.WRAPPER + """
(defun fnn-executor-wait (worker)
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (fnn-observed-condition-wait (cold-ready worker) *fnn-extent-lock* :extent)))
"""
        found = [f for f in run(src, ["R2"]) if f.rule == "R2"]
        self.assertEqual([f.key for f in found], [])

    def test_a_wrapper_wait_still_blocks_every_other_held_lock(self):
        src = self.WRAPPER + """
(defun fnn-executor-wait (worker)
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (fnn-observed-condition-wait (cold-ready worker) *fnn-extent-lock* :extent)))
(defun fnn-wait-under-owner (service worker)
  (sb-thread:with-mutex ((fnn-owner-service-lock service)) (fnn-executor-wait worker)))
(defun fnn-wait-on-the-other-lock (service worker)
  (sb-thread:with-mutex ((fnn-owner-service-lock service))
    (fnn-observed-condition-wait (cold-ready worker) *fnn-extent-lock* :extent)))
"""
        found = [f for f in run(src, ["R2"]) if f.rule == "R2"]
        self.assertEqual(sorted({(f.function, f.key) for f in found}),
                         [("fnn-executor-wait", "O:sb-thread:condition-wait"),
                          ("fnn-wait-on-the-other-lock", "O:sb-thread:condition-wait")])
        self.assertFalse(any(f.key == "E:sb-thread:condition-wait" for f in found))

    def test_a_wrapper_that_waits_on_another_parameter_is_not_trusted(self):
        src = """
(defun fnn-observed-condition-wait (queue mutex label &key timeout)
  (sb-thread:condition-wait queue label :timeout timeout))
(defun fnn-executor-wait (worker)
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (fnn-observed-condition-wait (cold-ready worker) *fnn-extent-lock* :extent)))
"""
        found = run(src, ["R2"])
        self.assertIn("E:sb-thread:condition-wait", [f.key for f in found if f.rule == "R2"])


class LowerStale(unittest.TestCase):
    """--lower-stale is shrink-only: it never adds a key, never raises a count."""

    A = ldc.Finding("R3", "violation", "fn-a", "x.lisp", 1, "m", "naked:p")
    B = ldc.Finding("R2", "violation", "fn-b", "x.lisp", 2, "m", "O:leaf", weight=3)
    C = ldc.Finding("R1", "violation", "fn-c", "x.lisp", 3, "m", "state:s")
    D = ldc.Finding("R1", "violation", "fn-d", "x.lisp", 4, "m", "state:t")

    def row(self, f, count, reason="why"):
        return {"key": f.baseline_key(), "count": count, "rule": f.rule, "category": f.category,
                "where": f"{f.path}:{f.line}", "reason": reason}

    def lower(self, rows, findings):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "baseline.json"
            path.write_text(json.dumps({"comment": "c", "findings": rows}, indent=1) + "\n")
            before = path.read_bytes()
            changes, raised = ldc.lower_stale(path, findings)
            after = path.read_bytes()
            return changes, raised, before, after, json.loads(after)["findings"]

    def test_lowers_a_row_whose_count_dropped(self):
        _, _, _, _, rows = self.lower([self.row(self.B, 5)], [self.B])
        self.assertEqual([r["count"] for r in rows], [3])

    def test_removes_a_row_at_zero(self):
        changes, _, _, _, rows = self.lower([self.row(self.A, 1), self.row(self.B, 3)], [self.B])
        self.assertEqual([r["key"] for r in rows], [self.B.baseline_key()])
        self.assertEqual(len(changes), 1)

    def test_never_adds_a_new_key(self):
        changes, _, before, after, rows = self.lower([self.row(self.B, 5)], [self.B, self.C, self.D])
        self.assertEqual([r["key"] for r in rows], [self.B.baseline_key()])
        self.assertEqual(len(changes), 1)

    def test_never_raises_a_grown_row(self):
        grown = ldc.Finding("R2", "violation", "fn-b", "x.lisp", 2, "m", "O:leaf", weight=9)
        changes, raised, before, after, rows = self.lower([self.row(self.B, 3)], [grown])
        self.assertEqual(len(raised), 1)
        self.assertEqual(changes, [])
        self.assertEqual(before, after)

    def test_other_rows_stay_byte_identical(self):
        keep = self.row(self.A, 1, reason="unicode \u2014 reason")
        _, _, before, after, rows = self.lower([keep, self.row(self.B, 5), self.row(self.C, 1)],
                                               [self.A, self.B])
        self.assertEqual(rows[0], keep)
        self.assertEqual(list(rows[0]), list(keep))
        self.assertEqual([r["key"] for r in rows], [self.A.baseline_key(), self.B.baseline_key()])
        self.assertEqual(json.loads(after)["comment"], "c")

    def test_a_no_op_writes_nothing(self):
        changes, raised, before, after, _ = self.lower([self.row(self.A, 1), self.row(self.B, 3)],
                                                       [self.A, self.B, self.C])
        self.assertEqual((changes, raised), ([], []))
        self.assertEqual(before, after)

    def test_main_refuses_an_unreadable_baseline(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "host" / "native").mkdir(parents=True)
            (root / "host" / "native" / "fixture.lisp").write_text(PRELUDE)
            contracts = root / "contracts.json"
            contracts.write_text(json.dumps(dict(CONTRACTS.raw, enclave={"functions": [], "files": []})))
            for body in ("{not json", None):
                baseline = root / "baseline.json"
                if body is None:
                    baseline.unlink(missing_ok=True)
                else:
                    baseline.write_text(body)
                with contextlib.redirect_stdout(io.StringIO()):
                    code = ldc.main(["--root", str(root), "--contracts", str(contracts),
                                     "--baseline", str(baseline), "--lower-stale"])
                self.assertEqual(code, 1)
                self.assertEqual(baseline.exists(), body is not None)




class R1bDynamicBinding(unittest.TestCase):
    """A `let' of a defvar makes every access in its dynamic extent name the
    binding of the thread that ran the `let', not the shared global."""

    BASE = """
(defvar *fnn-dyn-flag* nil)
(defun fnn-dyn-note () (setf *fnn-dyn-flag* t))
(defun fnn-dyn-run ()
  (let ((*fnn-dyn-flag* nil))
    (fnn-dyn-note)
    *fnn-dyn-flag*))
(defun fnn-dyn-start-a ()
  (sb-thread:make-thread (lambda () (fnn-dyn-run)) :name "dyn a"))
(defun fnn-dyn-start-b ()
  (sb-thread:make-thread (lambda () (fnn-dyn-run)) :name "dyn b"))
"""

    def r1b(self, source):
        return [k for k in keys(run(source, ["R1b"]), "R1b") if "fnn-dyn-flag" in k[1]]

    def test_a_flag_rebound_around_every_use_is_thread_local(self):
        self.assertEqual(self.r1b(self.BASE), [])

    def test_a_second_caller_outside_the_binding_keeps_the_finding(self):
        found = self.r1b(self.BASE + """
(defun fnn-dyn-other () (fnn-dyn-note))
(defun fnn-dyn-start-c ()
  (sb-thread:make-thread (lambda () (fnn-dyn-other)) :name "dyn c"))
""")
        self.assertTrue(found)

    def test_a_write_outside_the_let_keeps_the_finding(self):
        found = self.r1b(self.BASE + """
(defun fnn-dyn-bare () (setf *fnn-dyn-flag* 1))
(defun fnn-dyn-start-c ()
  (sb-thread:make-thread (lambda () (fnn-dyn-bare)) :name "dyn c"))
(defun fnn-dyn-start-d ()
  (sb-thread:make-thread (lambda () (fnn-dyn-bare)) :name "dyn d"))
""")
        self.assertTrue(found)

    def test_a_thread_started_inside_the_binding_does_not_inherit_it(self):
        found = self.r1b("""
(defvar *fnn-dyn-flag* nil)
(defun fnn-dyn-note () (setf *fnn-dyn-flag* t))
(defun fnn-dyn-spawn ()
  (let ((*fnn-dyn-flag* nil))
    (sb-thread:make-thread (lambda () (fnn-dyn-note)) :name "dyn a")
    (sb-thread:make-thread (lambda () (fnn-dyn-note)) :name "dyn b")))
""")
        self.assertTrue(found)

    def test_a_lexical_variable_named_like_a_special_is_not_special(self):
        found = self.r1b("""
(defvar *fnn-dyn-flag* nil)
(defun fnn-dyn-note () (setf *fnn-dyn-flag* t))
(defun fnn-dyn-run (flag) (let ((flag 1)) (fnn-dyn-note) flag))
(defun fnn-dyn-start-a ()
  (sb-thread:make-thread (lambda () (fnn-dyn-run 1)) :name "dyn a"))
(defun fnn-dyn-start-b ()
  (sb-thread:make-thread (lambda () (fnn-dyn-run 2)) :name "dyn b"))
""")
        self.assertTrue(found)


class R1bSynchronizedTable(unittest.TestCase):
    """One gethash/remhash/clrhash/count on a :synchronized table is atomic in
    the table's own lock; a bare mention (maphash, a read-modify-write of the
    cell) or an unsynchronized table is not."""

    HEAD = """
(defvar *fnn-sync-memo* (make-hash-table :test 'eq :synchronized t))
(defvar *fnn-plain-memo* (make-hash-table :test 'eq))
"""
    TAIL = """
(defun fnn-sync-start-a ()
  (sb-thread:make-thread (lambda () (fnn-sync-use 1)) :name "sync a"))
(defun fnn-sync-start-b ()
  (sb-thread:make-thread (lambda () (fnn-sync-use 2)) :name "sync b"))
"""

    def r1b(self, body, var="fnn-sync-memo"):
        found = run(self.HEAD + body + self.TAIL, ["R1b"])
        return [k for k in keys(found, "R1b") if var in k[1]]

    def test_atomic_operations_on_a_synchronized_table_pass(self):
        self.assertEqual(self.r1b("""
(defun fnn-sync-use (k)
  (or (gethash k *fnn-sync-memo*)
      (setf (gethash k *fnn-sync-memo*) (list k)))
  (remhash k *fnn-sync-memo*)
  (hash-table-count *fnn-sync-memo*))
"""), [])

    def test_the_same_shape_on_an_unsynchronized_table_is_refused(self):
        self.assertTrue(self.r1b("""
(defun fnn-sync-use (k)
  (or (gethash k *fnn-plain-memo*)
      (setf (gethash k *fnn-plain-memo*) (list k))))
""", "fnn-plain-memo"))

    def test_a_maphash_over_the_table_is_not_atomic(self):
        self.assertTrue(self.r1b("""
(defun fnn-sync-use (k)
  (setf (gethash k *fnn-sync-memo*) k)
  (maphash (lambda (key v) (list key v)) *fnn-sync-memo*))
"""))

    def test_a_read_modify_write_of_the_cell_is_not_atomic(self):
        self.assertTrue(self.r1b("""
(defun fnn-sync-use (k)
  (push k (gethash k *fnn-sync-memo*)))
"""))
        self.assertTrue(self.r1b("""
(defun fnn-sync-use (k)
  (incf (gethash k *fnn-sync-memo* 0))
  (gethash k *fnn-sync-memo*))
"""))

    def test_passing_the_table_on_is_not_atomic(self):
        self.assertTrue(self.r1b("""
(defun fnn-sync-poke (table k) (setf (gethash k table) k))
(defun fnn-sync-use (k)
  (fnn-sync-poke *fnn-sync-memo* k)
  (setf (gethash k *fnn-sync-memo*) k))
"""))


class RealThreadRows(unittest.TestCase):
    """The catchup spool worker and the developer REPL are declared threads:
    their rows are checked against the real host, so a row whose registry,
    join site or handler stops matching the code fails here."""

    SPOOL = ("fnn-csp-worker-start", "fn catchup spool")
    REPL = ("fnn-dev-repl-start", "fn trusted developer REPL")

    @classmethod
    def setUpClass(cls):
        an, model, checker = ldc.analyze_tree(ROOT, ldc.load_contracts(
            Path(os.environ.get("LMG_CONTRACTS", str(ROOT / "tools" / "lock_discipline_contracts.json")))))
        cls.found = [f for f in checker.run({"R4"}) if f.rule == "R4"]

    def about(self, function):
        return [(f.key, f.message) for f in self.found if f.function == function]

    def test_the_catchup_spool_thread_is_declared_and_its_row_holds(self):
        self.assertEqual(self.about(self.SPOOL[0]), [])

    def test_the_developer_repl_thread_is_declared_and_its_row_holds(self):
        self.assertEqual(self.about(self.REPL[0]), [])

    def test_the_rows_name_the_registry_and_join_the_code_has(self):
        rows = CONTRACTS.raw["threads"]
        self.assertEqual(rows[self.SPOOL[0]]["registry"], "fnn-csp-worker-thread")
        self.assertEqual(rows[self.SPOOL[0]]["join"], "fnn-csp-worker-join-now")
        self.assertEqual(rows[self.REPL[0]]["registry"], "fnn-control-state-accept-thread")
        self.assertEqual(rows[self.REPL[0]]["join"], "fnn-dev-repl-close")

    def test_a_thread_stored_nowhere_is_refused(self):
        found = run("""
(defun fnn-csp-worker-start (worker)
  (sb-thread:make-thread (lambda () (fnn-csp-worker-loop worker)) :name "fn catchup spool"))
(defun fnn-csp-worker-loop (worker)
  (handler-case (fnn-fault "x") (serious-condition (c) c)))
(defun fnn-csp-worker-join-now (worker) (sb-thread:join-thread (fnn-csp-worker-thread worker)))
""", ["R4"])
        self.assertIn(("fnn-csp-worker-start", "unregistered:fnn-csp-worker-thread"), keys(found, "R4"))

    def test_a_join_site_that_never_joins_is_refused(self):
        found = run("""
(defun fnn-dev-repl-start (control)
  (setf (fnn-control-state-accept-thread control)
        (sb-thread:make-thread (lambda () (fnn-dev-repl-loop control)) :name "fn trusted developer REPL")))
(defun fnn-dev-repl-loop (control)
  (handler-case (fnn-fault "x") (serious-condition (c) c)))
(defun fnn-dev-repl-close (control) (setf (fnn-control-state-stopping control) t))
""", ["R4"])
        self.assertIn(("fnn-dev-repl-start", "no-join:fnn-dev-repl-close"), keys(found, "R4"))

    def test_a_thread_whose_loop_handles_nothing_is_refused(self):
        found = run("""
(defun fnn-dev-repl-start (control)
  (setf (fnn-control-state-accept-thread control)
        (sb-thread:make-thread (lambda () (fnn-dev-repl-loop control)) :name "fn trusted developer REPL")))
(defun fnn-dev-repl-loop (control) (fnn-fault "x"))
(defun fnn-dev-repl-close (control) (sb-thread:join-thread (fnn-control-state-accept-thread control)))
""", ["R4"])
        self.assertTrue(any(k[1].startswith("no-handler:") for k in keys(found, "R4")))


class LeafLockRows(unittest.TestCase):
    """XPWAKE (fnn-pull-runtime-wake-lock) and XTLSKX (*fnn-tls-kx-lock*) are
    leaves: no order edge out of them, no blocking work under them."""

    @classmethod
    def setUpClass(cls):
        an, model, checker = ldc.analyze_tree(ROOT, ldc.load_contracts(
            Path(os.environ.get("LMG_CONTRACTS", str(ROOT / "tools" / "lock_discipline_contracts.json")))))
        cls.found = [f for f in checker.run({"R2", "R5"}) if f.rule in ("R2", "R5")]

    def test_every_region_of_both_locks_in_the_real_host_resolves_to_its_row(self):
        names = ("fnn-pull-runtime-wake", "fnn-pull-wakes-seen", "fnn-tls-decide-key-exchange",
                 "fnn-tls-key-exchange-observation", "fnn-tls-note-session")
        self.assertEqual([(f.function, f.key) for f in self.found
                          if f.function in names and f.key.startswith("unresolved:lock object")], [])

    def test_no_real_region_of_either_lock_blocks_or_nests(self):
        # the manual grab-mutex of fnn-pull-ready-wait stays unresolved (gap 10)
        mine = [f for f in self.found if ("XPWAKE" in f.key or "XTLSKX" in f.key)
                and not f.key.startswith("unresolved:manual grab-mutex")]
        self.assertEqual([(f.function, f.key) for f in mine], [])

    def test_the_rows_are_leaves(self):
        order = CONTRACTS.raw["lock_order"]
        for row in ("XPWAKE", "XTLSKX"):
            self.assertIn(row, CONTRACTS.raw["locks"])
            self.assertNotIn(row, order)
            self.assertFalse(CONTRACTS.raw["locks"][row].get("io_ok"))
            self.assertFalse(any(row in later for later in order.values()))
        self.assertEqual(CONTRACTS.raw["locks"]["XPWAKE"]["match"], ["(fnn-pull-runtime-wake-lock)"])
        self.assertEqual(CONTRACTS.raw["locks"]["XTLSKX"]["match"], ["*fnn-tls-kx-lock*"])

    def test_io_under_the_tls_record_lock_is_refused(self):
        found = run("""
(defun fnn-tls-note-session (channel)
  (sb-thread:with-mutex (*fnn-tls-kx-lock*)
    (sb-posix:fsync channel)))
""", ["R2"])
        self.assertIn(("fnn-tls-note-session", "XTLSKX:sb-posix:fsync"), keys(found, "R2"))

    def test_the_owner_mutex_under_the_wake_lock_is_an_undeclared_edge(self):
        found = run("""
(defun fnn-pull-runtime-wake (runtime service)
  (sb-thread:with-mutex ((fnn-pull-runtime-wake-lock runtime))
    (sb-thread:with-mutex ((fnn-owner-service-lock service))
      (incf (fnn-pull-runtime-wakes runtime)))))
""", ["R5"])
        self.assertTrue(any("XPWAKE" in str(k[1]) for k in keys(found, "R5")), keys(found, "R5"))


class R1bDeadThreadGuard(unittest.TestCase):
    """A stop that runs only when the loop's thread is absent or no longer
    running is ordered after that thread (contract dead_thread_guards)."""

    def source(self, guard="(unless (and thread (sb-thread:thread-alive-p thread)) (fnn-mux-stop-loop loop))",
               extra="", spawns=1):
        second = ("""
  (sb-thread:make-thread (lambda () (fnn-mux-idle loop)) :name "fn owner io")""" if spawns == 2 else "")
        return f"""
(defstruct fnn-mux-loop thread buffer)
(defun fnn-mux-run (loop) (setf (fnn-mux-loop-buffer loop) 1))
(defun fnn-mux-idle (loop) (fnn-mux-loop-thread loop))
(defun fnn-mux-stop-loop (loop) (setf (fnn-mux-loop-buffer loop) nil))
(defun fnn-mux-start (loop other ready)
  (setf (fnn-mux-loop-thread loop)
        (sb-thread:make-thread (lambda () (fnn-mux-run loop)) :name "fn owner io")){second}
  (let* ((thread (fnn-mux-loop-thread loop)))
    {guard}))
{extra}"""

    def r1b(self, source):
        return [k for k in keys(run(source, ["R1b"]), "R1b") if "fnn-mux-loop-buffer" in k[1]]

    def test_the_guarded_stop_is_ordered_after_the_thread(self):
        self.assertEqual(self.r1b(self.source()), [])

    def test_an_unguarded_stop_races_with_the_thread(self):
        self.assertTrue(self.r1b(self.source(guard="(fnn-mux-stop-loop loop)")))

    def test_the_wrong_polarity_races(self):
        self.assertTrue(self.r1b(self.source(guard="(when (and thread (sb-thread:thread-alive-p thread)) (fnn-mux-stop-loop loop))")))

    def test_a_stop_of_another_object_is_not_ordered(self):
        self.assertTrue(self.r1b(self.source(
            guard="(unless (and thread (sb-thread:thread-alive-p thread)) (fnn-mux-stop-loop other))")))

    def test_an_unrelated_conjunct_leaves_the_thread_running(self):
        self.assertTrue(self.r1b(self.source(
            guard="(unless (and ready (sb-thread:thread-alive-p thread)) (fnn-mux-stop-loop loop))")))

    def test_a_third_actor_keeps_the_finding(self):
        self.assertTrue(self.r1b(self.source(extra="""
(defun fnn-mux-adopt (loop) (setf (fnn-mux-loop-buffer loop) 2))
(defun fnn-mux-acceptor (loop)
  (sb-thread:make-thread (lambda () (fnn-mux-adopt loop)) :name "fn acceptor"))
""")))

    def test_two_threads_of_the_declared_name_void_the_row(self):
        self.assertTrue(self.r1b(self.source(spawns=2)))


class TestOnlyEntry(unittest.TestCase):
    """contract test_only_entries: an uncalled host function that only a test
    calls is not a main-thread actor; the row is checked against the host."""

    HOST = """
(defvar *fnn-tov-n* 0)
(defun fnn-tov-work () (incf *fnn-tov-n*))
(defun fnn-tov-guarded () (fnn-tov-work))
(defun fnn-tov-start ()
  (sb-thread:make-thread (lambda () (fnn-tov-work)) :name "tov"))
"""
    MOCK = "(fnn-tov-guarded)\n"

    def analyze(self, host, mock, row=True, file="host/native/fixture.lisp"):
        raw = json.loads((ROOT / "tools" / "lock_discipline_contracts.json").read_text())
        raw["test_only_entries"] = {"fnn-tov-guarded": {"file": file, "why": "fixture"}} if row else {}
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "host" / "native").mkdir(parents=True)
            (root / "tests").mkdir()
            (root / "host" / "native" / "fixture.lisp").write_text(PRELUDE + host)
            if mock is not None:
                (root / "tests" / "mock.lisp").write_text(mock)
            cpath = root / "contracts.json"
            cpath.write_text(json.dumps(raw))
            an, model, checker = ldc.analyze_tree(root, ldc.load_contracts(cpath), ["host/native/fixture.lisp"], {})
            return [k for k in keys(checker.run({"R1b"}), "R1b") if "fnn-tov-n" in k[1]]

    def test_the_declared_test_only_wrapper_is_not_an_actor(self):
        self.assertEqual(self.analyze(self.HOST, self.MOCK), [])

    def test_without_the_row_the_wrapper_races_with_the_thread(self):
        self.assertTrue(self.analyze(self.HOST, self.MOCK, row=False))

    def test_a_host_caller_makes_the_row_stale(self):
        with self.assertRaisesRegex(ValueError, "called or referenced"):
            self.analyze(self.HOST + "(defun fnn-tov-command () (fnn-tov-guarded))\n", self.MOCK)

    def test_a_function_no_test_mentions_is_refused(self):
        with self.assertRaisesRegex(ValueError, "no file under tests"):
            self.analyze(self.HOST, "(fnn-tov-other)\n")

    def test_a_row_for_a_function_the_file_no_longer_defines_is_refused(self):
        with self.assertRaisesRegex(ValueError, "not a function"):
            self.analyze(self.HOST.replace("fnn-tov-guarded", "fnn-tov-renamed"), self.MOCK)

    def test_another_uncalled_function_stays_a_main_actor(self):
        self.assertTrue(self.analyze(self.HOST + "(defun fnn-tov-command () (fnn-tov-work))\n", self.MOCK))


class PrivateOwnerCommands(unittest.TestCase):
    """contract private_owner_commands: the checker proves, from the source, that
    a one-shot command's owner is private, and only then exempts its R2 findings."""

    HOST = """
(defvar *fnn-pv-verbs* nil)
(defvar *fnn-pv-escaped* nil)
(defstruct (fnn-owner-service (:conc-name fnn-owner-service-)) lock store)
(defstruct fnn-pv-box owner)
(defun fnn-pv-register (verb handler) (push (cons verb handler) *fnn-pv-verbs*) verb)
(defun fnn-pv-handler (verb) (cdr (assoc verb *fnn-pv-verbs*)))
(defun fnn-pv-main (verb args) (funcall (fnn-pv-handler verb) args))
(defun fnn-pv-install (root) (%make-fnn-owner-service :store root))
(defun fnn-pv-note (service) (fnn-owner-service-store service))
(defun fnn-pv-run (root thunk)
  (let ((service nil))
    (setq service (fnn-pv-install root))
    (sb-thread:with-mutex ((fnn-owner-service-lock service))
      (funcall thunk service))))
(defun fnn-pv-command (root)
  (fnn-pv-run root
              (lambda (service)
                (fnn-pv-note service)
                @BODY@
                (write-sequence "x" *standard-output*)
                (finish-output *standard-output*)
                0)))
(defun fnn-pv-dispatch (args) (fnn-pv-command (first args)))
(fnn-pv-register "pv" #'fnn-pv-dispatch)
@EXTRA@
"""
    ROW = {
        "file": "host/native/fixture.lisp", "lock": "O", "owner": "service", "thunk": "thunk",
        "constructor": "fnn-pv-install", "owner_makers": ["%make-fnn-owner-service"],
        "exempt_leaves": ["write-sequence", "finish-output", "sleep"], "exempt_sites": 2,
        "exempt_leaf_functions": ["fnn-pv-command"], "commands": ["fnn-pv-command"], "dispatch": ["fnn-pv-dispatch"],
        "registrars": ["fnn-pv-register"], "table_writers": ["fnn-pv-register"],
        "table_readers": {"*fnn-pv-verbs*": ["fnn-pv-handler"]}, "why": "fixture",
    }

    def analyze(self, body="", extra="", row=True, **changes):
        raw = json.loads((ROOT / "tools" / "lock_discipline_contracts.json").read_text())
        raw["private_owner_commands"] = {"fnn-pv-run": dict(self.ROW, **changes)} if row else {}
        src = PRELUDE + self.HOST.replace("@BODY@", body).replace("@EXTRA@", extra)
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "host" / "native").mkdir(parents=True)
            (root / "host" / "native" / "fixture.lisp").write_text(src)
            an, model, checker = ldc.analyze_tree(root, ldc.Contracts(raw), ["host/native/fixture.lisp"], {})
            found = [f for f in checker.run({"R2"}) if f.rule == "R2"]
            return sorted(f.key for f in found if not f.key.startswith("private-owner-sites")), checker.private_io

    def pin_findings(self, **changes):
        raw = json.loads((ROOT / "tools" / "lock_discipline_contracts.json").read_text())
        raw["private_owner_commands"] = {"fnn-pv-run": dict(self.ROW, **changes)}
        src = PRELUDE + self.HOST.replace("@BODY@", "").replace("@EXTRA@", "")
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "host" / "native").mkdir(parents=True)
            (root / "host" / "native" / "fixture.lisp").write_text(src)
            an, model, checker = ldc.analyze_tree(root, ldc.Contracts(raw), ["host/native/fixture.lisp"], {})
            return [f for f in checker.run({"R2"}) if f.key.startswith("private-owner-sites")]

    def refused(self, pattern, **kw):
        with self.assertRaisesRegex(ValueError, pattern):
            self.analyze(**kw)

    def test_a_private_owner_command_exempts_its_stdout_and_nothing_else(self):
        keys, private = self.analyze("(sb-posix:open \"/x\" 0)")
        self.assertEqual(keys, ["O:sb-posix:open"])
        self.assertEqual(private, {"O": 2})

    def test_without_the_row_the_stdout_writes_under_the_owner_are_findings(self):
        keys, private = self.analyze(row=False)
        self.assertEqual(keys, ["O:finish-output", "O:write-sequence"])
        self.assertEqual(private, {})

    def test_the_owner_published_to_a_global_is_refused(self):
        self.refused("stored into the global \\*fnn-pv-escaped\\*", body="(setq *fnn-pv-escaped* service)")

    def test_the_owner_pushed_onto_a_global_list_is_refused(self):
        self.refused("global", body="(push service *fnn-pv-escaped*)")

    def test_the_owner_stored_into_a_struct_slot_is_refused(self):
        self.refused("stored into the place", body="(setf (fnn-pv-box-owner (make-fnn-pv-box)) service)")

    def test_the_owner_stored_by_a_helper_it_is_passed_to_is_refused(self):
        self.refused("global", body="(fnn-pv-keep service)",
                     extra="(defun fnn-pv-keep (o) (setq *fnn-pv-escaped* o))")

    def test_the_owner_passed_to_a_thread_start_is_refused(self):
        self.refused("thread-start", body="(sb-thread:make-thread (lambda () (fnn-pv-note service)) :name \"t\")")

    def test_a_closure_over_the_owner_held_by_a_helper_that_spawns_is_refused(self):
        self.refused("thread-start", body="(fnn-pv-later (lambda () (fnn-pv-note service)))",
                     extra="(defun fnn-pv-later (f) (sb-thread:make-thread f :name \"u\"))")

    def test_an_actor_started_on_the_owner_is_refused(self):
        self.refused("thread-start", body="(fnn-owner-start-pv service)",
                     extra="(defun fnn-owner-start-pv (service) (fnn-pv-note service))")

    def test_the_owner_passed_to_an_undefined_function_is_refused(self):
        self.refused("neither a host function", body="(fnn-pv-elsewhere service)")

    def test_a_second_owner_made_in_the_command_is_refused(self):
        self.refused("second-owner", body="(fnn-pv-install \"other\")")

    def test_a_second_owner_entered_outside_the_thunk_is_refused(self):
        self.refused("entered outside the thunk", body="", extra="""
(defun fnn-pv-command-two (root)
  (fnn-pv-install root)
  (fnn-pv-run root (lambda (service) service)))
(defun fnn-pv-dispatch-two (args) (fnn-pv-command-two (first args)))
(fnn-pv-register "pv2" #'fnn-pv-dispatch-two)""",
                     commands=["fnn-pv-command", "fnn-pv-command-two"],
                     dispatch=["fnn-pv-dispatch", "fnn-pv-dispatch-two"])

    def test_the_command_reachable_from_a_served_thread_is_refused(self):
        self.refused("reached from the root", extra="""
(defun fnn-pv-serve ()
  (sb-thread:make-thread (lambda () (fnn-pv-command "r")) :name "served"))""")

    def test_the_command_reachable_from_a_serving_root_is_refused(self):
        self.refused("reached from the root", extra='(defun fnn-owner-accept (r) (fnn-pv-command r))')

    def test_a_dispatch_started_in_a_thread_is_refused(self):
        self.refused("reached from the root", extra="""
(defun fnn-pv-serve () (sb-thread:make-thread #'fnn-pv-dispatch :name "served"))""")

    def test_a_table_reader_a_thread_reaches_is_refused(self):
        self.refused("table reader", extra="""
(defun fnn-pv-serve () (sb-thread:make-thread (lambda () (fnn-pv-main "pv" nil)) :name "served"))""")

    def test_an_undeclared_table_reader_is_refused(self):
        self.refused("is read by", extra="(defun fnn-pv-peek () (length *fnn-pv-verbs*))")

    def test_a_dispatch_never_registered_is_refused(self):
        self.refused("not registered", extra="", dispatch=["fnn-pv-dispatch", "fnn-pv-main"])

    def test_an_undeclared_caller_of_the_runner_is_refused(self):
        self.refused("callers", extra="(defun fnn-pv-command-two (root) (fnn-pv-run root (lambda (s) s)))")

    def test_a_row_without_exempt_leaves_is_refused(self):
        raw_row = dict(self.ROW)
        del raw_row["exempt_leaves"]
        with self.assertRaisesRegex(ValueError, "no exempt_leaves"):
            self.refused_row(raw_row)

    def refused_row(self, row):
        raw = json.loads((ROOT / "tools" / "lock_discipline_contracts.json").read_text())
        raw["private_owner_commands"] = {"fnn-pv-run": row}
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "host" / "native").mkdir(parents=True)
            (root / "host" / "native" / "fixture.lisp").write_text(
                PRELUDE + self.HOST.replace("@BODY@", "").replace("@EXTRA@", ""))
            ldc.analyze_tree(root, ldc.Contracts(raw), ["host/native/fixture.lisp"], {})

    def test_empty_or_unknown_exempt_leaves_are_refused(self):
        self.refused("no exempt_leaves", exempt_leaves=[])
        self.refused("leaf names the leaf table knows", exempt_leaves=["not-a-leaf"])
        self.refused("leaf names the leaf table knows", exempt_leaves="sleep")

    def test_a_row_without_exempt_sites_is_refused(self):
        raw_row = dict(self.ROW)
        del raw_row["exempt_sites"]
        with self.assertRaisesRegex(ValueError, "no exempt_sites"):
            self.refused_row(raw_row)

    def test_the_pinned_site_count_matching_is_quiet(self):
        self.assertEqual(self.pin_findings(), [])

    def test_a_rise_in_exempted_sites_is_a_finding(self):
        found = self.pin_findings(exempt_sites=1)
        self.assertEqual(len(found), 1)
        self.assertIn("review it, then raise", found[0].message)

    def test_a_drop_in_exempted_sites_is_a_finding(self):
        found = self.pin_findings(exempt_sites=3)
        self.assertEqual(len(found), 1)
        self.assertIn("lower exempt_sites", found[0].message)

    def test_an_exempt_leaf_name_in_an_undeclared_function_is_not_exempt(self):
        keys, private = self.analyze("(fnn-pv-pause)", extra="(defun fnn-pv-pause () (sleep 1))")
        self.assertIn("O:sleep", keys)

    def test_a_row_without_exempt_leaf_functions_is_refused(self):
        row = dict(self.ROW)
        del row["exempt_leaf_functions"]
        with self.assertRaisesRegex(ValueError, "no exempt_leaf_functions"):
            self.refused_row(row)

    def test_a_non_exempt_leaf_keeps_its_key_and_weight_with_and_without_the_row(self):
        def weights(row):
            raw = json.loads((ROOT / "tools" / "lock_discipline_contracts.json").read_text())
            raw["private_owner_commands"] = {"fnn-pv-run": dict(self.ROW, exempt_sites=2)} if row else {}
            src = PRELUDE + self.HOST.replace("@BODY@", '(sb-posix:open "/x" 0) (sb-posix:open "/y" 0)').replace(
                "@EXTRA@", "(defun fnn-pv-served (service) (sb-thread:with-mutex ((fnn-owner-service-lock service)) "
                '(sb-posix:open "/z" 0) (write-sequence "x" *standard-output*)))')
            with tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                (root / "host" / "native").mkdir(parents=True)
                (root / "host" / "native" / "fixture.lisp").write_text(src)
                an, model, checker = ldc.analyze_tree(root, ldc.Contracts(raw), ["host/native/fixture.lisp"], {})
                total = {}
                for f in checker.run({"R2"}):
                    if f.rule == "R2" and not f.key.startswith("private-owner-sites"):
                        total[f.key] = total.get(f.key, 0) + f.weight
                return total
        without, with_row = weights(False), weights(True)
        self.assertEqual(without["O:sb-posix:open"], with_row["O:sb-posix:open"])
        self.assertGreater(without["O:sb-posix:open"], 0)
        self.assertEqual(without["O:write-sequence"] - with_row["O:write-sequence"], 1)
        self.assertEqual(without["O:finish-output"] - with_row.get("O:finish-output", 0), 1)
        self.assertEqual({k: v for k, v in without.items() if "write-seq" not in k and "finish" not in k},
                         {k: v for k, v in with_row.items() if "write-seq" not in k and "finish" not in k})

    def test_the_real_row_holds_on_the_real_tree(self):
        an, model, checker = ldc.build(ROOT, ROOT / "tools" / "lock_discipline_contracts.json")
        self.assertIn("fnn-carry-execute", model.private_owner["O"]["functions"])


class ManualGrabCriticalSection(unittest.TestCase):
    """(grab-mutex L) directly followed by (unwind-protect BODY (when
    (holding-mutex-p L) (release-mutex L))) is a critical section of L; the
    re-grab after a timed wait is a no-op under the held model (gap 10)."""

    def source(self, cleanup="(when (sb-thread:holding-mutex-p lock) (sb-thread:release-mutex lock))",
               regrab="(unless (sb-thread:holding-mutex-p lock) (sb-thread:grab-mutex lock))",
               grab_arg="lock"):
        return f"""
(defun fnn-feed-idle-wait (service queue)
  (let ((lock (fnn-owner-service-wait-lock service)))
    (sb-thread:grab-mutex {grab_arg})
    (unwind-protect
         (progn (sb-thread:condition-wait queue lock :timeout 1d0)
                {regrab}
                (fnn-owner-service-commits service))
      {cleanup})))
"""

    def r5(self, **kw):
        return [k for k in keys(run(self.source(**kw), ["R5"]), "R5")]

    def test_the_paired_grab_is_a_critical_section_of_its_lock(self):
        self.assertEqual(self.r5(), [])

    def test_a_cleanup_releasing_another_lock_stays_unresolved(self):
        bad = self.r5(cleanup="(when (sb-thread:holding-mutex-p lock) (sb-thread:release-mutex other))")
        self.assertTrue(any(k[1].startswith("unresolved:manual grab-mutex") for k in bad), bad)

    def test_a_cleanup_that_releases_unconditionally_stays_unresolved(self):
        bad = self.r5(cleanup="(sb-thread:release-mutex lock)")
        self.assertTrue(any(k[1].startswith("unresolved:manual grab-mutex") for k in bad), bad)

    def test_a_grab_with_no_unwind_protect_stays_unresolved(self):
        found = run("""
(defun fnn-feed-idle-wait (service)
  (let ((lock (fnn-owner-service-wait-lock service)))
    (sb-thread:grab-mutex lock)
    (fnn-owner-service-commits service)))
""", ["R5"])
        self.assertTrue(any(k[1].startswith("unresolved:manual grab-mutex") for k in keys(found, "R5")))

    def test_the_paired_region_still_holds_the_lock_for_blocking_work(self):
        found = run("""
(defun fnn-feed-idle-wait (service)
  (let ((lock (fnn-owner-service-lock service)))
    (sb-thread:grab-mutex lock)
    (unwind-protect (sb-posix:fsync 3)
      (when (sb-thread:holding-mutex-p lock) (sb-thread:release-mutex lock)))))
""", ["R2"])
        self.assertTrue(any(k[1].endswith("sb-posix:fsync") for k in keys(found, "R2")), keys(found, "R2"))

    def test_a_regrab_of_a_lock_not_held_is_not_waved_through(self):
        found = run("""
(defun fnn-feed-idle-wait (service)
  (let ((lock (fnn-owner-service-wait-lock service)))
    (unless (sb-thread:holding-mutex-p lock) (sb-thread:grab-mutex lock))))
""", ["R5"])
        self.assertTrue(any(k[1].startswith("unresolved:manual grab-mutex") for k in keys(found, "R5")))


class DiagnosticSinkSwallow(unittest.TestCase):
    """A handler that swallows only a diagnostic sink's own failure is exempt
    from R7 (contract diagnostic_sinks), and only when the checker verifies the
    sink and the handler's shape."""

    SINKS = {"fnn-err": {"file": "host/native/fixture.lisp", "why": "test"}}

    def run7(self, source, sinks=None):
        raw = json.loads((ROOT / "tools" / "lock_discipline_contracts.json").read_text())
        raw["diagnostic_sinks"] = self.SINKS if sinks is None else sinks
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "host" / "native").mkdir(parents=True)
            (root / "host" / "native" / "fixture.lisp").write_text(PRELUDE + source)
            cpath = root / "contracts.json"
            cpath.write_text(json.dumps(raw))
            an, model, checker = ldc.analyze_tree(root, ldc.load_contracts(cpath),
                                                  ["host/native/fixture.lisp"], {})
            return [(f.function, f.key) for f in checker.run({"R7"}) if f.rule == "R7"]

    BASE = """
(defun fnn-err (control &rest args) (fnn-emit-line control args))
(defun fnn-emit-line (control args) (fnn-fault control))
(defun fnn-worker-start ()
  (sb-thread:make-thread (lambda () (fnn-trace-it 1)) :name "w"))
"""

    def test_a_failure_swallowed_around_only_the_sink_is_exempt(self):
        found = self.run7(self.BASE + """
(defun fnn-trace-it (x)
  (handler-case (fnn-err "x ~a" x) (serious-condition () nil)))
""")
        self.assertEqual(found, [])

    def test_ignore_errors_around_only_the_sink_is_exempt(self):
        found = self.run7(self.BASE + """
(defun fnn-trace-it (x) (ignore-errors (fnn-err "x ~a" x)))
""")
        self.assertEqual(found, [])

    def test_the_same_swallow_without_a_declared_sink_is_refused(self):
        found = self.run7(self.BASE + """
(defun fnn-trace-it (x)
  (handler-case (fnn-err "x ~a" x) (serious-condition () nil)))
""", sinks={})
        self.assertTrue(any(k[1].startswith("swallow:") for k in found), found)

    def test_a_protected_form_that_also_does_real_work_is_refused(self):
        found = self.run7(self.BASE + """
(defun fnn-trace-it (x)
  (handler-case (progn (fnn-fault "x") (fnn-err "x ~a" x)) (serious-condition () nil)))
""")
        self.assertTrue(any(k[1].startswith("swallow:") for k in found), found)

    def test_a_clause_that_does_work_is_refused(self):
        found = self.run7(self.BASE + """
(defun fnn-trace-it (x)
  (handler-case (fnn-err "x ~a" x) (serious-condition () (fnn-fault "y"))))
""")
        self.assertEqual([k for k in found if k[1].startswith("swallow:")], [], found)
        found2 = self.run7(self.BASE + """
(defun fnn-trace-it (x)
  (handler-case (fnn-err "x ~a" x) (serious-condition () (fnn-close x))))
""")
        self.assertTrue(any(k[1].startswith("swallow:") for k in found2), found2)

    def test_a_sink_that_reaches_a_descriptor_close_is_a_loud_error(self):
        with self.assertRaises(ValueError):
            self.run7("""
(defun fnn-err (control &rest args) (fnn-close args))
(defun fnn-trace-it (x) (ignore-errors (fnn-err "x ~a" x)))
""")


class StatusRethrow(unittest.TestCase):
    """A handler that hands an indeterminate condition on as a returned status
    is a deferred rethrow when every caller converts that status back to a
    signal on every path (contract status_rethrows, verified)."""

    ROW = {"fnn-app-result": {"file": "host/native/fixture.lisp", "clause": "fnn-store-indeterminate",
                              "status": ":uncertain", "why": "test"}}

    def run7(self, source, row=None):
        raw = json.loads((ROOT / "tools" / "lock_discipline_contracts.json").read_text())
        raw["status_rethrows"] = self.ROW if row is None else row
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "host" / "native").mkdir(parents=True)
            (root / "host" / "native" / "fixture.lisp").write_text(PRELUDE + source)
            cpath = root / "contracts.json"
            cpath.write_text(json.dumps(raw))
            an, model, checker = ldc.analyze_tree(root, ldc.load_contracts(cpath),
                                                  ["host/native/fixture.lisp"], {})
            return [(f.function, f.key) for f in checker.run({"R7"}) if f.rule == "R7"]

    def src(self, caller_body, clause="(values :uncertain 0)", extra=""):
        return f"""
(defun fnn-indeterminate (control) (error 'fnn-store-indeterminate :message control))
(defun fnn-app-core (view) (error 'fnn-store-indeterminate :message view))
(defun fnn-app-result (view)
  (handler-case (fnn-app-core view)
    (fnn-store-indeterminate (e) {clause})))
(defun fnn-app-step (view)
  (multiple-value-bind (status detail) (fnn-app-result view)
    {caller_body}))
(defun fnn-app-start ()
  (sb-thread:make-thread (lambda () (fnn-app-step 1)) :name "w"))
{extra}
"""

    GOOD = """(when (eq status :uncertain) (fnn-indeterminate "uncertain"))
    detail"""

    def swallow(self, found):
        return [k for k in found if k[0] == "fnn-app-result" and k[1].startswith("swallow:")]

    def test_a_converted_status_is_a_deferred_rethrow(self):
        self.assertEqual(self.swallow(self.run7(self.src(self.GOOD))), [])

    def test_the_same_handler_without_the_row_is_a_swallow(self):
        found = self.run7(self.src(self.GOOD), row={})
        self.assertEqual(len(self.swallow(found)), 1, found)

    def test_a_caller_that_drops_the_status_is_a_loud_error(self):
        with self.assertRaises(ValueError):
            self.run7(self.src("detail"))

    def test_an_early_return_before_the_conversion_is_a_loud_error(self):
        with self.assertRaises(ValueError):
            self.run7(self.src("""(when (null detail) (return-from fnn-app-step nil))
    (when (eq status :uncertain) (fnn-indeterminate "uncertain"))"""))

    def test_a_conversion_that_may_return_normally_is_a_loud_error(self):
        with self.assertRaises(ValueError):
            self.run7(self.src("""(when (eq status :uncertain) (when detail (fnn-indeterminate "u")))"""))

    def test_a_second_caller_that_ignores_the_status_is_a_loud_error(self):
        with self.assertRaises(ValueError):
            self.run7(self.src(self.GOOD, extra="(defun fnn-other (v) (fnn-app-result v))"))

    def test_a_clause_that_returns_another_status_is_a_loud_error(self):
        with self.assertRaises(ValueError):
            self.run7(self.src(self.GOOD, clause="(values :ok 0)"))


class DeadCallArm(unittest.TestCase):
    """The mux loop's step excludes the cold arm before it calls the shared
    result function, so reached through that edge the arm's await is dead
    (contract dead_call_arms, verified)."""

    ROW = [{"function": "fnn-step", "call": "fnn-results", "file": "host/native/fixture.lisp",
            "results_param": "results", "tag": ":cold", "arm_calls": ["fnn-cold-line"], "why": "test"}]

    def run9(self, source, rows=None):
        raw = json.loads((ROOT / "tools" / "lock_discipline_contracts.json").read_text())
        raw["dead_call_arms"] = self.ROW if rows is None else rows
        raw["actors"] = {"mux-loop": {"roots": ["fnn-mux-run"], "no_await": True, "await_ok": [], "why": "t"}}
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "host" / "native").mkdir(parents=True)
            (root / "host" / "native" / "fixture.lisp").write_text(PRELUDE + source)
            cpath = root / "contracts.json"
            cpath.write_text(json.dumps(raw))
            an, model, checker = ldc.analyze_tree(root, ldc.load_contracts(cpath),
                                                  ["host/native/fixture.lisp"], {})
            return [(f.function, f.key) for f in checker.run({"R9"}) if f.rule == "R9"]

    def src(self, step_body=None, results_arm="(:cold (fnn-cold-line results))", extra="", mux="(fnn-step x)"):
        step_body = step_body or """(let ((results (list (fnn-read x))))
    (if (eq (first results) :cold)
        (values :cold results)
        (fnn-results x results)))"""
        return f"""
(defun fnn-wait-q (queue lock) (sb-thread:condition-wait queue lock))
(defun fnn-cold-line (results) (fnn-wait-q results results))
(defun fnn-read (x) x)
(defun fnn-results (x results)
  (case (first results)
    {results_arm}
    (t (fnn-other results x))))
(defun fnn-other (results x) (fnn-cold-line (list results x)))
(defun fnn-step (x)
  {step_body})
(defun fnn-mux-run (x) {mux})
{extra}
"""

    def waits(self, found):
        return [k for k in found if k[0] == "fnn-wait-q"]

    def test_the_excluded_arm_is_not_a_blocking_path_of_the_mux_loop(self):
        # fnn-results' other arm still reaches the wait through fnn-other: only the
        # one call named in the row is dropped, and only inside fnn-results
        found = self.waits(self.run9(self.src(results_arm="(:cold (fnn-cold-line results))")))
        self.assertTrue(found)
        self.assertEqual(self.waits(self.run9(self.src().replace("(t (fnn-other results x))", "(t (values results x))"))), [])

    def test_without_the_row_the_mux_loop_is_charged_with_the_await(self):
        self.assertTrue(self.waits(self.run9(self.src(), rows=[])))

    def test_a_call_outside_the_else_branch_is_a_loud_error(self):
        with self.assertRaises(ValueError):
            self.run9(self.src(step_body="""(let ((results (list (fnn-read x))))
    (fnn-results x results))"""))

    def test_a_guard_on_the_then_branch_is_a_loud_error(self):
        with self.assertRaises(ValueError):
            self.run9(self.src(step_body="""(let ((results (list (fnn-read x))))
    (if (eq (first results) :cold)
        (fnn-results x results)
        (values :other results)))"""))

    def test_an_assigned_results_variable_is_a_loud_error(self):
        with self.assertRaises(ValueError):
            self.run9(self.src(step_body="""(let ((results (list (fnn-read x))))
    (if (eq (first results) :cold)
        (values :cold results)
        (progn (setq results (list :cold)) (fnn-results x results))))"""))

    def test_a_cold_call_outside_the_tag_arm_is_a_loud_error(self):
        with self.assertRaises(ValueError):
            self.run9(self.src(results_arm="(:warm (fnn-cold-line results))"))

    def test_another_route_of_the_mux_loop_to_the_callee_keeps_the_arm(self):
        found = self.run9(self.src(mux="(progn (fnn-step x) (fnn-results x (list :cold)))"))
        self.assertTrue(self.waits(found), found)


class DebtRethrow(unittest.TestCase):
    """A cleanup failure captured into a debt slot while a primary escape may
    be unwinding is a deferred rethrow when the checker verifies the whole
    chain to the close hook that signals it (contract debt_rethrows)."""

    ROW = {"fnn-w": {"file": "host/native/fixture.lisp", "clause": "serious-condition", "var": "failure",
                     "slot": "fnn-rt-debt", "slot_keyword": ":debt", "closer": "fnn-rt-close",
                     "registry": "*rts*", "registry_reader": "fnn-rt-get",
                     "special": "*fnn-owner-close-hooks*", "hooks_reader": "fnn-svc-close-hooks",
                     "why": "test"}}

    def run7(self, source, row=None):
        raw = json.loads((ROOT / "tools" / "lock_discipline_contracts.json").read_text())
        raw["debt_rethrows"] = self.ROW if row is None else row
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "host" / "native").mkdir(parents=True)
            (root / "host" / "native" / "fixture.lisp").write_text(PRELUDE + source)
            cpath = root / "contracts.json"
            cpath.write_text(json.dumps(raw))
            an, model, checker = ldc.analyze_tree(root, ldc.load_contracts(cpath),
                                                  ["host/native/fixture.lisp"], {})
            return [(f.function, f.key) for f in checker.run({"R7"}) if f.rule == "R7"]

    def src(self, store="(when failure (setf (fnn-rt-debt rt) failure))",
            closer_body="(when (fnn-rt-debt rt) (error (fnn-rt-debt rt)))",
            binding="(list #'fnn-rt-close)", extra="", top="(fnn-run)",
            stop_test="(unless joined (fnn-fault \"x\"))",
            remover="(when (fnn-rt-debt rt) (fnn-fault \"x\"))"):
        return f"""
(defstruct (fnn-rt (:constructor %make-fnn-rt)) service (debt nil))
(defstruct (fnn-svc (:constructor %make-fnn-svc)) close-hooks)
(defvar *rts* (make-hash-table))
(defvar *fnn-owner-close-hooks* nil)
(defun fnn-rt-get (service) (gethash service *rts*))
(defun fnn-w-core (x) (fnn-fault x))
(defun fnn-w (rt primary)
  (let ((failure nil))
    (flet ((release (thunk)
             (handler-case (funcall thunk)
               (serious-condition (c) (unless failure (setq failure c))))))
      (release (lambda () (fnn-w-core rt))))
    {store}
    (when (and failure (null primary)) (error failure))))
(defun fnn-rt-close (service)
  (let ((rt (fnn-rt-get service)))
    (when rt
      {closer_body}
      (remhash service *rts*)))
  nil)
(defun fnn-rt-abort (service rt)
  (unless (fnn-rt-debt rt) (remhash service *rts*)))
(defun fnn-install () (%make-fnn-svc :close-hooks *fnn-owner-close-hooks*))
(defun fnn-stop (svc)
  (let ((joined t))
    (dolist (hook (fnn-svc-close-hooks svc))
      (handler-case (funcall hook svc) (serious-condition () (setq joined nil))))
    {stop_test}))
(defun fnn-run () (let ((svc (fnn-install))) (fnn-stop svc)))
(defun fnn-top () (let ((*fnn-owner-close-hooks* {binding})) {top}))
(defun fnn-other (service) service)
(defun fnn-start () (sb-thread:make-thread (lambda () (fnn-w 1 nil)) :name "w"))
{extra}
"""

    def swallow(self, found):
        return [k for k in found if k[0] == "fnn-w" and k[1].startswith("swallow:")]

    def test_the_verified_chain_makes_the_capture_a_deferred_rethrow(self):
        self.assertEqual(self.swallow(self.run7(self.src())), [])

    def test_the_same_capture_without_the_row_is_a_swallow(self):
        self.assertEqual(len(self.swallow(self.run7(self.src(), row={}))), 1)

    def test_a_slot_cleared_before_the_signal_is_a_loud_error(self):
        with self.assertRaises(ValueError):
            self.run7(self.src(closer_body="""(let ((d (fnn-rt-debt rt)))
        (setf (fnn-rt-debt rt) nil)
        (when d (error d)))"""))

    def test_a_closer_that_is_not_a_close_hook_is_a_loud_error(self):
        with self.assertRaises(ValueError):
            self.run7(self.src(binding="(list #'fnn-other)"))

    def test_a_signal_on_only_one_branch_is_a_loud_error(self):
        with self.assertRaises(ValueError):
            self.run7(self.src(closer_body="(when (fnn-rt-debt rt) (when service (error (fnn-rt-debt rt))))"))

    def test_an_early_exit_before_the_signal_is_a_loud_error(self):
        with self.assertRaises(ValueError):
            self.run7(self.src(closer_body="""(when (null service) (return-from fnn-rt-close nil))
      (when (fnn-rt-debt rt) (error (fnn-rt-debt rt)))"""))

    def test_a_store_that_does_not_happen_on_the_spine_is_a_loud_error(self):
        with self.assertRaises(ValueError):
            self.run7(self.src(store="(when (and failure primary) (setf (fnn-rt-debt rt) failure))"))

    def test_another_writer_of_the_slot_is_a_loud_error(self):
        with self.assertRaises(ValueError):
            self.run7(self.src(extra="(defun fnn-clear (rt) (setf (fnn-rt-debt rt) nil))"))

    def test_a_registry_removal_that_ignores_the_debt_is_a_loud_error(self):
        with self.assertRaises(ValueError):
            self.run7(self.src(extra="(defun fnn-drop (service) (remhash service *rts*))"))

    def test_a_stop_function_that_ignores_a_failed_hook_is_a_loud_error(self):
        with self.assertRaises(ValueError):
            self.run7(self.src(stop_test="nil"))

    def test_a_binding_whose_body_never_reaches_the_stop_path_is_a_loud_error(self):
        with self.assertRaises(ValueError):
            self.run7(self.src(top="(fnn-other 1)"))


class CheckPrintsEveryKey(unittest.TestCase):
    """--check prints every NEW and STALE key (sorted, deduplicated, with counts),
    not a window of 40, and ends with a count line; --cap N is the explicit human cap."""

    def host(self, n):
        return "\n".join(
            f'(defun fnn-ck-io{i} (service) (sb-thread:with-mutex ((fnn-owner-service-lock service)) '
            f'(write-sequence "x" *standard-output*)))' for i in range(n)) + "\n"

    def run_check(self, n, *extra):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "host" / "native").mkdir(parents=True)
            (root / "host" / "native" / "fixture.lisp").write_text(PRELUDE + self.host(n))
            (root / "baseline.json").write_text('{"findings": []}')
            raw = dict(CONTRACTS.raw, enclave={"functions": [], "files": []})
            (root / "contracts.json").write_text(json.dumps(raw))
            out = io.StringIO()
            with contextlib.redirect_stdout(out):
                code = ldc.main(["--root", str(root), "--contracts", str(root / "contracts.json"),
                                 "--baseline", str(root / "baseline.json"), "--check", "--rule", "R2", "--all-files", *extra])
            return code, out.getvalue().splitlines()

    def test_more_than_forty_new_keys_are_all_printed(self):
        code, lines = self.run_check(45)
        new = [l for l in lines if " NEW " in l]
        self.assertEqual(code, 1)
        self.assertGreater(len(new), 40)
        self.assertEqual(len(new), len({l.split(" NEW ")[1].split(" (count")[0] for l in new}))
        self.assertEqual(new, sorted(new, key=lambda l: l.split(" NEW ")[1]))
        self.assertRegex(lines[-1], rf"^lock_discipline_check: {len(new)} new key\(s\), \d+ stale$")
        self.assertTrue(all("(count " in l and "baseline" in l for l in new))

    def test_cap_is_an_explicit_flag(self):
        code, lines = self.run_check(45, "--cap", "5")
        self.assertEqual(len([l for l in lines if " NEW " in l]), 5)
        self.assertTrue(any("hidden by --cap 5" in l for l in lines))


if __name__ == "__main__":
    unittest.main()


class R1bBindingOnlySpecial(unittest.TestCase):
    """contracts `binding_only_specials': a special only rebound by let to a
    fresh list, never assigned, is no shared cell; the row is checked."""

    SRC = """
(defvar *fnn-bo-deferred* nil)
(defun fnn-bo-note (x)
  (if *fnn-bo-deferred*
      (push x (cdr *fnn-bo-deferred*))
    (fnn-bo-write x)))
(defun fnn-bo-write (x) x)
(defun fnn-bo-batch ()
  (let ((deferred (list :d)))
    (let ((*fnn-bo-deferred* deferred))
      (fnn-bo-note 1))))
(defun fnn-bo-open () (fnn-bo-note 2))
(defun fnn-bo-start-a ()
  (sb-thread:make-thread (lambda () (fnn-bo-batch)) :name "bo a"))
(defun fnn-bo-start-b ()
  (sb-thread:make-thread (lambda () (fnn-bo-open)) :name "bo b"))
"""

    def run_with(self, src, rows):
        raw = dict(CONTRACTS.raw, binding_only_specials=rows)
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "host" / "native").mkdir(parents=True)
            (root / "host" / "native" / "fixture.lisp").write_text(PRELUDE + src)
            an, model, checker = ldc.analyze_tree(root, ldc.Contracts(raw), ["host/native/fixture.lisp"], {})
            return [k for k in keys(checker.run({"R1b"}), "R1b") if "fnn-bo-deferred" in k[1]]

    ROW = {"*fnn-bo-deferred*": "test"}

    def test_without_the_row_the_unbound_path_is_reported(self):
        self.assertTrue(self.run_with(self.SRC, {}))

    def test_a_verified_row_removes_the_finding(self):
        self.assertEqual(self.run_with(self.SRC, self.ROW), [])

    def test_an_assignment_of_the_symbol_refuses_the_row(self):
        with self.assertRaises(ValueError):
            self.run_with(self.SRC + "(defun fnn-bo-set () (setq *fnn-bo-deferred* (list :x)))", self.ROW)

    def test_a_rebinding_to_another_global_refuses_the_row(self):
        with self.assertRaises(ValueError):
            self.run_with(self.SRC + """
(defvar *fnn-bo-shared* (list :s))
(defun fnn-bo-alias () (let ((*fnn-bo-deferred* *fnn-bo-shared*)) (fnn-bo-note 3)))""", self.ROW)

    def test_a_non_nil_initial_value_refuses_the_row(self):
        with self.assertRaises(ValueError):
            self.run_with(self.SRC.replace("(defvar *fnn-bo-deferred* nil)", "(defvar *fnn-bo-deferred* (list :g))"), self.ROW)


class R7EscalationLoop(unittest.TestCase):
    """A let tail (dolist (X (nreverse V)) (WRAPPER (lambda () (CLASSIFIER .. X ..)) ..))
    escalates every condition the handler captured into V; the wrapper row is
    verified against its source."""

    WRAPPER = """
(defun fnn-owner-install-or-end (install original label)
  (handler-case (funcall install)
    (serious-condition (failure)
      (let ((code 4)) (fnn-exit code)))))
(defun fnn-owner-thread-escape (service condition label) (list service condition label))
"""
    ACTOR = """
(defun fnn-actor (s items)
  (let ((conditions nil))
    (dolist (item items)
      (handler-case (fnn-fault "x")
        (serious-condition (c) (push c conditions))))
    %s
    nil))
(defun fnn-spawn (s) (sb-thread:make-thread (lambda () (fnn-actor s nil)) :name "t"))
"""
    ROWS = {"fnn-owner-install-or-end": {"param": "install", "why": "test"}}
    GOOD = """(dolist (c (nreverse conditions))
      (fnn-owner-install-or-end (lambda () (fnn-owner-thread-escape s c "x")) c "x"))"""

    def swallow(self, tail, wrapper=None, rows=None):
        src = (self.WRAPPER if wrapper is None else wrapper) + self.ACTOR % tail
        # the rows are stated here: other tests edit the shared CONTRACTS in place
        raw = dict(CONTRACTS.raw, escalation_wrappers=self.ROWS if rows is None else rows,
                   classifying_escape_functions={"fnn-owner-thread-escape": "test"},
                   fence_functions=sorted(set(CONTRACTS.raw["fence_functions"]) | {"fnn-exit"}))
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "host" / "native").mkdir(parents=True)
            (root / "host" / "native" / "fixture.lisp").write_text(PRELUDE + src)
            an, model, checker = ldc.analyze_tree(root, ldc.Contracts(raw), ["host/native/fixture.lisp"], {})
            return [f for f in checker.run({"R7"}) if f.function == "fnn-actor" and f.key.startswith("swallow")]

    def test_the_escalation_loop_is_recognised(self):
        self.assertEqual(self.swallow(self.GOOD), [])

    def test_an_undeclared_wrapper_is_not_recognised(self):
        self.assertTrue(self.swallow(self.GOOD, rows={}))

    def test_without_the_loop_the_capture_is_a_swallow(self):
        self.assertTrue(self.swallow('(fnn-out "x")'))

    def test_a_loop_that_only_logs_is_not_an_escalation(self):
        self.assertTrue(self.swallow('(dolist (c (nreverse conditions)) (fnn-err "x" c))'))

    def test_a_closure_that_calls_no_classifier_is_not(self):
        self.assertTrue(self.swallow("""(dolist (c (nreverse conditions))
      (fnn-owner-install-or-end (lambda () (fnn-err "x" c)) c "x"))"""))

    def test_a_classifier_given_another_variable_is_not(self):
        self.assertTrue(self.swallow("""(dolist (c (nreverse conditions))
      (fnn-owner-install-or-end (lambda () (fnn-owner-thread-escape s items "x")) c "x"))"""))

    def test_a_loop_over_another_list_is_not(self):
        self.assertTrue(self.swallow("""(dolist (c items)
      (fnn-owner-install-or-end (lambda () (fnn-owner-thread-escape s c "x")) c "x"))"""))

    def test_a_return_inside_the_loop_is_not(self):
        self.assertTrue(self.swallow("""(dolist (c (nreverse conditions))
      (when c (return-from fnn-actor nil))
      (fnn-owner-install-or-end (lambda () (fnn-owner-thread-escape s c "x")) c "x"))"""))

    def test_a_wrapper_that_swallows_its_own_failure_is_refused(self):
        bad = self.WRAPPER.replace("(let ((code 4)) (fnn-exit code))", "nil")
        rows = {"fnn-owner-install-or-end": {"param": "install", "why": "t"}}
        with self.assertRaises(ValueError):
            self.swallow(self.GOOD, wrapper=bad, rows=rows)

    def test_a_verified_wrapper_row_is_accepted(self):
        rows = {"fnn-owner-install-or-end": {"param": "install", "why": "t"}}
        self.assertEqual(self.swallow(self.GOOD, rows=rows), [])


class CloseHookFence(unittest.TestCase):
    """contracts `close_hook_fences': a failed close hook clears the flag, the
    clean-close block needs it, and the not-joined arm exits uncertain."""

    BOOK = (ROOT / "books" / "owner-retire-settlement.lisp").read_text()
    SRC = """
(defun fnn-run (service)
  (let ((log-close-action nil))
    (when service
      (setq log-close-action (fnn-core 'fn-ort-report-close-action nil :unobserved))
      (let ((modules-joined t))
        (dolist (hook (fnn-owner-service-close-hooks service))
          (handler-case (funcall hook service)
            (serious-condition () (setq modules-joined nil))))
        (when (and modules-joined (fnn-drained-p service))
          (setq log-close-action (fnn-core 'fn-ort-report-close-action log-close-action (fnn-journal-close)))
          (setq log-close-action :joined))
        (setq log-close-action (fnn-owner-store-settlement service log-close-action))
        (if (eq log-close-action :joined)
            (fnn-ok service)
          (return-from fnn-run
            (progn (fnn-err "x")
                   (fnn-core 'fn-ort-log-close-exit (fnn-code service) +fnn-exit-uncertain+ log-close-action))))))))
"""
    ROW = {"fnn-run": {"flag": "modules-joined", "hooks": "fnn-owner-service-close-hooks",
                       "action": "log-close-action", "exit_call": "fn-ort-log-close-exit",
                       "exit_const": "+fnn-exit-uncertain+", "book": "books/owner-retire-settlement.lisp",
                       "why": "test"}}

    def check(self, src=None, book=None, row=None):
        raw = dict(CONTRACTS.raw, close_hook_fences=row or self.ROW)
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "host" / "native").mkdir(parents=True)
            (root / "books").mkdir()
            (root / "books" / "owner-retire-settlement.lisp").write_text(book or self.BOOK)
            (root / "host" / "native" / "fixture.lisp").write_text(PRELUDE + (src or self.SRC))
            ldc.analyze_tree(root, ldc.Contracts(raw), ["host/native/fixture.lisp"], {})

    def refuses(self, old, new, **kw):
        self.assertIn(old, kw.get("src", self.SRC))
        with self.assertRaises(ValueError):
            self.check(src=self.SRC.replace(old, new))

    def test_the_real_shape_is_accepted(self):
        self.check()

    def test_a_hook_handler_that_does_not_clear_the_flag_is_refused(self):
        self.refuses("(serious-condition () (setq modules-joined nil))", "(serious-condition () nil)")

    def test_a_clean_close_block_not_guarded_by_the_flag_is_refused(self):
        self.refuses("(when (and modules-joined (fnn-drained-p service))", "(when (and (fnn-drained-p service) modules-joined)")

    def test_a_stray_joined_assignment_outside_the_block_is_refused(self):
        self.refuses("(setq log-close-action (fnn-owner-store-settlement service log-close-action))",
                     "(setq log-close-action :joined) (setq log-close-action (fnn-owner-store-settlement service log-close-action))")

    def test_an_exit_that_is_not_the_uncertain_one_is_refused(self):
        self.refuses("+fnn-exit-uncertain+ log-close-action", "+fnn-exit-fault+ log-close-action")

    def test_a_flag_set_back_to_t_is_refused(self):
        self.refuses("(fnn-journal-close)))", "(fnn-journal-close))) (setq modules-joined t)")

    def test_a_book_that_lost_its_theorem_is_refused(self):
        with self.assertRaises(ValueError):
            self.check(book=self.BOOK.replace("fn-ort-log-close-held-is-uncertain", "fn-ort-log-close-renamed"))


class R2NonblockingLeaf(unittest.TestCase):
    """contracts `nonblocking_leaves': shutdown(2) does not wait, close and
    send on a socket still do."""

    SRC = """
(defun fnn-teardown-%s (service socket)
  (sb-thread:with-mutex ((fnn-owner-service-lock service)) (%s socket)))
(defun fnn-teardown-%s-start (service socket)
  (sb-thread:make-thread (lambda () (fnn-teardown-%s service socket)) :name "t"))
"""

    def r2(self, leaf, rows=None):
        name = leaf.split(":")[-1]
        raw = dict(CONTRACTS.raw)
        if rows is not None:
            raw["nonblocking_leaves"] = rows
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "host" / "native").mkdir(parents=True)
            (root / "host" / "native" / "fixture.lisp").write_text(PRELUDE + self.SRC % (name, leaf, name, name))
            an, model, checker = ldc.analyze_tree(root, ldc.Contracts(raw), ["host/native/fixture.lisp"], {})
            return [f.key for f in checker.run({"R2"}) if f.rule == "R2"]

    def test_socket_shutdown_is_not_a_blocking_leaf(self):
        self.assertEqual(self.r2("sb-bsd-sockets:socket-shutdown"), [])

    def test_without_the_row_it_is_blocking(self):
        self.assertTrue(self.r2("sb-bsd-sockets:socket-shutdown", rows={}))

    def test_socket_close_still_blocks(self):
        self.assertTrue(self.r2("sb-bsd-sockets:socket-close"))

    def test_socket_send_still_blocks(self):
        self.assertTrue(self.r2("sb-bsd-sockets:socket-send"))


class R2PipeClose(unittest.TestCase):
    """contracts `nonblocking_close_sites': a close of a descriptor that can only
    be a pipe end the loop made does not block; the provenance is checked."""

    SRC = """
(defstruct (fnn-pc-loop (:constructor %make-fnn-pc-loop)) lock wake-read wake-write)
(defun fnn-pc-start ()
  (let ((loop (%make-fnn-pc-loop)))
    (multiple-value-bind (read write) (sb-posix:pipe)
      (setf (fnn-pc-loop-wake-read loop) read
            (fnn-pc-loop-wake-write loop) write))
    loop))
(defun fnn-pc-close-wake (service loop)
  (sb-thread:with-mutex ((fnn-owner-service-lock service))
    (dolist (slot '(:read :write))
      (let ((fd (if (eq slot :read) (fnn-pc-loop-wake-read loop) (fnn-pc-loop-wake-write loop))))
        (when fd
          (sb-posix:close fd)
          (if (eq slot :read) (setf (fnn-pc-loop-wake-read loop) nil)
            (setf (fnn-pc-loop-wake-write loop) nil)))))))
(defun fnn-pc-run ()
  (let ((l (fnn-pc-start))) (sb-thread:make-thread (lambda () (fnn-pc-close-wake nil l)) :name "pc")))
"""
    ROW = {"fnn-pc-close-wake": {"close_call": "sb-posix:close",
                                 "slots": ["fnn-pc-loop-wake-read", "fnn-pc-loop-wake-write"],
                                 "pipe_call": "sb-posix:pipe", "why": "test"}}

    def r2(self, src=None, rows=None):
        raw = dict(CONTRACTS.raw, nonblocking_close_sites=self.ROW if rows is None else rows)
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "host" / "native").mkdir(parents=True)
            (root / "host" / "native" / "fixture.lisp").write_text(PRELUDE + (src or self.SRC))
            an, model, checker = ldc.analyze_tree(root, ldc.Contracts(raw), ["host/native/fixture.lisp"], {})
            return [f.key for f in checker.run({"R2"}) if f.rule == "R2" and f.function == "fnn-pc-close-wake"]

    def test_a_close_of_the_pipe_slots_is_not_blocking(self):
        self.assertEqual(self.r2(), [])

    def test_without_the_row_the_close_blocks(self):
        self.assertTrue(self.r2(rows={}))

    def test_a_slot_stored_from_another_source_refuses_the_row(self):
        with self.assertRaises(ValueError):
            self.r2(self.SRC + "(defun fnn-pc-other (loop fd) (setf (fnn-pc-loop-wake-read loop) fd))")

    def test_a_constructor_passing_a_slot_refuses_the_row(self):
        with self.assertRaises(ValueError):
            self.r2(self.SRC + "(defun fnn-pc-make (fd) (%make-fnn-pc-loop :wake-read fd))")

    def test_a_close_of_another_variable_refuses_the_row(self):
        with self.assertRaises(ValueError):
            self.r2(self.SRC.replace("(sb-posix:close fd)", "(sb-posix:close (sb-posix:open \"/x\" 0))"))

    def test_a_close_of_a_variable_bound_to_a_foreign_value_refuses_the_row(self):
        with self.assertRaises(ValueError):
            self.r2(self.SRC.replace("(let ((fd (if (eq slot :read) (fnn-pc-loop-wake-read loop) (fnn-pc-loop-wake-write loop))))",
                                     "(let ((fd (sb-posix:open \"/x\" 0)))"))
