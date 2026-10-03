"""Developer-image owner diagnostic: writable NNTP POST with no Python peer."""
import datetime
import os
import re
import socket
import struct
import subprocess
import sys
import time
import unittest

from tests.campaign.native_cuts import host_function
from tests.native_harness import (
    EXIT, ROOT, Client, Node, dot_stuff, environment, native_image, native_peer_add,
    runtime_sbcl)

IMAGE = native_image("FN_NATIVE_DEVELOPER_HOST")


def assert_funded_syncer_custody(case, trace):
    """Consume the exact native producer and dual receipts; no synthetic outcome."""
    case.assertRegex(trace, rb"(?i)custody: install threads=\d+ stack=\d+ word=:installed")
    issues = list(re.finditer(
        rb"custody: issue generation=(\d+) token=(\(:resource :owner 2 \d+\)) word=:drawn",
        trace, re.IGNORECASE))
    case.assertTrue(issues, trace[-4000:])
    receipts = list(re.finditer(
        rb"custody: receipt kind=:(physical|outcome) operation=(\d+) "
        rb"token=(\(:resource :owner 2 \d+\)) receipt=([^ ]+) word=:(pending|settled)",
        trace, re.IGNORECASE))
    for issue in issues:
        generation, token = issue.groups()
        own = [row for row in receipts
               if row.group(2) == generation and row.group(3).lower() == token.lower()]
        case.assertEqual([row.group(1).lower() for row in own].count(b"physical"), 1, trace[-4000:])
        case.assertEqual([row.group(1).lower() for row in own].count(b"outcome"), 1, trace[-4000:])
        case.assertTrue(all(row.start() > issue.start() for row in own), trace[-4000:])
        case.assertEqual([row.group(5).lower() for row in own], [b"pending", b"settled"], trace[-4000:])
        physical = next(row for row in own if row.group(1).lower() == b"physical")
        outcome = next(row for row in own if row.group(1).lower() == b"outcome")
        case.assertEqual(physical.group(4).lower(), b":terminal", trace[-4000:])
        case.assertEqual(outcome.group(4), generation, trace[-4000:])
    drained = list(re.finditer(
        rb"custody: drained typed=t retained=nil result=t", trace, re.IGNORECASE))
    case.assertTrue(drained, trace[-4000:])
    case.assertGreater(drained[-1].start(), receipts[-1].start(), trace[-4000:])

class NativeOwnerHandlerStructureTests(unittest.TestCase):
    def test_extent_close_uncertainty_fences_before_unlock_and_never_retries(self):
        from tests.campaign.native_cuts import host_function
        sys.path.insert(0, str(ROOT / "tools"))
        from ledger import head, read_forms
        owner = (ROOT / "host/native/owner.lisp").read_text()
        extent = (ROOT / "host/native/extent.lisp").read_text()
        release = host_function(owner, "fnn-owner-release-extents")
        release_form = read_forms(release)[0]
        release_handler = release_form[-1][-1]
        self.assertEqual(head(release_handler), "handler-case")
        # Lane failure-scope (t45): ONE arm; ACL2 decides the kind from the
        # concrete class (fnn-owner-thread-escape: an uncertain outcome
        # fences, a fault stops, a known refusal retries).  A parent-class
        # arm would pass an unlisted subclass as a refusal (review M1).
        self.assertEqual([head(arm) for arm in release_handler[2:]], ["serious-condition"])
        self.assertIn("(fnn-owner-thread-escape service e \"CHECKPOINT release\")", release)
        pending = host_function(owner, "fnn-owner-release-pending-extents-locked")
        self.assertIn("(service &optional pin)", pending)
        self.assertLess(pending.index("(fnn-owner-service-stopping service)"),
                        pending.index("(fnn-extent-close"))
        form = read_forms(pending)[0]

        def ancestors(form, target, parents=()):
            if isinstance(form, list):
                if head(form) == target:
                    yield parents
                for child in form:
                    yield from ancestors(child, target, parents + (form,))

        paths = list(ancestors(form, "fnn-extent-close"))
        self.assertEqual(len(paths), 1)
        self.assertIn("fnn-owner-shared-action-locked", [head(p) for p in paths[0]])
        close = host_function(extent, "fnn-extent-close")
        forms = read_forms(close)[0]
        for target in ("fnn-close", "remhash"):
            for parents in ancestors(forms, target):
                handlers = [p for p in parents if head(p) == "handler-case"]
                self.assertTrue(handlers, target)
                self.assertEqual(head(handlers[-1][-1]), "serious-condition")
                self.assertTrue(list(ancestors(handlers[-1][-1], "fnn-indeterminate")))
        self.assertLess(close.index("(fnn-close fd)"),
                        close.index("'fn-owner-page-read-close id"))
        # Held files are normal retry results, not ambiguous close errors.
        def nodes(form):
            if isinstance(form, list):
                yield form
                for child in form:
                    yield from nodes(child)
        held = next(f for f in nodes(forms) if head(f) == ":read-file-held")
        self.assertEqual(held[1], ["push", "id", "keep"])
        self.assertFalse(list(ancestors(held, "fnn-close")))
        release = host_function(owner, "fnn-owner-release-extents")
        escape = host_function(owner, "fnn-owner-thread-escape")
        self.assertIn("(fnn-owner-fence-service service)", escape)
        self.assertIn("(fnn-owner-fault-service service nil condition)", escape)
        self.assertNotIn("release failed (files stay retired)", release)
        # Every family caller supplies the service needed to fence under lock.
        for path in (ROOT / "host/native").glob("*.lisp"):
            text = path.read_text()
            for call in re.findall(r"\(fnn-owner-release-pending-extents-locked([^)]*)\)", text):
                self.assertIn("service", call, str(path))

    # Lane failure-scope (t45): the ONE fence boundary (r71 F1/F2; sweep S015,
    # S016, S017, S019, S020, S023; r72 F6; review failure-scope-review-1.md
    # M1/M2/M3).  Each test fails on d52815d5d (t43) and passes after.

    @staticmethod
    def _forms(path):
        sys.path.insert(0, str(ROOT / "tools"))
        from ledger import read_forms
        return read_forms((ROOT / path).read_text(encoding="utf-8"))

    @staticmethod
    def _definition(forms, kind, name):
        sys.path.insert(0, str(ROOT / "tools"))
        from ledger import head
        return next(f for f in forms if head(f) == kind and str(f[1]) == name)

    @staticmethod
    def _nodes(form):
        if isinstance(form, list):
            yield form
            for child in form:
                yield from NativeOwnerHandlerStructureTests._nodes(child)

    @staticmethod
    def _ancestors(form, target, parents=()):
        sys.path.insert(0, str(ROOT / "tools"))
        from ledger import head
        if isinstance(form, list):
            if head(form) == target or (len(form) > 1 and str(form[1]) == target):
                yield parents
            for child in form:
                yield from NativeOwnerHandlerStructureTests._ancestors(child, target, parents + (form,))

    BOUNDARIES = ("fnn-owner-gated", "fnn-owner-serialized", "fnn-owner-transit-serialized",
                  "fnn-owner-serialized-with-control-turn")
    NIL_BLOCKS = ("loop", "dolist", "dotimes", "do", "do*")

    def test_every_owner_quantum_runs_inside_the_one_fence_boundary(self):
        # r71 F1, sweep S017/S019/S020: fnn-owner-gated's body (and its gate
        # check and cleanup) run inside fnn-owner-shared-action-locked, so the
        # fence is installed before the mutex is released; fnn-owner-serialized
        # adds only the stopping refusal (one boundary, not two); an unwind no
        # condition explains is a fault installed under the mutex (M3).
        sys.path.insert(0, str(ROOT / "tools"))
        from ledger import head
        owner = (ROOT / "host/native/owner.lisp").read_text(encoding="utf-8")
        forms = self._forms("host/native/owner.lisp")
        gated = self._definition(forms, "defmacro", "fnn-owner-gated")
        paths = list(self._ancestors(gated, "fnn-owner-measured"))
        self.assertEqual(len(paths), 1)
        self.assertIn("fnn-owner-shared-action-locked", [head(p) for p in paths[0]])
        self.assertIn("with-mutex", [head(p)[-10:] for p in paths[0]])
        start = owner.index("(defmacro fnn-owner-gated")
        text = owner[start:owner.index("\n(def", start + 1)]
        self.assertLess(text.index("(unless *fnn-boundary-outcome*"),
                        text.index("(fnn-owner-gate-leave"))
        self.assertIn("(fnn-owner-stop-service-locked ,s +fnn-exit-fault+)", text)
        self.assertIn("(*fnn-section-step* nil)", text)
        serialized = host_function(owner, "fnn-owner-serialized")
        self.assertNotIn("fnn-owner-shared-action-locked", serialized)
        self.assertIn("(fnn-owner-gated (service class :cid cid)", serialized)
        self.assertIn("(fnn-refuse \"owner service is stopping\")", serialized)
        # No non-local exit crosses a boundary: a return-from, return or throw
        # inside a quantum targets a block, loop or catch established inside it.
        escapes = []

        def walk(form, inside, blocks, catches, where):
            if not isinstance(form, list):
                return
            h = head(form)
            if h in self.BOUNDARIES:
                inside, blocks, catches = True, (), ()
            elif inside:
                if h == "block" and len(form) > 1:
                    blocks = blocks + (str(form[1]),)
                elif h in self.NIL_BLOCKS:
                    blocks = blocks + ("nil",)
                elif h == "catch" and len(form) > 1:
                    catches = catches + (str(form[1]),)
                elif h == "return-from" and len(form) > 1 and str(form[1]) not in blocks:
                    escapes.append((where, "return-from", str(form[1])))
                elif h == "return" and "nil" not in blocks:
                    escapes.append((where, "return", ""))
                elif h == "throw" and len(form) > 1 and str(form[1]) not in catches:
                    escapes.append((where, "throw", str(form[1])))
            for child in form:
                walk(child, inside, blocks, catches, where)

        for path in sorted((ROOT / "host/native").glob("*.lisp")):
            for form in self._forms("host/native/" + path.name):
                if head(form) in ("defun", "defmacro"):
                    walk(form, False, (), (), "{}:{}".format(path.name, form[1]))
        self.assertEqual(escapes, [])

    def test_a_condition_leaving_a_boundary_is_classified_by_acl2_from_its_concrete_class(self):
        # Review M1: the host names the condition's concrete class, never a
        # parent; ACL2's tables are closed (books/failure-scope.lisp), so an
        # unlisted subclass is a fault, not the refusal its parent is.  Every
        # condition the host defines under fnn-store-error or fnn-os-error is
        # in a table.  Review M2: the step the boundary completed is named by
        # the namespace primitives, and the top-level classifier takes it.
        sys.path.insert(0, str(ROOT / "tools"))
        from ledger import head
        owner = (ROOT / "host/native/owner.lisp").read_text(encoding="utf-8")
        io = (ROOT / "host/native/io.lisp").read_text(encoding="utf-8")
        forms = self._forms("host/native/owner.lisp")
        shared = self._definition(forms, "defun", "fnn-owner-shared-action-locked")
        handler = next(f for f in self._nodes(shared) if head(f) == "handler-case")
        self.assertEqual([head(arm) for arm in handler[2:]], ["serious-condition"])
        self.assertTrue(list(self._ancestors(handler[2], "fnn-owner-classify-escape-locked")))
        classify = host_function(owner, "fnn-owner-classify-escape-locked")
        self.assertIn("(fn-fs-classify (fnn-condition-class condition) *fnn-section-step*)", classify)
        self.assertLess(classify.index("+fnn-exit-uncertain+"), classify.index("+fnn-exit-fault+"))
        condition_class = host_function(io, "fnn-condition-class")
        self.assertIn("(class-of condition)", condition_class)
        exit_code = host_function(io, "fnn-exit-code-for")
        self.assertNotIn("typecase", exit_code)
        self.assertIn("(fn-fs-exit-code (fnn-condition-class condition) step)", exit_code)
        book = (ROOT / "books/failure-scope.lisp").read_text(encoding="utf-8")
        tables = {}
        for name in ("indeterminate", "fault", "usage", "refusal", "os"):
            start = book.index("(defconst *fn-fs-{}-classes*".format(name))
            end = book.index("))", start)
            tables[name] = set(re.findall(r'"([a-z0-9-]+)"', book[start:end]))
        named = set().union(*tables.values())
        parents = {}
        for path in sorted((ROOT / "host/native").glob("*.lisp")):
            for cls, parent in re.findall(r"\(define-condition\s+([a-z0-9-]+)\s+\(([a-z0-9:-]+)",
                                          path.read_text(encoding="utf-8")):
                parents[cls] = parent

        def store_rooted(cls):
            while cls in parents:
                if cls in ("fnn-store-error", "fnn-os-error"):
                    return True
                cls = parents[cls]
            return cls in ("fnn-store-error", "fnn-os-error")

        rooted = {cls for cls in parents if store_rooted(cls)}
        self.assertEqual(sorted(rooted - named), [], "a host condition no table names")
        self.assertEqual(sorted(named - rooted - {"fnn-store-error", "fnn-os-error"}), [],
                         "a table names a condition the host does not define")
        # Each refusal is listed by its own name: fnn-store-error's subclasses
        # are not refusals by inheritance.
        self.assertIn("fnn-owner-admission-pending", tables["refusal"])
        self.assertEqual(parents["fnn-owner-admission-pending"], "fnn-store-error")
        self.assertIn("fnn-store-indeterminate", tables["indeterminate"])
        self.assertIn("fnn-extent-fault", tables["fault"])
        # The uncertain window is the byte model's: a rename or link that
        # landed opens it, the directory barrier closes it; an unlink (a
        # failed stage's cleanup) or a mkdir opens none.
        for primitive in ("fnn-link", "fnn-replace"):
            self.assertIn("(fnn-durable-step", host_function(io, primitive), primitive)
        for primitive in ("fnn-unlink", "fnn-mkdir", "fnn-at", "fnn-log-at"):
            self.assertNotIn("fnn-durable-step", host_function(io, primitive), primitive)
            self.assertNotIn("*fnn-section-step*", host_function(io, primitive), primitive)
        self.assertGreaterEqual(host_function(io, "fnn-rename-no-replace").count("(fnn-durable-step :replaced)"), 2)
        self.assertIn("(setq *fnn-section-step* nil)", host_function(io, "fnn-fsync-dir"))
        # the publisher is a private job: a failed stage write is a failed
        # publication (serving continues), not the service's fault
        self.assertIn('(fnn-owner-thread-escape service e "CHECKPOINT auto" t)',
                      host_function(owner, "fnn-owner-publish-captured"))
        self.assertIn("(fn-fs-classify-job (fnn-condition-class condition) *fnn-section-step*)",
                      host_function(owner, "fnn-owner-thread-escape"))
        for name in ("fnn-owner-committer-loop", "fnn-owner-publish-captured", "fnn-owner-export-captured"):
            self.assertIn("(*fnn-section-step* nil)", host_function(owner, name), name)

    def test_worker_threads_classify_through_the_thread_boundary(self):
        # Sweep S016 (Astra B1): the committer's refusal arm caught every store
        # fault and uncertain outcome and died silently with the batch in
        # flight.  S019 / t43 rows 233-235: the publisher's and the exporter's
        # parent catches logged an uncertain publication and served on.
        sys.path.insert(0, str(ROOT / "tools"))
        from ledger import head
        owner = (ROOT / "host/native/owner.lisp").read_text(encoding="utf-8")
        forms = self._forms("host/native/owner.lisp")
        escape = host_function(owner, "fnn-owner-thread-escape")
        self.assertIn("(fn-fs-classify (fnn-condition-class condition) *fnn-section-step*)", escape)
        self.assertLess(escape.index("(fnn-owner-fence-service service)"),
                        escape.index("(fnn-owner-fault-service service nil condition)"))
        committer = self._definition(forms, "defun", "fnn-owner-committer-loop")
        handler = next(f for f in self._nodes(committer) if head(f) == "handler-case")
        self.assertEqual([head(arm) for arm in handler[2:]], ["serious-condition"])
        self.assertTrue(list(self._ancestors(handler[2], "fnn-owner-thread-escape")))
        self.assertNotIn("(fnn-store-error ()", host_function(owner, "fnn-owner-committer-loop"))
        publisher = self._definition(forms, "defun", "fnn-owner-publish-captured")
        handlers = [f for f in self._nodes(publisher) if head(f) == "handler-case"]
        heads = [[head(arm) for arm in h[2:]] for h in handlers]
        # the write's arm names only the known refusal; the thread's arm is one
        self.assertIn(["fnn-store-io-refusal"], heads)
        self.assertNotIn(["(or", "fnn-store-io-refusal"], [h[:2] for h in heads])
        thread_arm = [h for h in handlers if [head(arm) for arm in h[2:]] == ["serious-condition"]
                      and list(self._ancestors(h[2], "fnn-owner-thread-escape"))]
        self.assertEqual(len(thread_arm), 1)
        self.assertNotIn("(or fnn-store-io-refusal fnn-store-indeterminate)",
                         host_function(owner, "fnn-owner-publish-captured"))
        # the publication's done step is a live quantum (refused once stopping)
        done = list(self._ancestors(publisher, "fn-owner-sco-publication-done"))
        self.assertTrue(done)
        self.assertIn("fnn-owner-serialized", [head(p) for p in done[0]])
        exporter = host_function(owner, "fnn-owner-export-captured")
        self.assertIn("(fn-fs-classify-job (fnn-condition-class e) *fnn-section-step*)", exporter)
        self.assertIn("(cons :uncertain :archive-publication)", exporter)
        book = (ROOT / "books/owner-export-request.lisp").read_text(encoding="utf-8")
        self.assertIn("(equal (car outcome) :uncertain)) :archive-uncertain)", book)
        self.assertIn("((equal word :archive-uncertain) :uncertain)", book)
        operator = (ROOT / "host/native/operator.lisp").read_text(encoding="utf-8")
        self.assertEqual(operator.count("(eq status-word :archive-uncertain)")
                         + operator.count("(eq word :archive-uncertain)"), 2)

    def test_the_stop_exit_escalates_on_the_lattice_and_a_failed_barrier_fences(self):
        # Sweep S015: the first stop won; a graceful SIGTERM's exit 0 hid a
        # barrier that failed after it.  ACL2's lattice decides the exit (a
        # fence is never masked), and the syncer's stopping branch fences the
        # store on a :stop step.
        owner = (ROOT / "host/native/owner.lisp").read_text(encoding="utf-8")
        stop = host_function(owner, "fnn-owner-stop-service-locked")
        self.assertIn("(fn-fs-stop-exit-escalate current exit-code)", stop)
        # the fence step (STOPPING, the exit code) precedes every log line
        self.assertLess(stop.index("(fn-fs-stop-exit-escalate"), stop.index("(fnn-err "))
        self.assertIn("dominated by exit", stop)
        pipeline = host_function(owner, "fnn-owner-commit-pipeline")
        told = pipeline.index("(fnn-owner-deliver service (first m) :uncertain)")
        fence = pipeline.index("(when (eq step :stop)", told)
        self.assertLess(fence, pipeline.index("((eq step :complete)", told))
        self.assertIn("(setf (fnn-store-fenced store) t)", pipeline[fence:fence + 400])
        self.assertIn("(fnn-owner-stop-service-locked service +fnn-exit-uncertain+)",
                      pipeline[fence:fence + 400])
        book = (ROOT / "books/failure-scope.lisp").read_text(encoding="utf-8")
        for theorem in ("fn-fs-stop-exit-fence-is-never-masked", "fn-fs-stop-exit-escalate-is-monotone",
                        "fn-fs-stop-exit-ok-is-the-bottom", "fn-fs-unknown-class-is-a-fault",
                        "fn-fs-os-error-after-a-durable-step-is-the-fence"):
            self.assertIn("(defthm {}\n".format(theorem), book)

    def test_the_reclaim_install_quantum_is_live_and_its_cleanup_finishes_before_the_raise(self):
        # r71 F1, sweep S017: the capture and the install/swap ran in bare
        # gated quanta (no stopping check, no fence); the cleanup raised before
        # finishing the pass and unlinked the stage after a fence.
        sys.path.insert(0, str(ROOT / "tools"))
        from ledger import head
        owner = (ROOT / "host/native/owner.lisp").read_text(encoding="utf-8")
        forms = self._forms("host/native/owner.lisp")
        reclaim = self._definition(forms, "defun", "fnn-owner-reclaim-pass")
        for target in ("fnn-state-checkpoint-install", "fn-owner-orcp-swap", "fnn-owner-reclaim-barriers",
                       "fn-owner-orcp-capture"):
            paths = list(self._ancestors(reclaim, target))
            self.assertTrue(paths, target)
            heads = [head(p) for p in paths[0]]
            self.assertIn("fnn-owner-serialized", heads, target)
            self.assertNotIn("fnn-owner-gated", heads, target)
        text = host_function(owner, "fnn-owner-reclaim-pass")
        cleanup = text[text.index("(when pin (fnn-arena-unpin pin))"):]
        finish = cleanup.index("'fn-owner-orcp-finish")
        unlink = cleanup.index("(fnn-unlink stage)")
        fence = cleanup.index("(fnn-owner-fence-service service)")
        raise_ = cleanup.index("reclaim swap failed after the install")
        self.assertLess(finish, unlink)
        self.assertLess(unlink, fence)
        self.assertLess(fence, raise_)
        self.assertNotIn("(ignore-errors (fnn-unlink stage))", cleanup)
        self.assertLess(cleanup.index("(not (fnn-owner-service-stopping service))"), unlink)

    def test_tcpcl_listen_re_signals_an_uncertain_outcome_and_a_fault(self):
        # Sweep S023: a store fault was this session's refusal and the loop
        # accepted the next peer after an uncertain staging barrier.
        sys.path.insert(0, str(ROOT / "tools"))
        from ledger import head
        forms = self._forms("host/native/tcpcl.lisp")
        listen = self._definition(forms, "defun", "fnn-command-tcpcl-listen")
        handler = next(f for f in self._nodes(listen) if head(f) == "handler-case")
        self.assertEqual([head(arm) for arm in handler[2:]], ["serious-condition"])
        self.assertTrue(list(self._ancestors(handler[2], "fn-fs-classify")))
        text = host_function((ROOT / "host/native/tcpcl.lisp").read_text(encoding="utf-8"),
                             "fnn-command-tcpcl-listen")
        self.assertIn("(t (error e))", text)
        self.assertNotIn("(fnn-store-error (e)", text)

    def test_a_node_secret_publication_barrier_failure_is_uncertain(self):
        # r72 F6: the directory barrier after the secret's rename escaped as a
        # raw OS error (exit 4) for what is an uncertain publication (exit 3).
        io = (ROOT / "host/native/io.lisp").read_text(encoding="utf-8")
        durable = host_function(io, "fnn-node-secret-durable")
        self.assertIn("(fnn-os-error (e)", durable)
        self.assertIn("(fnn-indeterminate ", durable)
        for name in ("fnn-node-secret-create", "fnn-node-secret-rotate"):
            text = host_function(io, name)
            self.assertIn("(fnn-node-secret-durable dir", text, name)
            # the only bare barrier left in rotate is the keep link's, before
            # any publication
            self.assertLessEqual(text.count("(fnn-fsync-dir dir)"), 1 if name.endswith("rotate") else 0, name)

    def test_an_admission_pending_verdict_is_a_refusal_of_the_request(self):
        # TCB-SHRINK review: fnn-owner-admission-pending was a serious condition
        # no handler named, ending the owner with exit 4; a pending verdict is
        # a refusal of that request, named, connection-scoped.
        owner = (ROOT / "host/native/owner.lisp").read_text(encoding="utf-8")
        self.assertIn("(define-condition fnn-owner-admission-pending (fnn-store-error)", owner)
        signal = host_function(owner, "fnn-owner-admission-pending")
        self.assertIn(":message", signal)
        verdict = host_function(owner, "fnn-owner-existing-verdict")
        self.assertNotIn("(error 'fnn-owner-admission-pending", verdict)
        self.assertEqual(verdict.count("(fnn-owner-admission-pending verdict)"), 2)
        book = (ROOT / "books/failure-scope.lisp").read_text(encoding="utf-8")
        self.assertIn('"fnn-owner-admission-pending"', book)

    def test_transit_take_uses_transfer_decision_and_store_outcome(self):
        # A transit take is a normal queued submission.  Treating the tag as
        # a fault stopped the whole owner before Store ran; the later reply
        # then surfaced only a secondary broken pipe.
        source = (ROOT / "host/native/owner.lisp").read_text()
        start = source.index("(defun fnn-owner-drain-one")
        end = source.index("(defun fnn-owner-complete-bound-submission", start)
        drain = source[start:end]
        self.assertIn("(eq taken :taken-control)", drain)
        self.assertNotIn("(not (eq taken :taken))", drain)
        self.assertIn("'fn-owner-transit-decide", drain)
        self.assertIn("'fn-owner-transit-evidence", drain)
        # The outcome and its service-log line go through one helper.
        self.assertIn("fnn-owner-transit-complete", drain)
        self.assertNotIn("'fn-owner-transit-outcome", drain)
        helper_start = source.index("(defun fnn-owner-transit-complete")
        helper = source[helper_start:start]
        self.assertIn("'fn-owner-transit-log-line", helper)
        self.assertIn("'fn-owner-transit-outcome", helper)
        self.assertIn("(fnn-owner-log)", helper)
        self.assertIn("(eq word :uncertain)", drain)

    def test_condition_handlers_and_cleanup_enclose_the_served_body(self):
        # Balanced source alone missed a live failure: handler clauses became
        # cleanup calls, and (e) invoked an undefined function on every EOF.
        # The served connection lives in host/native/mux.lisp (lane
        # connection-multiplexing): every event runs inside fnn-mux-guarded,
        # whose handlers are the per-connection worker's, and each ends in
        # fnn-mux-finish, the worker's unwind.  This checks macro structure;
        # the saved-image tests establish behavior.
        sys.path.insert(0, str(ROOT / "tools"))
        from ledger import head, read_forms
        forms = read_forms((ROOT / "host/native/mux.lisp").read_text())
        guarded = next(form for form in forms if head(form) == "defmacro"
                       and str(form[1]) == "fnn-mux-guarded")
        text = (ROOT / "host/native/mux.lisp").read_text()
        start = text.index("(defmacro fnn-mux-guarded")
        body = text[start:text.index("(defun fnn-mux-arm-idle", start)]
        order = ["(fnn-store-indeterminate (e)", "(fnn-store-fault (e)",
                 "(fnn-owner-connection-fault (e)",
                 "((or fnn-store-error fnn-os-error sb-bsd-sockets:socket-error) (e)",
                 "(fnn-tls-error (e)", "(serious-condition (e)"]
        at = [body.index(clause) for clause in order]
        self.assertEqual(at, sorted(at))
        self.assertEqual(body.count("(fnn-mux-finish ,l ,c)"), 6)
        self.assertTrue(guarded)
        finish = next(form for form in forms if head(form) == "defun"
                      and str(form[1]) == "fnn-mux-finish")
        start = text.index("(defun fnn-mux-finish")
        cleanup = text[start:text.index("(defmacro fnn-mux-guarded", start)]
        # Cleanup: the owner close (CID), the exposure release (the id
        # fn-exp-open registered, kept even when a fault path cleared CID;
        # PRF-161), the TLS channel, then the socket.
        steps = ["'fn-owner-close", "'fn-owner-exposure-release",
                 "(fnn-tls-close-channel", "(fnn-socket-shut"]
        at = [cleanup.index(step) for step in steps]
        self.assertEqual(at, sorted(at))
        self.assertTrue(finish)

    def test_no_os_error_after_publication_is_classified_as_a_refusal(self):
        # Campaign W2, 2026-09-24: an EIO at a finish cut escaped fnn-finish
        # and the owner's catch-all answered a durable article `441 ...
        # refused'.  Both finish cuts sit inside a handler that fences and
        # raises indeterminate, and no Store attempt maps an OS error to a
        # refusal word.
        sys.path.insert(0, str(ROOT / "tools"))
        from ledger import head, read_forms
        io_forms = read_forms((ROOT / "host/native/io.lisp").read_text())
        finish = next(form for form in io_forms if head(form) == "defun"
                      and str(form[1]) == "fnn-finish")

        def calls(form, parents=()):
            if isinstance(form, list):
                if (head(form) == "fnn-at" and len(form) == 3
                        and str(form[2]).startswith(":finish-")):
                    yield str(form[2]), [head(p) for p in parents]
                for child in form:
                    yield from calls(child, parents + (form,))
        cuts = dict(calls(finish))
        self.assertEqual(set(cuts), {":finish-consumed", ":finish-durable"})
        for cut, heads in cuts.items():
            self.assertEqual(heads[-1], "handler-case", cut)
        owner = (ROOT / "host/native/owner.lisp").read_text()
        self.assertNotIn("((or fnn-store-error fnn-os-error) () :refused)", owner)
        start = owner.index("(defmacro fnn-owner-attempt-handlers")
        end = owner.index("(defun fnn-owner-attempt ", start)
        self.assertIn("(fnn-os-error (e)", owner[start:end])
        self.assertIn(":uncertain)))", owner[start:end])

    def test_the_served_listener_passes_a_documented_accept_queue(self):
        # `ss -ltn` read `LISTEN 0 1` against the 915 node: the owner took
        # fnn-listen's default backlog, which is written for the one-client
        # diagnostic reader.  The accept thread hands each connection to a
        # worker, so a queue of one drops the client that arrives while it is
        # doing that.  The connection LIMIT is fn-own-open's and stays there.
        source = (ROOT / "host/native/owner.lisp").read_text()
        self.assertIn("(defconstant +fnn-owner-listen-backlog+", source)
        start = source.index("(defun fnn-owner-run ")
        self.assertIn(":backlog +fnn-owner-listen-backlog+", source[start:])

    def test_the_chunk_loop_keeps_its_suffix_and_reads_a_clock_per_step(self):
        # tests/native_owner_chunk_loop_raw.lisp evaluates the deployed
        # connection life (host/native/mux.lisp), fnn-owner-handle-chunk and
        # fnn-owner-advance-clock against recording stubs, so the two 915
        # defects have a check that needs no image.  The harness extracts the
        # closure of its roots from the host and refuses a stale stub or an
        # unstubbed callee by name, so a host change fails it at load, not as
        # a scenario's wrong answer; and it checks the time model's disk
        # clock event on the batched POST path.
        runtime = runtime_sbcl(IMAGE)
        if runtime is None:
            raise unittest.SkipTest("no SBCL runtime for the image and none on PATH")
        sbcl, sbcl_env = runtime
        result = subprocess.run(
            [sbcl, "--noinform", "--script",
             "tests/native_owner_chunk_loop_raw.lisp"],
            cwd=ROOT, env=sbcl_env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            timeout=180, check=False)
        output = result.stdout.decode("utf-8", "replace")
        self.assertEqual(result.returncode, 0, output)
        self.assertIn("suffix, refusal, no-progress, clock and time-event passed", output)


    def test_developer_selectors_gate_arm_the_owner_and_stop_synchronously(self):
        # tests/native_developer_selectors_raw.lisp evaluates the deployed
        # fnn-main, fnn-developer-selector and its gate, fnn-post-entry-fault,
        # fnn-owner-run-normalized, the control reply and the control stop
        # against recording stubs; the stop itself runs for real in forked
        # children.  Campaign dabebb84 findings F1 and F3 to F7.
        runtime = runtime_sbcl(IMAGE)
        if runtime is None:
            raise unittest.SkipTest("no SBCL runtime for the image and none on PATH")
        sbcl, sbcl_env = runtime
        result = subprocess.run(
            [sbcl, "--noinform", "--script",
             "tests/native_developer_selectors_raw.lisp"],
            cwd=ROOT, env=sbcl_env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            timeout=300, check=False)
        output = result.stdout.decode("utf-8", "replace")
        self.assertEqual(result.returncode, 0, output)
        self.assertIn("native developer selectors passed", output)


class NativeOwnerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not os.access(IMAGE, os.X_OK):
            raise unittest.SkipTest(
                "developer native image missing: {} "
                "(FN_NATIVE_PROFILE=developer tools/build_native_host.sh)".format(IMAGE))

    def setUp(self):
        self.node = Node(self, IMAGE, listener=False, control=False)
        self.store = self.node.store_path
        self.node.store("init", "fn.test", expect=EXIT.OK)

    def connect_owner(self, port):
        client = Client(port, timeout=30, greeting=(b"200",))
        self.addCleanup(client.close, False)
        return client

    def inspect(self, message_id):
        return self.node.store("inspect", message_id)

    def assert_live_writer_and_reader(self, port, writer, reader, message_id):
        first, final = writer.post(self.article(message_id, b"surviving native owner body\r\n"))
        self.assertTrue(first.startswith(b"340 "))
        self.assertTrue(final.startswith(b"240 "))

        # This connection predates the post and deliberately retains its
        # pinned archive snapshot.  Prove it is still served without asking
        # that old snapshot to expose a later commit.
        status, _ = reader.multiline(b"CAPABILITIES")
        self.assertTrue(status.startswith(b"101 "))

        # A fresh reader pins the post-commit archive and proves the healthy
        # writer's article became visible without restarting the service.
        current_reader = self.connect_owner(port)
        self.assertTrue(current_reader.command(b"GROUP fn.test").startswith(b"211 "))
        answer, received = current_reader.multiline(b"ARTICLE " + message_id)
        self.assertTrue(answer.startswith(b"220 "), answer)
        self.assertIn(b"Message-ID: " + message_id + b"\r\n", received)
        self.assertIn(b"surviving native owner body\r\n", received)

    @staticmethod
    def article(message_id, body=b"native owner body\r\n"):
        return (b"From: sender@example.invalid\r\n"
                b"Newsgroups: fn.test\r\n"
                b"Subject: native owner\r\n"
                b"Date: Mon, 21 Sep 2026 08:00:00 +0000\r\n"
                b"Message-ID: " + message_id + b"\r\n\r\n" + body)

    DISPATCH_ID = b"<dispatch-both-ways@example.invalid>"

    def served_post_transcript(self, env):
        """A fresh node's served POST, its duplicate, the group and the
        article read back, under ENV: (the reply lines, the owner's stderr).
        Lines with a clock reading (Date, Injection-Date) are not compared;
        the decisions and the stored octets are."""
        node = Node(self, IMAGE, listener=False, control=False)
        node.store("init", "fn.test", expect=EXIT.OK)
        process, port = node.start_store_owner(once=False, env=env)
        writer = self.connect_owner(port)
        first, final = writer.post(self.article(self.DISPATCH_ID, b"dispatch both ways\r\n"))
        dup_first, dup_final = writer.post(self.article(self.DISPATCH_ID, b"dispatch both ways\r\n"))
        reader = self.connect_owner(port)
        group = reader.command(b"GROUP fn.test")
        answer, received = reader.multiline(b"ARTICLE " + self.DISPATCH_ID)
        body = b"\r\n".join(line for line in received.split(b"\r\n")
                            if b"date:" not in line.lower())
        self.assertTrue(writer.command(b"QUIT").startswith(b"205 "))
        self.assertTrue(reader.command(b"QUIT").startswith(b"205 "))
        node.stop(process=process)
        return [first, final, dup_first, dup_final, group, answer, body], process.stderr.since(0)

    def test_unqualified_raw_annotations_stay_on_counterpart(self):
        # D40's real-owner annotations are withheld pending complete host
        # guard establishment and preservation. The selector must explicitly
        # report zero entries; both runs still exercise POST and retrieval.
        raw, raw_stderr = self.served_post_transcript(None)
        counterpart, counterpart_stderr = self.served_post_transcript(
            {"FN_NATIVE_DISPATCH_COUNTERPART": "1"})
        self.assertTrue(raw[0].startswith(b"340 "), raw[0])
        self.assertTrue(raw[1].startswith(b"240 "), raw[1])
        self.assertFalse(raw[3].startswith(b"240 "), raw[3])
        self.assertTrue(raw[5].startswith(b"220 "), raw[5])
        self.assertIn(b"dispatch both ways\r\n", raw[6])
        self.assertEqual(raw, counterpart)
        self.assertNotIn(b"fn-dispatch: counterpart", raw_stderr)
        match = re.search(rb"fn-dispatch: counterpart for (\d+) raw-dispatched entries",
                          counterpart_stderr)
        self.assertIsNotNone(match, counterpart_stderr[-2000:])
        self.assertEqual(int(match.group(1)), 0, counterpart_stderr[-2000:])

    def test_client_disconnect_is_not_a_global_owner_fault(self):
        process, port = self.node.start_store_owner(once=False)
        with socket.create_connection(("127.0.0.1", port), timeout=30) as client:
            self.assertTrue(client.makefile("rb", buffering=0).readline().startswith(b"200 "))
        with Client(port, timeout=30, greeting=(b"200",)) as client:
            self.assertTrue(client.command(b"QUIT").startswith(b"205 "))
        self.assertIsNone(process.poll(), "owner stopped after an ordinary disconnect")

    def test_reset_peer_does_not_stop_concurrent_writer_or_reader(self):
        process, port = self.node.start_store_owner(once=False)
        resetter = self.connect_owner(port)
        reader = self.connect_owner(port)
        writer = self.connect_owner(port)
        # Force an attributable transport reset.  The peer owns this
        # socket and no shared owner transition is in progress.
        resetter.sock.setsockopt(socket.SOL_SOCKET, socket.SO_LINGER, struct.pack("ii", 1, 0))
        resetter.close(quit=False)
        time.sleep(0.1)
        self.assert_live_writer_and_reader(
            port, writer, reader, b"<after-native-reset@example.invalid>")
        self.assertIsNone(process.poll(), "peer reset stopped the owner")

    def test_local_handler_fault_uses_core_fault_and_preserves_other_clients(self):
        process, port = self.node.start_store_owner(once=False, fault="connectionhandler")
        faulted = self.connect_owner(port)
        reader = self.connect_owner(port)
        writer = self.connect_owner(port)
        self.assertEqual(
            faulted.command(b"CAPABILITIES"),
            b"403 internal fault; this connection is closed and the server continues\r\n")
        # SCN-026: the 403 line and nothing else, then the server closes it
        # (an orderly EOF or a reset: the owner aborts the faulted socket).
        self.assertEqual(faulted.pending, b"")
        faulted.sock.settimeout(30)
        try:
            after = faulted.sock.recv(4096)
        except ConnectionResetError:
            after = b""
        self.assertEqual(after, b"")
        self.assert_live_writer_and_reader(
            port, writer, reader, b"<after-native-handler-fault@example.invalid>")
        self.assertIsNone(process.poll(), "local handler fault stopped the owner")

    def test_invalid_complete_feed_evidence_is_process_fault(self):
        feed = self.store / "feed"
        feed.mkdir()
        (feed / "bad.fnfd").write_bytes(b"not-a-valid-complete-feed-frame")
        result = self.node.invoke("owner", "run", self.store, "0", "1", "8",
                                  expect=EXIT.FAULT)
        self.assertIn(b"invalid complete FNFD evidence", result.stderr)

    def test_empty_v1_feed_namespace_is_preserved_as_conflicting_evidence(self):
        (self.store / "feed" / "v1").mkdir(parents=True)
        result = self.node.invoke("owner", "run", self.store, "0", "1", "8",
                                  expect=EXIT.FAULT)
        self.assertIn(b"empty FNFD v1 namespace", result.stderr)
        self.assertTrue((self.store / "feed" / "v1").is_dir())

    def test_configured_source_address_opens_native_transit_session(self):
        configured = native_peer_add(
            IMAGE, self.store, ["source", "source.invalid", "127.0.0.1", "9", "fn.*", "-",
                                "127.0.0.1", "true"], environment(), ROOT)
        self.assertEqual(configured.returncode, 0, configured.stderr.decode())

        process, port = self.node.start_store_owner()
        with Client(port, timeout=30, greeting=(b"200",)) as client:
            status, capabilities = client.multiline(b"CAPABILITIES")
            self.assertTrue(status.startswith(b"101 "))
            self.assertIn(b"IHAVE\r\n", capabilities.splitlines(keepends=True))
            self.assertTrue(client.command(b"IHAVE <native-transit@example.invalid>")
                            .startswith(b"335 "))
            # EOF, not QUIT: the once-owner finishes on the closed connection.
            client.close(quit=False)
        self.node.exited(EXIT.OK, process=process)

    def test_once_sigterm_closes_client_with_incomplete_post(self):
        process, port = self.node.start_store_owner()
        with Client(port, timeout=30, greeting=(b"200",)) as client:
            self.assertTrue(client.command(b"POST").startswith(b"340 "))
            client.send(b"From: incomplete")
            # Keep the client's descriptor open: this is SIGTERM,
            # not the easier ordinary-EOF shutdown path.
            process.terminate()
            _out, err = process.communicate(timeout=15)
            self.assertEqual(process.returncode, EXIT.OK, err.decode())

    def test_two_client_uncertainty_fences_before_later_mutation(self):
        process, port = self.node.start_store_owner(once=False, fault="postpublish")
        one = self.connect_owner(port)
        two = self.connect_owner(port)
        first, final = one.post(self.article(b"<uncertain-native-owner@example.invalid>"))
        self.assertTrue(first.startswith(b"340 "))
        # The poster is told, before the fence closes its connection
        # (campaign W1, 2026-09-24: it read a bare close).
        self.assertEqual(
            final, b"441 posting failed; the outcome is uncertain, do not repost\r\n")
        try:
            two.send(b"POST\r\n")
        except OSError:
            pass
        self.node.exited(EXIT.UNCERTAIN, process=process)
        # The already-open second session was shut down by the fence; it
        # cannot enter fn-owner-chunk after the ambiguous publication.
        try:
            later = two.line()
        except (OSError, EOFError):
            later = b""
        self.assertFalse(later.startswith(b"340 "), later)

        committed = self.inspect("<uncertain-native-owner@example.invalid>")
        self.assertEqual(committed.returncode, EXIT.OK, committed.stderr.decode())
        self.assertNotEqual(self.inspect("<later-native-owner@example.invalid>").returncode,
                            EXIT.OK)

    def test_uncertain_commit_reconciles_its_durable_feed_intent_on_restart(self):
        configured = native_peer_add(
            IMAGE, self.store, ["sink", "sink.example.invalid", "127.0.0.1", "9", "-", "fn.*",
                                "127.0.0.2", "true"], environment(), ROOT)
        self.assertEqual(configured.returncode, 0, configured.stderr.decode())

        msgid = b"<native-owner-feed-recovery@example.invalid>"
        article = self.article(msgid)
        process, port = self.node.start_store_owner(once=False, fault="postpublish")
        with Client(port, timeout=30, greeting=(b"200",)) as client:
            self.assertTrue(client.command(b"POST").startswith(b"340 "))
            client.send(dot_stuff(article) + b".\r\n")
            client.close(quit=False)
        self.node.exited(EXIT.UNCERTAIN, process=process)

        journal = self.store / "feed" / "sink.fnfd"
        self.assertTrue(journal.is_file())
        intent_size = journal.stat().st_size
        self.assertGreater(intent_size, 0)

        # Opening the same native owner resolves the retained intent against
        # the physically committed Store record before it serves a client.
        restarted, port = self.node.start_store_owner()
        with Client(port, timeout=30, greeting=(b"200",)) as client:
            self.assertTrue(client.command(b"QUIT").startswith(b"205 "))
            client.close(quit=False)
        self.node.exited(EXIT.OK, process=restarted)
        self.assertGreater(journal.stat().st_size, intent_size)

        inspected = self.inspect(msgid.decode("ascii"))
        self.assertEqual(inspected.returncode, EXIT.OK, inspected.stderr.decode())
        self.assertTrue(inspected.stdout.endswith(article), inspected.stdout[-80:])

    def test_post_is_committed_and_readable_after_owner_exit(self):
        process, port = self.node.start_store_owner()
        article = self.article(
            b"<native-owner@example.invalid>",
            (b"0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ\r\n"
             * 145))
        self.assertGreater(len(article), 8192)
        self.assertLessEqual(len(article), 32768)
        with Client(port, timeout=30, greeting=(b"200",)) as client:
            first, final = client.post(article)
            self.assertTrue(first.startswith(b"340 "))
            self.assertTrue(final.startswith(b"240 "))
            self.assertTrue(client.command(b"QUIT").startswith(b"205 "))
            client.close(quit=False)
        self.node.exited(EXIT.OK, process=process)
        inspected = self.inspect("<native-owner@example.invalid>")
        self.assertEqual(inspected.returncode, EXIT.OK, inspected.stderr.decode())
        # The injection transition prepends the ACL2-produced Path field.  The
        # accepted source article, including the 9 KiB body, remains exact.
        self.assertTrue(inspected.stdout.startswith(
            b"Path: fn.example.invalid!not-for-mail\r\n"), inspected.stdout[:80])
        self.assertTrue(inspected.stdout.endswith(article), inspected.stdout[-80:])

    def test_article_over_the_body_limit_is_refused_and_the_owner_survives(self):
        # The 915 node's first defect.  An article whose CRLF-canonical size
        # passes fn-own-body-limit (books/owner.lisp; *fn-record-max-payload*
        # is 32768) closes the wire mid-article -- books/wire.lisp
        # fn-wire-after-line answers (fn-wire-close ... :body-overlimit) -- so
        # the served step consumes a PREFIX of the socket read and leaves the
        # rest.  The host used to fault on that suffix and stop the process,
        # taking the listener with it.  The answer is the model's and was read
        # out of the certified books/served-tls-prefix on 2026-09-22: over one
        # chunk carrying POST and an article past the limit,
        # fn-served-step-counted consumes 61 of 130 octets and emits
        # (:reply :begin-article :reply :close) whose second reply is the line
        # below (books/nntp-post.lisp fn-nntp-post-step, on the :reject event
        # fn-wire-close raised).  That run is in
        # planning/evidence/owner-defects-2026-09-22.md.
        process, port = self.node.start_store_owner(once=False)
        oversize = self.article(b"<native-owner-oversize@example.invalid>",
                                b"z" * 70 + b"\r\n")
        oversize += b"y" * 70 + b"\r\n"
        while len(oversize) < 40960:
            oversize += b"y" * 70 + b"\r\n"
        self.assertGreater(len(oversize), 32768)
        client = self.connect_owner(port)
        self.assertTrue(client.command(b"POST").startswith(b"340 "))
        try:
            client.send(dot_stuff(oversize) + b".\r\n")
        except OSError:
            # The node refused and closed while the body was still going
            # out.  That is the refusal arriving early, not a failure.
            pass
        try:
            answer = client.line()
        except (OSError, EOFError):
            answer = b""
        self.assertEqual(
            answer,
            b"441 posting failed; the article exceeds the configured size\r\n",
            "an oversize article got {!r}".format(answer))
        client.close(quit=False)

        # The listener is still there and still serves, which is the whole
        # point: one long article is not a reason to stop the node.
        with Client(port, timeout=30, greeting=(b"200",)) as later:
            self.assertTrue(later.command(b"QUIT").startswith(b"205 "))
        self.assertIsNone(process.poll(), "an oversize article stopped the owner")

        # Nothing durable came of a refused article.
        self.assertNotEqual(self.inspect("<native-owner-oversize@example.invalid>").returncode,
                            EXIT.OK)

    def date_reading(self, port):
        with Client(port, timeout=30, greeting=(b"200",)) as client:
            line = client.command(b"DATE")
        self.assertTrue(line.startswith(b"111 "), line)
        return line.split()[1]

    def post_article(self, port, message_id, dated=True):
        # An article that supplies Date and Message-ID gets no Injection-Date
        # (RFC 5537 section 3.5 item 11), so a test of the injection clock
        # posts without a Date.
        article = self.article(message_id)
        if not dated:
            article = article.replace(b"Date: Mon, 21 Sep 2026 08:00:00 +0000\r\n", b"")
        with Client(port, timeout=30, greeting=(b"200",)) as client:
            first, final = client.post(article)
            self.assertTrue(first.startswith(b"340 "))
            self.assertTrue(final.startswith(b"240 "))

    def injection_date(self, message_id):
        inspected = self.inspect(message_id.decode("ascii"))
        self.assertEqual(inspected.returncode, EXIT.OK, inspected.stderr.decode())
        found = re.search(br"^Injection-Date: (.*)\r$", inspected.stdout,
                          re.MULTILINE)
        self.assertIsNotNone(found, inspected.stdout[:400])
        return found.group(1)

    def test_date_on_connection_older_than_a_minute_is_current(self):
        process, port = self.node.start_store_owner(once=False)
        with Client(port, timeout=30, greeting=(b"200",)) as client:
            first = client.command(b"DATE")
            self.assertTrue(first.startswith(b"111 "), first)
            opened = time.monotonic()
            # Keep this same connection active so idle policy cannot turn
            # the clock regression into a reconnect test.
            while time.monotonic() - opened <= 61:
                time.sleep(5)
                self.assertTrue(client.command(b"DATE").startswith(b"111 "))
            before = time.time()
            answer = client.command(b"DATE")
            after = time.time()
            self.assertTrue(answer.startswith(b"111 "), answer)
            current = datetime.datetime.strptime(
                answer.split()[1].decode("ascii"), "%Y%m%d%H%M%S"
            ).replace(tzinfo=datetime.timezone.utc).timestamp()
            self.assertNotEqual(first, answer)
            self.assertGreaterEqual(current, before - 3, answer)
            self.assertLessEqual(current, after + 3, answer)
        self.assertIsNone(process.poll(), "the owner stopped mid-run")

    def test_each_submission_and_each_connection_take_a_fresh_reading(self):
        # The 915 node's second defect.  Every article of a run carried one
        # Date and one Injection-Date and DATE answered one value for the life
        # of the process, because the native host took a clock reading at
        # startup and never again.  books/owner.lisp fn-own-open pins a
        # reading as the connection's READER environment and fn-own-read takes
        # the owner's CURRENT reading per read, so each submission is injected
        # at its own time (RFC 5537 section 3.4): supplying them is the host's
        # job, and tools/run_owner.py already did it at both points.
        process, port = self.node.start_store_owner(once=False)
        first = self.date_reading(port)
        self.post_article(port, b"<native-owner-clock-one@example.invalid>", dated=False)
        # Past the one-second resolution of the rendered value, so a fresh
        # reading cannot be mistaken for the pinned one.
        time.sleep(1.2)
        second = self.date_reading(port)
        self.post_article(port, b"<native-owner-clock-two@example.invalid>", dated=False)
        self.assertLess(first, second, "DATE answered {!r} twice".format(first))
        self.assertIsNone(process.poll(), "the owner stopped mid-run")
        self.node.stop(expect=None, process=process)

        one = self.injection_date(b"<native-owner-clock-one@example.invalid>")
        two = self.injection_date(b"<native-owner-clock-two@example.invalid>")
        self.assertNotEqual(one, two,
                            "both articles were injected at {!r}".format(one))


if __name__ == "__main__":
    unittest.main()
