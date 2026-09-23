"""tools/proof_repl.py: a live ACL2 session driven one form at a time.

The reader, the trimming and the sentinel protocol are tested against a fake
ACL2 that speaks just enough of the loop; one case runs the real ACL2 when
one is on PATH, since the point of the tool is the seconds-per-try loop the
freeze lanes did not have (review of 2026-09-22, F1 and F5).
"""
from __future__ import annotations

import json
import os
import pathlib
import shutil
import signal
import stat
import subprocess
import sys
import tempfile
import unittest
from contextlib import nullcontext
from types import SimpleNamespace
from unittest import mock

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import proof_repl  # noqa: E402
from tests.test_certs import manifest_for, worktree, TEST_COMPATIBILITY  # noqa: E402

FAKE_ACL2 = r'''#!/usr/bin/env python3
import sys
for line in sys.stdin:
    text = line.strip()
    if text.startswith('(cw "~%FN-REPL-DONE'):
        print(text.split('FN-REPL-DONE ')[1].split('~%')[0].join(["FN-REPL-DONE ", ""]))
        sys.stdout.flush()
        continue
    if "(good-bye)" in text:
        break
    if "(defthm bad" in text:
        print("ACL2 Error [Failure] in ( DEFTHM BAD ...):  See :DOC failure.")
    elif "(defthm" in text or "(defun" in text or "with-prover-time-limit" in text:
        for i in range(70):
            print("Subgoal *1/%d" % i)
        print("*** Key checkpoint at the top level: ***")
        print("Summary")
        print("Form:  ( DEFTHM OK ...)")
    else:
        print("GOT " + text)
    sys.stdout.flush()
'''


class ReaderTests(unittest.TestCase):
    def test_forms_keep_raw_text_quotes_and_strings_and_drop_comments(self):
        text = ('; comment (a)\n(in-package "ACL2")\n'
                "'(quoted form)\n"
                '(defthm t1 (equal "a ) b" "a ) b") :hints (("Goal")))\n'
                "#| block ( |# (local (defthm t2 t))\n")
        self.assertEqual(proof_repl.forms(text),
                         ['(in-package "ACL2")', "'(quoted form)",
                          '(defthm t1 (equal "a ) b" "a ) b") :hints (("Goal")))',
                          "(local (defthm t2 t))"])

    def test_head_and_name_sees_through_local_and_names_only_events(self):
        self.assertEqual(proof_repl.head_and_name("(defthm foo t)"), ("defthm", "foo"))
        self.assertEqual(proof_repl.head_and_name("(local (defthm Foo t))"), ("defthm", "foo"))
        self.assertEqual(proof_repl.head_and_name("(in-theory (enable x))"), ("in-theory", None))
        self.assertTrue(proof_repl.is_event("(defun f (x) x)"))
        self.assertFalse(proof_repl.is_event('(include-book "x")'))

    def test_an_event_is_wrapped_in_a_prover_time_limit_and_a_query_is_not(self):
        self.assertEqual(proof_repl.wrap_limit("(defthm a t)", 30),
                         "(with-prover-time-limit 30 (defthm a t))")
        self.assertEqual(proof_repl.wrap_limit("(pe 'a)", 30), "(pe 'a)")

    def test_brief_keeps_the_checkpoints_and_summary_of_a_long_output(self):
        long = "\n".join(["Goal", "x"] + ["Subgoal %d" % i for i in range(100)]
                         + ["*** Key checkpoint at the top level: ***", "(NOT (P X))",
                            "Summary", "Time: 1.0"])
        out = proof_repl.brief(long)
        self.assertIn("*** Key checkpoint", out)
        self.assertIn("Time: 1.0", out)
        self.assertNotIn("Subgoal 50", out)
        self.assertEqual(proof_repl.brief("short\noutput"), "short\noutput")
        self.assertTrue(proof_repl.errored("ACL2 Error [Failure] in ( DEFTHM X ...)"))


class CacheStartupTests(unittest.TestCase):
    def test_incompatible_cached_parent_and_child_refuse_without_session(self):
        with tempfile.TemporaryDirectory() as temporary:
            base = pathlib.Path(temporary)
            older = worktree(str(base / "older"), certified=["books/base"])
            parent = worktree(str(base / "parent"), certified=["books/mid"])
            target = worktree(str(base / "target"), certified=["books/base", "books/mid"])
            cache = base / "cache"
            toolchain = proof_repl.certs.stable_identity(TEST_COMPATIBILITY)
            for source, name, origin in (
                    (older, "books/base", "/farm/base"),
                    (parent, "books/mid", "/farm/parent")):
                proof_repl.certs.publish(
                    source, cache, [manifest_for(source, [name], write=False)],
                    [name], origin=origin, origin_kind="run")
            fake_acl2 = base / "acl2"
            fake_acl2.write_text("#!/bin/sh\nexit 0\n")
            fake_acl2.chmod(0o755)
            sessions = base / "sessions"
            args = SimpleNamespace(name="bad-cache", book="tests/acl2/mid-tests")
            with mock.patch.object(proof_repl, "ROOT", target), \
                 mock.patch.object(proof_repl, "SESSIONS", sessions), \
                 mock.patch.dict(os.environ, {"FN_ACL2": str(fake_acl2)}), \
                 mock.patch.object(proof_repl.certs, "cache_directory",
                                   return_value=cache), \
                 mock.patch.object(proof_repl.acl2_toolchain, "fingerprint",
                                   return_value=SimpleNamespace(
                                       qualified=True, identity=toolchain,
                                       reason="")), \
                 mock.patch.object(proof_repl.acl2_slots, "slot",
                                   side_effect=lambda label: nullcontext()), \
                 mock.patch.object(proof_repl.certs.cert_alists,
                                   "acl2_certificate_pairs",
                                   side_effect=lambda paths, pairs, acl2, root:
                                       {pair: (True, False) for pair in pairs}), \
                 mock.patch.object(proof_repl.subprocess, "Popen") as launched:
                self.assertEqual(proof_repl.start(args), 1)
                launched.assert_not_called()
            self.assertFalse((sessions / "bad-cache").exists())
            self.assertFalse((target / "books/base.cert").exists())
            self.assertFalse((target / "books/mid.cert").exists())


class ProcessLifetimeTests(unittest.TestCase):
    def test_stopping_busy_session_stops_descendants_and_releases_output(self):
        # A busy prover can have its own child holding the output pipe open.
        # The old wrapper-only kill left both alive until their sleep ended.
        with tempfile.TemporaryDirectory() as temporary:
            base = pathlib.Path(temporary)
            fake = base / "busy-acl2"
            child = "import time; print('DESCENDANT_READY', flush=True); time.sleep(60)"
            fake.write_text("#!" + sys.executable + "\nimport subprocess, sys, time\n"
                            + "subprocess.Popen([sys.executable, '-c', " + repr(child) + "])\n"
                            + "time.sleep(60)\n")
            fake.chmod(0o755)
            with mock.patch.dict(os.environ, {"FN_ACL2": str(fake),
                    "FN_ACL2_SLOT_DIR": str(base / "slots"), "FN_ACL2_SLOTS": "1"}):
                session = proof_repl.Acl2("busy-test", base / "log")
                try:
                    self.assertEqual(session.lines.get(timeout=10).strip(), "DESCENDANT_READY")
                    session.kill()
                    self.assertIsNotNone(session.process.returncode)
                    self.assertFalse(session.reader.is_alive())
                    self.assertTrue(session.log.closed)
                    # Stop is idempotent after the owned process group is gone.
                    session.kill()
                finally:
                    try:
                        os.killpg(session.process.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    session.process.wait(timeout=5)


class SessionTests(unittest.TestCase):
    """The protocol against a fake ACL2, end to end through the command line."""

    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory()
        fake = pathlib.Path(cls.tmp.name) / "fake-acl2"
        fake.write_text(FAKE_ACL2)
        fake.chmod(fake.stat().st_mode | stat.S_IXUSR)
        cls.env = {**os.environ, "FN_ACL2": str(fake)}
        cls.scratch = ROOT / "build" / "proof-repl-test"
        cls.scratch.mkdir(parents=True, exist_ok=True)
        (cls.scratch / "scratch.lisp").write_text(
            '(in-package "ACL2")\n(defun f (x) x)\n(defthm bad (equal 1 2))\n'
            "(defthm never (equal 2 2))\n")
        cls.name = "test-%d" % os.getpid()

    @classmethod
    def tearDownClass(cls):
        cls.cli("stop", cls.name)
        shutil.rmtree(proof_repl.SESSIONS / cls.name, ignore_errors=True)
        shutil.rmtree(cls.scratch, ignore_errors=True)
        cls.tmp.cleanup()

    @classmethod
    def cli(cls, *words, timeout=120):
        return subprocess.run([sys.executable, str(ROOT / "tools" / "proof_repl.py"), *words],
                              capture_output=True, text=True, env=cls.env, cwd=ROOT,
                              timeout=timeout)

    def test_1_start_loads_up_to_the_first_refused_form_and_reports_it(self):
        result = self.cli("start", self.name, "build/proof-repl-test/scratch",
                          "--limit", "5", "--load-timeout", "20")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("stopped at bad", result.stdout)
        state = json.loads((proof_repl.SESSIONS / self.name / "state.json").read_text())
        self.assertEqual(state["loaded"], ["in-package", "f"])
        self.assertTrue(state["ready"])

    def test_2_send_answers_with_the_trimmed_output_and_the_exit_says_error(self):
        ok = self.cli("send", self.name, "(defthm good t)", "--limit", "5")
        self.assertEqual(ok.returncode, 0, ok.stdout + ok.stderr)
        self.assertIn("*** Key checkpoint", ok.stdout)
        self.assertNotIn("Subgoal *1/50", ok.stdout)
        full = self.cli("send", self.name, "(defthm good t)", "--full")
        self.assertIn("Subgoal *1/50", full.stdout)
        bad = self.cli("send", self.name, "(defthm bad t)")
        self.assertEqual(bad.returncode, 1)
        self.assertIn("ACL2 Error", bad.stdout)
        two = self.cli("send", self.name, "(a) (b)")
        self.assertEqual(two.returncode, 1)
        self.assertIn("exactly one form", two.stdout)
        log = (proof_repl.SESSIONS / self.name / "log").read_text()
        self.assertIn(">>> (with-prover-time-limit 5 (defthm good t))", log)

    def test_3_status_and_stop(self):
        status = self.cli("status", self.name)
        self.assertIn("live", status.stdout)
        self.assertIn("sends", status.stdout)
        stopped = self.cli("stop", self.name)
        self.assertEqual(stopped.returncode, 0, stopped.stdout)
        self.assertFalse((proof_repl.SESSIONS / self.name / "sock").exists())
        again = self.cli("send", self.name, "(defthm x t)")
        self.assertEqual(again.returncode, 1)


@unittest.skipUnless(shutil.which(os.environ.get("FN_ACL2", "acl2")), "no ACL2 on PATH")
class RealAcl2Tests(unittest.TestCase):
    def test_a_true_theorem_is_admitted_and_a_false_one_is_refused(self):
        scratch = ROOT / "build" / "proof-repl-real"
        scratch.mkdir(parents=True, exist_ok=True)
        (scratch / "tiny.lisp").write_text(
            '(in-package "ACL2")\n(defun f (x) x)\n(defthm f-id (equal (f x) x))\n')
        name = "real-%d" % os.getpid()
        cli = lambda *w: subprocess.run(  # noqa: E731
            [sys.executable, str(ROOT / "tools" / "proof_repl.py"), *w],
            capture_output=True, text=True, cwd=ROOT, timeout=300)
        try:
            started = cli("start", name, "build/proof-repl-real/tiny", "--upto", "f-id",
                          "--limit", "20")
            self.assertEqual(started.returncode, 0, started.stdout + started.stderr)
            self.assertIn("last loaded: f", started.stdout)
            good = cli("send", name, "(defthm f-id (equal (f x) x))")
            self.assertEqual(good.returncode, 0, good.stdout)
            self.assertIn("Summary", good.stdout)
            bad = cli("send", name, "(defthm f-wrong (equal (f x) 1))")
            self.assertEqual(bad.returncode, 1)
            self.assertIn("ACL2 Error", bad.stdout)
        finally:
            cli("stop", name)
            shutil.rmtree(proof_repl.SESSIONS / name, ignore_errors=True)
            shutil.rmtree(scratch, ignore_errors=True)


if __name__ == "__main__":
    unittest.main()
