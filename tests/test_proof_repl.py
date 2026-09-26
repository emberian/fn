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
import socket
import stat
import subprocess
import sys
import tempfile
import threading
import time
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
    def test_start_preserves_an_old_live_json_server(self):
        with tempfile.TemporaryDirectory() as temporary:
            sessions = pathlib.Path(temporary)
            directory = sessions / "old-session"
            directory.mkdir()
            listener = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
            listener.bind(str(directory / "sock"))
            listener.listen(1)
            received = []

            def answer():
                connection, _ = listener.accept()
                with connection:
                    received.append(json.loads(proof_repl.read_all(connection)))
                    connection.sendall(b'{"state":{"ready":true}}')

            worker = threading.Thread(target=answer)
            worker.start()
            try:
                args = SimpleNamespace(name="old-session", book="books/irrelevant")
                with mock.patch.object(proof_repl, "SESSIONS", sessions), \
                     mock.patch.object(proof_repl, "install_closure") as acquire:
                    self.assertEqual(proof_repl.start(args), 2)
                    acquire.assert_not_called()
                self.assertTrue(worker.is_alive(), "start must not touch the old socket")
                with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as client:
                    client.connect(str(directory / "sock"))
                    client.sendall(b'{"op":"status"}')
                    client.shutdown(socket.SHUT_WR)
                    self.assertEqual(json.loads(proof_repl.read_all(client)),
                                     {"state": {"ready": True}})
                worker.join(timeout=2)
                self.assertEqual(received, [{"op": "status"}])
                self.assertTrue((directory / "sock").exists())
            finally:
                listener.close()

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
                    if not session._terminated:
                        session.kill()

    def test_duplicate_start_cannot_detach_an_older_server(self):
        # The first start holds the name while its fake ACL2 is still loading.
        # A retry must not replace its socket and leave its child behind.
        with tempfile.TemporaryDirectory() as temporary:
            base = pathlib.Path(temporary)
            fake = base / "slow-acl2"
            heartbeat = base / "heartbeat"
            child = (
                "import os,time; from pathlib import Path; "
                "p=Path(os.environ['FN_REPL_TEST_HEARTBEAT']); "
                "\nwhile True:\n"
                " with p.open('a') as stream: stream.write('x')\n"
                " time.sleep(.05)\n"
            )
            fake.write_text(
                "#!" + sys.executable + "\nimport subprocess,sys,time\n"
                + "subprocess.Popen([sys.executable, '-c', " + repr(child) + "])\n"
                + "time.sleep(1)\n"
                + "for line in sys.stdin:\n"
                + " if '(good-bye)' in line: break\n"
                + " if 'FN-REPL-DONE ' in line:\n"
                + "  print('FN-REPL-DONE ' + line.split('FN-REPL-DONE ')[1].split('~%')[0], flush=True)\n"
            )
            fake.chmod(0o755)
            scratch = ROOT / "build" / ("proof-repl-lock-test-" + str(os.getpid()))
            scratch.mkdir(parents=True, exist_ok=True)
            (scratch / "tiny.lisp").write_text('(in-package "ACL2")\n')
            name = "lock-test-" + str(os.getpid())
            env = {**os.environ, "FN_ACL2": str(fake),
                   "FN_ACL2_SLOT_DIR": str(base / "slots"),
                   "FN_ACL2_SLOTS": "1",
                   "FN_REPL_TEST_HEARTBEAT": str(heartbeat)}
            command = [sys.executable, str(ROOT / "tools" / "proof_repl.py")]
            first = subprocess.Popen(
                command + ["start", name, str((scratch / "tiny").relative_to(ROOT)),
                           "--load-timeout", "10"],
                cwd=ROOT, env=env, stdout=subprocess.PIPE,
                stderr=subprocess.PIPE, text=True,
            )
            try:
                lock = proof_repl.session_lock_path(name)
                deadline = time.monotonic() + 5
                while not lock.exists() and time.monotonic() < deadline:
                    time.sleep(.01)
                self.assertTrue(lock.exists())
                second = subprocess.run(
                    command + ["start", name,
                               str((scratch / "tiny").relative_to(ROOT)),
                               "--load-timeout", "10"],
                    cwd=ROOT, env=env, capture_output=True, text=True, timeout=5,
                )
                self.assertEqual(second.returncode, 2, second.stdout + second.stderr)
                self.assertIn("starting or live", second.stdout)
                out, err = first.communicate(timeout=15)
                self.assertEqual(first.returncode, 0, out + err)
                self.assertTrue(heartbeat.exists())
                stopped = subprocess.run(command + ["stop", name], cwd=ROOT,
                                         env=env, capture_output=True, text=True,
                                         timeout=15)
                self.assertEqual(stopped.returncode, 0,
                                 stopped.stdout + stopped.stderr)
                count = len(heartbeat.read_text())
                time.sleep(.2)
                self.assertEqual(len(heartbeat.read_text()), count)
                self.assertFalse((proof_repl.session_dir(name) / "sock").exists())
            finally:
                if first.poll() is None:
                    first.terminate()
                    first.wait(timeout=5)
                if (proof_repl.session_dir(name) / "sock").exists():
                    subprocess.run(command + ["stop", name], cwd=ROOT, env=env,
                                   capture_output=True, timeout=15)
                shutil.rmtree(proof_repl.session_dir(name), ignore_errors=True)
                shutil.rmtree(scratch, ignore_errors=True)


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


class OwnershipTests(unittest.TestCase):
    """PKT-346: a session carries its lane and an idle deadline; list and reap."""

    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory()
        fake = pathlib.Path(cls.tmp.name) / "fake-acl2"
        fake.write_text(FAKE_ACL2)
        fake.chmod(fake.stat().st_mode | stat.S_IXUSR)
        cls.env = {**os.environ, "FN_ACL2": str(fake),
                   "FN_ACL2_SLOT_DIR": str(pathlib.Path(cls.tmp.name) / "slots"),
                   "FN_ACL2_SLOTS": "4"}
        cls.scratch = ROOT / "build" / ("proof-repl-own-" + str(os.getpid()))
        cls.scratch.mkdir(parents=True, exist_ok=True)
        (cls.scratch / "tiny.lisp").write_text('(in-package "ACL2")\n(defun f (x) x)\n')
        cls.book = str((cls.scratch / "tiny").relative_to(ROOT))
        cls.names = []

    @classmethod
    def tearDownClass(cls):
        for name in cls.names:
            cls.cli("stop", name)
            shutil.rmtree(proof_repl.SESSIONS / name, ignore_errors=True)
        shutil.rmtree(cls.scratch, ignore_errors=True)
        cls.tmp.cleanup()

    @classmethod
    def cli(cls, *words, timeout=60):
        return subprocess.run([sys.executable, str(ROOT / "tools" / "proof_repl.py"), *words],
                              capture_output=True, text=True, env=cls.env, cwd=ROOT,
                              timeout=timeout)

    def start(self, suffix, *extra):
        name = f"own-{suffix}-{os.getpid()}"
        self.names.append(name)
        answer = self.cli("start", name, self.book, "--load-timeout", "20", *extra)
        self.assertEqual(answer.returncode, 0, answer.stdout + answer.stderr)
        return name

    def state(self, name):
        return json.loads((proof_repl.SESSIONS / name / "state.json").read_text())

    def test_a_session_records_its_lane_and_stops_itself_when_idle(self):
        name = self.start("idle", "--lane", "lane-idle", "--idle-seconds", "1.5")
        state = self.state(name)
        self.assertEqual(state["lane"], "lane-idle")
        self.assertEqual(state["idle_seconds"], 1.5)
        self.assertIsInstance(state["acl2_pgid"], int)
        deadline = time.monotonic() + 20
        while time.monotonic() < deadline and (proof_repl.SESSIONS / name / "sock").exists():
            time.sleep(0.2)
        self.assertFalse((proof_repl.SESSIONS / name / "sock").exists())
        state = self.state(name)
        self.assertIn("idle", state["ended"])
        self.assertFalse(state["ready"])
        # The name, and with it the slot, is free again.
        fd = proof_repl.open_session_lock(name)
        self.assertIsNotNone(fd)
        os.close(fd)

    def test_a_send_postpones_the_idle_deadline_and_a_status_does_not(self):
        name = self.start("busy", "--lane", "lane-busy", "--idle-seconds", "3")
        for _ in range(4):
            time.sleep(1)
            self.assertEqual(self.cli("send", name, "(+ 1 2)").returncode, 0)
        self.assertTrue((proof_repl.SESSIONS / name / "sock").exists())
        for _ in range(8):
            time.sleep(1)
            if not (proof_repl.SESSIONS / name / "sock").exists():
                break
            self.cli("status", name)
        self.assertFalse((proof_repl.SESSIONS / name / "sock").exists())

    def test_list_names_the_lane_and_reap_by_lane_stops_only_that_lane(self):
        mine = self.start("reap-a", "--lane", f"lane-a-{os.getpid()}")
        other = self.start("reap-b", "--lane", f"lane-b-{os.getpid()}")
        listing = self.cli("list")
        self.assertEqual(listing.returncode, 0, listing.stderr)
        row = next(line for line in listing.stdout.splitlines() if line.startswith(mine))
        self.assertIn(f"lane-a-{os.getpid()}", row)
        self.assertIn("live", row)
        self.assertIn("2h00m", row)  # the default deadline, stated
        dry = self.cli("reap", "--lane", f"lane-a-{os.getpid()}", "--dry-run")
        self.assertIn(f"would reap {mine}", dry.stdout)
        self.assertTrue((proof_repl.SESSIONS / mine / "sock").exists())
        reaped = self.cli("reap", "--lane", f"lane-a-{os.getpid()}")
        self.assertIn(f"reaped {mine}", reaped.stdout)
        self.assertIn("stopped through its socket", reaped.stdout)
        self.assertNotIn(other, reaped.stdout)
        self.assertFalse((proof_repl.SESSIONS / mine / "sock").exists())
        self.assertTrue((proof_repl.SESSIONS / other / "sock").exists())
        self.assertEqual(self.cli("stop", other).returncode, 0)

    def test_reap_signals_only_pids_that_are_still_the_session(self):
        # A dead server whose recorded PIDs now belong to unrelated processes:
        # reap removes the stale socket and signals nobody.
        with tempfile.TemporaryDirectory() as temporary:
            sessions = pathlib.Path(temporary)
            stranger = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(60)"])
            try:
                directory = sessions / "ghost"
                directory.mkdir()
                (directory / "state.json").write_text(json.dumps({
                    "name": "ghost", "book": "books/x", "pid": stranger.pid,
                    "acl2_pgid": stranger.pid, "loaded": [], "sends": 0,
                    "lane": "gone", "idle_seconds": 1, "last_active": 0}))
                (directory / "sock").write_text("")
                with mock.patch.object(proof_repl, "SESSIONS", sessions):
                    rows = proof_repl.session_rows()
                    self.assertFalse(rows[0]["server"])
                    self.assertEqual(proof_repl.reap_reason(rows[0], None, None), "dead server")
                    self.assertEqual(proof_repl.reap_one(rows[0]), "removed a stale socket")
                self.assertIsNone(stranger.poll())
                self.assertFalse((directory / "sock").exists())
            finally:
                stranger.kill()
                stranger.wait()

    def test_an_older_sessions_idle_time_is_its_state_files_age(self):
        with tempfile.TemporaryDirectory() as temporary:
            sessions = pathlib.Path(temporary)
            directory = sessions / "old"
            directory.mkdir()
            state_path = directory / "state.json"
            state_path.write_text(json.dumps({"name": "old", "book": "books/x",
                                              "pid": 999999, "loaded": [], "sends": 0}))
            os.utime(state_path, (time.time() - 7200, time.time() - 7200))
            with mock.patch.object(proof_repl, "SESSIONS", sessions):
                row = proof_repl.session_rows()[0]
            self.assertGreaterEqual(row["idle"], 7199)
            self.assertIsNone(row["deadline"])
            self.assertIsNone(proof_repl.reap_reason(row, None, None))  # dead, nothing held

    def test_list_reads_other_trees_with_root(self):
        with tempfile.TemporaryDirectory() as temporary:
            tree = pathlib.Path(temporary) / "lane-tree"
            directory = tree / "build" / "proof-repl" / "far"
            directory.mkdir(parents=True)
            (directory / "state.json").write_text(json.dumps(
                {"name": "far", "book": "books/y", "pid": 999999, "loaded": [],
                 "sends": 0, "lane": "far-lane", "idle_seconds": 60}))
            rows = proof_repl.session_rows([str(tree)])
            self.assertEqual([row["name"] for row in rows], ["far"])
            listing = subprocess.run(
                [sys.executable, str(ROOT / "tools" / "proof_repl.py"), "list", "--root", str(tree)],
                capture_output=True, text=True, cwd=ROOT, timeout=30)
            self.assertIn("far-lane", listing.stdout)
            self.assertIn(str(tree), listing.stdout)


if __name__ == "__main__":
    unittest.main()
