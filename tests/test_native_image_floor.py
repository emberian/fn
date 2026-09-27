"""HST-017: the saved image's logical world is the execution world.

host/native/build.lisp strips the world before save-exec
(host/native/strip-world.lisp): every property the prover, the undo stack and
the history commands read goes, and what the executable counterparts, guard
checking, stobj and attachment dispatch, LP's start and error reporting read
stays at its current value.  These witnesses run the saved images:

* a guard violation at the host boundary (the developer verb `guard-probe'
  calls fn-sha256-of-string on 42 through fnn-call) is the fault it was
  before the strip: the same stderr line and exit 4
  (planning/evidence/image-floor-2026-09-26.md has the unstripped image's
  line, byte-identical);
* the same with ACL2_SYSTEM_BOOKS set, the start path on which LP's
  replace-project-dir-alist walks the world from event 0 (the strip keeps a
  bottom of command 0, event 0 and the project-dir-alist triple for it);
* the production image refuses the verb by name (exit 5);
* the core's dynamic content is under 128 MiB (271 MiB before the strip and
  the residue drop), and
  a fresh node started with a 256 MB dynamic space takes a POST and serves
  it back;
* the control stack books/heap-reservation.lisp decides for the small,
  development and scale profiles (1,192 KiB: 512 KiB + 40 octets for each
  of the 16,384 + 1,024 lines a 32,768-octet article can have) posts, serves,
  reopens and serves again the worst such article the small preset accepts
  (32,000 octets offered, every body line empty: under 4 GiB `init' makes
  the small preset, which refuses 32,768 once the node adds its headers); and
  a third of it (384 KiB) does not (the owner faults on control-stack
  exhaustion), so the witness measures the stack and not the harness.

Each witness skips, naming the image, when that image is absent.
"""
import json
import os
from pathlib import Path
import re
import socket
import subprocess
import sys
import tempfile
import unittest

from tests.native_process import stop_and_diagnostics, wait_for_announcement


ROOT = Path(__file__).resolve().parent.parent
IMAGE = Path(os.environ.get("FN_NATIVE_HOST", ROOT / "build" / "fn-host"))
DEVELOPER = Path(os.environ.get(
    "FN_NATIVE_DEVELOPER_HOST", ROOT / "build" / "fn-host-developer"))
MEASURE = ROOT / "tools" / "runtime_image" / "node_measure.py"

EXIT_FAULT, EXIT_USAGE = 4, 5
GUARD_LINE = (b"store: ACL2 error in fn-sha256-of-string: "
              b"(EV-FNCALL-GUARD-ER FN-SHA256-OF-STRING (42) (STRINGP S) (NIL) NIL)\n")
CORE_CEILING_KIB = 128 * 1024
SMALL_STACK_KIB = 1192          # fn-heap-stack-kib of the 32,768-octet presets


def environment(**extra):
    env = dict(os.environ)
    env["ACL2_CUSTOMIZATION"] = "NONE"
    env.pop("ACL2_SYSTEM_BOOKS", None)
    env.pop("SBCL_USER_ARGS", None)
    env.update(extra)
    return env


def executable(image):
    return image.is_file() and os.access(image, os.X_OK)


def run(image, args, env):
    return subprocess.run([str(image), "--fn"] + args, env=env, stdin=subprocess.DEVNULL,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=300)


class GuardViolationTests(unittest.TestCase):
    def setUp(self):
        if not executable(DEVELOPER):
            self.skipTest("needs the developer image %s" % DEVELOPER)

    def test_guard_violation_is_one_fault_line(self):
        res = run(DEVELOPER, ["guard-probe"], environment())
        self.assertEqual(res.returncode, EXIT_FAULT, res.stderr)
        self.assertEqual(res.stdout, b"")
        self.assertEqual(res.stderr, GUARD_LINE)

    def test_guard_violation_with_system_books(self):
        with tempfile.TemporaryDirectory() as books:
            res = run(DEVELOPER, ["guard-probe"], environment(ACL2_SYSTEM_BOOKS=books))
        self.assertEqual(res.returncode, EXIT_FAULT, res.stderr)
        self.assertEqual(res.stderr, GUARD_LINE)


class ProductionTests(unittest.TestCase):
    def setUp(self):
        if not executable(IMAGE):
            self.skipTest("needs the production image %s" % IMAGE)

    def test_production_refuses_guard_probe(self):
        res = run(IMAGE, ["guard-probe"], environment())
        self.assertEqual(res.returncode, EXIT_USAGE, res.stderr)
        self.assertIn(b"guard-probe is available only in the developer image", res.stderr)

    def test_core_dynamic_content(self):
        res = subprocess.run([sys.executable, str(MEASURE), "core", str(IMAGE)],
                             env=environment(), stdout=subprocess.PIPE, check=True, timeout=120)
        doc = json.loads(res.stdout)
        self.assertIsNotNone(doc["core_required_kib"], doc)
        self.assertLess(doc["core_required_kib"], CORE_CEILING_KIB, doc)

    def test_fresh_node_serves_in_256_mb(self):
        with tempfile.TemporaryDirectory() as work:
            res = subprocess.run([sys.executable, str(MEASURE), "floor", str(IMAGE), work,
                                  "--lo", "248", "--hi", "256"],
                                 env=environment(), stdout=subprocess.PIPE, check=True,
                                 timeout=600)
        doc = json.loads(res.stdout)
        self.assertEqual(doc["trials"][0][:2], [256, True], doc)

    def stack_trial(self, kib):
        with tempfile.TemporaryDirectory() as work:
            res = subprocess.run([sys.executable, str(MEASURE), "stack-floor", str(IMAGE),
                                  work, "--octets", "32000", "--line-octets", "2",
                                  "--heap", "1024", "--hi", str(kib), "--lo", str(kib - 1)],
                                 env=environment(), stdout=subprocess.PIPE, check=True,
                                 timeout=900)
        return json.loads(res.stdout)

    def test_decided_stack_holds_the_largest_small_article(self):
        doc = self.stack_trial(SMALL_STACK_KIB)
        self.assertEqual(doc["trials"][0][:2], [SMALL_STACK_KIB, True], doc)

    def test_a_third_of_the_stack_does_not(self):
        doc = self.stack_trial(384)
        self.assertEqual(doc["trials"][0][:2], [384, False], doc)
        self.assertIsNone(doc["stack_floor_kib"], doc)


def cgroup_limit():
    """The least memory.max from this process's cgroup up, or None."""
    try:
        line = next(l for l in Path("/proc/self/cgroup").read_text().splitlines()
                    if l.startswith("0::"))
    except (OSError, StopIteration):
        return None
    path, found = line[3:], []
    while path and path != "/":
        try:
            text = (Path("/sys/fs/cgroup" + path) / "memory.max").read_text().strip()
            if text.isdigit():
                found.append(int(text))
        except OSError:
            pass
        path = path.rsplit("/", 1)[0]
    return min(found) if found else None


def free_port():
    with socket.socket() as s:
        s.bind(("127.0.0.1", 0))
        return s.getsockname()[1]


class Nntp:
    def __init__(self, port, timeout=600):
        self.conn = socket.create_connection(("127.0.0.1", port), timeout=timeout)
        self.stream = self.conn.makefile("rwb")
        self.greeting = self.stream.readline()

    def command(self, text):
        self.stream.write(text.encode("ascii") + b"\r\n")
        self.stream.flush()
        return self.stream.readline()

    def body(self):
        n = 0
        while True:
            line = self.stream.readline()
            if line in (b".\r\n", b""):
                return n, line
            n += 1

    def post(self, headers, lines):
        first = self.command("POST")
        if not first.startswith(b"340"):
            return first
        self.stream.write(headers.encode("ascii") + b"\r\n" + b"\r\n" * lines + b".\r\n")
        self.stream.flush()
        return self.stream.readline()

    def close(self):
        try:
            self.command("QUIT")
        finally:
            self.conn.close()


def headers(n, groups="local.test"):
    return ("From: deep@example.invalid\r\nNewsgroups: {}\r\nSubject: deep {}\r\n"
            "Message-ID: <deep-{}@example.invalid>\r\n".format(groups, n, n))


class DeepInputStackTests(unittest.TestCase):
    """Deep-input witnesses for the control stack books/heap-reservation.lisp
    decides (gpt-6's wave-5 review s.4: large permitted messages, long
    recovery histories, error paths).  Each node runs at the stack the
    launcher's own probe (`heap -- operator CONFIG run') prints for its
    store, with no other change; the served path's per-line recursion (lane
    served-line-iterative, not merged) is what the per-line term covers."""

    def setUp(self):
        if not executable(IMAGE):
            self.skipTest("needs the production image %s" % IMAGE)
        self.tmp = Path(tempfile.mkdtemp(prefix="fn-deep-"))
        self.addCleanup(lambda: subprocess.run(["rm", "-rf", str(self.tmp)]))

    def store(self, name, flags, **init_env):
        port = free_port()
        cfg = self.tmp / (name + ".toml")
        cfg.write_text('[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\nport = {}\n'
                       .format(self.tmp / name, port), encoding="ascii")
        made = run(IMAGE, ["operator", str(cfg), "init"] + flags + ["local.test"],
                   environment(**init_env))
        self.assertEqual(made.returncode, 0, made.stderr)
        probe = run(IMAGE, ["heap", "--", "operator", str(cfg), "run"], environment())
        self.assertEqual(probe.returncode, 0, probe.stderr)
        stack = int(re.search(rb"stack=(\d+) KB", probe.stdout).group(1))
        return cfg, port, stack

    def start(self, cfg, stack_kib, heap_mb=2048):
        env = environment(SBCL_USER_ARGS="--dynamic-space-size %dMB --control-stack-size %dKB"
                          % (heap_mb, stack_kib))
        owner = subprocess.Popen([str(IMAGE), "--fn", "operator", str(cfg), "run"], env=env,
                                 stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        wait_for_announcement(owner, b"LISTENING ", timeout=900)
        return owner

    def stop(self, owner):
        diagnostics = stop_and_diagnostics(owner, timeout=300)
        self.assertNotIn("Control stack exhausted", diagnostics)
        self.assertEqual(owner.returncode, 0, diagnostics)

    def test_a_1_mib_article_of_empty_lines_at_its_decided_stack(self):
        """A = 1 MiB (the default mission's article bound): 524,288 lines
        admitted; posted, served, reopened and served at the probe's stack
        (21,032 KiB), and a third of it does not serve it."""
        limit = cgroup_limit()
        if limit is not None and limit < 8 * 1024 ** 3:
            self.skipTest("A = 1 MiB reserves 60 stacks of 21 MB: run without a memory "
                          "limit under 8 GiB (this one is %d MiB)" % (limit >> 20))
        cfg, port, stack = self.store("big", ["--profile", "development",
                                              "--max-article-octets", "1048576",
                                              "--max-groups-per-article", "8"])
        print("NATIVE-DEEP big-article stack={} KB".format(stack))
        self.assertGreaterEqual(stack, 21032)
        lines = (1048576 - 400) // 2
        for phase in ("post", "reopen"):
            owner = self.start(cfg, stack)
            try:
                c = Nntp(port)
                if phase == "post":
                    self.assertTrue(c.post(headers(1), lines).startswith(b"240"))
                self.assertTrue(c.command("ARTICLE <deep-1@example.invalid>").startswith(b"220"))
                n, end = c.body()
                self.assertEqual(end, b".\r\n")
                self.assertGreaterEqual(n, lines)
                c.close()
            finally:
                self.stop(owner)
        owner = self.start(cfg, stack // 3)
        try:
            c = Nntp(port)
            reply = c.command("ARTICLE <deep-1@example.invalid>")
            served = reply.startswith(b"220") and c.body()[1] == b".\r\n"
        except OSError:
            served = False
        diagnostics = stop_and_diagnostics(owner, timeout=300)
        print("NATIVE-DEEP big-article at {} KB served={} tail={!r}".format(
            stack // 3, served, diagnostics[-160:]))
        self.assertFalse(served and owner.returncode == 0)

    def test_a_long_history_reopens_and_replays_at_the_decided_stack(self):
        """2,000 articles; reopened from the checkpoint and by full replay
        (no checkpoint) at the probe's stack."""
        # The small preset (T = 16,384) on any machine: a 1,500 MB budget.
        cfg, port, stack = self.store("long", ["--profile", "default"],
                                      FN_INIT_BUDGET_MB="1500")
        print("NATIVE-DEEP long-history stack={} KB".format(stack))
        owner = self.start(cfg, stack)
        try:
            c = Nntp(port)
            for n in range(2000):
                self.assertTrue(c.post(headers(n), 3).startswith(b"240"), n)
            c.close()
        finally:
            self.stop(owner)
        for phase in ("reopen", "replay"):
            if phase == "replay":
                for p in sorted((self.tmp / "long").rglob("*"), reverse=True):
                    if p.is_file() and "checkpoint" in p.name:
                        p.unlink()
            owner = self.start(cfg, stack)
            try:
                c = Nntp(port)
                self.assertTrue(c.command("GROUP local.test").startswith(b"211 2000 "))
                for n in (0, 1999):
                    self.assertTrue(c.command("ARTICLE <deep-%d@example.invalid>" % n)
                                    .startswith(b"220"), (phase, n))
                    c.body()
                c.close()
            finally:
                self.stop(owner)

    def test_error_paths_at_the_decided_stack(self):
        """At the small presets' stack: a POST without Newsgroups of 16,000
        lines, and one of 20,000 lines over the 32,768-octet bound, are
        refused (441) and the node serves on."""
        cfg, port, stack = self.store("errors", ["--profile", "default"],
                                      FN_INIT_BUDGET_MB="1500")
        print("NATIVE-DEEP errors stack={} KB".format(stack))
        owner = self.start(cfg, stack)
        try:
            # Each refusal on its own connection: an over-size POST may be
            # answered before its terminator arrives.
            no_groups = ("From: deep@example.invalid\r\nSubject: none\r\n"
                         "Message-ID: <deep-none@example.invalid>\r\n")
            for head, lines in ((no_groups, 16000), (headers(2), 20000)):
                c = Nntp(port)
                reply = c.post(head, lines)
                print("NATIVE-DEEP errors {} lines -> {!r}".format(lines, reply[:60]))
                self.assertTrue(reply.startswith(b"441"), reply)
                c.conn.close()
            c = Nntp(port)
            self.assertTrue(c.post(headers(3), 10).startswith(b"240"))
            self.assertTrue(c.command("ARTICLE <deep-3@example.invalid>").startswith(b"220"))
            c.body()
            c.close()
        finally:
            self.stop(owner)


if __name__ == "__main__":
    unittest.main()
