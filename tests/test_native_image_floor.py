"""HST-025: the saved image's logical world is the execution world.

host/native/build.lisp strips the world before save-exec
(host/native/strip-world.lisp): every property the prover, the undo stack and
the history commands read goes, and what the executable counterparts, guard
checking, stobj and attachment dispatch, LP's start and error reporting read
stays at its current value.  These witnesses run the saved images:

* a guard violation at the host boundary (the developer verb `guard-probe'
  calls fn-b3-left-chunks on 42 and -1 through fnn-call) is the fault it was
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
* the control stack books/heap-reservation.lisp decides (a constant 1,024
  KiB since lane served-line-iterative made the served path's per-line
  recursions loops) posts, serves, reopens and serves again the worst
  article the small preset accepts (32,000 octets offered, every body line
  empty); 96 KiB, under the 142 KiB floor, does not, so the witness
  measures the stack and not the harness;
* DeepInputStackTests: the image's own launcher passes the probe's stack
  (PKT-876); a 1 MiB article of empty lines, a 2,000-article
  history reopened and fully replayed, and refused POSTs of 16,000 and
  20,000 lines, each at the stack the launcher's probe prints.

Each witness skips, naming the image, when that image is absent.
"""
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest

from tests import native_harness
from tests.native_harness import (
    EXIT_FAULT, EXIT_USAGE, ROOT, Client, Node, executable, native_image)


IMAGE = native_image("FN_NATIVE_HOST")
DEVELOPER = native_image("FN_NATIVE_DEVELOPER_HOST")
MEASURE = ROOT / "tools" / "runtime_image" / "node_measure.py"
# The entry is caught by the host's entry guard (io.lisp fnn-call's
# host-entry-guard) before ACL2 evaluates it: still one fault line, exit 4.
# (Until store format 10 the probe called fn-sha256-of-string, which the
# entry guard did not describe, and the line was ACL2's EV-FNCALL-GUARD-ER.)
GUARD_LINE = (b"store: host-entry-guard: fn-b3-left-chunks argument 2 (n) must be a "
              b"natural (natp); the host passed the integer -1\n")
CORE_CEILING_KIB = 128 * 1024
SMALL_STACK_KIB = 1024          # fn-heap-stack-kib: the constant (served-line-iterative)


# This module measures the control stack, so it names every stack itself:
# no SBCL_USER_ARGS from the shell or the harness's deployed-stack override.
NO_STACK = {"SBCL_USER_ARGS": None}


def environment(**extra):
    return native_harness.environment(dict(NO_STACK, **extra), stack=False)


def run(image, args, env):
    return native_harness.run([image, "--fn", *args], env=env, stdin=subprocess.DEVNULL,
                              timeout=300)


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
        # The node as the launcher starts it: 1 MiB control stacks (books/
        # heap-reservation.lisp fn-heap-stack-octets).  The raw image script's
        # own 64 MiB stacks count 78 x 68 MiB in connection-multiplexing's
        # run budget, which a 2 GiB limit refuses (holds=0, batch AR).
        stack_env = dict(environment(), NM_STACK_MB="1")
        with tempfile.TemporaryDirectory() as work:
            res = subprocess.run([sys.executable, str(MEASURE), "floor", str(IMAGE), work,
                                  "--lo", "248", "--hi", "256"],
                                 env=stack_env, stdout=subprocess.PIPE, check=True,
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

    def test_below_the_measured_floor_it_does_not(self):
        """96 KiB, under the 142 KiB the node needs whatever the article
        (served-line-iterative's record, section 5): the trial fails, so the
        witness above measures the stack and not the harness."""
        doc = self.stack_trial(96)
        self.assertEqual(doc["trials"][0][:2], [96, False], doc)
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


def body_lines(client):
    """The line count of a dot-terminated block (the terminator excluded)."""
    return client.block().count(b"\r\n")


def post(client, head, lines):
    """POST HEAD, a blank line and LINES empty body lines; the final reply."""
    first, final = client.post(head.encode("ascii") + b"\r\n" + b"\r\n" * lines)
    return final if final is not None else first


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
        node = Node(self, IMAGE, root=self.tmp / name, control=False, env=NO_STACK)
        made = node.operator("init", *flags, "local.test", env=init_env)
        self.assertEqual(made.returncode, 0, made.stderr)
        probe = node.invoke("heap", "--", "operator", node.config, "run")
        self.assertEqual(probe.returncode, 0, probe.stderr)
        stack = int(re.search(rb"stack=(\d+) KB", probe.stdout).group(1))
        return node, stack

    def start(self, node, stack_kib, heap_mb=2048):
        return node.start(env={"SBCL_USER_ARGS": "--dynamic-space-size %dMB --control-stack-size %dKB"
                                                  % (heap_mb, stack_kib)}, timeout=900)

    def stop(self, node, owner):
        node.stop(process=owner, grace=300)
        self.assertNotIn(b"Control stack exhausted", owner.stderr.since(0))

    def test_the_image_launcher_runs_at_the_decided_stack(self):
        """PKT-876: the image's own launcher (the one every native test runs)
        passes the control stack the installed launcher's probe decides for
        a store, not ACL2's save-exec 64 MiB."""
        _node, stack = self.store("launcher", ["--profile", "default"],
                                      FN_INIT_BUDGET_MB="1500")
        found = re.findall(r"--control-stack-size (\S+) ", IMAGE.read_text(encoding="utf-8"))
        self.assertEqual(found, ["%dKB" % stack], found)

    def test_a_1_mib_article_of_empty_lines_at_its_decided_stack(self):
        """A = 1 MiB (the default mission's article bound): 524,088 lines
        admitted; posted, served, reopened and served at the probe's stack,
        the constant 1,024 KiB.  Needs lane served-line-iterative's loops
        (merged in the same batch): before them this article needed 16 MiB."""
        limit = cgroup_limit()
        if limit is not None and limit < 8 * 1024 ** 3:
            self.skipTest("A = 1 MiB reserves 60 stacks of 21 MB: run without a memory "
                          "limit under 8 GiB (this one is %d MiB)" % (limit >> 20))
        node, stack = self.store("big", ["--profile", "development",
                                              "--max-article-octets", "1048576",
                                              "--max-groups-per-article", "8"])
        print("NATIVE-DEEP big-article stack={} KB".format(stack))
        self.assertEqual(stack, SMALL_STACK_KIB)
        lines = (1048576 - 400) // 2
        for phase in ("post", "reopen"):
            owner = self.start(node, stack)
            try:
                c = Client(node.port, timeout=600, greeting=None)
                if phase == "post":
                    self.assertTrue(post(c, headers(1), lines).startswith(b"240"))
                self.assertTrue(c.command("ARTICLE <deep-1@example.invalid>").startswith(b"220"))
                n = body_lines(c)  # block() returns only at the ".\r\n" terminator
                self.assertGreaterEqual(n, lines)
                c.close()
            finally:
                self.stop(node, owner)

    def test_a_long_history_reopens_and_replays_at_the_decided_stack(self):
        """2,000 articles; reopened from the checkpoint, and by full replay
        (no checkpoint) of a store whose log holds the whole history, at the
        probe's stack.  The full replay needs a store the owner never
        compacted: deleting the checkpoint of a compacted store leaves the log
        short of the history, which the open refuses by name
        (checkpoint-damaged; batch AY, as lane fitness found for
        test_native_image_differential)."""
        # The small preset (T = 16,384) on any machine: a 1,500 MB budget.
        # The replay store keeps its whole history in one segment: its open
        # suffix (the automatic checkpoint's period) is above 2,000 records.
        for name, extra in (("long", []), ("long-replay", ["--max-open-suffix", "4096"])):
            node, stack = self.store(name, ["--profile", "default"] + extra,
                                          FN_INIT_BUDGET_MB="1500")
            print("NATIVE-DEEP {} stack={} KB".format(name, stack))
            owner = self.start(node, stack)
            try:
                c = Client(node.port, timeout=600, greeting=None)
                for n in range(2000):
                    self.assertTrue(post(c, headers(n), 3).startswith(b"240"), (name, n))
                c.close()
            finally:
                self.stop(node, owner)
            if name == "long-replay":
                for p in sorted((self.tmp / name).rglob("*"), reverse=True):
                    if p.is_file() and "checkpoint" in p.name:
                        p.unlink()
            owner = self.start(node, stack)
            try:
                c = Client(node.port, timeout=600, greeting=None)
                self.assertTrue(c.command("GROUP local.test").startswith(b"211 2000 "), name)
                for n in (0, 1999):
                    self.assertTrue(c.command("ARTICLE <deep-%d@example.invalid>" % n)
                                    .startswith(b"220"), (name, n))
                    c.block()
                c.close()
            finally:
                self.stop(node, owner)

    def test_error_paths_at_the_decided_stack(self):
        """At the small presets' stack: a POST without Newsgroups of 16,000
        lines, and one of 20,000 lines over the 32,768-octet bound, are
        refused (441) and the node serves on."""
        node, stack = self.store("errors", ["--profile", "default"],
                                      FN_INIT_BUDGET_MB="1500")
        print("NATIVE-DEEP errors stack={} KB".format(stack))
        owner = self.start(node, stack)
        try:
            # Each refusal on its own connection: an over-size POST may be
            # answered before its terminator arrives.
            no_groups = ("From: deep@example.invalid\r\nSubject: none\r\n"
                         "Message-ID: <deep-none@example.invalid>\r\n")
            for head, lines in ((no_groups, 16000), (headers(2), 20000)):
                c = Client(node.port, timeout=600, greeting=None)
                reply = post(c, head, lines)
                print("NATIVE-DEEP errors {} lines -> {!r}".format(lines, reply[:60]))
                self.assertTrue(reply.startswith(b"441"), reply)
                c.close(quit=False)
            c = Client(node.port, timeout=600, greeting=None)
            self.assertTrue(post(c, headers(3), 10).startswith(b"240"))
            self.assertTrue(c.command("ARTICLE <deep-3@example.invalid>").startswith(b"220"))
            c.block()
            c.close()
        finally:
            self.stop(node, owner)


if __name__ == "__main__":
    unittest.main()
