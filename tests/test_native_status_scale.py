"""The running owner's `status' and `obligations' at scale, and its stop.

Lane scale-reads (item 2), after lane serve-depth's finding: at 1,000,000
articles `status' and `obligations' answered uncertain after the control
client's 10 s and the owner, still rendering them, took over 600 s to stop
(native-sd5).  The cause: every `status' read and hashed every article's
payload four times under the owner mutex, to ask whether it is a reclaim
tombstone (books/native-status-columns.lisp).

Opt-in: FN_STATUS_SCALE_FIXTURES names the fixture directory
(hbox:/tank/fn/scratch/fixtures) and FN_STATUS_SCALE_NAMES a comma (or colon)
list (default syn100k-2k; syn1m-2k needs an 80G scope).  For each store the
owner opens it, answers `status' (asserted: exit 0, inside the control
client's deadline), `health' and `obligations' (recorded).
The owner is stopped (idle), reopened, and stopped again one second
after an `obligations' request: each stop is asserted to end, exit 0,
within FN_STATUS_SCALE_STOP_SECONDS (default 120).  Prints
`STATUS-SCALE NAME VERB exit=E bytes=B seconds=S' and
`STATUS-SCALE NAME stop-idle|stop-in-flight exit=E seconds=S'.

Lane obligations-paged: `obligations' is sent page by page
(books/native-live-pages.lisp).  Asserted: exit 0, the report's header
count equals its obligation lines, two concurrent requests both answer the
same report and the owner still answers `status' after them (at syn1m-2k the
whole-report render exhausted the heap and killed the owner), and the
offline report of the stopped owner's Store is the same octets.  Printed:
`STATUS-SCALE NAME report-pages ...' (the client's requests, first-page and
total seconds) and `STATUS-SCALE NAME owner-peak-rss-kib=K'.
"""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import time
import unittest

from tests import test_native_open_depth as od
from tests.native_harness import ROOT, executable, native_image, start

IMAGE = native_image("FN_NATIVE_HOST")

FIXTURES = os.environ.get("FN_STATUS_SCALE_FIXTURES")
NAMES = [n for n in os.environ.get("FN_STATUS_SCALE_NAMES", "syn100k-2k").replace(":", ",").split(",") if n]
STOP_SECONDS = float(os.environ.get("FN_STATUS_SCALE_STOP_SECONDS", "120"))


class StatusScaleTests(unittest.TestCase):
    # The fixture copy and the owner start of tests.test_native_open_depth.
    prepare = od.OpenDepthTests.prepare
    start_owner = od.OpenDepthTests.start_owner

    def setUp(self):
        if not executable(IMAGE):
            self.skipTest("needs the production image {}".format(IMAGE))
        if not FIXTURES or not Path(FIXTURES).is_dir():
            self.skipTest("FN_STATUS_SCALE_FIXTURES names no directory (hbox: /tank/fn/scratch/fixtures)")
        od.FIXTURES = FIXTURES
        self.work = Path(tempfile.mkdtemp(prefix="fn-status-scale-",
                                          dir=os.environ.get("FN_OPEN_DEPTH_WORK")))
        self.addCleanup(shutil.rmtree, self.work, True)

    def verb(self, name, node, words, env=None):
        started = time.monotonic()
        done = node.operator(*words, env=env, timeout=3600)
        seconds = time.monotonic() - started
        print("STATUS-SCALE {} {} exit={} bytes={} seconds={:.2f}".format(
            name, " ".join(words), done.returncode, len(done.stdout), seconds), flush=True)
        return done, seconds

    def stop(self, name, owner, what):
        started = time.monotonic()
        try:
            owner.stop(grace=3600)
        finally:
            seconds = time.monotonic() - started
            print("STATUS-SCALE {} stop-{} exit={} seconds={:.2f}".format(
                name, what, owner.returncode, seconds), flush=True)
            # What the owner said last (a publication or drain it waited for).
            log = owner.stderr.since(0).decode("utf-8", "replace")
            lines = log.splitlines()
            if owner.returncode != 0:
                # the fault's own lines, whole (frames shortened to their names)
                lines = [l.split(" pc=")[-1] if "fp=0x" in l else l for l in lines[-160:]]
            else:
                lines = lines[-12:]
            for line in lines:
                print("STATUS-SCALE {} stop-{} | {}".format(name, what, line[:240]), flush=True)
        self.assertEqual(owner.returncode, 0, log[-3000:])
        self.assertLessEqual(seconds, STOP_SECONDS)

    def peak_rss_kib(self, pid):
        """The owner's high-water resident set (VmHWM), itself and its children."""
        total = 0
        pids = [pid]
        try:
            children = subprocess.run(["ps", "-o", "pid=", "--ppid", str(pid)],
                                      stdout=subprocess.PIPE, text=True).stdout.split()
            pids += [int(c) for c in children]
        except (OSError, ValueError):
            pass
        for p in pids:
            try:
                for line in Path("/proc/{}/status".format(p)).read_text().splitlines():
                    if line.startswith("VmHWM:"):
                        total += int(line.split()[1])
            except OSError:
                pass
        return total

    @staticmethod
    def report_part(stdout):
        """The obligations report: its header line and one line per obligation."""
        lines = stdout.split(b"\n")
        count = int(lines[0].split(b" ")[0].split(b"=")[1])
        return b"\n".join(lines[:count + 1])

    def obligations(self, name, node, owner):
        """`obligations' from the live owner: checked, timed, twice at once."""
        done, _ = self.verb(name, node, ["obligations"], env={"FN_REPORT_TIMING": "1"})
        self.assertEqual(done.returncode, 0, done.stderr[-2000:])
        for line in done.stderr.decode("utf-8", "replace").splitlines():
            if line.startswith("report-pages"):
                print("STATUS-SCALE {} {}".format(name, line), flush=True)
        lines = done.stdout.split(b"\n")
        self.assertTrue(lines[0].startswith(b"obligations="), lines[0][:200])
        count = int(lines[0].split(b" ")[0].split(b"=")[1])
        self.assertEqual(len([l for l in lines[1:] if l.startswith(b"obligation id=")]), count)
        # The report is the header and COUNT lines; the heap and result
        # lines follow it.
        self.assertTrue(all(l.startswith(b"obligation id=") for l in lines[1:count + 1]))
        # Two at once: the crash at syn1m-2k was the second whole render.
        both = [start([IMAGE, "--fn", "operator", node.config, "obligations"],
                      cwd=ROOT, env=node.environment())
                for _ in range(2)]
        outs = [p.communicate(timeout=3600) for p in both]
        for p, (out, err) in zip(both, outs):
            self.assertEqual(p.returncode, 0, err[-2000:])
            self.assertEqual(self.report_part(out), self.report_part(done.stdout))
        print("STATUS-SCALE {} concurrent-obligations exit={}".format(
            name, [p.returncode for p in both]), flush=True)
        after, _ = self.verb(name, node, ["status"])
        self.assertEqual(after.returncode, 0, after.stderr[-2000:])
        print("STATUS-SCALE {} owner-peak-rss-kib={}".format(
            name, self.peak_rss_kib(owner.pid)), flush=True)
        return done.stdout

    def test_status_and_stop(self):
        for name in NAMES:
            with self.subTest(name=name):
                node = self.prepare(name)
                owner, listening, _ = self.start_owner(node)
                print("STATUS-SCALE {} open seconds={:.1f}".format(name, listening), flush=True)
                try:
                    status, _ = self.verb(name, node, ["status"])
                    self.assertEqual(status.returncode, 0, status.stderr[-2000:])
                    self.assertIn(b"reclaim rule=", status.stdout)
                    self.verb(name, node, ["health"])
                    live = self.obligations(name, node, owner)
                finally:
                    self.stop(name, owner, "idle")
                # The offline words of the same Store, a page at a time.
                offline, _ = self.verb(name, node, ["obligations"])
                self.assertEqual(offline.returncode, 0, offline.stderr[-2000:])
                self.assertEqual(self.report_part(offline.stdout), self.report_part(live))
                # Again with a report in flight when the stop comes.
                owner, listening, _ = self.start_owner(node)
                late = start([IMAGE, "--fn", "operator", node.config, "obligations"],
                             cwd=ROOT, env=node.environment())
                try:
                    time.sleep(1.0)
                finally:
                    try:
                        self.stop(name, owner, "in-flight")
                    finally:
                        try:
                            late.wait(60)
                        except subprocess.TimeoutExpired:
                            late.kill()
                            late.wait(60)
                        late.finish()

if __name__ == "__main__":
    unittest.main()
