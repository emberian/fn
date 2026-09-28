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
"""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import time
import unittest

from tests import test_native_operator_verbs as verbs
from tests import test_native_open_depth as od

FIXTURES = os.environ.get("FN_STATUS_SCALE_FIXTURES")
NAMES = [n for n in os.environ.get("FN_STATUS_SCALE_NAMES", "syn100k-2k").replace(":", ",").split(",") if n]
STOP_SECONDS = float(os.environ.get("FN_STATUS_SCALE_STOP_SECONDS", "120"))


class StatusScaleTests(unittest.TestCase):
    # The fixture copy and the owner start of tests.test_native_open_depth.
    prepare = od.OpenDepthTests.prepare
    start_owner = od.OpenDepthTests.start_owner

    def setUp(self):
        if not verbs.executable(verbs.IMAGE):
            self.skipTest("needs the production image {}".format(verbs.IMAGE))
        if not FIXTURES or not Path(FIXTURES).is_dir():
            self.skipTest("FN_STATUS_SCALE_FIXTURES names no directory (hbox: /tank/fn/scratch/fixtures)")
        od.FIXTURES = FIXTURES
        self.work = Path(tempfile.mkdtemp(prefix="fn-status-scale-",
                                          dir=os.environ.get("FN_OPEN_DEPTH_WORK")))
        self.addCleanup(shutil.rmtree, self.work, True)

    def verb(self, name, config, words):
        started = time.monotonic()
        done = subprocess.run([str(verbs.IMAGE), "--fn", "operator", str(config)] + words,
                              env=verbs.environment(), stdout=subprocess.PIPE,
                              stderr=subprocess.PIPE, timeout=3600)
        seconds = time.monotonic() - started
        print("STATUS-SCALE {} {} exit={} bytes={} seconds={:.2f}".format(
            name, " ".join(words), done.returncode, len(done.stdout), seconds), flush=True)
        return done, seconds

    def stop(self, name, owner, err_path, what):
        started = time.monotonic()
        if owner.poll() is None:
            owner.terminate()
        try:
            owner.wait(3600)
        finally:
            seconds = time.monotonic() - started
            print("STATUS-SCALE {} stop-{} exit={} seconds={:.2f}".format(
                name, what, owner.returncode, seconds), flush=True)
            # What the owner said last (a publication or drain it waited for).
            lines = err_path.read_text("utf-8", "replace").splitlines()
            if owner.returncode != 0:
                # the fault's own lines, whole (frames shortened to their names)
                lines = [l.split(" pc=")[-1] if "fp=0x" in l else l for l in lines[-160:]]
            else:
                lines = lines[-12:]
            for line in lines:
                print("STATUS-SCALE {} stop-{} | {}".format(name, what, line[:240]), flush=True)
        self.assertEqual(owner.returncode, 0, err_path.read_text("utf-8", "replace")[-3000:])
        self.assertLessEqual(seconds, STOP_SECONDS)

    def test_status_and_stop(self):
        for name in NAMES:
            with self.subTest(name=name):
                root, config, port = self.prepare(name)
                err_path = root / "owner.err"
                owner, listening, _ = self.start_owner(name, "scale", root, config, err_path)
                self.state = {"owner": owner, "err_at": 0}
                print("STATUS-SCALE {} open seconds={:.1f}".format(name, listening), flush=True)
                try:
                    status, _ = self.verb(name, config, ["status"])
                    self.assertEqual(status.returncode, 0, status.stderr[-2000:])
                    self.assertIn(b"reclaim rule=", status.stdout)
                    self.verb(name, config, ["health"])
                    self.verb(name, config, ["obligations"])
                finally:
                    self.stop(name, owner, err_path, "idle")
                # Again with a report in flight when the stop comes.
                owner, listening, _ = self.start_owner(name, "scale-2", root, config, err_path)
                self.state = {"owner": owner, "err_at": 0}
                late = subprocess.Popen([str(verbs.IMAGE), "--fn", "operator", str(config),
                                         "obligations"], env=verbs.environment(),
                                        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                try:
                    time.sleep(1.0)
                finally:
                    try:
                        self.stop(name, owner, err_path, "in-flight")
                    finally:
                        try:
                            late.wait(60)
                        except subprocess.TimeoutExpired:
                            late.kill()


if __name__ == "__main__":
    unittest.main()
