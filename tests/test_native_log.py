"""The record log through the native images (lane w6-log-core).

`fn log append|recover` (developer image) drive host/native/io.lisp's
fnn-log-* functions: recovery (fn-lg-recover-program), then batches of the
workload records, each appended (fn-lg-append-program), fenced
(fn-lg-fence-program) and acknowledged, one `ACK` line per batch.  `fn log
scan` reads a segment without writing, on both images.  The cut cases kill
the developer process at every LOG_CUTS cut (FN_NATIVE_LOG_FAULT) and check
what the next recovery reads: the process-death oracle (the page cache
survives; power loss is tools/power_loss.py's `log` workload).

The oracle is outside ACL2 only in what it compares: the lines the verbs
print (ACL2's counts, frontier, next txid and `workload=t`, ACL2's check that
the records are the workload records 1..N) and the segment's raw bytes past
the frontier (all zero after a recovery).
"""
from __future__ import annotations

import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from tests.campaign import native_cuts  # noqa: E402

DEVELOPER = os.environ.get("FN_NATIVE_DEVELOPER_HOST", "")
PRODUCTION = os.environ.get("FN_NATIVE_HOST", "")
EXTENT, UNIT, MAX, SIZE = 262144, 4096, 65536, 100
LINE = re.compile(r"^(\S+(?: batch=\d+)?) records=(\d+) frontier=(\d+) next=(\d+) "
                  r"last=([0-9a-f]+) workload=(t|nil)$")


def run(image, *argv, fault=None):
    env = dict(os.environ)
    env.pop("FN_NATIVE_LOG_FAULT", None)
    if fault:
        env["FN_NATIVE_LOG_FAULT"] = fault
    return subprocess.run([image, "--fn", "log", *[str(a) for a in argv]], env=env,
                          capture_output=True, text=True, timeout=300)


def lines(result):
    out = []
    for text in result.stdout.splitlines():
        m = LINE.match(text)
        if m:
            out.append({"what": m.group(1), "records": int(m.group(2)),
                        "frontier": int(m.group(3)), "next": int(m.group(4)),
                        "last": m.group(5), "workload": m.group(6) == "t"})
    return out


@unittest.skipUnless(DEVELOPER and PRODUCTION,
                     "FN_NATIVE_DEVELOPER_HOST and FN_NATIVE_HOST name the images")
class NativeLogTests(unittest.TestCase):
    def setUp(self):
        self.dir = tempfile.TemporaryDirectory(prefix="fn-log-")
        self.seg = os.path.join(self.dir.name, "segment")

    def tearDown(self):
        self.dir.cleanup()

    def args(self, *more):
        return (self.seg, EXTENT, UNIT, MAX, SIZE) + more

    def append(self, batches, per, fault=None):
        return run(DEVELOPER, "append", *self.args(batches, per), fault=fault)

    def scan(self, image):
        result = run(image, "scan", *self.args())
        self.assertEqual(result.returncode, 0, result.stderr)
        (line,) = lines(result)
        return line

    def zeros_past(self, frontier):
        data = Path(self.seg).read_bytes()
        self.assertEqual(len(data), EXTENT)
        return data[frontier:] == bytes(EXTENT - frontier)

    def test_append_then_scan_on_both_images(self):
        result = self.append(5, 3)
        self.assertEqual(result.returncode, 0, result.stderr)
        acks = [l for l in lines(result) if l["what"].startswith("ACK")]
        self.assertEqual([a["records"] for a in acks], [3, 6, 9, 12, 15])
        self.assertTrue(all(a["workload"] for a in acks))
        self.assertEqual(acks[-1]["next"], 16)
        dev, prod = self.scan(DEVELOPER), self.scan(PRODUCTION)
        self.assertEqual(dev, prod)
        self.assertEqual((dev["records"], dev["next"], dev["workload"]), (15, 16, True))
        self.assertEqual(dev["frontier"], acks[-1]["frontier"])
        self.assertEqual(dev["frontier"] % UNIT, 0)
        self.assertTrue(self.zeros_past(dev["frontier"]))
        # A second run recovers the fifteen and continues at txid 16.
        again = self.append(1, 2)
        self.assertEqual(again.returncode, 0, again.stderr)
        self.assertEqual([(l["records"], l["next"]) for l in lines(again)],
                         [(15, 16), (17, 18)])

    def test_production_refuses_the_writing_verbs(self):
        for verb in ("append", "recover"):
            result = run(PRODUCTION, verb, *self.args(1, 1))
            self.assertEqual(result.returncode, 5, (verb, result.stdout, result.stderr))
            self.assertIn("developer-image verb", result.stderr)
        self.assertFalse(os.path.exists(self.seg))
        result = run(PRODUCTION, "scan", *self.args())
        self.assertEqual(result.returncode, 1, result.stderr)

    def test_a_torn_tail_is_zeroed_and_the_history_kept(self):
        self.assertEqual(self.append(2, 3).returncode, 0)
        frontier = self.scan(DEVELOPER)["frontier"]
        with open(self.seg, "r+b") as f:
            f.seek(frontier)
            f.write(b"FNLG" + bytes(range(200)) * 30)
        self.assertFalse(self.zeros_past(frontier))
        result = run(DEVELOPER, "recover", *self.args())
        self.assertEqual(result.returncode, 0, result.stderr)
        (line,) = lines(result)
        self.assertEqual((line["records"], line["frontier"], line["workload"]),
                         (6, frontier, True))
        self.assertTrue(self.zeros_past(frontier))

    def test_every_log_cut_recovers_to_a_prefix(self):
        seen = []
        # The extension's cuts (fn-lg-extend-program) are the served commit's:
        # this verb writes a fixed extent; tests/test_native_commit_log.py
        # kills at them.
        rig_cuts = [c for c in native_cuts.LOG_CUTS if c.program != "fn-lg-extend-program"]
        for cut in rig_cuts:
            with self.subTest(cut=cut.name):
                if os.path.exists(self.seg):
                    os.unlink(self.seg)
                self.assertEqual(self.append(2, 3).returncode, 0)
                if cut.program == "fn-lg-recover-program":
                    killed = run(DEVELOPER, "recover", *self.args(), fault=cut.name)
                    expect = {6}
                else:
                    killed = self.append(1, 3, fault=cut.name)
                    expect = {9} if cut.candidate == "present" else set(range(6, 10))
                self.assertEqual(killed.returncode, -signal.SIGKILL,
                                 (cut.name, killed.stdout, killed.stderr))
                result = run(DEVELOPER, "recover", *self.args())
                self.assertEqual(result.returncode, 0, result.stderr)
                (line,) = lines(result)
                self.assertIn(line["records"], expect, cut.name)
                self.assertTrue(line["workload"], cut.name)
                self.assertEqual(line["next"], line["records"] + 1)
                self.assertTrue(self.zeros_past(line["frontier"]))
                seen.append(cut.name)
        self.assertEqual(seen, [c.name for c in rig_cuts])


if __name__ == "__main__":
    unittest.main()
