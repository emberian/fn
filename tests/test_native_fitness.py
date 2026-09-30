"""A short soak under real clients: the fitness driver's fail conditions as a
module (lane fitness, 2026-09-28; planning/evidence/fitness-2026-09-28.md).

tools/fitness.py soak runs a production owner over implicit TLS with
`[auth] required', four accounts redeemed by XREDEEM, posters (with
References, cancels and supersedes mixed in) and readers (GROUP, ARTICLE,
OVER, HDR, XPAT, LISTGROUP, STAT of acknowledged articles), a maintenance
window (stop, `store compact', start), then a stop, `store digest' of the
store as left against a copy without its checkpoint, `store journal', a
restart and the same ARTICLE replies again.  This module runs it for
FN_FITNESS_MINUTES (default 4) and asserts what the evidence's f1 section
states as its fail conditions:

  * no finding: every acknowledged article is served after the maintenance
    window and after the restart, nothing refused is served, the replies
    sampled before the stop equal the ones after it;
  * the decision journal replays (`store journal' exit 0): lane fitness
    found its entries reaching the writer out of JSEQ order under eight
    clients (host/native/owner.lisp now offers each entry under the gate
    mutex that numbered it);
  * no uncertain POST outside a disk event or a stop, no 5xx outside the
    command's row.

Needs FN_NATIVE_HOST (the production image); tools/hbox_native.sh supplies
it.  About FN_FITNESS_MINUTES + 3 minutes.
"""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
IMAGE = os.environ.get("FN_NATIVE_HOST")
MINUTES = os.environ.get("FN_FITNESS_MINUTES", "4")


@unittest.skipUnless(IMAGE and os.access(IMAGE, os.X_OK), "set FN_NATIVE_HOST")
class ShortSoakTests(unittest.TestCase):
    def test_a_short_soak_has_no_finding_and_the_journal_replays(self):
        work = Path(tempfile.mkdtemp(prefix="fn-fitness-"))
        keep = os.environ.get("FN_FITNESS_EVIDENCE")
        try:
            result = subprocess.run(
                [sys.executable, str(ROOT / "tools" / "fitness.py"), "soak", "--image", IMAGE,
                 "--work", str(work), "--minutes", MINUTES, "--sample-minutes", "1",
                 "--client-minutes", "0", "--posters", "8", "--readers", "8",
                 "--init-flag=--profile", "--init-flag=default",
                 "--init-flag=--max-transactions", "--init-flag=65536",
                 "--init-flag=--max-history-octets", "--init-flag=268435456",
                 "--init-flag=--max-article-octets", "--init-flag=32768"],
                cwd=str(ROOT), stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                timeout=int(float(MINUTES) * 60) + 1200, check=False)
            summary = json.loads((work / "summary.json").read_text())
            events = [json.loads(l) for l in (work / "events.jsonl").read_text().splitlines()]
            digest = [e for e in events if e["kind"] == "digest"]
            maint = [e for e in events if e["kind"] == "maintenance"]
            print("FITNESS-SOAK " + json.dumps({
                "accepted": summary.get("posts_accepted"), "refused": summary.get("posts_refused"),
                "uncertain": summary.get("posts_uncertain"),
                "rss_kb": summary.get("rss_kb"), "findings": summary.get("findings"),
                "journal": [d.get("journal") for d in digest],
                "maintenance": maint}, sort_keys=True), flush=True)
            self.assertEqual(result.returncode, 0, result.stderr.decode()[-2000:])
            self.assertGreater(summary["posts_accepted"], 100, summary)
            self.assertEqual(summary["findings"], [], summary["findings"])
            self.assertEqual(summary["uncertain_outside_window"], [], summary)
            self.assertEqual(summary["unexpected_5xx"], [], summary)
            self.assertEqual(len(digest), 1, digest)
            self.assertEqual(digest[0]["journal_rc"], 0, digest[0]["journal"])
            self.assertTrue(digest[0]["same"], digest[0])
            self.assertEqual(len(maint), 1, maint)
            self.assertEqual(maint[0]["compact_rc"], 0, maint[0])
        finally:
            if keep:
                shutil.copytree(work, Path(keep) / "fitness-soak", dirs_exist_ok=True)
            shutil.rmtree(work, ignore_errors=True)


if __name__ == "__main__":
    unittest.main()
