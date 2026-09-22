"""The native operator campaign driver, as a test.

The table checks need no image.  The campaign check needs a frozen image
directory holding both `fn-host-developer` and `fn-host` (FN_NATIVE_IMAGES)
and Linux (the control stop row reads /proc); without them it skips and says
which it wanted.  It runs one post cut and one recovery cut through the driver
and asserts what the fixes of campaign dabebb84 promise on an image: the
served owner dies at the cut (F1), the control stop's client answers 3 every
time (F3), and the production image refuses every developer selector at
startup with its store unchanged (F4 to F6).
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tests.campaign import native_cuts  # noqa: E402
from tests.campaign import native_operator_campaign  # noqa: E402

IMAGES = Path(os.environ.get("FN_NATIVE_IMAGES", ROOT / "build" / "images" / "current"))
EXIT_UNCERTAIN, EXIT_USAGE, KILLED = 3, 5, -9


def executable(path: Path) -> bool:
    return path.is_file() and os.access(path, os.X_OK)


class NativeCutTableTests(unittest.TestCase):
    def test_the_table_agrees_with_the_host(self):
        native_cuts.verify_native_cut_map()

    def test_the_recovery_program_cuts_are_selectable(self):
        self.assertEqual([cut.name for cut in native_cuts.RECOVERY_CUTS],
                         ["recover-replayed", "recover-barrier",
                          "recovery-stage-unlinked"])
        self.assertEqual({cut.program for cut in native_cuts.RECOVERY_CUTS[:2]},
                         {"fn-bs-recover-program"})
        unlinked = native_cuts.RECOVERY_CUTS[2]
        self.assertEqual(unlinked.follows, "fn-bs-recover-program")

    def test_every_developer_selector_is_registered(self):
        self.assertEqual(set(native_cuts.developer_selectors()), {
            "FN_NATIVE_INIT_FAULT", "FN_NATIVE_RECOVERY_FAULT",
            "FN_NATIVE_POST_FAULT", "FN_NATIVE_CONTROL_FAULT",
            "FN_NATIVE_CONTROL_TEST_STOP", "FN_NATIVE_AUTH_ADMIN_FAULT",
            "FN_NATIVE_OWNER_TEST_SIGTERM", "FN_NATIVE_OWNER_TEST_PAUSE_CLEANUP"})


class NativeOperatorCampaignTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        missing = [name for name in ("fn-host-developer", "fn-host")
                   if not executable(IMAGES / name)]
        if missing:
            raise unittest.SkipTest(
                "FN_NATIVE_IMAGES must name an image directory holding "
                "fn-host-developer and fn-host (missing {} under {})".format(
                    ", ".join(missing), IMAGES))
        if not Path("/proc/self/stat").is_file():
            raise unittest.SkipTest(
                "the control stop row reads /proc/<pid>/stat: Linux is required")

    def test_served_owner_cuts_stop_and_production_refusals(self):
        with tempfile.TemporaryDirectory(prefix="fn-native-campaign-") as tmp:
            out = Path(tmp) / "campaign.json"
            native_operator_campaign.main([
                "--images", str(IMAGES), "--work", str(Path(tmp) / "work"),
                "--out", str(out), "--only", "record-attempted",
                "--only", "recovery-stage-unlinked"])
            result = json.loads(out.read_text())
        cuts = {row["cut"]: row for row in result["cuts"]}
        post = cuts["record-attempted"]["served"]
        self.assertEqual(post["owner"]["rc"], KILLED, post["owner"])
        self.assertTrue(post["recover"]["rc"] == 0, post["recover"])
        self.assertTrue(post["inspect_candidate"]["identical"])
        self.assertEqual(post["recover_counts"]["transactions"], 2)
        recovery = cuts["recovery-stage-unlinked"]["served"]
        self.assertFalse(recovery["owner_ready"])
        self.assertEqual(recovery["owner"]["rc"], KILLED, recovery["owner"])
        self.assertEqual(recovery["killed"]["staging"], {})
        faults = {row["name"]: row for row in result["faults"]}
        for repetition in range(5):
            stop = faults["dev-control-test-stop-kill-{}".format(repetition)]
            self.assertTrue(stop["owner_stopped_itself"])
            self.assertIsNone(stop["client_exited_before_kill"])
            self.assertEqual(stop["post"]["rc"], EXIT_UNCERTAIN, stop["post"])
        refused = faults["prod-selectors-refused-at-start"]
        self.assertTrue(refused["unchanged"])
        self.assertEqual(len(refused["starts"]), len(native_cuts.developer_selectors()))
        for start in refused["starts"]:
            with self.subTest(selector=start["variable"]):
                for entry in ("operator_run", "operator_recover", "store_post"):
                    self.assertEqual(start[entry]["rc"], EXIT_USAGE, start[entry])
                    self.assertIn(start["variable"], start[entry]["stderr"])
        self.assertEqual(refused["store_post_fault_argument"]["rc"], EXIT_USAGE)
        self.assertEqual(faults["prod-init-fault"]["init"]["rc"], EXIT_USAGE)
        self.assertFalse(faults["prod-init-fault"]["store_created"])


if __name__ == "__main__":
    unittest.main()
