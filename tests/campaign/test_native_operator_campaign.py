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


class InjectedFormTests(unittest.TestCase):
    """The reread judgement for an article the owner injected (a0b6d41f)."""

    payload = native_operator_campaign.article(
        native_operator_campaign.CANDIDATE_ID, "candidate", "candidate content")
    # The shape the da5fd8cb image stored for `operator CFG post` of `payload`.
    injection = (b"Path: fn.example.invalid!not-for-mail\r\n"
                 b"Injection-Date: Wed, 23 Sep 2026 02:47:48 +0000\r\n"
                 b"Injection-Info: fn.example.invalid\r\n"
                 b"Date: Wed, 23 Sep 2026 02:47:48 +0000\r\n")

    def judge(self, stored):
        return native_operator_campaign.injected_from(stored, self.payload)

    def test_the_injected_article_is_the_payload_injected(self):
        self.assertTrue(self.judge(self.injection + self.payload))
        self.assertTrue(native_operator_campaign.matches(
            self.injection + self.payload, self.payload, injected=True))
        self.assertFalse(native_operator_campaign.matches(
            self.injection + self.payload, self.payload, injected=False))

    def test_a_changed_body_is_not(self):
        self.assertFalse(self.judge(self.injection + self.payload.replace(
            b"candidate content", b"candidate contenT")))

    def test_an_added_field_outside_the_injection_is_not(self):
        self.assertFalse(self.judge(
            self.injection + b"Xref: fn.example.invalid fn.letters:1\r\n" + self.payload))

    def test_a_dropped_or_reordered_payload_field_is_not(self):
        head, _, body = self.payload.partition(b"\r\n\r\n")
        lines = head.split(b"\r\n")
        dropped = b"\r\n".join(lines[1:]) + b"\r\n\r\n" + body
        swapped = b"\r\n".join([lines[1], lines[0]] + lines[2:]) + b"\r\n\r\n" + body
        self.assertFalse(self.judge(self.injection + dropped))
        self.assertFalse(self.judge(self.injection + swapped))

    def test_a_field_injected_twice_or_over_the_payloads_own_is_not(self):
        path = b"Path: fn.example.invalid!not-for-mail\r\n"
        self.assertFalse(self.judge(path + self.injection + self.payload))
        dated = self.payload.replace(b"Subject:", b"Date: Tue, 22 Sep 2026 00:00:00 +0000\r\nSubject:")
        self.assertFalse(native_operator_campaign.injected_from(
            self.injection + dated, dated))

    def test_a_headless_octet_string_is_not(self):
        self.assertFalse(self.judge(b"no header separator"))
        self.assertFalse(self.judge(b""))


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
        # The owner's injected candidate reads back as the injected payload,
        # and a retry through the same entry is its duplicate.
        self.assertTrue(post["nntp_candidate"]["identical"])
        self.assertTrue(post["nntp_candidate"]["same_as_inspect"])
        self.assertIn("DUPLICATE", post["resubmit"]["stderr"])
        cut = cuts["record-attempted"]["cut_run"]
        self.assertTrue(cut["inspect_candidate"]["identical"])
        self.assertEqual((cut["resubmit"]["rc"], cut["resubmit"]["stdout"]), (0, "duplicate\n"))
        self.assertEqual(cut["after_resubmit"]["transactions"], cut["recovered"]["transactions"])
        # Campaign dabebb84 F2: after the deaths the store opens and the
        # orphans are gone.
        orphans = faults["dev-allocation-orphans-recover"]
        self.assertEqual(set(orphans["deaths"]), {KILLED})
        self.assertEqual(orphans["recover"]["rc"], 0, orphans["recover"])
        self.assertEqual(orphans["opened"]["staging"], {})
        self.assertIn("ACCEPTED", orphans["post"]["stderr"])
        # One payload through the two entries is a conflict either way round.
        for order in ("store-then-operator", "operator-then-store"):
            retry = faults["cross-entry-retry-" + order]
            self.assertEqual(retry["first"]["rc"], 0, retry["first"])
            self.assertEqual(retry["second"]["rc"], 1, retry["second"])
            self.assertEqual(retry["after_second"], retry["after_first"])
        refused = faults["prod-selectors-refused-at-start"]
        self.assertTrue(refused["unchanged"])
        self.assertEqual(len(refused["starts"]), len(native_cuts.developer_selectors()))
        for start in refused["starts"]:
            with self.subTest(selector=start["variable"]):
                for entry in ("operator_run", "operator_recover", "store_post"):
                    self.assertEqual(start[entry]["rc"], EXIT_USAGE, start[entry])
                    self.assertIn(start["variable"], start[entry]["stderr"])
        self.assertEqual(refused["store_post_fault_argument"]["rc"], EXIT_USAGE)
        raw = faults["prod-raw-store-post-guard"]
        self.assertEqual(raw["plain_post"]["rc"], EXIT_USAGE)
        self.assertFalse(raw["store_created"])
        self.assertFalse(raw["payload_created"])
        self.assertEqual(faults["prod-init-fault"]["init"]["rc"], EXIT_USAGE)
        self.assertFalse(faults["prod-init-fault"]["store_created"])


if __name__ == "__main__":
    unittest.main()
