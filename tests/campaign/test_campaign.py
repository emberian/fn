"""The generated crash campaign, as a test.

`FN_CAMPAIGN=quick` runs the marked subset (one cut per barrier class per
write path) instead of the full matrix; the subset is the iteration loop, not
the gate.  Both run the same checks against the same real host.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import shutil
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tests.campaign import cuts  # noqa: E402
from tests.campaign.campaign import Campaign  # noqa: E402


class CutTableTests(unittest.TestCase):
    """These need no ACL2: they check the table against the host source."""

    def test_the_table_and_the_injector_agree(self) -> None:
        # A fault point added to tools/ with no cut here fails this, which is
        # what makes the campaign generated rather than hand-enumerated.
        cuts.verify_table()

    def test_every_cut_is_run_or_carries_its_reason(self) -> None:
        for cut in cuts.CUTS:
            with self.subTest(cut=cut.cut_id):
                self.assertTrue(bool(cut.scenarios) != bool(cut.uncovered))
                self.assertTrue(cut.model)

    def test_each_write_path_has_at_least_one_cut(self) -> None:
        paths = {cut.path for cut in cuts.CUTS}
        for required in ("advance_frontier", "publish", "finish", "recover",
                         "stage_inbound", "receive_bpa_request"):
            self.assertIn(required, paths)


class CampaignTests(unittest.TestCase):
    """Slow: every pair spawns a host process with its own ACL2."""

    def test_the_campaign_reports_no_failure(self) -> None:
        quick = os.environ.get("FN_CAMPAIGN", "full").lower() == "quick"
        workdir = Path(tempfile.mkdtemp(prefix="fn-campaign-test-"))
        try:
            campaign = Campaign(workdir, quick=quick,
                                log=lambda message: print(message, flush=True))
            report = campaign.run()
        finally:
            shutil.rmtree(workdir, ignore_errors=True)
        print("campaign pairs={} seconds={:.1f} quick={}".format(
            report.pairs, report.seconds, quick))
        self.assertGreater(report.pairs, 0)
        if report.failures:
            self.fail("campaign failures:\n" + json.dumps(
                [failure.as_json() for failure in report.failures],
                indent=2, sort_keys=True))


if __name__ == "__main__":
    unittest.main()
