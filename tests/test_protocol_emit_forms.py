"""tools/protocol_emit.py forms_owed: archive rows owe :forms; :dispatch :pinned peer rows do not (DC03)."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import protocol_emit  # noqa: E402


def row(name, dispatch, arms=True, cost=None):
    return {"name": name, "dispatch": dispatch, "arms": arms, "cost": cost}


class FormsOwedTests(unittest.TestCase):
    def test_pinned_peer_rows_owe_no_forms(self):
        table = {"rows": [row("XFNCATCHUP", "pinned"), row("XFN-ZARTICLE", "pinned")]}
        self.assertEqual(protocol_emit.forms_owed(table), [])
        self.assertEqual(protocol_emit.check_forms(table), [])

    def test_archive_row_with_hand_arms_and_no_forms_is_owed(self):
        table = {"rows": [row("ARTICLE", "archive"), row("GROUP", "archive", cost={"unrestricted": "x"}),
                          row("XFNCATCHUP", "pinned")]}
        self.assertEqual(protocol_emit.forms_owed(table), ["ARTICLE"])
        self.assertEqual(len(protocol_emit.check_forms(table)), 1)

    def test_rows_without_arms_are_not_served_archive_rows(self):
        self.assertEqual(protocol_emit.forms_owed({"rows": [row("X", "archive", arms=False)]}), [])

    def test_the_real_table_owes_nothing(self):
        table = protocol_emit.load()
        self.assertEqual(protocol_emit.forms_owed(table), [])
        pinned = [r["name"] for r in table["rows"] if r["dispatch"] == "pinned"]
        self.assertEqual(sorted(pinned), ["XFN-ZARTICLE", "XFNCATCHUP"])


if __name__ == "__main__":
    unittest.main()
