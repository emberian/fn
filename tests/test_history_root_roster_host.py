"""The terminal-root roster witness, loaded over the ld-only host files.

host/history-root-host.lisp sits on host/owner-host.lisp, which `ld`s its own
host files and so is not certifiable as a book; the witness is therefore a
fixture run by the owner-feed host runner (host/owner-host.lisp first, then the
fixture) under host_check's error and prompt discipline.
"""
from __future__ import annotations

from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tests"))
sys.path.insert(0, str(ROOT))
import owner_feed_connection_host_check as runner  # noqa: E402
from tools import host_check  # noqa: E402


@unittest.skipIf(host_check.executable() is None, "FN_ACL2 is unset or does not name an executable")
class HistoryRootRosterHost(unittest.TestCase):
    def test_terminal_root_roster_deletion(self) -> None:
        ok, reason, output = runner.run("tests/history-root-roster-host.lsp")
        self.assertTrue(ok, f"{reason}\n{output[-2000:]}")


if __name__ == "__main__":
    unittest.main()
