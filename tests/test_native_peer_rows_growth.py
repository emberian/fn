"""D27, PRF-171, SCN-101: a peer's carried rows grow past the old 1,024.

Before PRF-171 every `peer carries NAME HEX` published the peer's WHOLE row
group as one (:set-peer NAME ROWS) delta, so a peer stopped at
`*fn-cfg-max-rows*` (1,024) rows: its carried principals were data capped by
a constant.  Now each request publishes only its own rows, (:add-peer-rows
NAME ROWS) (books/peer-carriage-rows.lisp `fn-pcb-extend-deltas', through
books/native-admin.lisp `fn-native-admin-plan-deltas-over' from
host/native-admin-host.lisp `fn-native-admin-host-apply'), and 1,024 is the
work bound of one delta (`fn-cfg-add-peer-rows-refuses-exactly-past-the-work-
bound').

On the developer image, offline: `init` with room for the requests
(`--max-transactions` and `--max-config-generations`), `peer add far ...`,
then N separate `peer carries far HEX` requests (N = 1,100 by default,
FN_PEER_ROWS_REQUESTS to change it), each accepted; `peer list` (a fresh open
that replays every configuration record) lists all N principals in request
order; `peer budget far ...` twice over the grown group (the second
publishes :remove-peer-rows for the first's two rows) keeps every
principal; repeating a principal adds no row.
"""
import os
import time
import unittest

from tests.native_harness import EXIT_OK, Node, native_image, requires, slow
# The harness stores' init budget (tools/native_env.py): init refuses a
# store without `init --budget MB' on a large machine (batch AZ, 2026-09-28).
from tools.native_env import HARNESS_INIT_BUDGET_MB  # noqa: E402


DEVELOPER = native_image("FN_NATIVE_DEVELOPER_HOST")
REQUESTS = int(os.environ.get("FN_PEER_ROWS_REQUESTS", "1100"))


def principal(k):
    return "{:064x}".format(k + 1)


@requires(DEVELOPER)
class NativePeerRowsGrowthTests(unittest.TestCase):
    listener = False

    def setUp(self):
        self.node = Node(self, DEVELOPER, listener=self.listener, control=self.listener)
        self.root, self.store = self.node.root, self.node.store_path

    def ok(self, *words):
        return self.node.operator(*words, expect=EXIT_OK)

    def carried(self):
        listed = self.ok("peer", "list")
        lines = listed.stdout.decode("ascii").splitlines()
        self.assertEqual(len(lines), 1, listed.stdout[:400])
        words = lines[0].split()
        return ([w.split("=", 1)[1] for w in words
                 if w.startswith("carries-principal=")], lines[0])

    @slow("1,100 peer requests: 6,440 s on a loaded hbox (PKT-722); "
          "FN_PEER_ROWS_REQUESTS=300 decides the same row cap")
    def test_a_peer_carries_more_than_the_old_row_cap(self):
        room = str(REQUESTS + 64)
        # The small preset's record, article and group bounds (tools/fixtures.py
        # SYNTH_SMALL_BOUNDS): with the defaults, init's reservation for this
        # profile is 11.5 TB and the budget check refuses it (batch AZ).
        self.ok("init", "--budget", HARNESS_INIT_BUDGET_MB, "--profile", "default",
                "--max-transactions", room,
                "--max-config-generations", room,
                "--max-record-octets", "196608", "--max-article-octets", "32768",
                "--max-groups-per-article", "16",
                "--max-history-octets", "67108864", "fn.test")
        self.ok("peer", "add", "far", "far.example.invalid", "192.0.2.44",
                "1119", "fn.*", "-", "192.0.2.44", "true")
        started = time.monotonic()
        for k in range(REQUESTS):
            carried = self.ok("peer", "carries", "far", principal(k))
            # PKT-601 (2): the published record read back under the lock
            # (host/native/admin.lisp fnn-admin-verify-under-lock,
            # fn-cfgc-readback-verdict) verified every request.
            self.assertIn(b"verification=VERIFIED", carried.stdout)
        elapsed = time.monotonic() - started
        print("peer-rows-growth: {} requests in {:.1f} s".format(REQUESTS, elapsed))

        carried, _ = self.carried()
        self.assertEqual(carried, [principal(k) for k in range(REQUESTS)])
        if REQUESTS >= 1100:
            self.assertGreater(len(carried), 1024)

        # A single-valued slot over the grown group: the old budget rows go,
        # the principals stay.
        self.ok("peer", "budget", "far", "1048576", "3")
        self.ok("peer", "budget", "far", "2097152", "5")
        carried_after, _ = self.carried()
        self.assertEqual(carried_after, carried)

        # Repeating a principal adds nothing (the row moves to the end, as
        # the whole-group extension always did).
        self.ok("peer", "carries", "far", principal(0))
        carried_again, _ = self.carried()
        self.assertEqual(len(carried_again), REQUESTS)
        self.assertEqual(sorted(carried_again), sorted(carried))


@requires(DEVELOPER)
class NativePeerRowsLiveTests(unittest.TestCase):
    """PKT-451 (4): the live owner's arm.

    With a node running, `peer carries` and `peer budget` reach the owner
    over the control socket (host/native/control.lisp -> host/native/admin.lisp
    `fnn-owner-live-admin-serialized' -> host/native-admin-host.lisp
    `fn-native-admin-host-owner-reconfigure', the same
    `fn-native-admin-plan-deltas-over'), so the owner publishes
    :add-peer-rows (code 18) and, for the second budget, :remove-peer-rows
    (code 19).  After the owner stops, `peer list' (a fresh open replaying
    every record) names the principals and the second budget.
    """
    listener = True
    setUp = NativePeerRowsGrowthTests.setUp
    ok = NativePeerRowsGrowthTests.ok

    def test_the_live_owner_extends_a_peer(self):
        self.ok("init", "fn.test")
        self.node.start()
        self.ok("peer", "add", "far", "far.example.invalid", "192.0.2.44",
                "1119", "fn.*", "-", "192.0.2.44", "true")
        for k in range(3):
            self.ok("peer", "carries", "far", principal(k))
        self.ok("peer", "budget", "far", "1048576", "3")
        self.ok("peer", "budget", "far", "2097152", "5")
        self.node.stop()
        listed = self.ok("peer", "list").stdout.decode("ascii")
        words = listed.split()
        self.assertEqual([w.split("=", 1)[1] for w in words
                          if w.startswith("carries-principal=")],
                         [principal(k) for k in range(3)])
        self.assertIn("2097152", listed)
        self.assertNotIn("1048576", listed)
        print("peer-rows-live:", listed.strip()[:300])


if __name__ == "__main__":
    unittest.main()
