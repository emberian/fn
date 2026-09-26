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

from tests import test_native_operator_verbs as verbs

EXIT_OK = verbs.EXIT_OK
REQUESTS = int(os.environ.get("FN_PEER_ROWS_REQUESTS", "1100"))


def principal(k):
    return "{:064x}".format(k + 1)


@unittest.skipUnless(verbs.executable(verbs.DEVELOPER), "the developer image is required")
class NativePeerRowsGrowthTests(verbs.NativeOperatorVerbFixture):
    def operator(self, *words, **kwargs):
        return super().operator(*words, image=verbs.DEVELOPER, **kwargs)

    def ok(self, *words):
        result = self.operator(*words)
        self.assertEqual(result.returncode, EXIT_OK,
                         "{}: {}".format(" ".join(words[:3]),
                                         result.stderr.decode(errors="replace")))
        return result

    def carried(self):
        listed = self.ok("peer", "list")
        lines = listed.stdout.decode("ascii").splitlines()
        self.assertEqual(len(lines), 1, listed.stdout[:400])
        words = lines[0].split()
        return ([w.split("=", 1)[1] for w in words
                 if w.startswith("carries-principal=")], lines[0])

    def test_a_peer_carries_more_than_the_old_row_cap(self):
        room = str(REQUESTS + 64)
        self.ok("init", "--max-transactions", room,
                "--max-config-generations", room, "fn.test")
        self.ok("peer", "add", "far", "far.example.invalid", "192.0.2.44",
                "1119", "fn.*", "-", "192.0.2.44", "true")
        started = time.monotonic()
        for k in range(REQUESTS):
            self.ok("peer", "carries", "far", principal(k))
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


if __name__ == "__main__":
    unittest.main()
