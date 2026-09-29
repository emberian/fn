"""Row S1 (lane limits-live-3, STO-038, PRF-940): the store's limits are
operator policy changed in place.

`policy set max-transactions|max-history-octets|max-article-octets N' is one
configuration record (a :set-limit row folded over the sealed profile,
books/limits-live.lisp fn-lim-effective).  ACL2 decides it (fn-lim-decide)
before anything is staged: applied now when the new profile's heap figure fits
the reservation the running owner started with; recorded for the next start
(no data moved) when it does not; refused by name with the number below the
store's current use.  config.json is never rewritten (its digest is sealed in
journal/000000.log).

Cases: a live raise of T within the reservation (posting continues past the
old T); a raise beyond it (recorded; effective after a restart); a lowering
below use (refused by name, nothing recorded); replay determinism (two
restarts serve the same budget); recovery (a kill -9 after the durable record
reopens with the new T).
"""

import hashlib
import signal

from tests.native_harness import EXIT_OK
from tests.test_native_checkpoint_auto import AutoCheckpointFixture


def article(tag, n):
    message_id = "<{}-{}@example.invalid>".format(tag, n)
    payload = ("From: a <a@example.invalid>\r\nNewsgroups: fn.test\r\n"
               "Subject: {} {}\r\nMessage-ID: {}\r\n"
               "Date: Tue, 29 Sep 2026 00:00:00 +0000\r\n\r\nbody\r\n"
               .format(tag, n, message_id)).encode("ascii")
    return message_id, payload


class LimitsLiveTests(AutoCheckpointFixture):
    T = 12

    def init_small(self):
        created = self.op("init", "--profile", "development", "--max-transactions",
                          str(self.T), "fn.test")
        self.assertEqual(created.returncode, EXIT_OK, created.stderr.decode())

    def post(self, tag, n):
        message_id, payload = article(tag, n)
        return self.node.post(message_id, payload).returncode

    def fill(self, tag, first, count):
        return [self.post(tag, n) for n in range(first, first + count)]

    def policy(self, field, n):
        return self.op("policy", "set", field, str(n))

    def config_digest(self):
        return hashlib.sha256((self.root / "config.json").read_bytes()).hexdigest()

    def budget(self):
        return self.headroom()["transactions-budget"]

    def test_a_live_raise_within_the_reservation_serves_past_the_old_budget(self):
        self.init_small()
        sealed = self.config_digest()
        owner = self.node.start()
        outcomes = self.fill("within", 0, self.T + 1)
        self.assertEqual(outcomes[-1], 1, "the post past T is refused before the raise")
        raised = self.policy("max-transactions", self.T + 2)
        self.assertEqual(raised.returncode, EXIT_OK, raised.stderr.decode())
        self.assertIn(b"applied:max-transactions=14", raised.stderr)
        self.assertIn(b"no-data-moved", raised.stderr)
        # Served now: the same owner admits a post past the old T.
        self.assertEqual(self.post("within", 100), EXIT_OK)
        self.node.stop(process=owner)
        self.assertEqual(self.config_digest(), sealed, "config.json is never rewritten")

    def test_a_raise_beyond_the_reservation_is_recorded_for_the_next_start(self):
        self.init_small()
        owner = self.node.start()
        self.fill("beyond", 0, self.T)
        raised = self.policy("max-history-octets", 805306368)
        self.assertEqual(raised.returncode, EXIT_OK, raised.stderr.decode())
        self.assertIn(b"recorded:max-history-octets=805306368:effective-at-next-start",
                      raised.stderr)
        self.assertIn(b"no-data-moved", raised.stderr)
        self.node.stop(process=owner)
        # The next open serves the recorded profile.
        lines = self.status_lines()
        self.assertTrue(any("history-bound=805306368" in line for line in lines), lines)

    def test_a_lowering_below_use_is_refused_by_name_and_records_nothing(self):
        self.init_small()
        owner = self.node.start()
        self.fill("below", 0, 6)
        before = sorted(p.name for p in (self.root / "config").iterdir())
        lowered = self.policy("max-transactions", 3)
        self.assertEqual(lowered.returncode, 1, lowered.stderr.decode())
        self.assertIn(b"below-current-use:max-transactions=3:the-store-holds=", lowered.stderr)
        self.assertEqual(sorted(p.name for p in (self.root / "config").iterdir()), before)
        self.node.stop(process=owner)
        # Offline, the same refusal, in ACL2's sentence.
        offline = self.policy("max-transactions", 3)
        self.assertEqual(offline.returncode, 1, offline.stderr.decode())
        self.assertIn(b"below-current-use: the store holds", offline.stderr)

    def test_an_offline_change_is_recorded_and_every_restart_serves_it(self):
        self.init_small()
        changed = self.policy("max-transactions", self.T + 4)
        self.assertEqual(changed.returncode, EXIT_OK, changed.stderr.decode())
        self.assertIn(b"recorded limit max-transactions=16 effective-at-next-start: "
                      b"takes effect at the next restart (about ", changed.stdout)
        self.assertIn(b"no data moved", changed.stdout)
        first = self.budget()
        owner = self.node.start()
        self.node.stop(process=owner)
        second = self.budget()
        owner = self.node.start()
        self.node.stop(process=owner)
        self.assertEqual((first, second, self.budget()), (first, first, first))
        self.assertGreater(first, 0)

    def test_a_kill_after_the_durable_record_reopens_with_the_new_budget(self):
        self.init_small()
        owner = self.node.start()
        self.fill("kill", 0, self.T)
        raised = self.policy("max-transactions", self.T + 2)
        self.assertEqual(raised.returncode, EXIT_OK, raised.stderr.decode())
        owner.send_signal(signal.SIGKILL)
        owner.wait()
        again = self.node.start()
        self.assertEqual(self.post("kill", 100), EXIT_OK,
                         "the recovered owner serves the recorded T")
        self.node.stop(process=again)


if __name__ == "__main__":
    import unittest
    unittest.main()
