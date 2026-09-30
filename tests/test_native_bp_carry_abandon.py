"""PRF-950 (HST-035, PKT-869): the operator's waiver of a BP carry obligation.

`operator CONFIG carry JOURNAL drop WORK --abandon REASON...' over one
enqueued, undertaken work: a drop without --abandon keeps the Store pin; the
waiver is durable in the carry journal (principal, reason), then the Store pin
is released through the receipt's own retention event; a waiver of an
obligation not held is refused by name with nothing written; a waiver whose
Store event a process death cut off is completed, once, by the next writable
open, and the waiver replays unchanged after every restart
(books/bp-carry-waiver.lisp)."""

import os
import unittest

from tests.native_harness import EXIT, article, native_image, requires, run, scratch, environment
from tests.bp_producer import post_articles

IMAGE = native_image("FN_NATIVE_DEVELOPER_HOST")
PRODUCER = native_image("FN_NATIVE_HOST")


@requires(IMAGE, PRODUCER)
class NativeBpCarryAbandonTests(unittest.TestCase):
    def setUp(self):
        self.tmp = scratch(self, "fn-native-bp-carry-abandon-")
        self.store = self.tmp / "store"
        self.journal = self.tmp / "workflow"
        self.config = self.tmp / "fn.toml"
        self.config.write_text('[store]\npath = "{}"\n'.format(self.store), encoding="ascii")
        self.msgid = "<native-abandon@example.invalid>"
        self.other = "<native-abandon-b@example.invalid>"
        initialized = self.invoke("store", self.store, "init", "fn.test")
        self.assertEqual(initialized.returncode, EXIT.OK, initialized.stderr)
        post_articles(self, PRODUCER, self.store,
                      [(msgid, article(msgid)) for msgid in (self.msgid, self.other)])
        steps = [("app-journal", "workflow-init", self.store, self.journal,
                   "dtn://fn-a/", "dtn://fn-b/", "policy-a", "authority-a",
                   "3600000", "incarnation-a", "authorization-a"),
                  ("app-journal", "workflow-enqueue", self.store, self.journal,
                   "1", "0", "work-a", self.msgid, "forward-a",
                   "dtn://fn-b/", "policy-a", "terms-a"),
                  ("app-journal", "workflow-enqueue", self.store, self.journal,
                   "2", "0", "work-b", self.other, "forward-b",
                   "dtn://fn-b/", "policy-a", "terms-a"),
                  ("bp-obligation", "undertake", self.store, self.journal, "work-a", "3")]
        for args in steps:
            done = self.invoke(*args)
            self.assertEqual(done.returncode, EXIT.OK, (args, done.stderr))
        self.principal = "uid:%d" % os.geteuid()

    def invoke(self, *args, env=None):
        return run([IMAGE, "--fn", *args], env=environment(env), timeout=60, text=True)

    def carry(self, *words, env=None):
        return self.invoke("operator", self.config, "carry", self.journal, *words, env=env)

    def line(self, work):
        listed = self.carry("inspect", work)
        self.assertEqual(listed.returncode, EXIT.OK, listed.stderr)
        return listed.stdout

    def pinned(self, work):
        status = self.invoke("bp-obligation", "status", self.store, self.journal, work)
        self.assertEqual(status.returncode, EXIT.OK, status.stderr)
        return "pinned=yes" in status.stdout

    def carry_records(self):
        root = self.journal / "carry" / "records"
        return {p.name: p.read_bytes() for p in sorted(root.glob("*"))} if root.exists() else {}

    def test_drop_keeps_the_pin_and_abandon_releases_it_once(self):
        dropped = self.carry("drop", "work-a", "peer", "retired")
        self.assertEqual(dropped.returncode, EXIT.OK, dropped.stderr)
        self.assertIn("pinned=yes hold=dropped", self.line("work-a"))
        self.assertTrue(self.pinned("work-a"))

        waived = self.carry("drop", "work-a", "--abandon", "peer", "gone")
        self.assertEqual(waived.returncode, EXIT.OK, waived.stderr)
        self.assertIn("BP carry durable abandon work=work-a", waived.stdout)
        line = self.line("work-a")
        self.assertIn("pinned=no hold=waived", line)
        # The first drop's reason stays; the waiver has its own.
        self.assertIn("reason=peer retired", line)
        self.assertIn("waived-by=" + self.principal + " waiver=peer gone", line)
        self.assertFalse(self.pinned("work-a"))
        # Exactly once: a second waiver is refused by name, nothing written.
        before = self.carry_records()
        again = self.carry("drop", "work-a", "--abandon", "again")
        self.assertEqual(again.returncode, EXIT.REFUSED, again.stderr)
        self.assertIn("reason=already-waived", again.stderr)
        self.assertEqual(before, self.carry_records())
        # The other work's hold and pin are untouched.
        self.assertIn("hold=none", self.line("work-b"))

    def test_waiver_of_an_obligation_not_held_is_refused(self):
        before = self.carry_records()
        refused = self.carry("drop", "work-b", "--abandon", "never", "undertaken")
        self.assertEqual(refused.returncode, EXIT.REFUSED, refused.stderr)
        self.assertIn("reason=not-held", refused.stderr)
        unknown = self.carry("drop", "work-z", "--abandon", "x")
        self.assertEqual(unknown.returncode, EXIT.REFUSED, unknown.stderr)
        self.assertIn("reason=unknown-work", unknown.stderr)
        self.assertEqual(before, self.carry_records())
        self.assertIn("hold=none", self.line("work-b"))
        usage = self.carry("drop", "work-a", "--abandon")
        self.assertEqual(usage.returncode, EXIT.USAGE, usage.stderr)

    def test_a_waiver_cut_before_its_store_release_is_completed_once(self):
        # A process death at the Store publication's first model cut, after
        # the waiver is durable in the carry journal.
        cut = self.carry("drop", "work-a", "--abandon", "peer", "gone",
                         env={"FN_NATIVE_POST_FAULT": "frontier-reserved:kill"})
        self.assertNotEqual(cut.returncode, EXIT.OK, cut.stdout)
        self.assertNotIn("BP carry durable abandon", cut.stdout)
        self.assertEqual(len(self.carry_records()), 2)      # :config, :waive
        # A read-only open replays the waiver; the pin still stands.
        self.assertIn("pinned=yes hold=waived", self.line("work-a"))
        # The next writable open completes the release before its verb.
        paused = self.carry("pause", "work-b")
        self.assertEqual(paused.returncode, EXIT.OK, paused.stderr)
        self.assertIn("BP carry recovered waiver release work=work-a", paused.stdout)
        self.assertIn("pinned=no hold=waived", self.line("work-a"))
        self.assertFalse(self.pinned("work-a"))
        # Once: the next writable open has nothing to complete.
        resumed = self.carry("resume", "work-b")
        self.assertEqual(resumed.returncode, EXIT.OK, resumed.stderr)
        self.assertNotIn("recovered waiver", resumed.stdout)
        self.assertIn("waived-by=" + self.principal, self.line("work-a"))


if __name__ == "__main__":
    unittest.main()
