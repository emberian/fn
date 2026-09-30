"""SCN-1003: actual FNLS keyed contributions agree with independent pins.

The fixture creates archive and forwarding holds of the same content subject.
The aggregate is read-only; receipt processing still releases an obligation ID.
This requires a matching developer image; runner owns execution.
"""
import re

from tests.test_native_capacity_vector import _Bp
from tests.test_bp_app_native import IMAGE
from tests.native_harness import EXIT, Node


class NativeObligationSubjectTests(_Bp):
    def query(self, owner, subject):
        reply = owner.operator("obligations", "subject", subject,
                               timeout=600, expect=EXIT.OK)
        match = re.fullmatch(rb"subject-hex=([0-9a-f]+) obligations=([0-9]+) charge=([0-9]+)\n",
                             reply.stdout)
        self.assertIsNotNone(match, reply.stdout)
        self.assertEqual(bytes.fromhex(match[1].decode()), subject.encode())
        return reply.stdout, int(match[2]), int(match[3])

    def test_live_offline_release_and_reopen_keep_independent_hold(self):
        store, workflow = self.prepare_sender_obligation()
        owner = Node(self, IMAGE, root=self.temp / "owner")
        owner.store_path = store
        owner.write_config()
        listing = owner.operator("obligations", expect=EXIT.OK).stdout
        pins = re.findall(rb"^obligation id=\S+ kind=\S+ charge=([0-9]+) subject=(\S+)\n",
                          listing, re.MULTILINE)
        self.assertEqual(len(pins), 2, listing)
        self.assertEqual(pins[0][1], pins[1][1], listing)
        subject = pins[0][1].decode("ascii")
        offline, count, charge = self.query(owner, subject)
        self.assertEqual(count, 2)
        self.assertEqual(charge, sum(int(p[0]) for p in pins))
        missing, missing_count, missing_charge = self.query(owner, "absent-subject")
        self.assertEqual((missing_count, missing_charge), (0, 0))
        owner.start(timeout=600)
        self.assertEqual(self.query(owner, subject)[0], offline)
        self.assertEqual(self.query(owner, "absent-subject")[0], missing)
        # Actual served completion changes the carried total without changing
        # the old subject contribution or importing uncommitted reader state.
        from tests.native_harness import Client
        client = Client(owner.port, timeout=600)
        self.addCleanup(client.close)
        self.assertTrue(client.command("POST").startswith(b"340"))
        article = self.article.replace(self.msgid, b"<w9-live@example.invalid>")
        client.send(article + b".\r\n")
        self.assertTrue(client.line().startswith(b"240"))
        self.assertEqual(self.query(owner, subject)[0], offline)
        client.close()
        owner.stop()
        receiver, port = self.start_receiver()
        sender = self.start_sender(port)
        _, sender_err = sender.communicate(timeout=600)
        _, receiver_err = receiver.communicate(timeout=600)
        self.assertEqual(sender.returncode, EXIT.OK, sender_err)
        self.assertEqual(receiver.returncode, EXIT.OK, receiver_err)
        receipts = sorted((self.sender_spool / "receive-evidence").glob("*.adu"))
        self.assertEqual(len(receipts), 1)
        release = self.invoke("bp-obligation", "receipt", store, workflow, receipts[0],
                              "2", "0", "trusted-local-observation-v0")
        self.assertEqual(release.returncode, EXIT.OK, release.stderr)
        after, count_after, charge_after = self.query(owner, subject)
        self.assertEqual((count_after, charge_after), (1, charge - 3))
        owner.start(timeout=600)
        self.assertEqual(self.query(owner, subject)[0], after)
