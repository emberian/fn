"""Live BP ADU ingress checks through workflow staging, ACL2, and Store files."""
import tempfile
import unittest
import zlib
from pathlib import Path

import sys

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
import run_bp_ingress  # noqa: E402
import run_store  # noqa: E402

WORKFLOW_JOURNAL = ROOT / "tools" / "workflow_journal.py"

# The ingress boundary takes the bundle octets the agent holds and lets ACL2
# derive the identity and the expiry decision from the primary block; nothing
# below spells a BPv7 field.  `fn-bpi-host-bundle-prefix` returns the
# indefinite-array head and the certified primary-block encoding, and the
# break stop code stands in for the blocks the boundary never interprets.
# The same fixture is in tests/test_bp_receive.py, which covers the receiver.
LIVE_LIFETIME = 10 ** 15


def lab_bundles(sequences):
    """Build one bundle per sequence number in a single ACL2 session."""
    bridge = run_bp_ingress.Acl2BpIngress()
    try:
        def eid(ssp):
            return "(cons :dtn '" + bridge.literal(ssp) + ")"

        built = []
        for sequence in sequences:
            form = ("(fn-bpi-host-bundle-prefix (fn-bpp-make-block 0 0 {} {} {} "
                    "1000 {} {} nil nil))".format(
                        eid(b"//fn.lab/inbox"), eid(b"//peer.lab/"),
                        eid(b"//fn.lab/report"), sequence, LIVE_LIFETIME))
            built.append(run_store.acl2_octets(bridge.call(form)) + b"\xff")
        return built
    finally:
        bridge.close()


class BpIngressHostTests(unittest.TestCase):
    def setUp(self):
        if not WORKFLOW_JOURNAL.is_file():
            self.fail("coordinated workflow journal candidate is unavailable")
        self.temporary = tempfile.TemporaryDirectory(prefix="fn-bp-ingress-")
        self.store_root = Path(self.temporary.name) / "store"
        self.journal_root = Path(self.temporary.name) / "workflow"
        run_store.Store(self.store_root, writable=True).initialize()
        self.inventory = {}
        self.bundles = {}
        self.deleted = []

    def tearDown(self):
        self.temporary.cleanup()

    @staticmethod
    def adu(label, group=b"fn.letters"):
        return (b"Message-ID: <" + label.encode("ascii") + b"@bp.example>\r\n"
                b"Newsgroups: " + group + b"\r\n\r\nBody " + label.encode("ascii") + b"\r\n")

    def stage(self, bid, payload):
        """Register one BPA bundle: its ADU to download, its octets to identify.

        Each BID gets its own creation sequence, so these are distinct
        bundles that one agent happens to carry.
        """
        self.inventory[bid] = payload
        self.bundles[bid] = lab_bundles([zlib.crc32(bid.encode("ascii")) + 1])[0]

    def invoke(self, bid, delete=None):
        def inventory():
            return list(self.inventory)

        def download(found_bid):
            return self.inventory[found_bid]

        def default_delete(found_bid):
            self.deleted.append(found_bid)
            del self.inventory[found_bid]

        return run_bp_ingress.ingest_bpa_adu(
            store_root=self.store_root, journal_root=self.journal_root,
            journal_module_path=WORKFLOW_JOURNAL, bid=bid, inventory=inventory,
            download=download, delete=default_delete if delete is None else delete,
            bundle=lambda found_bid: self.bundles[found_bid],
            source_eid="dtn://peer.lab", lifetime=3600)

    def live(self):
        return run_bp_ingress.open_live_bp_store(self.store_root, writable=False)

    def test_distinct_adus_get_distinct_store_bindings_and_conflict_refuses(self):
        payload = self.adu("once")
        second_payload = self.adu("second")
        self.stage("bpa-001", payload)
        self.stage("bpa-003", second_payload)
        result = self.invoke("bpa-001")
        second_result = self.invoke("bpa-003")
        self.assertEqual(result.outcome, "accepted")
        self.assertEqual(second_result.outcome, "accepted")
        self.assertEqual(self.deleted, ["bpa-001", "bpa-003"])
        store, bridge, records = self.live()
        try:
            self.assertEqual(len(records), 2)
            self.assertEqual(bridge.article_count(), 2)
            self.assertEqual(bridge.lookup(b"<once@bp.example>"), payload)
            self.assertEqual(bridge.lookup(b"<second@bp.example>"), second_payload)
            self.assertEqual(bridge.pin_count(), 2)
        finally:
            bridge.close()
            store.close()
        # A fresh BPA transport reference carrying the byte-identical first
        # ADU is an article duplicate.  BID is deliberately absent from the
        # ACL2 article identity/binding comparison.
        self.stage("bpa-replay-new-bid", payload)
        replay = self.invoke("bpa-replay-new-bid")
        self.assertEqual(replay.outcome, "duplicate")
        self.assertEqual(self.deleted, ["bpa-001", "bpa-003", "bpa-replay-new-bid"])
        store, bridge, records = self.live()
        try:
            self.assertEqual(len(records), 2)
            self.assertEqual(bridge.article_count(), 2)
            self.assertEqual(bridge.pin_count(), 2)
        finally:
            bridge.close()
            store.close()
        # A distinct byte payload under an accepted Message-ID is not a
        # duplicate, even though the host metadata is per-payload.  ACL2's
        # actual immutable-node conflict gate rejects it and BPA stays staged.
        self.stage("bpa-conflict", payload.replace(b"Body once", b"Body changed"))
        conflict = self.invoke("bpa-conflict")
        self.assertEqual(conflict.outcome, "rejected")
        self.assertIn("bpa-conflict", self.inventory)
        store, bridge, records = self.live()
        try:
            self.assertEqual(len(records), 2)
            self.assertEqual(bridge.article_count(), 2)
        finally:
            bridge.close()
            store.close()

    def test_delete_failure_restart_uses_durable_acl2_duplicate_check(self):
        payload = self.adu("restart")
        self.stage("bpa-002", payload)
        with self.assertRaises(run_bp_ingress.BpDeletePending):
            self.invoke("bpa-002", delete=lambda _bid: (_ for _ in ()).throw(OSError("delete lost")))
        # The BPA item and journal file remain; a fresh bridge recovery sees
        # the published Store article before allowing an explicit retry delete.
        self.assertIn("bpa-002", self.inventory)
        first_store, first_bridge, first_records = self.live()
        try:
            self.assertEqual(len(first_records), 1)
            self.assertTrue(first_bridge.lookup_found(b"<restart@bp.example>"))
        finally:
            first_bridge.close()
            first_store.close()
        result = self.invoke("bpa-002")
        self.assertEqual(result.outcome, "duplicate")
        self.assertEqual(self.deleted, ["bpa-002"])
        second_store, second_bridge, second_records = self.live()
        try:
            self.assertEqual(len(second_records), 1)
            self.assertEqual(second_bridge.article_count(), 1)
        finally:
            second_bridge.close()
            second_store.close()

    def test_malformed_or_unknown_group_stays_staged_and_unaccepted(self):
        self.stage("bpa-bad", b"not an article")
        rejected = self.invoke("bpa-bad")
        self.assertEqual(rejected.outcome, "rejected")
        self.assertIn("bpa-bad", self.inventory)
        self.stage("bpa-group", self.adu("group", b"fn.unknown"))
        rejected_group = self.invoke("bpa-group")
        self.assertEqual(rejected_group.outcome, "rejected")
        self.assertIn("bpa-group", self.inventory)
        store, bridge, records = self.live()
        try:
            self.assertEqual(records, [])
            self.assertEqual(bridge.article_count(), 0)
        finally:
            bridge.close()
            store.close()

    def test_nonempty_workflow_namespace_is_refused_without_replay_bridge(self):
        workflow = run_bp_ingress.load_workflow_journal(WORKFLOW_JOURNAL)
        journal = workflow.WorkflowJournal(self.journal_root, lambda records: records)
        journal.open()
        try:
            journal.publish("config", {
                "local-eid": "dtn://fn.lab/inbox", "peer-eid": "dtn://peer.lab",
                "policy-id": "bp-lab-policy-v0", "receipt-authority": "dtn://fn.lab/issuer",
                "bp-lifetime": 3600, "incarnation": "bp-lab-incarnation-v0",
                "authorization-context": "bp-lab-authz-v0",
            })
        finally:
            journal.close()
        self.stage("bpa-workflow", self.adu("workflow"))
        with self.assertRaises(workflow.JournalFault):
            self.invoke("bpa-workflow")
        self.assertIn("bpa-workflow", self.inventory)
        store, bridge, records = self.live()
        try:
            self.assertEqual(records, [])
            self.assertEqual(bridge.article_count(), 0)
        finally:
            bridge.close()
            store.close()


if __name__ == "__main__":
    unittest.main()
