"""Live checks that a durable provenance survives the store, not only ACL2.

`tests/acl2/provenance-tests.lisp` proves the codec on values.  These checks
drive the real store and the interpreted ACL2 host, so what they establish is
narrower and different: that the value ACL2 decides for a local acceptance is
the value that reaches the journal record, that reopening the store (which
replays that journal into a fresh node) recovers the same typed provenance,
and that an evidence value written before the typed record existed still
reads back as itself.

They do NOT establish anything about the transit path's durable provenance:
`fn-peer-injection-arguments` still passes `fn-peer-evidence`'s rendering, an
open item recorded in planning/lanes/HANDOFF-w10-provenance.md.
"""
import contextlib
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
import run_store  # noqa: E402


class ProvenanceTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="fn-prov-")
        self.root = Path(self.temporary.name) / "store"
        run_store.Store(self.root, writable=True).initialize()

    def tearDown(self):
        self.temporary.cleanup()

    def post(self, msgid, payload):
        payload_path = Path(self.temporary.name) / "payload"
        payload_path.write_bytes(payload)
        return run_store.command_post(SimpleNamespace(
            store=self.root, message_id=msgid, payload=payload_path,
            group=["fn.letters"], charge=None, inject_fault=None))

    @contextlib.contextmanager
    def live(self):
        store, bridge, records = run_store.open_live_store(self.root, writable=False)
        try:
            yield store, bridge, records
        finally:
            bridge.close()
            store.close()

    def test_acl2_decides_the_post_provenance_and_it_is_typed(self):
        """The host no longer types b"unsigned-legacy-v0": ACL2 answers."""
        with self.live() as (unused_store, bridge, unused_records):
            evidence = bridge.prov_post()
            # Not the old constant, and not a rendering: the canonical wire
            # form, which is prefixed and printable so that the host boundary
            # guard `fn-store-text-octetsp' (octets 33 to 126) admits it.
            self.assertNotEqual(evidence, b"unsigned-legacy-v0")
            self.assertTrue(evidence.startswith(b"fnprov1:"), evidence)
            self.assertTrue(all(33 <= byte <= 126 for byte in evidence), evidence)
            self.assertLessEqual(len(evidence), 256)
            described = bridge.prov_describe(evidence)
            self.assertTrue(described.startswith(b"post principal="),
                            described)
            self.assertIn(b"generation=", described)

    def test_the_provenance_a_post_stored_survives_reopening(self):
        """Reopening replays the journal into a fresh node; the typed
        provenance the acceptance recorded comes back with it."""
        msgid = b"<prov-1@example.invalid>"
        self.assertEqual(self.post(msgid.decode("ascii"), b"first"), 0)
        with self.live() as (unused_store, bridge, records):
            self.assertEqual(len(records), 1)
            first = bridge.prov_for_msgid(msgid)
        self.assertTrue(first.startswith(b"post principal="), first)

        # A second open is a second replay from the same journal bytes.
        with self.live() as (unused_store, bridge, unused_records):
            second = bridge.prov_for_msgid(msgid)
        self.assertEqual(first, second)

    def test_a_legacy_evidence_value_still_reads_back_as_itself(self):
        """K-PROV-2 on the live host: a store written before this lane holds
        strings, and they decode as the `:legacy` kind, verbatim."""
        with self.live() as (unused_store, bridge, unused_records):
            self.assertEqual(bridge.prov_describe(b"peer-transit:innA"),
                             b"legacy peer-transit:innA")
            self.assertEqual(bridge.prov_describe(b"unsigned-legacy-v0"),
                             b"legacy unsigned-legacy-v0")

    def test_inspect_provenance_prints_the_acl2_line(self):
        msgid = "<prov-2@example.invalid>"
        self.assertEqual(self.post(msgid, b"second"), 0)
        code = run_store.command_inspect(SimpleNamespace(
            store=self.root, message_id=msgid, provenance=True))
        self.assertEqual(code, run_store.EXIT_OK)
        # Absence stays a clean refusal, distinct from a fault.
        code = run_store.command_inspect(SimpleNamespace(
            store=self.root, message_id="<absent@example.invalid>",
            provenance=True))
        self.assertEqual(code, run_store.EXIT_REFUSED)


if __name__ == "__main__":
    unittest.main()
