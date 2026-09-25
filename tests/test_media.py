"""Carried media: the same staging and acceptance path as network receipt.

Every case below checks two things together: the reported outcome, and that a
non-acceptance left the store, the pins and the receipt records exactly as they
were.  There is no partial acceptance to observe: an item is accepted whole
through `receive_bpa_request` or it changes nothing.
"""

import hashlib
import os
from pathlib import Path
import shutil
import sys
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from tools import media, run_bp_ingress, run_store  # noqa: E402

ARTICLE_ONE = (b"Message-ID: <media-one@fn.example>\r\nNewsgroups: fn.letters\r\n"
               b"Subject: Carried on a volume\r\n\r\nthe first carried letter\r\n")
ARTICLE_TWO = (b"Message-ID: <media-two@fn.example>\r\nNewsgroups: fn.letters\r\n"
               b"Subject: Carried beside it\r\n\r\nthe second carried letter\r\n")


def build_request(article, *, incarnation=b"origin-media-1", work_id=b"work-media"):
    """Build one portable fn-bpa request ADU through ACL2, as the lab does."""
    bridge = run_bp_ingress.Acl2BpIngress()
    try:
        bridge.call('(include-book "books/bp-adu")')
        msgid = bridge.extract_message_id(article)
        _archive, subject, _evidence = run_store.metadata(msgid, article)

        def text(value):
            return "(fn-store-octets->string '" + bridge.literal(value) + ")"

        fields = [work_id, subject, b"dtn://media.lab",
                  run_bp_receive_destination(), run_bp_receive_policy(),
                  incarnation, b"wire-auth", b"terms-1"]
        form = ("(fn-bpa-encode (fn-bpa-make-request "
                + " ".join(text(value) for value in fields)
                + " '" + bridge.literal(article) + "))")
        return run_store.acl2_octets(bridge.call(form))
    finally:
        bridge.close()


def build_bundle(bridge, *, sequence, lifetime=10 ** 15):
    """One BPv7 bundle whose primary block ACL2 encodes, as the lab does.

    Nothing here spells a BPv7 field: `fn-bpi-host-bundle-prefix` returns the
    indefinite-array head and the certified primary-block encoding, and the
    break stop code stands in for the blocks the boundary never interprets.
    A media item carries these octets so that the importing node derives the
    carried identity from the bundle rather than from the volume.
    """
    def eid(ssp):
        return "(cons :dtn '" + bridge.literal(ssp) + ")"

    form = ("(fn-bpi-host-bundle-prefix (fn-bpp-make-block 0 0 {} {} {} 1000 {} {} nil nil))"
            .format(eid(b"//fn.lab/inbox"), eid(b"//media.lab/"),
                    eid(b"//fn.lab/report"), sequence, lifetime))
    return run_store.acl2_octets(bridge.call(form)) + b"\xff"


def build_bundles(sequences):
    """Build every carried bundle in one ACL2 session rather than one each."""
    bridge = run_bp_ingress.Acl2BpIngress()
    try:
        return [build_bundle(bridge, sequence=sequence) for sequence in sequences]
    finally:
        bridge.close()


def run_bp_receive_destination():
    from tools import run_bp_receive
    return run_bp_receive.DESTINATION.encode("ascii")


def run_bp_receive_policy():
    from tools import run_bp_receive
    return run_bp_receive.POLICY_ID.encode("ascii")


class MediaManifestTests(unittest.TestCase):
    """Manifest and read-only volume behaviour; no ACL2 and no store."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="fn-media-")
        self.root = Path(self.tmp.name)
        self.exported = media.export_media(
            media_root=self.root / "volume", media_id="volume-1",
            items=[("media:volume-1:one", b"first bundle", b"first bundle octets"),
                   ("media:volume-1:two", b"second bundle bytes",
                    b"second bundle octets!")])

    def tearDown(self):
        self.tmp.cleanup()

    def item_path(self, bid):
        return self.root / "volume" / media.ITEM_DIRECTORY / media.item_file_name(bid)

    def copy(self, name):
        target = self.root / name
        shutil.copytree(self.root / "volume", target)
        for path in target.rglob("*"):
            if path.is_file():
                os.chmod(path, 0o600)
        return target

    def test_manifest_names_identity_size_and_digest_of_every_bundle(self):
        items = media.read_manifest(self.root / "volume")
        self.assertEqual([item.bid for item in items],
                         ["media:volume-1:one", "media:volume-1:two"])
        self.assertEqual([item.octets for item in items], [12, 19])
        self.assertEqual(items[0].sha256, hashlib.sha256(b"first bundle").hexdigest())
        self.assertEqual(items[0].file, media.item_file_name("media:volume-1:one"))

    def test_exported_media_is_written_read_only(self):
        for path in (self.root / "volume").rglob("*"):
            if path.is_file():
                self.assertEqual(os.stat(path).st_mode & 0o222, 0)

    def test_partial_copy_is_absent_from_the_inventory_rather_than_short(self):
        partial = self.copy("partial")
        (partial / media.ITEM_DIRECTORY / media.item_file_name(
            "media:volume-1:two")).write_bytes(b"second")
        volume = media.MediaVolume(partial)
        self.assertEqual(volume.inventory(), ["media:volume-1:one"])
        self.assertFalse(volume.present("media:volume-1:two"))
        with self.assertRaises(media.MediaIncomplete):
            volume.download("media:volume-1:two")

    def test_same_length_damage_is_caught_by_the_copy_digest(self):
        corrupt = self.copy("corrupt")
        (corrupt / media.ITEM_DIRECTORY / media.item_file_name(
            "media:volume-1:two")).write_bytes(b"second bundle bytez")
        volume = media.MediaVolume(corrupt)
        self.assertEqual(volume.inventory(),
                         ["media:volume-1:one", "media:volume-1:two"])
        with self.assertRaises(media.MediaCorrupt):
            volume.download("media:volume-1:two")

    def test_manifest_boundaries_are_refused(self):
        broken = self.copy("broken")
        (broken / media.MANIFEST_NAME).write_text('{"schema": 2, "items": []}')
        with self.assertRaises(media.MediaError):
            media.read_manifest(broken)
        (broken / media.MANIFEST_NAME).write_text(
            '{"schema": 1, "media-id": "v", "items":'
            ' [{"bid": "b", "file": "wrong.bp", "octets": 1, "sha256": "' + "0" * 64 + '"}]}')
        with self.assertRaises(media.MediaError):
            media.read_manifest(broken)

    def test_export_refuses_a_repeated_bundle_identity(self):
        with self.assertRaises(media.MediaError):
            media.export_media(media_root=self.root / "repeat", media_id="v",
                               items=[("media:v:one", b"a", b"A"),
                                      ("media:v:one", b"b", b"B")])


class MediaImportTests(unittest.TestCase):
    """The four carried-media cases against the actual receiver path."""

    @classmethod
    def setUpClass(cls):
        cls.request_one = build_request(ARTICLE_ONE, work_id=b"work-media-one")
        cls.request_two = build_request(ARTICLE_TWO, work_id=b"work-media-two")
        cls.bundle_one, cls.bundle_two = build_bundles([1, 2])

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="fn-media-import-")
        self.root = Path(self.tmp.name)
        self.node = self.root / "node"
        # `run_store.Store._safe_directory` creates the store leaf only, never
        # a parent it did not check; the caller owns the node directory.
        self.node.mkdir(mode=0o700, parents=True, exist_ok=True)
        run_store.Store(self.node / "store", True).initialize()
        self.volume = media.export_media(
            media_root=self.root / "volume", media_id="volume-1",
            items=[("media:volume-1:one", self.request_one, self.bundle_one),
                   ("media:volume-1:two", self.request_two, self.bundle_two)])
        self.before = media.media_digest(self.root / "volume")

    def tearDown(self):
        self.tmp.cleanup()

    def import_all(self, media_root=None, **kwargs):
        return media.import_media(
            media_root=media_root or self.root / "volume",
            store_root=self.node / "store", inbox_root=self.node / "inbox",
            receipt_root=self.node / "receipts", consumed_root=self.node / "consumed",
            source_eid="dtn://carrier.lab", **kwargs)

    def state(self):
        store, bridge, records = run_bp_ingress.open_live_bp_store(self.node / "store", False)
        try:
            return (len(records), bridge.article_count(), bridge.pin_count())
        finally:
            bridge.close()
            store.close()

    def receipts(self):
        root = self.node / "receipts" / "records"
        if not root.is_dir():
            return {}
        return {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(root.iterdir())}

    def copy_volume(self, name):
        target = self.root / name
        shutil.copytree(self.root / "volume", target)
        for path in target.rglob("*"):
            if path.is_file():
                os.chmod(path, 0o600)
        return target

    def test_import_accepts_through_the_receiver_and_leaves_the_media_unchanged(self):
        outcomes = self.import_all()
        self.assertEqual([o.outcome for o in outcomes], ["accepted", "accepted"])
        self.assertTrue(all(o.receipt_sha256 for o in outcomes))
        self.assertEqual(self.state(), (2, 2, 2))
        # The media is read-only: nothing under it changed, and the deletion
        # the BPA path performs became a consumption record beside the journals.
        self.assertEqual(media.media_digest(self.root / "volume"), self.before)
        self.assertEqual(media.consumed_identities(self.node / "consumed"), 2)

    def test_reimport_of_the_same_media_is_a_duplicate_with_the_same_receipt(self):
        first = self.import_all()
        receipts = self.receipts()
        second = self.import_all()
        self.assertEqual([o.outcome for o in second], ["duplicate", "duplicate"])
        self.assertEqual([o.receipt_sha256 for o in second],
                         [o.receipt_sha256 for o in first])
        self.assertEqual(self.receipts(), receipts)
        self.assertEqual(self.state(), (2, 2, 2))
        self.assertEqual(media.media_digest(self.root / "volume"), self.before)

    def test_partial_copy_accepts_the_whole_item_and_refuses_the_truncated_one(self):
        partial = self.copy_volume("partial")
        (partial / media.ITEM_DIRECTORY / media.item_file_name(
            "media:volume-1:two")).write_bytes(self.request_two[:16])
        outcomes = self.import_all(media_root=partial)
        self.assertEqual([o.outcome for o in outcomes], ["accepted", "refused"])
        self.assertEqual(outcomes[1].reason, "media-incomplete")
        self.assertEqual(outcomes[1].receipt_sha256, "")
        # Exactly one acceptance: the truncated item charged nothing at all.
        self.assertEqual(self.state(), (1, 1, 1))

    def test_a_corrupted_file_is_refused_before_anything_is_staged(self):
        corrupt = self.copy_volume("corrupt")
        path = corrupt / media.ITEM_DIRECTORY / media.item_file_name("media:volume-1:one")
        damaged = bytearray(self.request_one)
        damaged[-1] ^= 0xFF
        path.write_bytes(bytes(damaged))
        outcomes = self.import_all(media_root=corrupt)
        self.assertEqual([o.outcome for o in outcomes], ["refused", "accepted"])
        self.assertEqual(outcomes[0].reason, "media-digest")
        self.assertEqual(self.state(), (1, 1, 1))
        self.assertEqual(media.consumed_identities(self.node / "consumed"), 1)
        staged = list((self.node / "inbox" / "inbound").iterdir())
        self.assertEqual(len(staged), 1)

    def test_quota_exhaustion_refuses_without_charging_or_promising(self):
        # A store whose configured transaction bound is already reached: the
        # receiver refuses before any frontier advance, charge or receipt.
        # ACL2's verdict (`fn-sbud-verdict`) refuses the second publication.
        with mock.patch.object(run_store, "publication_admissible",
                               side_effect=[True, False]):
            quota_node = self.root / "quota"
            quota_node.mkdir(mode=0o700, parents=True, exist_ok=True)
            run_store.Store(quota_node / "store", True).initialize()
            outcomes = media.import_media(
                media_root=self.root / "volume", store_root=quota_node / "store",
                inbox_root=quota_node / "inbox", receipt_root=quota_node / "receipts",
                consumed_root=quota_node / "consumed", source_eid="dtn://carrier.lab")
        self.assertEqual([o.outcome for o in outcomes], ["accepted", "refused"])
        self.assertEqual(outcomes[1].reason, "refused-capacity")
        self.assertEqual(outcomes[1].receipt_sha256, "")
        self.assertEqual(media.media_digest(self.root / "volume"), self.before)

    def test_an_uncertain_staging_cut_is_reported_uncertain_not_refused(self):
        cut = run_store.ScriptedFaults("inbound-linked", error=OSError("staging cut"))
        outcomes = media.import_media(
            media_root=self.root / "volume", store_root=self.node / "store",
            inbox_root=self.node / "inbox", receipt_root=self.node / "receipts",
            consumed_root=self.node / "consumed", source_eid="dtn://carrier.lab",
            inbox_faults=cut)
        self.assertEqual(outcomes[0].outcome, "uncertain")
        self.assertEqual(outcomes[0].receipt_sha256, "")
        self.assertNotEqual(outcomes[0].outcome, "refused")
        # Uncertain means exactly that: nothing was accepted, charged or
        # promised, and the media still carries the item for a later attempt.
        self.assertEqual(self.state(), (0, 0, 0))
        self.assertEqual(media.media_digest(self.root / "volume"), self.before)
        self.assertEqual(media.consumed_identities(self.node / "consumed"), 0)

    def test_every_reported_outcome_is_one_of_the_four(self):
        outcomes = self.import_all()
        for outcome in outcomes:
            self.assertIn(outcome.outcome, media.OUTCOMES)
        with self.assertRaises(media.MediaError):
            media.ImportOutcome("b", "maybe", "not a reported outcome")


class MediaCommandLineTests(unittest.TestCase):
    """The three outcomes stay distinct out to the exit code (D13).

    No ACL2 process is started here: `export` and `verify` are copy-integrity
    commands, and the exit-code arithmetic is exercised on outcome values the
    receiver would have produced.  `import`'s own outcomes are the cases in
    `MediaImportTests` above.
    """

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="fn-media-cli-")
        self.root = Path(self.tmp.name)
        self.adu = self.root / "one.bp"
        self.adu.write_bytes(b"carried-adu-one")
        self.bundle = self.root / "one.bundle"
        self.bundle.write_bytes(b"carried-bundle-one")

    def tearDown(self):
        self.tmp.cleanup()

    def export(self, *extra):
        return media.main(["export", "--media", str(self.root / "vol"),
                           "--media-id", "cli-1",
                           "--bundle", "media:cli-1:one={}".format(self.adu),
                           "--bp-bundle", "media:cli-1:one={}".format(self.bundle),
                           *extra])

    def test_export_then_verify_reports_accepted(self):
        self.assertEqual(self.export(), run_store.EXIT_OK)
        self.assertEqual(media.main(["verify", "--media", str(self.root / "vol")]),
                         run_store.EXIT_OK)

    def test_a_second_export_over_a_written_volume_is_refused(self):
        self.assertEqual(self.export(), run_store.EXIT_OK)
        self.assertEqual(self.export(), run_store.EXIT_REFUSED)

    def test_a_damaged_copy_is_refused_by_verify_with_no_store_touched(self):
        self.assertEqual(self.export(), run_store.EXIT_OK)
        item = (self.root / "vol" / media.ITEM_DIRECTORY
                / media.item_file_name("media:cli-1:one"))
        os.chmod(item, 0o600)
        item.write_bytes(b"carried-adu-TWO")
        self.assertEqual(media.main(["verify", "--media", str(self.root / "vol")]),
                         run_store.EXIT_REFUSED)

    def test_a_missing_volume_is_refused_not_a_fault(self):
        self.assertEqual(media.main(["verify", "--media", str(self.root / "absent")]),
                         run_store.EXIT_REFUSED)

    def test_a_bundle_without_an_identity_is_a_usage_error(self):
        self.assertEqual(media.main(["export", "--media", str(self.root / "vol2"),
                                     "--media-id", "cli-2", "--bundle", str(self.adu)]),
                         run_store.EXIT_USAGE)

    def test_an_adu_without_its_bundle_octets_is_a_usage_error(self):
        # Every carried identity needs both files: the importing node reads
        # the identity and expiry out of the bundle, and a volume that carried
        # only the ADU would have the node decide identity locally.
        self.assertEqual(media.main(["export", "--media", str(self.root / "vol3"),
                                     "--media-id", "cli-3", "--bundle",
                                     "media:cli-3:one={}".format(self.adu)]),
                         run_store.EXIT_USAGE)

    def test_uncertain_dominates_refused_in_a_volume_exit_code(self):
        accepted = media.ImportOutcome("a", "accepted", "accepted")
        duplicate = media.ImportOutcome("b", "duplicate", "duplicate")
        refused = media.ImportOutcome("c", "refused", "refused-capacity")
        uncertain = media.ImportOutcome("d", "uncertain", "JournalUncertain")
        self.assertEqual(media.volume_exit_code([accepted, duplicate]),
                         run_store.EXIT_OK)
        self.assertEqual(media.volume_exit_code([accepted, refused]),
                         run_store.EXIT_REFUSED)
        # An uncertain item never reports as a refusal: refusing the volume
        # would assert that nothing landed, which is what the cut does not
        # know.
        self.assertEqual(media.volume_exit_code([refused, uncertain]),
                         run_store.EXIT_UNCERTAIN)
        self.assertEqual(media.volume_exit_code([uncertain, accepted]),
                         run_store.EXIT_UNCERTAIN)


if __name__ == "__main__":
    unittest.main()
