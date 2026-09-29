"""`checkpoint clone' and `operator CONFIG store compact' over the record log
(format 9); "the history" a case keeps is the `store export' archive of it
(transaction_bytes).

The generation checkpoints (`checkpoint publish [select]', `checkpoint
select', `checkpoint status', and the open's restore of a selected
generation) are retired (lane matrix-reds, 2026-09-27): their frame is the
node of books/checkpoint.lisp fn-checkpoint-capture, which since the records
flip holds arena handles the frame does not resolve, so every capture of a
store holding an article was refused.  The verbs now refuse by name
(test_retired_generation_verbs_refuse_by_name).  The record log's checkpoint is
the state checkpoint (fn-bs-scp-program with the arena run, lane
checkpoint-arena), covered by tests.test_native_state_checkpoint (the open
equals the full replay, a corrupt or arena-less file falls back to the
replay, every cut of its program), tests.test_native_checkpoint_auto (the
owner's publication, a kill between batches) and
tests.test_native_log_compaction (the rotation and the drop, their cuts).
Deleted here with them: test_selected_corruption_is_reported_without_rollback_
or_lost_replay, test_corrupt_unselected_generation_is_invisible,
test_acl2_namespace_codec_rejects_alias_overflow_and_excess,
test_differential_mismatch_is_always_corruption,
test_known_and_ambiguous_failures_keep_distinct_exit_codes,
test_process_death_at_every_native_checkpoint_cut_reopens,
test_process_death_at_every_selection_cut_preserves_event_bytes, and the
module tests.test_native_checkpoint_generations (PRF-171's generation arm).

Retired earlier with the per-file layout and the pack chain (design
2026-09-27 storage-log section 9 row 5; lane log-recovery-2 deleted the
`checkpoint pack*' verbs):
* test_native_and_python_frames_cross_open_byte_identically -- the Python
  store (tools/run_store.py, tools/checkpoint.py) reads only the per-file
  layout; it has no record-log reader;
* test_selected_lossless_pack_splices_before_generic_replay -- packs;
* test_retiring_old_pack_generations_keeps_exact_retained_sources -- pack-retire;
* test_pack_generation_retirement_death_reopens_and_retries -- pack-retire cuts;
* test_selected_pack_missing_or_corrupt_fails_closed -- a selected pack (the
  log's refusals by name are tests.test_native_log_compaction's);
* test_surviving_covered_transaction_conflict_fails_closed -- transaction files
  under a pack;
* test_selected_pack_reclaims_physical_prefix_and_replays_suffix,
  test_pack_prefix_reclaim_process_death_recovers_from_selected_pack,
  test_partial_multi_file_prefix_reclaim_resumes_from_selected_pack,
  test_death_after_each_covered_unlink_preserves_exact_suffix_and_resumes,
  test_missing_retained_suffix_gap_fails_closed_without_reclamation,
  test_arbitrary_covered_deletion_image_recovers_and_resumes,
  test_reclaim_keeps_served_view_watermarks_and_next_number,
  test_reclaim_cuts_keep_served_view_and_next_number -- pack-reclaim of the
  covered transaction files (the log's drop and its cuts:
  tests.test_native_log_compaction);
* test_active_reader_blocks_pack_reclaim_and_reopen_keeps_archive_pin -- the
  reader's pin on a pack generation.
* test_fenced_clone_rollover_after_selected_pack_reclaim -- a clone of a
  pack-reclaimed store compared pack files (lane log-recovery-2 deleted it
  with the pack verbs); the clone over a compacted log is
  test_clone_reopens_historical_authorship_verdict (opt-in
  FN_RUN_NATIVE_CLONE), which compacts the source twice before the clone.
"""

import os
import shutil
import subprocess
import sys
import unittest

from tests.native_harness import (
    EXIT_OK, EXIT_REFUSED, Client, Node, assert_outcome, environment, executable,
    native_image, requires, run, scratch)


IMAGE = native_image("FN_NATIVE_DEVELOPER_HOST")
PRODUCTION_IMAGE = native_image("FN_NATIVE_HOST")


@unittest.skipUnless(executable(IMAGE),
                     "build/fn-host-developer is required for raw Store fixtures")
class NativeCheckpointTests(unittest.TestCase):
    image = IMAGE

    def setUp(self):
        self.base = scratch(self, "fn-native-checkpoint-")
        self.payload = self.base / "payload"
        self.payload.write_bytes(b"native checkpoint payload\r\n")
        # The whole environment a verb gets (a caller passes a variant of it).
        self.env = environment()
        self.nodes = {}

    def native(self, *args, expected=0, env=None):
        """`IMAGE --fn ARGS...`, asserted to exit EXPECTED; text streams."""
        result = run([self.image, "--fn", *args], env=env or self.env,
                     timeout=getattr(self, "native_timeout", 30))
        assert_outcome(self, result, expected)
        return subprocess.CompletedProcess(
            result.args, result.returncode, result.stdout.decode("utf-8", "replace"),
            result.stderr.decode("utf-8", "replace"))

    def initialized(self, name="store", article=True):
        store = self.base / name
        self.native("store", store, "init", "fn.letters")
        if article:
            self.native("store", store, "post", "<checkpoint@example.invalid>",
                        self.payload, "-", "-", "fn.letters")
        return store

    def consumer_history(self, control, name):
        """Commit real owner bootstrap, registration, and zero-position ACK."""
        cursor = self.base / (name + "-register.fncu")
        position = self.base / (name + "-position.fncu")
        self.assertIn("consumer accepted",
                      self.native("consumer", "bootstrap", control).stdout)
        self.assertIn("consumer accepted",
                      self.native("consumer", "register", control, name,
                                  "fn.letters", cursor).stdout)
        self.assertTrue(cursor.read_bytes().startswith(b"fncu\x01"))
        self.assertIn("consumer accepted",
                      self.native("consumer", "position", control, name,
                                  position).stdout)
        self.assertEqual(position.read_bytes(), cursor.read_bytes())
        self.assertIn("consumer accepted",
                      self.native("consumer", "ack", control, cursor).stdout)
        self.assertEqual(position.read_bytes(), cursor.read_bytes())
        return cursor

    @unittest.skipUnless(sys.platform.startswith("linux") and
                         os.environ.get("FN_RUN_NATIVE_CLONE") == "1",
                         "run only against a combined E2/checkpoint developer image")
    def test_clone_refuses_canonical_parent_alias_above_path_bound(self):
        long_parent = (self.base / ("a" * 180) / ("b" * 180) /
                       ("c" * 180))
        long_parent.mkdir(parents=True)
        alias = self.base / "short-parent"
        alias.symlink_to(long_parent, target_is_directory=True)
        source = alias / "source"
        self.native("store", source, "init", "fn.letters")
        target = alias / "target"
        refused = self.native("checkpoint", "clone", source, target,
                              expected=EXIT_REFUSED)
        self.assertIn("clone path", refused.stderr)
        self.assertFalse(target.exists())

    @unittest.skipUnless(sys.platform.startswith("linux") and
                         os.environ.get("FN_RUN_NATIVE_CLONE") == "1",
                         "run only against a combined E2/T10/checkpoint developer image")
    def test_clone_reopens_historical_authorship_verdict(self):
        source = self.initialized("authored-source", article=False)
        config, _port = self.owner_config(source, "author")
        control = self.nodes[config].control
        principal = self.base / "principal.bin"
        ed_public = self.base / "ed-public.bin"
        ed_secret = self.base / "ed-secret.bin"
        ml_private = self.base / "ml-private.pem"
        ml_public = self.base / "ml-public.pem"
        article = self.base / "authored.eml"
        principal.write_bytes(bytes([85]) * 32)
        ed_public.write_bytes(bytes.fromhex(
            "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"))
        ed_secret.write_bytes(bytes.fromhex(
            "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"
            "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"))
        openssl = os.environ.get("FN_TEST_OPENSSL", "openssl")
        subprocess.run([openssl, "genpkey", "-algorithm", "ML-DSA-65",
                        "-out", str(ml_private)], timeout=60, check=True)
        subprocess.run([openssl, "pkey", "-in", str(ml_private), "-pubout",
                        "-out", str(ml_public)], timeout=60, check=True)
        msgid = "<clone-authored@example.invalid>"
        article.write_bytes(
            b"From: author@example.invalid\r\n"
            b"Date: Wed, 23 Sep 2026 12:00:00 +0000\r\n"
            b"Newsgroups: fn.letters\r\n"
            b"Subject: clone historical verdict\r\nMessage-ID: " +
            msgid.encode("ascii") + b"\r\n\r\nexact authored source\r\n")

        owner = self.run_owner(config)
        try:
            self.native("hybrid-enroll", control, "1", principal,
                        ed_public, ml_public)
            signed = self.native("hybrid-sign", principal, ed_public,
                                 ed_secret, ml_public, ml_private, article)
            parts = dict(line.split() for line in signed.stdout.splitlines())
            ed_sig = self.base / "ed.sig"
            ml_sig = self.base / "ml.sig"
            ed_sig.write_bytes(bytes.fromhex(parts["ed25519"]))
            ml_sig.write_bytes(bytes.fromhex(parts["ml-dsa-65"]))
            self.native("hybrid-author", control, "1", article,
                        ed_sig, ml_sig, ml_public)
            wrong_ed = self.base / "wrong-ed-public.bin"
            wrong_ed.write_bytes(bytes([99]) * 32)
            self.native("hybrid-enroll", control, "2", principal,
                        wrong_ed, ml_public)
            self.consumer_history(control, "authored-worker")
        finally:
            self.stop_owner(owner)

        # Compact twice (the log's rotation and the drop of the covered
        # segments; lane log-recovery-2 re-targeted this from the pack
        # chain): the clone must still recover the historical author verdict
        # and exact signed source from the checkpoint and the surviving
        # segment.
        for _ in range(2):
            self.assertIn("compacted steps=checkpoint,drop",
                          self.native("operator", config, "store", "compact").stdout)
        target = self.base / "authored-clone"
        self.native("checkpoint", "clone", source, target)
        self.assertIn("articles=1",
                      self.native("store", target, "recover").stdout)

        target_config, target_port = self.owner_config(target, "clone")
        owner = self.run_owner(target_config)
        try:
            with Client(target_port, timeout=30, greeting=(b"200",)) as client:
                received = client.article(msgid)
                self.assertIsNotNone(received, "cloned ARTICLE was not served")
                self.assertIn(b"FN-Authorship: ", received[:200])
                self.assertTrue(received.endswith(article.read_bytes()))
                carried = self.base / "clone-received.eml"
                carried.write_bytes(received)
                self.native("hybrid-verify-carrier", carried, ml_public)
                self.assertEqual(client.command("HDR :fn-verified {}".format(msgid)),
                                 b"225 headers follow\r\n")
                self.assertEqual(client.line(),
                                 b"0 verified " + b"55" * 32 + b" keyring 1\r\n")
                self.assertEqual(client.line(), b".\r\n")
        finally:
            self.stop_owner(owner)

    def test_retired_generation_verbs_refuse_by_name(self):
        """`checkpoint publish/select/status' refuse by name, naming the state
        checkpoint, and write nothing: no checkpoints directory, the history
        unchanged."""
        store = self.initialized("retired")
        before = self.transaction_bytes(store)
        for args in (("publish", store), ("publish", store, "select"),
                     ("select", store, "0"), ("status", store)):
            with self.subTest(args=args):
                refused = self.native("checkpoint", *args,
                                      expected=EXIT_REFUSED)
                self.assertIn("generation checkpoints are retired on the record log",
                              refused.stderr)
                self.assertIn("store checkpoint", refused.stderr)
        self.assertFalse((store / "checkpoints").exists())
        self.assertEqual(self.transaction_bytes(store), before)
        recovered = self.native("store", store, "recover")
        self.assertIn("recovered transactions=", recovered.stdout)
        self.assertNotIn("checkpoint=", recovered.stdout.splitlines()[0])

    def transaction_bytes(self, store):
        """The committed history the store's open reads (the record
        log), as `store export' writes it: the archive's files and their
        octets.  Equal exactly when no record changed."""
        archive = self.base / "history-archive"
        shutil.rmtree(archive, ignore_errors=True)
        exported = self.native("store", store, "export", archive)
        self.assertIn("exported records=", exported.stdout)
        tree = {str(path.relative_to(archive)): path.read_bytes()
                for path in sorted(archive.rglob("*")) if path.is_file()}
        shutil.rmtree(archive)
        return tree

    def owner_config(self, store, name):
        """A node serving STORE; its fn.toml and listener port."""
        node = Node(self, self.image, root=self.base / (name + "-node"))
        node.store_path = store
        node.write_config()
        self.nodes[node.config] = node
        return node.config, node.port

    def run_owner(self, config):
        # A class that serves a scale store names its startup deadline
        # (served_timeout); 180 s otherwise.
        return self.nodes[config].start(timeout=getattr(self, "served_timeout", 180))

    def stop_owner(self, process):
        status = process.stop(grace=getattr(self, "served_timeout", 60))
        assert_outcome(self, status, EXIT_OK, log=process)

    def operator_post(self, config, msgid, subject):
        article = self.base / ("post-" + subject + ".eml")
        article.write_bytes(
            b"From: author@example.invalid\r\n"
            b"Date: Thu, 24 Sep 2026 12:00:00 +0000\r\n"
            b"Newsgroups: fn.letters\r\n"
            b"Subject: " + subject.encode("ascii") + b"\r\n"
            b"Message-ID: " + msgid.encode("ascii") +
            b"\r\n\r\nbody of " + subject.encode("ascii") + b"\r\n")
        posted = self.native("operator", config, "post", "--message-id", msgid,
                             "--payload", article, "--group", "fn.letters")
        self.assertIn("accepted operator post", posted.stderr)

    def served_view(self, config, port, msgids):
        """GROUP, every ARTICLE by number and by Message-ID, HDR Subject."""
        owner = self.run_owner(config)
        try:
            with Client(port, timeout=getattr(self, "served_timeout", 10),
                        greeting=(b"200",)) as client:

                def block():
                    # The served octets, dot-stuffing kept: the view compares them.
                    lines = []
                    while True:
                        line = client.line()
                        if line == b".\r\n":
                            return b"".join(lines)
                        lines.append(line)

                group = client.command("GROUP fn.letters")
                self.assertTrue(group.startswith(b"211 "), group)
                _, count, low, high = (int(x) for x in group.split()[:4])
                view = {"group": group}
                for number in range(low, high + 1):
                    status = client.command("ARTICLE {}".format(number))
                    self.assertTrue(status.startswith(b"220 "), status)
                    view[number] = (status, block())
                for msgid in msgids:
                    status = client.command("ARTICLE {}".format(msgid))
                    self.assertTrue(status.startswith(b"220 "), status)
                    view[msgid] = (status, block())
                status = client.command("HDR Subject {}-{}".format(low, high))
                self.assertTrue(status.startswith(b"225 "), status)
                view["hdr"] = block()
        finally:
            self.stop_owner(owner)
        return view

    def assert_view_kept_and_next_number(self, store, config, port, msgids,
                                         before, before_retention, name):
        after = self.served_view(config, port, msgids)
        self.assertEqual(after, before)
        self.assertEqual(self.native("store", store, "retention").stdout,
                         before_retention)
        high = int(before["group"].split()[3])
        owner = self.run_owner(config)
        try:
            self.operator_post(config, "<{}-next@example.invalid>".format(name),
                               name + "-next")
        finally:
            self.stop_owner(owner)
        grown = self.served_view(config, port,
                                 msgids + ["<{}-next@example.invalid>".format(name)])
        self.assertEqual(int(grown["group"].split()[3]), high + 1)
        self.assertIn(b"<" + name.encode("ascii") + b"-next@example.invalid>",
                      grown[high + 1][1])
        for key, value in before.items():
            if key not in ("group", "hdr"):
                self.assertEqual(grown[key], value)


@requires(PRODUCTION_IMAGE)
class NativeProductionCompactTests(unittest.TestCase):
    """`operator CONFIG store compact' on the production image (M5).

    The helpers are NativeCheckpointTests', run against the production image;
    no developer selector or developer verb is used here.
    """
    image = PRODUCTION_IMAGE
    setUp = NativeCheckpointTests.setUp
    native = NativeCheckpointTests.native
    owner_config = NativeCheckpointTests.owner_config
    run_owner = NativeCheckpointTests.run_owner
    stop_owner = NativeCheckpointTests.stop_owner
    operator_post = NativeCheckpointTests.operator_post
    served_view = NativeCheckpointTests.served_view
    transaction_bytes = NativeCheckpointTests.transaction_bytes
    assert_view_kept_and_next_number = NativeCheckpointTests.assert_view_kept_and_next_number

    def test_operator_compact_keeps_every_article_and_next_number(self):
        # compaction is the checkpoint with the log rotated and the
        # covered segments dropped (lane log-recovery; T8).  The history the
        # open reads (the export archive) and the served view are unchanged,
        # the next POST takes the next number, a second compaction covers
        # only the new suffix, and a third with nothing new keeps the one
        # segment it has.  A running owner is ASKED (PKT-868, lane
        # operations: host/native/operator.lisp
        # fnn-operator-execute-compaction; books/owner-compact-request.lisp
        # fn-ock-request-word): with nothing new it answers
        # nothing-to-compact by name and nothing changes.  (Until PKT-868 the
        # verb was refused while an owner ran; composed-owner-6 moved that
        # stanza to the end, where the owner's answer is determined.)
        name = "prod-compact"
        store = self.base / name
        config, port = self.owner_config(store, name)
        init = self.native("operator", config, "init", "fn.letters")
        self.assertIn("accepted operator init", init.stderr)
        msgids = ["<{}-{}@example.invalid>".format(name, k) for k in range(5)]
        owner = self.run_owner(config)
        try:
            for k, msgid in enumerate(msgids):
                self.operator_post(config, msgid, "{}-{}".format(name, k))
        finally:
            self.stop_owner(owner)
        # Format 10's genesis (journal/000000.log) is never rotated or
        # dropped: kept, and not listed (test_native_log_compaction.segments).
        def segments():
            self.assertTrue((store / "journal" / "000000.log").is_file())
            return sorted(p.name for p in (store / "journal").iterdir()
                          if p.name != "000000.log")
        history = self.transaction_bytes(store)
        records = sum(1 for n in history if n.startswith("records/"))
        self.assertGreaterEqual(records, 5)
        self.assertEqual(segments(), ["000001.log"])
        before = self.served_view(config, port, msgids)
        before_retention = self.native("store", store, "retention").stdout
        compacted = self.native("operator", config, "store", "compact")
        self.assertIn("compacted steps=checkpoint,drop records={} ".format(records),
                      compacted.stdout)
        self.assertIn("segment=2 dropped=1", compacted.stdout)
        self.assertIn("accepted operator compact", compacted.stderr)
        self.assertEqual(segments(), ["000002.log"])
        self.assertEqual(self.transaction_bytes(store), history)
        self.assert_view_kept_and_next_number(store, config, port, msgids,
                                              before, before_retention, name)
        again = self.native("operator", config, "store", "compact")
        self.assertIn("compacted steps=checkpoint,drop records={} ".format(records + 1),
                      again.stdout)
        self.assertIn("segment=3 dropped=1", again.stdout)
        self.assertEqual(segments(), ["000003.log"])
        grown = self.transaction_bytes(store)
        idle = self.native("operator", config, "store", "compact")
        self.assertIn("accepted operator compact", idle.stderr)
        self.assertEqual(segments(), ["000003.log"])
        self.assertEqual(self.transaction_bytes(store), grown)
        owner = self.run_owner(config)
        try:
            asked = self.native("operator", config, "store", "compact")
            self.assertIn("compaction nothing-to-compact", asked.stdout)
            self.assertIn("accepted operator compact", asked.stderr)
        finally:
            self.stop_owner(owner)
        self.assertEqual(segments(), ["000003.log"])
        self.assertEqual(self.transaction_bytes(store), grown)
        usage = self.native("operator", config, "store", "compact", "now", expected=5)
        self.assertIn("usage operator store", usage.stderr)
        grown_ids = msgids + ["<{}-next@example.invalid>".format(name)]
        view = self.served_view(config, port, grown_ids)
        self.assertEqual(int(view["group"].split()[3]),
                         int(before["group"].split()[3]) + 1)
        for key, value in before.items():
            if key not in ("group", "hdr"):
                self.assertEqual(view[key], value)


if __name__ == "__main__":
    unittest.main()
