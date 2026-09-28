"""D34 natively: `store export` / `store import` and the one store format.

books/store-export.lisp decides (fn-sxp-entries, fn-sxp-manifest,
fn-sxp-import-plan); host/native/io.lisp fnn-command-store-export and
fnn-command-store-import read and write.  On the image under test:

* a store with articles served by the owner is exported (the owner stopped),
  a fresh node imports the archive, and the two stores' `status` and
  `store inspect` observations are equal, article for article;
* the imported store holds the history in the record log and
  exports to the same archive, file for file; a process death at the
  import's log cuts (FN_NATIVE_LOG_FAULT=log-written|log-fenced) publishes
  no store;
* the import refuses by name, exit 1, writing no store: a MANIFEST with one
  octet changed (manifest-mismatch NAME), an existing store (store-exists)
  and a raised field that breaks a relation (profile REASON); a raised field
  that keeps the relations is imported and reported by `status`; a damaged
  archive -- an entry dropped or over its work bound, a torn record, a
  profile that does not decode -- is refused by name, never a fault;
* a store of another format is refused at open by name: that case is
  tests/test_native_foreign_format_open.py's.

TODO (continuation, SCN-133): the brief's 300-article store with a signed
composite, a cancel, a retention event and a consumer registration; this
module drives articles only.  Run on hbox with FN_NATIVE_HOST naming the
image under test.
"""
import hashlib
import os
from pathlib import Path
import shutil
import subprocess
import unittest

from tests import test_native_operator_verbs as verbs
from tests.native_profile_fixture import ProfileFixture, ProfileLineMixin
import sys
sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "tools"))
import blake3_ref  # noqa: E402  fn's digest (books/blake3.lisp), store format 10

EXIT_OK, EXIT_REFUSED = verbs.EXIT_OK, verbs.EXIT_REFUSED
COUNT = int(os.environ.get("FN_EXPORT_ARTICLES", "30"))


def tree(root):
    return {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(Path(root).rglob("*")) if p.is_file() and p.name != "writer.lock"}


class StoreExportTests(ProfileFixture):
    profile_line = ProfileLineMixin.profile_line

    def served_store(self):
        self.init()
        owner = self.start_owner(self.image)
        try:
            ids = ["<sx{}@example.invalid>".format(i) for i in range(COUNT)]
            self.post_many(ids, subject=b"export")
        finally:
            self.stop(owner)
        return ids

    def second_config(self, store):
        config = self.root / "second.toml"
        config.write_text(self.config.read_text(encoding="ascii").replace(
            str(self.store), str(store)), encoding="ascii")
        return config

    def operator_with(self, config, *words):
        saved = self.config
        try:
            self.config = config
            return self.op(*words)
        finally:
            self.config = saved

    def test_export_then_import_serves_the_same_history(self):
        ids = self.served_store()
        archive = self.root / "archive"
        exported = self.op("store", "export", str(archive))
        self.assertEqual(exported.returncode, EXIT_OK, exported.stderr.decode())
        self.assertIn("exported records=".encode(), exported.stdout)
        self.assertTrue((archive / "MANIFEST").is_file())
        # SEC-006: an export is Store history, not a node backup: the key
        # files never leave STORE/keys/.
        secret = (self.store / "keys" / "node-secret.key").read_bytes()
        for path in archive.rglob("*"):
            self.assertNotEqual(path.name, "keys", path)
            if path.is_file():
                self.assertNotIn(secret[-32:], path.read_bytes(), path)
        # The MANIFEST is b3sum's: every line names a file of the archive.
        named = set()
        for line in (archive / "MANIFEST").read_text(encoding="ascii").splitlines():
            digest, name = line.split("  ", 1)
            self.assertEqual(blake3_ref.blake3((archive / name).read_bytes()).hex(), digest)
            named.add(name)
        # PRF-366: the streamed export's staged MANIFEST was renamed onto
        # MANIFEST, and every other file of the archive is a named entry.
        files = {p.relative_to(archive).as_posix() for p in archive.rglob("*") if p.is_file()}
        self.assertEqual(files, named | {"MANIFEST"})

        store2 = self.root / "store2"
        config2 = self.second_config(store2)
        imported = self.operator_with(config2, "store", "import", str(archive))
        self.assertEqual(imported.returncode, EXIT_OK, imported.stderr.decode())
        # the imported history is in the record log (journal/),
        # never in transaction files, and exporting it again gives the same
        # archive, file for file: the same profile, frontier, configuration
        # records and records (PRF-205 over the log).
        self.assertTrue((store2 / "journal" / "000001.log").is_file())
        self.assertFalse((store2 / "transactions").exists())
        self.assertFalse((store2 / "allocation-frontier.json").exists())
        again_archive = self.root / "archive-again"
        reexported = self.operator_with(config2, "store", "export", str(again_archive))
        self.assertEqual(reexported.returncode, EXIT_OK, reexported.stderr.decode())
        self.assertEqual(tree(again_archive), tree(archive))
        for mid in ids:
            a = self.op("store", "inspect", mid)
            b = self.operator_with(config2, "store", "inspect", mid)
            self.assertEqual(a.returncode, EXIT_OK, a.stderr.decode())
            self.assertEqual(a.stdout, b.stdout)
        a, b = self.op("status"), self.operator_with(config2, "status")
        # The heap line is the launcher's figure from the store's size on
        # disk (reservation-after-flip), not the history: the imported log's
        # preallocated extent differs from the served one's.
        strip = lambda out: [l for l in out.decode().splitlines()
                             if str(self.root) not in l and not l.startswith("heap=")]
        self.assertEqual(strip(a.stdout), strip(b.stdout))

        # Refusals by name, exit 1, no store written.
        again = self.operator_with(config2, "store", "import", str(archive))
        self.assertEqual(again.returncode, EXIT_REFUSED)
        self.assertIn(b"import refused reason=store-exists", again.stderr + again.stdout)
        shutil.rmtree(store2)
        bad = self.root / "bad"
        shutil.copytree(archive, bad)
        manifest = bytearray((bad / "MANIFEST").read_bytes())
        manifest[0] = ord("0") if manifest[0] != ord("0") else ord("1")
        (bad / "MANIFEST").write_bytes(bytes(manifest))
        tampered = self.operator_with(config2, "store", "import", str(bad))
        self.assertEqual(tampered.returncode, EXIT_REFUSED)
        self.assertIn(b"import refused reason=manifest-mismatch profile",
                      tampered.stderr + tampered.stdout)
        self.assertFalse(store2.exists())
        broken = self.operator_with(config2, "store", "import", str(archive),
                                    "--max-history-octets", "1000")
        self.assertEqual(broken.returncode, EXIT_REFUSED)
        self.assertIn(b"import refused reason=profile", broken.stderr + broken.stdout)
        self.assertFalse(store2.exists())
        raised = self.operator_with(config2, "store", "import", str(archive),
                                    "--max-transactions", "1000")
        self.assertEqual(raised.returncode, EXIT_OK, raised.stderr.decode())

    def test_a_damaged_archive_is_refused_by_name_never_a_fault(self):
        """Lane fuzz-nntp (planning/evidence/fuzz-nntp-2026-09-27.md): the
        archive is external input.  A dropped entry, an entry over its work
        bound, a torn record and a profile the codec does not decode are
        refusals of that archive by name (exit 1, no store written); before
        the fix they were faults (exit 4): `[Errno 2]', `store file exceeds
        bound' naming a record for a damaged profile, and `ACL2 returned a
        non-natural' for a record that does not decode."""
        self.served_store()
        archive = self.root / "archive"
        exported = self.op("store", "export", str(archive))
        self.assertEqual(exported.returncode, EXIT_OK, exported.stderr.decode())
        store2 = self.root / "store2"
        config2 = self.second_config(store2)
        first = sorted((archive / "records").iterdir())[0].name

        def reseal(root):
            # A MANIFEST that matches the damaged files (b3sum's form),
            # so the refusal is the one after the MANIFEST check.
            lines = []
            for line in (root / "MANIFEST").read_text(encoding="ascii").splitlines():
                name = line.split("  ", 1)[1]
                lines.append("{}  {}".format(
                    blake3_ref.blake3((root / name).read_bytes()).hex(), name))
            (root / "MANIFEST").write_text("\n".join(lines) + "\n", encoding="ascii")

        def torn(root):
            path = root / "records" / first
            path.write_bytes(path.read_bytes()[:10])

        def flipped_profile(root):
            data = bytearray((root / "profile").read_bytes())
            data[len(data) // 2] ^= 1
            (root / "profile").write_bytes(bytes(data))

        cases = [
            ("dropped MANIFEST", lambda r: (r / "MANIFEST").unlink(),
             b"reason=archive-incomplete entry=MANIFEST"),
            ("dropped profile", lambda r: (r / "profile").unlink(),
             b"reason=archive-incomplete entry=profile"),
            ("frontier over its bound", lambda r: (r / "frontier").write_bytes(b"\0" * 5000),
             b"reason=entry-over-bound entry=frontier"),
            ("flipped profile", flipped_profile, b"reason=manifest-mismatch profile"),
            ("torn record", torn, b"reason=manifest-mismatch records/"),
            ("torn record, resealed", lambda r: (torn(r), reseal(r)),
             b"reason=record-out-of-sequence"),
            ("flipped profile, resealed", lambda r: (flipped_profile(r), reseal(r)),
             b"import refused reason="),
        ]
        for label, damage, expected in cases:
            with self.subTest(case=label):
                bad = self.root / "bad"
                shutil.rmtree(bad, ignore_errors=True)
                shutil.copytree(archive, bad)
                damage(bad)
                got = self.operator_with(config2, "store", "import", str(bad))
                self.assertEqual(got.returncode, EXIT_REFUSED, got.stderr.decode())
                self.assertIn(expected, got.stderr + got.stdout)
                self.assertFalse(store2.exists())

    def test_an_import_killed_in_the_log_publishes_no_store(self):
        """The import's log writes (P-BATCH's append and barrier into the
        unpublished stage): a process death at log-written or log-fenced
        leaves ROOT.import-XXXX and no store at ROOT; the next import is
        refused by name (interrupted-import) until the stage is removed, then
        succeeds."""
        if not verbs.executable(verbs.DEVELOPER):
            self.skipTest("the developer image is required (FN_NATIVE_LOG_FAULT)")
        self.served_store()
        archive = self.root / "archive"
        self.assertEqual(self.op("store", "export", str(archive)).returncode, EXIT_OK)
        for cut in ("log-written", "log-fenced"):
            store2 = self.root / ("store-" + cut)
            config2 = self.second_config(store2)
            env = dict(verbs.environment(), FN_NATIVE_LOG_FAULT=cut)
            saved = self.config
            try:
                self.config = config2
                killed = self.operator("store", "import", str(archive),
                                       image=verbs.DEVELOPER, env=env)
            finally:
                self.config = saved
            # SIGKILL at the cut (fnn-log-at), nothing else.
            self.assertEqual(killed.returncode, -9, killed.stderr.decode())
            self.assertFalse(store2.exists(), cut)
            stages = [p for p in store2.parent.iterdir()
                      if p.name.startswith(store2.name + ".import-")]
            self.assertEqual(len(stages), 1, cut)
            refused = self.operator_with(config2, "store", "import", str(archive))
            self.assertEqual(refused.returncode, EXIT_REFUSED)
            self.assertIn(b"import refused reason=interrupted-import",
                          refused.stderr + refused.stdout)
            shutil.rmtree(stages[0])
            done = self.operator_with(config2, "store", "import", str(archive))
            self.assertEqual(done.returncode, EXIT_OK, done.stderr.decode())

    def test_an_export_killed_at_every_cut_is_incomplete_or_complete(self):
        """PRF-370 (books/store-export-durability.lisp): the export's data
        share one sync and the MANIFEST is renamed into place last.  A
        process death at every cut of fn-sxd-program
        (FN_NATIVE_EXPORT_FAULT=CUT:kill, the cut's first occurrence; the
        table is tests/campaign/native_cuts.py EXPORT_CUTS) leaves an archive
        the import refuses by name -- archive-incomplete entry=MANIFEST, exit
        1, no store -- until the MANIFEST is in place, and after that the
        complete archive, which imports.  An OS error at the sync's cut is a
        known failure of the export, and its archive is refused the same way."""
        if not verbs.executable(verbs.DEVELOPER):
            self.skipTest("the developer image is required (FN_NATIVE_EXPORT_FAULT)")
        from tests.campaign import native_cuts
        native_cuts.verify_export_cut_map()
        self.assertIn("FN_NATIVE_EXPORT_FAULT", native_cuts.developer_selectors())
        self.served_store()
        runs = [(cut.name, "kill", cut.candidate) for cut in native_cuts.EXPORT_CUTS]
        runs.append(("export-data-written", "eio", "absent"))
        for name, action, candidate in runs:
            with self.subTest(cut=name, action=action):
                archive = self.root / ("archive-{}-{}".format(name, action))
                env = dict(verbs.environment(),
                           FN_NATIVE_EXPORT_FAULT="{}:{}".format(name, action))
                died = self.operator("store", "export", str(archive),
                                     image=verbs.DEVELOPER, env=env)
                if action == "kill":
                    self.assertEqual(died.returncode, -9, died.stderr.decode())
                else:
                    self.assertNotIn(died.returncode, (EXIT_OK, -9), died.stderr.decode())
                self.assertTrue(archive.is_dir(), name)
                store2 = self.root / ("store-{}-{}".format(name, action))
                config2 = self.second_config(store2)
                got = self.operator_with(config2, "store", "import", str(archive))
                present = (archive / "MANIFEST").exists()
                if candidate == "absent":
                    self.assertFalse(present, name)
                elif candidate == "present":
                    self.assertTrue(present, name)
                if present:
                    self.assertEqual(got.returncode, EXIT_OK, got.stderr.decode())
                    self.assertTrue(store2.exists(), name)
                else:
                    self.assertEqual(got.returncode, EXIT_REFUSED, got.stderr.decode())
                    self.assertIn(b"import refused reason=archive-incomplete entry=MANIFEST",
                                  got.stderr + got.stdout)
                    self.assertFalse(store2.exists(), name)


if __name__ == "__main__":
    unittest.main()
