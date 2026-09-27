"""D34 natively: `store export` / `store import` and the one store format.

books/store-export.lisp decides (fn-sxp-entries, fn-sxp-manifest,
fn-sxp-import-plan); host/native/io.lisp fnn-command-store-export and
fnn-command-store-import read and write.  On the image under test:

* a store with articles served by the owner is exported (the owner stopped),
  a fresh node imports the archive, and the two stores' `status` and
  `store inspect` observations are equal, article for article;
* the imported store holds the history in the record log (format 9) and
  exports to the same archive, file for file; a process death at the
  import's log cuts (FN_NATIVE_LOG_FAULT=log-written|log-fenced) publishes
  no store;
* the import refuses by name, exit 1, writing no store: a MANIFEST with one
  octet changed (manifest-mismatch NAME), an existing store (store-exists)
  and a raised field that breaks a relation (profile REASON); a raised field
  that keeps the relations is imported and reported by `status`;
* a store made by another release (synthesized by
  tests/older_release_store.py: a format-7 frame, a format-8 frame (the
  per-file layout before the record log), and the thirteen-field
  layout of every store made before batch AS) is refused at open by name:
  `open refused reason=store-format` and `open refused
  reason=older-release`, exit 1, its files unchanged (PKT-695: no fixture
  store is kept for it).

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
from tests import older_release_store as older

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
        # The MANIFEST is sha256sum's: every line names a file of the archive.
        for line in (archive / "MANIFEST").read_text(encoding="ascii").splitlines():
            digest, name = line.split("  ", 1)
            self.assertEqual(hashlib.sha256((archive / name).read_bytes()).hexdigest(), digest)

        store2 = self.root / "store2"
        config2 = self.second_config(store2)
        imported = self.operator_with(config2, "store", "import", str(archive))
        self.assertEqual(imported.returncode, EXIT_OK, imported.stderr.decode())
        # Format 9: the imported history is in the record log (journal/),
        # never in transaction files, and exporting it again gives the same
        # archive, file for file: the same profile, frontier, configuration
        # records and records (PRF-205 over the log).
        self.assertTrue((store2 / "journal" / "000001.log").is_file())
        self.assertEqual([p for p in (store2 / "transactions").iterdir() if p.is_file()], [])
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
        strip = lambda out: [l for l in out.decode().splitlines() if str(self.root) not in l]
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

    def refused_by_name(self, kind):
        made, config, _ = older.make_store(kind, self.image, self.root / "older",
                                           verbs.environment())
        before = tree(made)
        for head in (["operator", str(config), "status"], ["store", str(made), "recover"]):
            got = subprocess.run([str(self.image), "--fn", *head], cwd=verbs.ROOT,
                                 env=verbs.environment(), stdout=subprocess.PIPE,
                                 stderr=subprocess.PIPE, timeout=180, check=False)
            self.assertEqual(got.returncode, EXIT_REFUSED, got.stderr.decode())
            self.assertIn(older.LINES[kind].encode("ascii"), got.stderr + got.stdout)
        self.assertEqual(tree(made), before)

    def test_a_format_7_store_is_refused_by_name(self):
        self.refused_by_name("format-7")

    def test_a_store_of_the_older_layout_is_refused_by_name(self):
        self.refused_by_name("older-release")

    def test_a_format_8_store_is_refused_by_name(self):
        # The per-file layout (fn-store-8) opens on no image: D34's one
        # format is the record log's (fn-spo-open-of-a-format-8-profile-
        # refuses-by-name).
        self.refused_by_name("format-8")


if __name__ == "__main__":
    unittest.main()
