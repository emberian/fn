"""D34 natively: `store export` / `store import` and the one store format.

books/store-export.lisp decides (fn-sxp-entries, fn-sxp-manifest,
fn-sxp-import-plan); host/native/io.lisp fnn-command-store-export and
fnn-command-store-import read and write.  On the image under test:

* a store with articles served by the owner is exported (the owner stopped),
  a fresh node imports the archive, and the two stores' `status` and
  `store inspect` observations are equal, article for article;
* the import refuses by name, exit 1, writing no store: a MANIFEST with one
  octet changed (manifest-mismatch NAME), an existing store (store-exists)
  and a raised field that breaks a relation (profile REASON); a raised field
  that keeps the relations is imported and reported by `status`;
* a format-7 store (the fixture FN_FORMAT7_STORE, a copy of a pre-D34
  store; never /tank/fn/node) is refused at open by name: `open refused
  reason=store-format`, exit 1, its files unchanged.

TODO (continuation, SCN-133): the brief's 300-article store with a signed
composite, a cancel, a retention event and a consumer registration; this
module drives articles only.  Run on hbox with FN_NATIVE_HOST naming the
image under test.
"""
import hashlib
import os
from pathlib import Path
import shutil
import unittest

from tests import test_native_operator_verbs as verbs
from tests.native_profile_fixture import ProfileFixture, ProfileLineMixin

EXIT_OK, EXIT_REFUSED = verbs.EXIT_OK, verbs.EXIT_REFUSED
FORMAT7_STORE = Path(os.environ["FN_FORMAT7_STORE"]) if os.environ.get("FN_FORMAT7_STORE") else None
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
        # The MANIFEST is sha256sum's: every line names a file of the archive.
        for line in (archive / "MANIFEST").read_text(encoding="ascii").splitlines():
            digest, name = line.split("  ", 1)
            self.assertEqual(hashlib.sha256((archive / name).read_bytes()).hexdigest(), digest)

        store2 = self.root / "store2"
        config2 = self.second_config(store2)
        imported = self.operator_with(config2, "store", "import", str(archive))
        self.assertEqual(imported.returncode, EXIT_OK, imported.stderr.decode())
        self.assertEqual(sorted(p.name for p in (store2 / "transactions").iterdir()),
                         sorted(p.name for p in (self.store / "transactions").iterdir()
                                if p.is_file()))
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

    @unittest.skipUnless(FORMAT7_STORE, "FN_FORMAT7_STORE names the format-7 fixture store")
    def test_a_format_7_store_is_refused_by_name(self):
        shutil.copytree(FORMAT7_STORE, self.store, symlinks=True)
        before = tree(self.store)
        for words in (("status",), ("recover",)):
            got = self.op(*words)
            self.assertEqual(got.returncode, EXIT_REFUSED, got.stderr.decode())
            self.assertIn(b"open refused reason=store-format: reinstall from the release and import",
                          got.stderr + got.stdout)
        self.assertEqual(tree(self.store), before)


if __name__ == "__main__":
    unittest.main()
