"""`store import DIR`'s publication, natively (books/store-import-publication.lisp).

host/native/io.lisp `fnn-command-store-import` follows fn-bs-imp-program step
for step: it writes the plan's files into a staged directory ROOT.import-XXXX
beside ROOT (each file created exclusively, written, fenced; the
subdirectories and the staged directory fenced), admits it through the
ordinary open, publishes it by a rename that never replaces an existing ROOT
(renameat2 RENAME_NOREPLACE on Linux; lstat then rename(2) elsewhere) and
fences ROOT's parent.  Before writing anything it looks beside ROOT for a
staged directory an earlier import left, and ACL2 (fn-bs-imp-classify)
classifies the two observed presences.

What this module checks:

* source: the host's cuts, rename and fence are fn-bs-imp-program's in its
  order and the candidate column is the program's
  (native_cuts.verify_import_cut_map); the host calls fn-bs-imp-classify;
  FN_NATIVE_IMPORT_FAULT is a registered developer selector; the three
  image builds include the book;
* on the production image: a plain import publishes and leaves no
  ROOT.import-* behind; an empty ROOT.import-deadbeef0000 beside an absent
  ROOT is refused (exit 1, reason=interrupted-import, naming it) and ROOT
  stays absent; the same name beside an imported ROOT is refused
  (reason=publication-uncertain); an unrelated non-empty directory at ROOT is
  refused (reason=store-exists) and its file is untouched;
* on the developer image, at every cut of native_cuts.IMPORT_CUTS, SIGKILL
  and EIO (FN_NATIVE_IMPORT_FAULT=CUT:ACTION, the cut's first occurrence):
  SIGKILL ends the process; EIO exits 1 before the rename (candidate absent)
  and 3 at or after it, naming the classification.  Afterwards ROOT is
  present exactly when the candidate allows it (a death after a completed
  rename leaves ROOT present); a present ROOT opens (`status` exit 0) and
  serves every article's `store inspect` equal to the source store's; a
  retry imports, or refuses naming the leftover stage (interrupted-import),
  after whose removal the retry imports; a present ROOT refuses a retry with
  store-exists.

Not checked here: power loss (the fences are the platform's, not a
qualification), and the non-Linux lstat-then-rename path (OpenBSD evidence
is scoped separately).  Runs on hbox with FN_NATIVE_HOST and
FN_NATIVE_DEVELOPER_HOST naming the images under test.
"""
import os
import shutil
import signal
import unittest

from tests.campaign import native_cuts
from tests.native_harness import (
    EXIT_OK, EXIT_REFUSED, EXIT_UNCERTAIN, ROOT, native_image)
from tests.native_profile_fixture import ProfileFixture

IMAGE = native_image("FN_NATIVE_HOST")
DEVELOPER = native_image("FN_NATIVE_DEVELOPER_HOST")
COUNT = int(os.environ.get("FN_IMPORT_ARTICLES", "5"))
LEFTOVER = "store2.import-deadbeef0000"


class ImportPublicationSourceTests(unittest.TestCase):
    def test_the_host_follows_the_program_and_asks_acl2_to_classify(self):
        native_cuts.verify_import_cut_map()
        io = (ROOT / "host" / "native" / "io.lisp").read_text(encoding="ascii")
        self.assertIn("(fnn-core 'fn-bs-imp-classify",
                      native_cuts.host_function(io, "fnn-import-classify"))
        body = native_cuts.host_function(io, "fnn-command-store-import")
        self.assertIn("(fnn-import-classify leftover root-path)", body)
        self.assertIn("(fnn-import-classify stage-root root-path)",
                      native_cuts.host_function(io, "fnn-staged-publication"))
        self.assertIn("(fnn-import-test-fault)", body)
        self.assertIn("FN_NATIVE_IMPORT_FAULT", native_cuts.developer_selectors())
        for build in ("build.lisp", "build-dtn.lisp", "build-store-test.lisp"):
            text = (ROOT / "host" / "native" / build).read_text(encoding="ascii")
            self.assertIn('(include-book "books/store-import-publication")', text, build)


class ImportFixture(ProfileFixture):
    def served_store(self, count=COUNT):
        self.init()
        self.node.start(image=self.image)
        try:
            ids = ["<ip{}@example.invalid>".format(i) for i in range(count)]
            self.post_many(ids, subject="import")
        finally:
            self.node.stop()
        return ids

    def second_config(self, store):
        config = self.root / "second.toml"
        config.write_text(self.config.read_text(encoding="ascii").replace(
            str(self.store), str(store)), encoding="ascii")
        return config

    def operator_with(self, config, *words, env=None):
        return self.node.invoke("operator", config, *words, image=self.image, env=env)

    def exported(self):
        archive = self.root / "archive"
        got = self.op("store", "export", str(archive))
        self.assertEqual(got.returncode, EXIT_OK, got.stderr.decode())
        return archive

    def stages(self):
        return sorted(p for p in self.root.iterdir() if p.name.startswith("store2.import-"))

    def assert_complete(self, config2, ids):
        status = self.operator_with(config2, "status")
        self.assertEqual(status.returncode, EXIT_OK, status.stderr.decode())
        for mid in ids:
            a = self.op("store", "inspect", mid)
            b = self.operator_with(config2, "store", "inspect", mid)
            self.assertEqual(a.returncode, EXIT_OK, a.stderr.decode())
            self.assertEqual(a.stdout, b.stdout, mid)


class ImportPublicationTests(ImportFixture):
    image = IMAGE

    def test_publication_and_the_three_refusals(self):
        ids = self.served_store()
        archive = self.exported()
        store2 = self.root / "store2"
        config2 = self.second_config(store2)

        # An interrupted import's staged directory beside an absent ROOT.
        leftover = self.root / LEFTOVER
        leftover.mkdir()
        refused = self.operator_with(config2, "store", "import", str(archive))
        text = (refused.stdout + refused.stderr).decode()
        self.assertEqual(refused.returncode, EXIT_REFUSED, text)
        self.assertIn("import refused reason=interrupted-import stage={}".format(leftover), text)
        self.assertFalse(store2.exists())
        self.assertEqual(self.stages(), [leftover])
        leftover.rmdir()

        # A plain import publishes and leaves no staged directory.
        imported = self.operator_with(config2, "store", "import", str(archive))
        self.assertEqual(imported.returncode, EXIT_OK, imported.stderr.decode())
        self.assertEqual(self.stages(), [])
        self.assert_complete(config2, ids)

        # The same name beside a present ROOT: publication uncertain.
        leftover.mkdir()
        refused = self.operator_with(config2, "store", "import", str(archive))
        text = (refused.stdout + refused.stderr).decode()
        self.assertEqual(refused.returncode, EXIT_REFUSED, text)
        self.assertIn("import refused reason=publication-uncertain stage={}".format(leftover), text)
        leftover.rmdir()
        self.assert_complete(config2, ids)

        # An unrelated directory at ROOT is never replaced.
        shutil.rmtree(store2)
        store2.mkdir()
        marker = store2 / "marker"
        marker.write_bytes(b"not a store")
        refused = self.operator_with(config2, "store", "import", str(archive))
        text = (refused.stdout + refused.stderr).decode()
        self.assertEqual(refused.returncode, EXIT_REFUSED, text)
        self.assertIn("import refused reason=store-exists", text)
        self.assertEqual(sorted(p.name for p in store2.iterdir()), ["marker"])
        self.assertEqual(marker.read_bytes(), b"not a store")
        self.assertEqual(self.stages(), [])


class ImportCutTests(ImportFixture):
    """Every IMPORT_CUTS cut, SIGKILL and EIO, on the developer image."""
    image = DEVELOPER

    def run_cut(self, cut, action, archive, config2, ids):
        store2 = self.root / "store2"
        env = {"FN_NATIVE_IMPORT_FAULT": "{}:{}".format(cut.name, action)}
        died = self.operator_with(config2, "store", "import", str(archive), env=env)
        text = (died.stdout + died.stderr).decode()
        if action == "kill":
            self.assertEqual(died.returncode, -signal.SIGKILL, text)
        elif cut.candidate == "absent":
            self.assertEqual(died.returncode, EXIT_REFUSED, text)
            self.assertIn("import failed before publication", text)
        else:
            self.assertEqual(died.returncode, EXIT_UNCERTAIN, text)
            # The rename completed before the cut: ROOT alone is present.
            self.assertIn("import publication uncertain state=store-present", text)
        stages = self.stages()
        if store2.exists():
            self.assertIn(cut.candidate, ("either", "present"))
            self.assertEqual(stages, [])
            self.assert_complete(config2, ids)
            again = self.operator_with(config2, "store", "import", str(archive))
            self.assertEqual(again.returncode, EXIT_REFUSED, again.stderr.decode())
            self.assertIn(b"import refused reason=store-exists", again.stdout + again.stderr)
            return "present"
        # A process death does not undo a completed rename.
        self.assertEqual(cut.candidate, "absent")
        self.assertEqual(len(stages), 1, stages)
        if action == "eio":
            self.assertIn(str(stages[0]), text)
        retried = self.operator_with(config2, "store", "import", str(archive))
        text = (retried.stdout + retried.stderr).decode()
        self.assertEqual(retried.returncode, EXIT_REFUSED, text)
        self.assertIn("import refused reason=interrupted-import stage={}".format(stages[0]), text)
        self.assertFalse(store2.exists())
        shutil.rmtree(stages[0])
        retried = self.operator_with(config2, "store", "import", str(archive))
        self.assertEqual(retried.returncode, EXIT_OK, retried.stderr.decode())
        self.assertEqual(self.stages(), [])
        self.assert_complete(config2, ids)
        return "absent"

    def test_every_cut_leaves_no_store_or_the_complete_store(self):
        ids = self.served_store()
        archive = self.exported()
        store2 = self.root / "store2"
        config2 = self.second_config(store2)
        seen = {}
        for cut in native_cuts.IMPORT_CUTS:
            for action in ("kill", "eio"):
                with self.subTest(cut=cut.name, action=action):
                    if store2.exists():
                        shutil.rmtree(store2)
                    for stage in self.stages():
                        shutil.rmtree(stage)
                    seen[(cut.name, action)] = self.run_cut(cut, action, archive, config2, ids)
        print("import cuts:", sorted(seen.items()))


if __name__ == "__main__":
    unittest.main()
