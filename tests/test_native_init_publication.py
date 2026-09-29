"""`operator CONFIG init`'s publication, natively (PKT-647,
books/store-init-publication.lisp).

host/native/io.lisp `fnn-command-init-published` builds the empty store in
ROOT.init-XXXX beside ROOT and publishes it through `fnn-staged-publication`,
the import's program (fn-bs-imp-program) with init's cut names
(books/store-init-log-publication.lisp fn-bs-init-log-program).  Before writing anything it observes a leftover
ROOT.init-* and ROOT, and ACL2 (fn-bs-init-pub-admission over
fn-bs-imp-classify) proceeds or refuses by name, saying what to run.

What this module checks:

* source: the host's init cuts are the import program's renamed by the book's
  table, the candidate column is the import's, the host asks ACL2's
  admission before publishing and `operator init` runs this path
  (native_cuts.verify_init_publication_cut_map);
* on the production image: init publishes and leaves no ROOT.init-*; an empty
  ROOT.init-deadbeef0000 beside an absent ROOT is refused (exit 1,
  reason=interrupted-init, naming it) and ROOT stays absent; the same name
  beside the initialized ROOT is refused (reason=publication-uncertain); an
  empty directory at ROOT is refused (reason=store-path-exists) and stays
  empty;
* on the developer image, at every cut of native_cuts.INIT_PUB_CUTS, SIGKILL
  and EIO (FN_NATIVE_INIT_FAULT=CUT:ACTION, the cut's first occurrence):
  SIGKILL ends the process; EIO exits 1 before the rename and 3 at or after
  it.  Afterwards ROOT is present exactly when the candidate allows it, and a
  present ROOT is the complete empty store (`status` exit 0,
  transactions=0) that a second init refuses (STORE-EXISTS); an absent ROOT
  leaves one staged directory, which the next init names
  (reason=interrupted-init), after whose removal init succeeds;
* two init processes of one image killed at the same cut leave stages with
  different suffixes (PKT-819: the random state is seeded per process).

Not checked here: power loss (lane power-loss's campaign carries these cut
names), and the non-Linux ROOT.lock path (OpenBSD evidence is scoped
separately).  Runs on hbox with FN_NATIVE_HOST and FN_NATIVE_DEVELOPER_HOST.
"""
import shutil
import signal
import unittest

from tests.campaign import native_cuts
from tests.native_harness import (
    EXIT_OK, EXIT_REFUSED, EXIT_UNCERTAIN, ROOT, native_image)
from tests.native_profile_fixture import ProfileFixture

IMAGE = native_image("FN_NATIVE_HOST")
DEVELOPER = native_image("FN_NATIVE_DEVELOPER_HOST")
LEFTOVER = "store.init-deadbeef0000"


class InitPublicationSourceTests(unittest.TestCase):
    def test_operator_init_runs_the_publication_program(self):
        native_cuts.verify_init_publication_cut_map()
        self.assertIn("FN_NATIVE_INIT_FAULT", native_cuts.developer_selectors())
        for build in ("build.lisp", "build-dtn.lisp", "build-store-test.lisp"):
            text = (ROOT / "host" / "native" / build).read_text(encoding="ascii")
            self.assertIn('(include-book "books/store-init-publication")', text, build)


class InitFixture(ProfileFixture):
    def stages(self):
        return sorted(p for p in self.root.iterdir() if p.name.startswith("store.init-"))

    def init_words(self, env=None):
        return self.op("init", "--profile", "development", "fn.test", env=env)

    def assert_empty_store(self):
        status = self.op("status", "--replay")
        self.assertEqual(status.returncode, EXIT_OK, status.stderr.decode())
        self.assertIn(b"transactions=0", status.stdout)
        segment = self.store / "journal" / "000001.log"
        if segment.exists():
            # The record log (books/store-init-log-publication.lisp): the segment is
            # the plan's third file, its ACL2 extent of zeros; no allocator
            # file and no transactions/ are written.
            data = segment.read_bytes()
            self.assertEqual(len(data), 1048576)
            self.assertEqual(data.count(0), len(data))
            self.assertFalse((self.store / "transactions").exists())
            self.assertFalse((self.store / "allocation-frontier.json").exists())
        else:
            self.assertEqual(sorted(p.name for p in (self.store / "transactions").iterdir()), [])


class InitPublicationTests(InitFixture):
    image = IMAGE

    def test_publication_and_the_three_refusals(self):
        leftover = self.root / LEFTOVER
        leftover.mkdir()
        refused = self.init_words()
        text = (refused.stdout + refused.stderr).decode()
        self.assertEqual(refused.returncode, EXIT_REFUSED, text)
        self.assertIn("init refused reason=interrupted-init stage={}".format(leftover), text)
        self.assertFalse(self.store.exists())
        # PKT-781 (1), PRF-971: the other store actions name the stage too
        # (fn-nsst-store-outcome), never NO-STORE's "run init", which init
        # itself refuses while the stage remains.
        for verb in ("status", "recover"):
            answer = self.op(verb)
            text = (answer.stdout + answer.stderr).decode()
            self.assertEqual(answer.returncode, EXIT_REFUSED, text)
            self.assertIn("INTERRUPTED-INIT", text.upper(), text)
            self.assertNotIn("NO-STORE", text.upper(), text)
            self.assertIn("its stage {} remains".format(leftover), text)
            self.assertFalse(self.store.exists())
        leftover.rmdir()
        bare = self.op("status")
        self.assertEqual(bare.returncode, EXIT_REFUSED, bare.stderr.decode())
        self.assertIn("NO-STORE", (bare.stdout + bare.stderr).decode().upper())

        created = self.init_words()
        self.assertEqual(created.returncode, EXIT_OK, created.stderr.decode())
        self.assertIn(b"initialized", created.stdout)
        self.assertEqual(self.stages(), [])
        self.assert_empty_store()

        leftover.mkdir()
        refused = self.init_words()
        text = (refused.stdout + refused.stderr).decode()
        self.assertEqual(refused.returncode, EXIT_REFUSED, text)
        # The store's own markers answer first (fn-native-operator-init-outcome).
        self.assertIn("STORE-EXISTS", text.upper())
        leftover.rmdir()

        shutil.rmtree(self.store)
        leftover.mkdir()
        self.store.mkdir()
        refused = self.init_words()
        text = (refused.stdout + refused.stderr).decode()
        self.assertEqual(refused.returncode, EXIT_REFUSED, text)
        self.assertIn("init refused reason=publication-uncertain stage={}".format(leftover), text)
        leftover.rmdir()

        refused = self.init_words()
        text = (refused.stdout + refused.stderr).decode()
        self.assertEqual(refused.returncode, EXIT_REFUSED, text)
        self.assertIn("init refused reason=store-path-exists", text)
        self.assertEqual(list(self.store.iterdir()), [])
        self.assertEqual(self.stages(), [])


class InitCutTests(InitFixture):
    """Every INIT_PUB_CUTS cut, SIGKILL and EIO, on the developer image."""
    image = DEVELOPER

    def run_cut(self, cut, action):
        env = {"FN_NATIVE_INIT_FAULT": "{}:{}".format(cut.name, action)}
        died = self.init_words(env=env)
        text = (died.stdout + died.stderr).decode()
        if action == "kill":
            self.assertEqual(died.returncode, -signal.SIGKILL, text)
        elif cut.candidate == "absent":
            self.assertEqual(died.returncode, EXIT_REFUSED, text)
            self.assertIn("init failed before publication", text)
        else:
            self.assertEqual(died.returncode, EXIT_UNCERTAIN, text)
            self.assertIn("init publication uncertain state=store-present", text)
        stages = self.stages()
        if self.store.exists():
            self.assertIn(cut.candidate, ("either", "present"))
            self.assertEqual(stages, [])
            self.assert_empty_store()
            again = self.init_words()
            self.assertEqual(again.returncode, EXIT_REFUSED, again.stderr.decode())
            self.assertIn(b"STORE-EXISTS", (again.stdout + again.stderr).upper())
            return "present"
        self.assertEqual(cut.candidate, "absent")
        self.assertEqual(len(stages), 1, stages)
        if action == "eio":
            self.assertIn(str(stages[0]), text)
        retried = self.init_words()
        text = (retried.stdout + retried.stderr).decode()
        self.assertEqual(retried.returncode, EXIT_REFUSED, text)
        self.assertIn("init refused reason=interrupted-init stage={}".format(stages[0]), text)
        self.assertFalse(self.store.exists())
        shutil.rmtree(stages[0])
        retried = self.init_words()
        self.assertEqual(retried.returncode, EXIT_OK, retried.stderr.decode())
        self.assertEqual(self.stages(), [])
        self.assert_empty_store()
        return "absent"

    def test_two_inits_stage_under_different_names(self):
        """PKT-819: the stage suffix is drawn from a state each process seeds
        from the OS's entropy, not one the image carried from its build: two
        init processes killed at the same cut leave differently named
        stages."""
        cut = next(c for c in native_cuts.INIT_PUB_CUTS if c.candidate == "absent")
        env = {"FN_NATIVE_INIT_FAULT": "{}:kill".format(cut.name)}
        names = []
        for _ in range(2):
            died = self.init_words(env=env)
            self.assertEqual(died.returncode, -signal.SIGKILL, (died.stdout + died.stderr).decode())
            stages = self.stages()
            self.assertEqual(len(stages), 1, stages)
            names.append(stages[0].name)
            shutil.rmtree(stages[0])
        self.assertFalse(self.store.exists())
        self.assertNotEqual(names[0], names[1], names)
        print("init stages:", names)

    def test_every_cut_leaves_no_store_or_the_complete_empty_store(self):
        seen = {}
        for cut in native_cuts.INIT_PUB_CUTS:
            for action in ("kill", "eio"):
                with self.subTest(cut=cut.name, action=action):
                    if self.store.exists():
                        shutil.rmtree(self.store)
                    for stage in self.stages():
                        shutil.rmtree(stage)
                    seen[(cut.name, action)] = self.run_cut(cut, action)
        print("init cuts:", sorted(seen.items()))


if __name__ == "__main__":
    unittest.main()
