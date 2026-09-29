"""Current native existing-store recovery observations.

The native recovery host calls the ACL2 store-sweep subject after replay and
the five recovery barriers.  These tests use a saved native image and separate
processes; they do not turn the older Python/native differential finding into
a claim about this source revision.
"""

import re
import unittest

from tests.native_harness import (
    EXIT_FAULT, EXIT_OK, EXIT_REFUSED, EXIT_UNCERTAIN, ROOT, Acl2Session, acl2_keyword,
    acl2_octets, acl2_result, environment, executable, native_image, run, scratch)

IMAGE = native_image("FN_NATIVE_HOST")
# A fault selector is a developer-image selector: a production image refuses
# to start with FN_NATIVE_RECOVERY_FAULT in its environment (exit 5, host/native/io.lisp
# `fnn-developer-selector-gate'), so every faulted step runs this image.
DEVELOPER = native_image("FN_NATIVE_DEVELOPER_HOST")


def missing_enrollment_fixture():
    """The kind-4 record without its kind-3 enrollment, encoded entirely by
    ACL2 (the developer image's own session, `fn acl2 session`)."""
    with Acl2Session(DEVELOPER) as bridge:
        transaction = acl2_octets(bridge.call(
            "(let* ((msgid \"<missing-keyring@example.invalid>\")"
            " (source '(70 114 111 109 58 32 97 64 98 13 10 78 101 119 115 103 114 111 117 112 115 58 32 102 110 46 116 101 115 116 13 10 83 117 98 106 101 99 116 58 32 120 13 10 77 101 115 115 97 103 101 45 73 68 58 32 60 109 105 115 115 105 110 103 45 107 101 121 114 105 110 103 64 101 120 97 109 112 108 101 46 105 110 118 97 108 105 100 62 13 10 13 10 120 13 10))"
            " (profile *fn-hsig-profile-tag*) (subject \"fixture-subject\")"
            " (record (fn-record-make 0 0 0 msgid source '(\"fn.test\")"
            "                         \"fixture-obligation\" subject \"fixture-release\" 2 :legacy))"
            " (verdict (fn-stxe-make 0 0 0 msgid :verified '(1) 7 profile))"
            " (event (fn-stxa-make 0 0 0 7 profile"
            "                       (fn-record-string-octets subject)"
            "                       (fn-record-encode record)"
            "                       (fn-stxe-encode verdict)))"
            # The store's predicates read the HELD history the open interns
            # (records flip: host/store-host.lisp fn-store-intern-records-local,
            # the open's intern into a local arena); the journal stores the
            # wire event.
            " (rows (fn-store-intern-records-local (list event))))"
            " (if (and (fn-stxa-bindsp event)"
            "          (consp rows)"
            "          (fn-sn-observed-historyp 1 rows)"
            "          (fn-sf-history-recoverablep '(\"fn.test\") 32 rows 1)"
            "          (equal (fn-stxk-context-kind (fn-replay-identity rows))"
            "                 :fault))"
            "     (fn-store-event-encode event) nil))"))
    if not transaction:
        raise AssertionError("fixture must pass article replay and fail identity replay")
    return transaction


class NativeRecoverySourceMapTests(unittest.TestCase):
    def test_acquire_checks_staging_and_recovery_calls_the_acl2_sweep_subject(self):
        source = (ROOT / "host" / "native" / "io.lisp").read_text()
        acquire = re.search(r"\(defun fnn-acquire .*?\n\n\(defun fnn-store-close", source, re.S)
        self.assertIsNotNone(acquire)
        self.assertIn("(fnn-safe-directory (fnn-staging store))", acquire.group(0))
        # The open's recovery is the record log's (format 8 is refused at
        # the profile's open; fnn-recover calls fnn-recover-log).
        recover = re.search(r"\(defun fnn-recover-log .*?\n\n\(defun ", source, re.S)
        self.assertIsNotNone(recover)
        self.assertLess(recover.group(0).index("(fnn-sweep-staging store)"),
                        recover.group(0).index("(setf (fnn-store-fenced store) nil)"))
        self.assertIn("(fnn-bridge-sweep-round observed more)", source)
        self.assertIn("fn-store-sn-sweep-round", source)
        sweep = re.search(r"\(defun fnn-sweep-staging .*?\n\n\(defun ", source, re.S)
        self.assertIsNotNone(sweep)
        # The round loop refuses on :refused; it never faults on the bound.
        self.assertIn("(:refused", sweep.group(0))
        self.assertIn("fnn-refuse", sweep.group(0))
        self.assertNotIn("observation bound", sweep.group(0))
        self.assertIn("FN_NATIVE_RECOVERY_FAULT", source)

    def test_every_prefix_the_host_stages_under_is_an_acl2_staging_prefix(self):
        """A stage kind added without a sweep entry would orphan like F2."""
        model = (ROOT / "books" / "store-sweep.lisp").read_text()
        block = model[model.index("(defconst *fn-sn-staging-prefixes*"):]
        block = block[:block.index("\n\n")]
        prefixes = {bytes(int(n) for n in group.split()).decode()
                    for group in re.findall(r"\(([0-9 ]+)\)", block)}
        staged = set()
        for path in sorted((ROOT / "host" / "native").glob("*.lisp")):
            source = path.read_text()
            for match in re.finditer(r"\(fnn-join \(fnn-staging store\)\s*"
                                     r"\(format nil \"(\.[a-z-]+-)~d", source):
                staged.add(match.group(1))
        # Six since the per-file layout's allocator and marker stages went
        # (PKT-838); five since lane matrix-reds retired the generation
        # checkpoints and their .checkpoint- stage (PKT-848).
        self.assertGreaterEqual(len(staged), 5, staged)
        for prefix in staged:
            self.assertTrue(any(prefix.startswith(p) for p in prefixes),
                            "{} is staged but not swept".format(prefix))

    def test_missing_enrollment_fixture_is_acl2_encoded_and_nonempty(self):
        self.assertTrue(missing_enrollment_fixture().startswith(b"\x44fn-e"))


@unittest.skipUnless(executable(DEVELOPER), "the developer image is absent")
class StagingSweepDecisionTests(unittest.TestCase):
    """The ACL2 sweep decision itself, evaluated in the developer image's session."""

    @staticmethod
    def octets(name):
        return "(" + " ".join(str(octet) for octet in name.encode()) + ")"

    def names(self, names):
        return "(list " + " ".join("'" + self.octets(name) for name in names) + ")"

    def test_sweep_rounds_collect_sixty_five_allocation_orphans(self):
        orphans = [".allocation-4242-{:024x}".format(number) for number in range(65)]
        with Acl2Session(DEVELOPER) as bridge:
            ready = "(fn-sn-initial nil 0)"
            rounds = bridge.call("(fn-sn-sweep-rounds {} {} nil (fn-sn-staging-observation-limit))"
                                 .format(ready, self.names(orphans)))
            self.assertEqual(acl2_result(rounds).upper(), b"(:DONE NIL)")
            first = bridge.call("(car (fn-sn-sweep-round {} {} t nil))"
                                .format(ready, self.names(orphans[:64])))
            self.assertEqual(acl2_keyword(first), "again")
            foreign = [".operator-{:02d}".format(number) for number in range(65)]
            refused = bridge.call("(car (fn-sn-sweep-rounds {} {} nil 64))"
                                  .format(ready, self.names(foreign)))
            self.assertEqual(acl2_keyword(refused), "refused")


@unittest.skipUnless(executable(IMAGE),
                     "the developer image {} is absent; build it with "
                     "tools/runbooks/hbox-image-build.sh or set FN_NATIVE_HOST".format(IMAGE))
class NativeRecoveryFidelityTests(unittest.TestCase):
    def setUp(self):
        self.base = scratch(self, "fn-native-recovery-")

    def invoke(self, store, command, recovery_fault=None):
        image = IMAGE
        if recovery_fault is not None:
            if not executable(DEVELOPER):
                self.skipTest(
                    "build/fn-host-developer (or FN_NATIVE_DEVELOPER_HOST) is "
                    "required: FN_NATIVE_RECOVERY_FAULT is a developer-image selector and a "
                    "production image refuses to start with it")
            image = DEVELOPER
        return run([image, "--fn", "store", store, command], timeout=None,
                   env=environment({"FN_NATIVE_RECOVERY_FAULT": recovery_fault}))

    def initialized(self, name):
        store = self.base / name
        result = self.invoke(store, "init")
        self.assertEqual(result.returncode, EXIT_OK, result.stderr)
        return store

    def store_words(self, store, *words):
        return run([IMAGE, "--fn", "store", store, *words], timeout=None)

    def test_missing_staging_is_a_current_native_fault(self):
        store = self.initialized("missing-staging")
        (store / "staging").rmdir()
        result = self.invoke(store, "status")
        self.assertEqual(result.returncode, EXIT_FAULT, result.stderr)
        self.assertIn(b"missing store directory", result.stderr)

    def test_recover_removes_only_acl2_stage_names_and_preserves_unknown_names(self):
        store = self.initialized("policy")
        stage = store / "staging" / ".stage-interrupted"
        unknown = store / "staging" / ".operator-evidence"
        stage.write_bytes(b"staged but uncommitted")
        unknown.write_bytes(b"do not classify in raw Lisp")
        recovered = self.invoke(store, "recover")
        self.assertEqual(recovered.returncode, EXIT_OK, recovered.stderr)
        self.assertFalse(stage.exists())
        self.assertTrue(unknown.exists())
        self.assertIn(b"staging-orphans=1 [.operator-evidence]", recovered.stdout)

    def test_sixty_five_allocation_orphans_are_swept_in_rounds(self):
        """Finding F2 of planning/evidence/campaign-dabebb84-2026-09-22.md.

        65 deaths at frontier-staged-durable leave 65 `.allocation-' files.
        The store is built from files alone: the names are what
        fnn-advance-frontier stages, the content what a staged frontier holds.
        """
        store = self.initialized("allocation-orphans")
        # The store holds no allocator file (the log derives the frontier):
        # the orphans' bytes are what a per-file store's staged frontier held,
        # and the recovery must leave the history (the segment) as it was.
        segment = (store / "journal" / "000001.log").read_bytes()
        for number in range(65):
            (store / "staging" / ".allocation-4242-{:024x}".format(number)).write_bytes(
                b'{"next_txid": 4242}')
        # A reader does not sweep; it reports one bounded observation and
        # says there is more.  It still opens.
        status = self.invoke(store, "status")
        self.assertEqual(status.returncode, EXIT_OK, status.stderr)
        self.assertIn(b"staging-orphans=64+ [", status.stdout)
        self.assertEqual(len(list((store / "staging").iterdir())), 65)
        # The writer's recovery sweeps them all, in two rounds.
        recovered = self.invoke(store, "recover")
        self.assertEqual(recovered.returncode, EXIT_OK, recovered.stderr)
        self.assertIn(b"staging-orphans=0", recovered.stdout)
        self.assertEqual(list((store / "staging").iterdir()), [])
        self.assertEqual((store / "journal" / "000001.log").read_bytes(), segment)
        again = self.invoke(store, "status")
        self.assertEqual(again.returncode, EXIT_OK, again.stderr)
        self.assertIn(b"staging-orphans=0", again.stdout)

    def test_every_host_staging_prefix_is_swept(self):
        store = self.initialized("every-prefix")
        names = [".allocation-1-00", ".init-1-00", ".anchor-1-00", ".checkpoint-1-00",
                 ".selection-1-00", ".pack-1-00", ".pack-selection-1-00", ".stage-1-00"]
        for name in names:
            (store / "staging" / name).write_bytes(b"staged, never committed")
        recovered = self.invoke(store, "recover")
        self.assertEqual(recovered.returncode, EXIT_OK, recovered.stderr)
        self.assertEqual(list((store / "staging").iterdir()), [])

    def test_over_limit_unrecognized_names_refuse_without_removing_them(self):
        store = self.initialized("over-limit")
        for number in range(65):
            (store / "staging" / ".operator-{:02d}".format(number)).write_bytes(b"x")
        result = self.invoke(store, "recover")
        self.assertEqual(result.returncode, EXIT_REFUSED, result.stderr)
        self.assertIn(b"staging namespace holds more than 64 names recovery may not remove",
                      result.stderr)
        self.assertEqual(len(list((store / "staging").iterdir())), 65)

    def test_orphans_beyond_one_observation_go_with_foreign_names_kept(self):
        store = self.initialized("mixed")
        for number in range(100):
            (store / "staging" / ".allocation-7-{:04d}".format(number)).write_bytes(b"x")
        for number in range(10):
            (store / "staging" / ".operator-{:02d}".format(number)).write_bytes(b"x")
        result = self.invoke(store, "recover")
        self.assertEqual(result.returncode, EXIT_OK, result.stderr)
        self.assertEqual(sorted(path.name for path in (store / "staging").iterdir()),
                         [".operator-{:02d}".format(number) for number in range(10)])
        self.assertIn(b"staging-orphans=10 [", result.stdout)

    def test_post_unlink_eio_is_uncertain_then_a_new_process_recovers(self):
        store = self.initialized("post-unlink-eio")
        stage = store / "staging" / ".stage-post-unlink"
        stage.write_bytes(b"interrupted")
        failed = self.invoke(store, "recover", "recovery-stage-unlinked:eio")
        self.assertEqual(failed.returncode, EXIT_UNCERTAIN, failed.stderr)
        # The test seam runs after unlink.  It exercises source-cut routing;
        # it does not claim a platform EIO occurred after every successful unlink.
        self.assertFalse(stage.exists())
        restarted = self.invoke(store, "recover")
        self.assertEqual(restarted.returncode, EXIT_OK, restarted.stderr)
        self.assertIn(b"staging-orphans=0", restarted.stdout)

    def test_sigkill_after_one_unlink_restarts_and_reconciles_remaining_stage(self):
        store = self.initialized("post-unlink-kill")
        for suffix in ("a", "b"):
            (store / "staging" / ".stage-{}".format(suffix)).write_bytes(b"interrupted")
        killed = self.invoke(store, "recover", "recovery-stage-unlinked:kill")
        self.assertEqual(killed.returncode, -9, killed.stderr)
        self.assertEqual(len(list((store / "staging").iterdir())), 1)
        restarted = self.invoke(store, "recover")
        self.assertEqual(restarted.returncode, EXIT_OK, restarted.stderr)
        self.assertEqual(list((store / "staging").iterdir()), [])
        self.assertIn(b"staging-orphans=0", restarted.stdout)

    def test_atomic_hybrid_article_without_enrollment_faults_and_retains_bytes(self):
        """ACL2 emits kind-4 history whose missing kind-3 predecessor is fatal.

        The record log: a history reaches the log only through a
        commit, which ACL2 checks, or `store import', whose ordinary open
        replays the archive before anything is published at the store's
        path.  An archive whose history is that kind-4 record without its
        kind-3 enrollment is refused at that replay by the host's fault
        (exit 4, the same line as a per-file store's open gave): no store is
        published and the archive's bytes are kept."""
        source = self.initialized("hybrid-source")
        archive = self.base / "hybrid-archive"
        exported = self.store_words(source, "export", archive)
        self.assertEqual(exported.returncode, EXIT_OK, exported.stderr)
        self.assertEqual(list((archive / "records").iterdir()), [])
        record = missing_enrollment_fixture()
        name = "records/00000000000000000000.txn"
        (archive / name).write_bytes(record)
        # The archive's MANIFEST line for the record (b3sum's format), as
        # ACL2 renders it (books/store-export.lisp fn-sxp-manifest-line),
        # after the configuration lines.
        with Acl2Session(DEVELOPER) as bridge:
            line = acl2_octets(bridge.call("(fn-sxp-manifest-line (cons '%s '%s))" % (
                Acl2Session.literal(name.encode("ascii")), Acl2Session.literal(record))))
        with open(archive / "MANIFEST", "ab") as manifest:
            manifest.write(line)
        before = {p.relative_to(archive): p.read_bytes()
                  for p in archive.rglob("*") if p.is_file()}

        store = self.base / "missing-hybrid-enrollment"
        imported = self.store_words(store, "import", archive)
        self.assertEqual(imported.returncode, EXIT_FAULT, imported.stderr)
        self.assertIn(b"ACL2 replay rejected committed transaction history",
                      imported.stderr)
        self.assertFalse(store.exists())
        self.assertEqual({p.relative_to(archive): p.read_bytes()
                          for p in archive.rglob("*") if p.is_file()}, before)

if __name__ == "__main__":
    unittest.main()
