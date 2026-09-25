"""Actual native process death checked through byte scan/open and cut programs."""
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time
import unittest

from tests.campaign import model_images, native_cuts

ROOT = Path(__file__).resolve().parent.parent
IMAGE = Path(os.environ.get("FN_NATIVE_CRASH_HOST", ""))
IMAGE_AVAILABLE = IMAGE.is_file() and os.access(IMAGE, os.X_OK)
sys.path.insert(0, str(ROOT / "tools"))
import run_store  # noqa: E402


class NativeCrashFaultSurfaceTests(unittest.TestCase):
    def test_post_fault_environment_is_developer_image_only(self):
        source = (ROOT / "host/native/io.lisp").read_text()
        start = source.index("(defun fnn-post-test-fault")
        end = source.index("\n(defun fnn-command-post", start)
        body = source[start:end]
        # Read through the accessor that answers NIL on a production image;
        # a production image refuses to start with the variable set
        # (`fnn-developer-selector-gate', run by fnn-main before dispatch).
        self.assertIn('(fnn-developer-selector "FN_NATIVE_POST_FAULT")', body)
        self.assertNotIn("posix-getenv", body)
        main = source[source.index("(defun fnn-main ()"):]
        self.assertLess(main.index("(fnn-developer-selector-gate argv)"),
                        main.index("(fnn-dispatch argv)"))

    def test_every_native_cut_has_a_byte_program_coordinate(self):
        native_cuts.verify_native_cut_map()

    def test_missing_image_is_not_reported_as_a_skipped_campaign(self):
        self.assertEqual("NativeCrashModelTests" in globals(), IMAGE_AVAILABLE)
        self.assertFalse(getattr(NativeCampaignMixin, "__unittest_skip__", False))


class NativeCampaignMixin:
    def invoke(self, store, command, *arguments, expected=0, env=None):
        host_env = dict(os.environ)
        host_env.update(env or {})
        if command == "inspect" and arguments[:1] == ("--message-id",):
            arguments = arguments[1:]
        result = subprocess.run(
            [str(IMAGE), "--fn", "store", str(store), command,
             *map(str, arguments)], cwd=ROOT, env=host_env,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
        self.assertEqual(result.returncode, expected,
                         "stdout={}\nstderr={}".format(result.stdout, result.stderr))
        return result

    def native_post(self, store, message_id, payload, env):
        return subprocess.run(
            [str(IMAGE), "--fn", "store", str(store), "post",
             message_id, str(payload), "-", "-", "fn.letters"],
            cwd=ROOT, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            check=False)

    @staticmethod
    def transaction_bytes(store):
        return {p.name: p.read_bytes()
                for p in sorted((store / "transactions").iterdir()) if p.is_file()}

    @staticmethod
    def octet_list(data: bytes) -> str:
        return "'({})".format(" ".join(str(x) for x in data))

    def intended_frame(self, bridge, form, observed: bytes) -> tuple[bool, bytes]:
        """ACL2's octets for FORM, and whether OBSERVED is a prefix of them."""
        text = bridge.value("(let* ((f {})) (cons (if (and (true-listp f)"
                            " (fn-native-prefixp {} f)) 1 0) f))".format(
                                form, self.octet_list(observed)))
        values = [int(x) for x in re.findall(r"\d+", text)]
        return values[0] == 1, bytes(values[1:])

    def intended_frames(self, bridge, sent, before_frontier: bytes,
                        prior_frame: bytes, observed_frontier: bytes,
                        observed_record: bytes | None):
        """The frontier frame and the candidate's FNST frame this post intends.

        Campaign 6c0626c5 finding H2: the program's octets were read off the
        store at the cut, so at frontier-created and record-created (an empty
        staged file) the model ran a program writing zero octets, a check
        parameterized by the observation it judged.  Here ACL2 derives both
        frames from what the test sent: the next frontier from the frontier
        the store held before the post; the record from the Message-ID,
        payload and group the test posted, over the opened pre-post state,
        by fn-sn-article-record, the constructor fn-store-sn-prepare calls,
        framed by fn-frame-store-protected and sealed with fn-frame-trailer,
        as fnn-frame does.  Two inputs are not the article: the record stamp
        is the owner's wall-clock second on the DTN epoch, which the test
        brackets (each POSIX second in [t0, t1] is shifted by ACL2's
        fn-nntp-unix-dtn-ms, and the observed octets must be a prefix of the
        frame for one of them); and the release evidence is
        the local-post provenance of the store's configuration, taken from
        the prior record the same configuration wrote before the post.

        PAYLOAD is the stored article's octets, or, when the owner derives
        them (a served post is injected under the owner's clock), an ACL2
        form with a `{unix_ms}` hole that ACL2 evaluates per bracketed
        second to the octets the owner stores; it may use the bindings of
        `opened_before_bindings`.  The record's charge is ACL2's length of
        those octets.
        """
        message_id, payload, groups, (t0, t1) = sent
        frontier = ("(fn-bs-frontier-encode (fn-bs-frontier-next"
                    " (fn-bs-frontier-decode {})))".format(self.octet_list(before_frontier)))
        front_ok, front = self.intended_frame(bridge, frontier, observed_frontier)
        self.assertTrue(front_ok, "observed frontier {!r} is not a prefix of the "
                        "intended {!r}".format(observed_frontier, front))
        msgid = self.octet_list(message_id.encode("ascii"))
        record_frames = []
        for stamp in range(int(t0), int(t1) + 1):
            payload_form = (payload.format(unix_ms=1000 * stamp)
                            if isinstance(payload, str) else self.octet_list(payload))
            record = (
                "(let* ((payload {payload})"
                " (subject (fn-id-subject-of-payload payload))"
                " (event (fn-sn-article-record (fn-sn-open-state opened-before)"
                "  (fn-clock-observation 0 (fn-nntp-unix-dtn-ms {unix_ms}) 0 t)"
                " \"{msgid_text}\" payload"
                "  '({groups})"
                "  (fn-record-octets-string (fn-id-text (fn-id-obligation-of {msgid} subject)))"
                "  (fn-record-octets-string (fn-id-text subject))"
                "  (fn-record-release-evidence (fn-bs-record-of-octets {prior}))"
                "  (fn-charge-for-payload (len payload))))"
                " (protected (fn-frame-store-protected (fn-store-event-encode event))))"
                " (append protected (fn-frame-trailer protected)))").format(
                    payload=payload_form, unix_ms=1000 * stamp,
                    msgid_text=message_id, msgid=msgid,
                    groups=" ".join('"{}"'.format(g) for g in groups),
                    prior=self.octet_list(prior_frame))
            record_frames.append((stamp,) + self.intended_frame(
                bridge, "(let* ({}) {})".format(self.opened_before_bindings, record),
                observed_record or b""))
        matching = [(stamp, frame) for stamp, ok, frame in record_frames if ok]
        self.assertTrue(matching, "observed record octets {} are a prefix of no "
                        "intended frame: {}".format(
                            (observed_record or b"").hex(),
                            [(stamp, frame.hex()) for stamp, _, frame in record_frames]))
        return front, matching[0][1]

    def assert_observed_scan_is_program_image(self, before_form, store, cut,
                                              prior_names=(), sent=None,
                                              before_frontier=None, prior_frame=None,
                                              bridge_setup=(), before_marker=None):
        """Compare exact scan values with the model's process-death image.

        SIGKILL does not simulate loss of dirty kernel state.  Therefore the
        model choice used here applies every issued entry operation and keeps
        every pending write new.  This checks that the observed namespace and
        decoded event sequence are an allowed model image without making a
        power-loss claim.  The programs write the frames `intended_frames`
        derives from the post the test sent, not octets read at the cut, and
        every staged or published frame must be a prefix of its intended
        frame, the whole of it once the cut is past the program's write.
        """
        bridge = model_images.ModelBridge()
        try:
            bridge.call('(include-book "books/byte-store-keystones")')
            bridge.call('(include-book "books/byte-store-observation-scan")')
            bridge.call('(include-book "books/codec-attach")')
            bridge.call('(include-book "books/byte-store-frame")')
            bridge.call('(include-book "books/byte-store-txn-name")')
            bridge.call('(include-book "books/identity")')
            bridge.call('(include-book "books/crypto-attach")')
            bridge.call('(include-book "books/frame")')
            bridge.call('(include-book "books/frame-trailer")')
            bridge.call('(include-book "books/store-events")')
            bridge.call('(include-book "books/nntp-responses")')
            bridge.call('(include-book "books/byte-store-marker-program")')
            for form in bridge_setup:
                bridge.call(form, timeout=600)
            bridge.call("(defun fn-native-prefixp (x y)"
                        " (if (atom x) t (and (consp y) (equal (car x) (car y))"
                        "  (fn-native-prefixp (cdr x) (cdr y)))))")
            bridge.call("(defun fn-native-visible-choices (ops unit)"
                        " (if (atom ops) nil"
                        "  (cons (if (equal (car (car ops)) :write)"
                        "            (fn-bs-all-new (fn-bs-unit-count"
                        "             (nth 2 (car ops)) (len (nth 3 (car ops))) unit))"
                        "          :apply)"
                        "        (fn-native-visible-choices (cdr ops) unit))))")
            bindings = ["(before {})".format(before_form),
                        "(before-scan (fn-bs-scan-store before))",
                        "(opened-before (fn-sn-open-observed '(\"fn.letters\" \"fn.test\")"
                        " 10000000 (fn-bs-scan-frontier before-scan)"
                        " (fn-bs-scan-records before-scan)))",
                        "(ks (fn-sn-files (fn-sn-open-state opened-before)))"]
            self.opened_before_bindings = " ".join(bindings[:3])
            frontier = (store / "allocation-frontier.json").read_bytes()
            stages = sorted((store / "staging").glob(".allocation-*"))
            next_frontier = stages[0].read_bytes() if stages else frontier
            frontier_stage = stages[0].name if stages else ".allocation-campaign"
            txns = self.transaction_bytes(store)
            candidate_names = sorted(set(txns).difference(prior_names))
            # The marker's stage is `.stage-marker-' (fnn-mark-committed);
            # every other `.stage-' is the record's.
            marker_stages = sorted((store / "staging").glob(".stage-marker-*"))
            record_stages = sorted(set((store / "staging").glob(".stage-*"))
                                   - set(marker_stages))
            observed_record = (txns[candidate_names[0]] if candidate_names
                               else record_stages[0].read_bytes() if record_stages
                               else None)
            intended_frontier, intended_record = self.intended_frames(
                bridge, sent, before_frontier, prior_frame, next_frontier,
                observed_record)
            if self.past_write(cut, "fn-bs-frontier-program"):
                self.assertEqual(next_frontier, intended_frontier, cut.name)
            if observed_record is not None and self.past_write(cut, "fn-bs-record-program"):
                self.assertEqual(observed_record, intended_record, cut.name)
            if cut.program == "fn-bs-record-program" and cut.name == "record-created":
                self.assertEqual(observed_record, b"", "record-created stage is not empty")
            # The marker this commit writes: ACL2's frame for the committed
            # count, derived from the post (its sequence is the number of
            # records before it), never read off the store.  The prior
            # post's marker is the one in the pre-post image.
            sequence = len(prior_names)
            intended_marker = bytes(int(x) for x in re.findall(r"\d+", bridge.value(
                "(fn-hm-after-commit {})".format(sequence))))
            self.assertTrue(intended_marker, "no marker frame for sequence {}".format(sequence))
            old_marker = before_marker
            marker_path = store / "committed-history.json"
            observed_marker = marker_path.read_bytes() if marker_path.exists() else None
            fate = native_cuts.marker_fate(cut)
            allowed = {"old": [old_marker], "new": [intended_marker],
                       "either": [old_marker, intended_marker]}[fate]
            self.assertIn(observed_marker, allowed, "{}: marker {} is not the {} one".format(
                cut.name, observed_marker, fate))
            if marker_stages and self.past_write(cut, "fn-bs-marker-program"):
                self.assertEqual(marker_stages[0].read_bytes(), intended_marker, cut.name)
            # The program writes the frontier octets derived from the post.
            frontier_program = "(fn-bs-frontier-program \"{}\" {})".format(
                frontier_stage, self.octet_list(intended_frontier))
            bindings.append("(frontier-run (fn-bs-run before ks {} nil"
                            " '(\"fn.letters\" \"fn.test\") 10000000))".format(
                                frontier_program))
            if cut.program == "fn-bs-frontier-program":
                index = model_images.cut_index(cut.program,
                                               cut.model_name or cut.name,
                                               cut.occurrence)
                bindings.append("(cut-bs (car (nth {} frontier-run)))".format(index))
            else:
                bindings.extend(["(after-frontier (car (car (last frontier-run))))",
                                 "(reserved (cdr (car (last frontier-run))))"])
                if observed_record is None:
                    self.assertTrue(record_stages or candidate_names,
                                    "candidate frame absent from final and staging names")
                record_stage = record_stages[0].name if record_stages else ".stage-campaign"
                # The program writes the frame derived from the article sent.
                octets = " ".join(str(x) for x in intended_record)
                bindings.append("(candidate-record (fn-bs-record-of-octets '({})))".format(octets))
                bindings.append("(prepared (fn-sf-prepare-record reserved"
                                " candidate-record '(\"fn.letters\" \"fn.test\") 10000000))")
                next_name = "{:020d}.txn".format(len(prior_names))
                record_program = "(fn-bs-record-program \"{}\"".format(record_stage)
                record_program += " \"{}\" '({}))".format(next_name, octets)
                bindings.append("(record-run (fn-bs-run after-frontier prepared {} nil"
                                " '(\"fn.letters\" \"fn.test\") 10000000))".format(
                                    record_program))
                if cut.program == "fn-bs-record-program":
                    index = model_images.cut_index(cut.program, cut.name)
                    bindings.append("(cut-bs (car (nth {} record-run)))".format(index))
                else:
                    bindings.extend(["(after-record (car (car (last record-run))))",
                                     "(completing (cdr (car (last record-run))))"])
                    # P-MARKER (fnn-mark-committed) runs between the record
                    # and the acknowledgement, writing ACL2's frame for the
                    # committed count.
                    marker_stage = (marker_stages[0].name if marker_stages
                                    else ".stage-marker-campaign")
                    marker = "(fn-bs-marker-program \"{}\" (fn-hm-after-commit {}))".format(
                        marker_stage, sequence)
                    bindings.append("(marker-run (fn-bs-run after-record completing"
                                    " {} nil '(\"fn.letters\" \"fn.test\") 10000000))".format(marker))
                    if cut.program == "fn-bs-marker-program":
                        index = model_images.cut_index(cut.program, cut.name, 1, cut.book)
                        bindings.append("(cut-bs (car (nth {} marker-run)))".format(index))
                    else:
                        bindings.extend(["(after-marker (car (car (last marker-run))))",
                                         "(marked (cdr (car (last marker-run))))"])
                        finish = "(fn-bs-finish-program {} {})".format(
                            len(prior_names), len(prior_names))
                        bindings.append("(finish-run (fn-bs-run after-marker marked"
                                        " {} nil '(\"fn.letters\" \"fn.test\") 10000000))".format(finish))
                        index = model_images.cut_index(cut.program,
                                                       cut.model_name or cut.name,
                                                       cut.occurrence)
                        bindings.append("(cut-bs (car (nth {} finish-run)))".format(index))
            bindings.extend([
                "(observed {})".format(model_images.import_image(store)),
                "(choices (fn-native-visible-choices (fn-bs-pending cut-bs) (fn-bs-unit cut-bs)))",
                "(model-image (fn-bs-crash cut-bs choices))",
                "(model-scan (fn-bs-scan-store model-image))",
                "(scan (fn-bs-scan-store observed))",
                "(model-opened (fn-sn-open-observed '(\"fn.letters\" \"fn.test\")"
                " 10000000 (fn-bs-scan-frontier model-scan)"
                " (fn-bs-scan-records model-scan)))",
                "(opened (fn-sn-open-observed '(\"fn.letters\" \"fn.test\")"
                " 10000000 (fn-bs-scan-frontier scan) (fn-bs-scan-records scan)))",
            ])
            observed = bridge.value(
                "(let* ({} ) (list"
                " (fn-bs-crash-choicesp choices (fn-bs-pending cut-bs) (fn-bs-unit cut-bs))"
                " (fn-bs-scan-okp scan) (fn-sn-open-okp opened)"
                " (fn-bso-served-image-agree model-image observed)"
                " (equal (fn-bs-names model-image :transactions)"
                "        (fn-bs-names observed :transactions))"
                " (fn-bs-scan-okp model-scan)"
                " (equal model-scan scan)"
                " (equal model-opened opened)"
                " (list (fn-bso-directory-agree model-image observed :root)"
                "       (fn-bso-directory-agree model-image observed :transactions)"
                "       (fn-bso-directory-agree model-image observed :staging)"
                "       (fn-bs-names model-image :staging)"
                "       (fn-bs-names observed :staging))))".format(
                    " ".join(bindings)))
            self.assertRegex(observed, r"\(T\s+T\s+T\s+T\s+T\s+T\s+T\s+T\s+\(T\s+T\s+T",
                             "{}: {}".format(cut.name, observed))
        finally:
            bridge.close()

    @staticmethod
    def past_write(cut, program):
        """Whether the cut lies after PROGRAM's write-all step."""
        order = native_cuts.POST_PROGRAMS
        if order.index(cut.program) != order.index(program):
            return order.index(cut.program) > order.index(program)
        steps = native_cuts.model_steps(program, native_cuts.program_book(program))
        write = next(j for j, s in enumerate(steps) if s.kind == "write-all")
        return native_cuts.cut_step_index(cut) > write

    def run_post_cut(self, cut, claimed=None, skew=0):
        """CLAIMED replaces the payload the differential is told was sent,
        and SKEW shifts the bracketed clock window: the teeth below."""
        with tempfile.TemporaryDirectory(prefix="fn-native-cut-") as tmp:
            root = Path(tmp); store = root / "store"
            prior = root / "prior"; prior.write_bytes(b"prior accepted protected content")
            candidate = root / "candidate"; candidate.write_bytes(b"candidate protected content")
            self.invoke(store, "init")
            self.invoke(store, "post", "<prior@example.invalid>", prior, "-", "-", "fn.letters")
            before_form = model_images.import_image(store)
            prior_frames = self.transaction_bytes(store)
            self.assertEqual(len(prior_frames), 1)
            before_frontier = (store / "allocation-frontier.json").read_bytes()
            before_marker = (store / "committed-history.json").read_bytes()
            env = dict(os.environ); env["FN_NATIVE_POST_FAULT"] = cut.name + ":kill"
            t0 = time.time()
            killed = self.native_post(store, "<candidate@example.invalid>", candidate, env)
            t1 = time.time()
            self.assertEqual(killed.returncode, -9, killed.stderr)
            killed_frames = self.transaction_bytes(store)
            self.assertEqual(killed_frames.get(next(iter(prior_frames))),
                             next(iter(prior_frames.values())))
            self.assert_observed_scan_is_program_image(
                before_form, store, cut, prior_frames,
                sent=("<candidate@example.invalid>",
                      candidate.read_bytes() if claimed is None else claimed,
                      ("fn.letters",), (t0 + skew, t1 + skew)),
                before_frontier=before_frontier,
                prior_frame=next(iter(prior_frames.values())),
                before_marker=before_marker)
            recovered = self.invoke(store, "recover")
            self.assertIn(b"articles=", recovered.stdout)
            self.assertEqual(self.transaction_bytes(store), killed_frames)
            inspected = self.invoke(store, "inspect", "--message-id",
                                    "<prior@example.invalid>")
            self.assertEqual(inspected.stdout, prior.read_bytes())
            candidate_present = len(killed_frames) == 2
            self.assertIn(candidate_present, {"absent": {False}, "present": {True},
                                               "either": {False, True}}[cut.candidate])


# Runtime tests only exist when the caller supplies a source-matched executable.
# Absence is therefore zero runtime evidence, never a skipped passing campaign.
if IMAGE_AVAILABLE:
    class NativeCrashModelTests(NativeCampaignMixin, unittest.TestCase):
        def test_all_native_post_process_death_cuts(self):
            for cut in native_cuts.POST_CUTS:
                selected = os.environ.get("FN_NATIVE_LOWLEVEL_CUT")
                if selected and cut.name != selected:
                    continue
                with self.subTest(cut=cut.name):
                    self.run_post_cut(cut)

        def test_the_frame_is_the_sent_articles_not_anothers(self):
            # Teeth for the derivation: the frame on disk at record-written is
            # a prefix of no frame of a different article, nor of this
            # article stamped outside the bracketed window.
            cut = next(c for c in native_cuts.POST_CUTS if c.name == "record-written")
            for label, claimed, skew in (("other article", b"candidate protected contenT", 0),
                                         ("other second", None, 100)):
                with self.subTest(label), self.assertRaisesRegex(
                        AssertionError, "prefix of no intended frame"):
                    self.run_post_cut(cut, claimed=claimed, skew=skew)

        def test_recovery_stage_unlink_process_death_scans_and_reopens(self):
            with tempfile.TemporaryDirectory(prefix="fn-native-recovery-cut-") as tmp:
                root = Path(tmp); store = root / "store"
                prior = root / "prior"; prior.write_bytes(b"prior recovery content")
                candidate = root / "candidate"; candidate.write_bytes(b"orphan candidate")
                self.invoke(store, "init")
                self.invoke(store, "post", "<prior-recovery@example.invalid>",
                            prior, "-", "-", "fn.letters")
                prior_frames = self.transaction_bytes(store)
                env = dict(os.environ)
                env["FN_NATIVE_POST_FAULT"] = "record-staged-durable:kill"
                killed = self.native_post(store, "<orphan@example.invalid>", candidate, env)
                self.assertEqual(killed.returncode, -9, killed.stderr)
                self.assertTrue(list((store / "staging").glob(".stage-*")))
                recover_env = dict(os.environ)
                recover_env["FN_NATIVE_RECOVERY_FAULT"] = "recovery-stage-unlinked:kill"
                killed_recovery = subprocess.run(
                    [str(IMAGE), "--fn", "store", str(store), "recover"],
                    cwd=ROOT, env=recover_env, stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE, check=False)
                self.assertEqual(killed_recovery.returncode, -9, killed_recovery.stderr)
                self.assertFalse(list((store / "staging").glob(".stage-*")))
                bridge = model_images.ModelBridge()
                try:
                    bridge.call('(include-book "books/byte-store-keystones")')
                    bridge.call('(include-book "books/codec-attach")')
                    bridge.call('(include-book "books/byte-store-frame")')
                    bridge.call('(include-book "books/byte-store-txn-name")')
                    bridge.call("(defconst *fn-native-recovery-observed* {})".format(
                        model_images.import_image(store)))
                    value = bridge.value(
                        "(let* ((scan (fn-bs-scan-store *fn-native-recovery-observed*))"
                        " (opened (fn-sn-open-observed '(\"fn.letters\" \"fn.test\")"
                        "  10000000 (fn-bs-scan-frontier scan)"
                        "  (fn-bs-scan-records scan))))"
                        " (list (fn-bs-scan-okp scan) (fn-sn-open-okp opened)))")
                    self.assertRegex(value, r"\(T\s+T\)\s*$", value)
                finally:
                    bridge.close()
                self.invoke(store, "recover")
                self.assertEqual(self.transaction_bytes(store), prior_frames)
                inspected = self.invoke(store, "inspect", "--message-id",
                                        "<prior-recovery@example.invalid>")
                self.assertEqual(inspected.stdout, prior.read_bytes())

        def test_injected_outcomes_stay_refused_or_uncertain_and_recover(self):
            cases = (("prepublish", 1), ("postpublish", 3),
                     ("frontierbarrier", 3), ("recordbarrier", 3))
            for inject, expected in cases:
                with self.subTest(inject=inject), tempfile.TemporaryDirectory(
                        prefix="fn-native-eio-") as tmp:
                    root = Path(tmp); store = root / "store"
                    prior = root / "prior"; prior.write_bytes(b"prior")
                    candidate = root / "candidate"; candidate.write_bytes(b"candidate")
                    self.invoke(store, "init")
                    self.invoke(store, "post", "<prior-eio@example.invalid>",
                                prior, "-", "-", "fn.letters")
                    prior_frames = self.transaction_bytes(store)
                    self.invoke(store, "post", "<candidate-eio@example.invalid>",
                                candidate, "-", inject, "fn.letters", expected=expected)
                    after = self.transaction_bytes(store)
                    self.assertEqual(after.get(next(iter(prior_frames))),
                                     next(iter(prior_frames.values())))
                    self.invoke(store, "recover")
                    self.assertEqual(self.transaction_bytes(store), after)


if __name__ == "__main__":
    if not IMAGE_AVAILABLE:
        raise SystemExit("FN_NATIVE_CRASH_HOST must name a source-matched developer image")
    unittest.main()
