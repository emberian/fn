"""Decision tracing, the host's half (lane obs-decision-trace; observability
program section 3: DT-1h, DT-3, DT-5).

Two groups.

RAW (plain SBCL, runs anywhere): tests/native_decision_trace_raw.lisp drives
the deployed `fnn-call`, `fnn-core-mv` and host/native/trace.lisp against a
mock ACL2.  It is DT-5 (a ring of capacity 7 under 100 calls reports 7
recorded and 93 dropped; attempts = recorded + dropped + sampled-out in every
snapshot, under concurrent callers and a drainer), the shape of DT-1h (a
traced call's row holds what the call returned, values reach the caller
unchanged, a stobj position is masked), and the cost of off.  Its labelled
mutation, FN_DT_RAW_MUTATION=skew (the ring's row takes the previous call's
outcome, the mechanism of FN_NATIVE_TEST_TRACE_SKEW), must turn it red.

NATIVE (a developer image; hbox, through the slot deputy O grants, filtered to
this module): the same claims on the real image.

* DT-1h.  A scripted session with tracing on; every drained row of a
  replayable entry (every recorded input a :value, so the row carries its
  arguments: fn-store-charge) is replayed through ACL2 (`fn acl2 session`) on
  its recorded inputs and its outcome compared.  FN_NATIVE_TEST_TRACE_SKEW=1
  makes each row take the previous call's outcome: the comparison must fail.
* DT-3.  Tracing off and on leave the served and stored octets identical.  The
  same scripted session (an operator post, GROUP, OVER, ARTICLE, an NNTP POST,
  a refusal) with FN_NATIVE_TEST_CLOCK and FN_NATIVE_TEST_ENTROPY fixed, run
  three ways -- no [trace] table, a table with tracing off, a table with
  tracing on at every class -- gives byte-identical client transcripts and
  byte-identical files under the store (record log, journal, articles).
  FN_NATIVE_TEST_TRACE_PERTURB=1 makes an enabled trace consume one entropy
  draw: the on arm must then differ.

    FN_NATIVE_DEVELOPER_HOST=/path/to/developer-image \\
        python3 -m unittest tests.test_native_decision_trace
"""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import native_trace  # noqa: E402

from tests.native_harness import (Acl2Session, EXIT, Node, acl2_nat, article,  # noqa: E402
                                  executable, native_image)

IMAGE = native_image("FN_NATIVE_DEVELOPER_HOST")
RAW = ROOT / "tests/native_decision_trace_raw.lisp"
CLASSES = ("verdict", "refusal", "tariff", "schedule", "plan")
FIRST_WAVE = {
    "fn-otm-admit-post", "fn-owner-served-post-word", "fn-own-intent-refusal-word",
    "fn-owner-output-tariff-preview", "fn-store-charge", "fn-owner-exposure-charge",
    "fn-owner-connection-budget", "fn-otm-next", "fn-otm-wait-ms",
    "fn-otm-committer-wake", "fn-otm-disk-step", "fn-lgc-append-admitsp",
    "fn-lgdm-verdict", "fn-lgu-take-verdict", "fn-ctlk-frame-handler", "fn-rdv-admit",
}


class RawRing(unittest.TestCase):
    def run_raw(self, mutation=None):
        sbcl = shutil.which("sbcl")
        if not sbcl:
            self.skipTest("no SBCL runtime on PATH")
        env = dict(os.environ)
        env.pop("FN_DT_RAW_MUTATION", None)
        if mutation:
            env["FN_DT_RAW_MUTATION"] = mutation
        return subprocess.run([sbcl, "--noinform", "--script", str(RAW)], cwd=ROOT, env=env,
                              capture_output=True, text=True, timeout=120)

    def test_ring_counts_and_interposition_hold(self):
        result = self.run_raw()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("NATIVE_DECISION_TRACE_PASS", result.stdout)

    def test_mutation_closure_expansion_of_core_mv_turns_the_off_cost_tooth_red(self):
        result = self.run_raw("flet")
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn("FAIL: off: a fnn-core-mv site allocates no closure", result.stdout + result.stderr)

    def test_the_drained_lines_are_the_one_parsers(self):
        result = self.run_raw()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        rows, summaries = native_trace.decisions_from_text(result.stdout)
        self.assertTrue(rows, "no decision line drained")
        for row in rows:
            self.assertEqual(row["v"], 2)
            self.assertEqual(row["point"], "mock-word")
            self.assertIn(row["class"], CLASSES)
            self.assertIsInstance(row["seq"], int)
            self.assertIsInstance(row["inputs"], list)
        for summary in summaries:
            self.assertEqual(summary["attempts"],
                             summary["recorded"] + summary["dropped"] + summary["sampled_out"])

    def test_the_parser_refuses_what_is_not_a_decision_record(self):
        good = dict(v=2, type="decision", seq=1, **{"class": "verdict"}, point="fn-store-charge",
                    operation=None, connection_generation=None, start_us=1, duration_us=0,
                    inputs=[7], outcome=7)
        line = lambda event: native_trace.PREFIX + json.dumps(event) + "\n"  # noqa: E731
        self.assertEqual(native_trace.decisions_from_text(line(good))[0], [good])
        for change in (dict(v=1), dict(seq=0), {"class": "elsewhere"}, dict(point=""),
                       dict(duration_us=-1), dict(inputs="x"), dict(outcome=1 << 64),
                       dict(outcome=[1, 2, 3, 4, 5, 6, 7, 8, 9]), dict(outcome=[[1] * 9])):
            with self.assertRaises(ValueError, msg=change):
                native_trace.decisions_from_text(line(dict(good, **change)))
        unbalanced = dict(v=2, type="decision-summary", attempts=3, recorded=1, dropped=1,
                          sampled_out=0, live=1, next=2)
        with self.assertRaises(ValueError):
            native_trace.decisions_from_text(line(unbalanced))

    def test_skew_mutation_turns_dt_1h_red(self):
        result = self.run_raw("skew")
        self.assertNotEqual(result.returncode, 0, "a row that takes the previous outcome must be seen")
        self.assertIn("DT-1h: row", result.stdout)


@unittest.skipUnless(executable(IMAGE), "an executable FN_NATIVE_DEVELOPER_HOST is required")
class NativeDecisionTrace(unittest.TestCase):
    CLOCK = "5000:1000:0"       # MONO-MS:SECONDS:MICROSECONDS
    ENTROPY = "17"
    TABLE = '\n[trace]\ncapacity = 4096\nclasses = "all"\n'

    def fixed_env(self, extra=None):
        env = {"FN_NATIVE_TEST_CLOCK": self.CLOCK, "FN_NATIVE_TEST_ENTROPY": self.ENTROPY}
        env.update(extra or {})
        return env

    def node(self, arm, table):
        node = Node(self, IMAGE, name=arm, extra=table or "")
        node.init("fn.test", env=self.fixed_env())
        return node

    def drain(self, node):
        result = node.operator("trace", "drain", expect=EXIT.OK, env=self.fixed_env())
        return native_trace.decisions_from_text(result.stdout)

    def session(self, node):
        """The scripted session; returns the client transcripts, in order."""
        transcript = []
        posted = node.post(b"<control-post@example.invalid>", article(b"<control-post@example.invalid>"),
                           expect=EXIT.OK, env=self.fixed_env())
        transcript.append(posted.stdout.encode() if isinstance(posted.stdout, str) else posted.stdout)
        with node.session() as client:
            transcript.append(client.command("GROUP fn.test"))
            transcript.append(client.multiline("OVER 1-1"))
            transcript.append(client.multiline("ARTICLE 1"))
            first, final = client.post(article(b"<nntp-post@example.invalid>", body=b"a posted body\r\n"))
            transcript.extend([first, final])
            # a refusal: the same Message-ID again
            first, final = client.post(article(b"<nntp-post@example.invalid>", body=b"a posted body\r\n"))
            transcript.extend([first, final])
            transcript.append(client.command("ARTICLE <absent@example.invalid>"))
        return b"\n--\n".join(bytes(t) for t in transcript)

    def stored(self, node):
        """{relative path: sha256} of every regular file under the store."""
        out = {}
        for path in sorted(node.store_path.rglob("*")):
            if path.is_file() and not path.is_symlink() and path.suffix != ".lock":
                out[str(path.relative_to(node.store_path))] = hashlib.sha256(path.read_bytes()).hexdigest()
        return out

    def run_arm(self, arm, table, trace=False, env=None):
        node = self.node(arm, table)
        node.start(env=self.fixed_env(env))
        try:
            if trace:
                node.operator("trace", "on", expect=EXIT.OK, env=self.fixed_env(env))
            transcript = self.session(node)
            rows = self.drain(node) if trace else ([], [])
        finally:
            node.stop()
        return transcript, self.stored(node), rows

    # DT-1h ---------------------------------------------------------------
    def replay_mismatches(self, rows):
        """Rows of a replayable entry whose replayed outcome differs."""
        bad = []
        replayed = 0
        with Acl2Session(IMAGE) as acl2:
            for row in rows:
                if row["point"] != "fn-store-charge" or len(row["inputs"]) != 1:
                    continue
                replayed += 1
                again = acl2_nat(acl2.call("(fn-store-charge {})".format(row["inputs"][0])))
                if again != row["outcome"]:
                    bad.append((row["seq"], row["outcome"], again))
        self.assertGreater(replayed, 0, "no replayable row: fn-store-charge was not traced")
        return bad

    def test_dt_1h_every_row_replays_to_the_recorded_outcome(self):
        _, _, (rows, summaries) = self.run_arm("dt1h", self.TABLE, trace=True)
        self.assertTrue({r["point"] for r in rows} <= FIRST_WAVE, {r["point"] for r in rows} - FIRST_WAVE)
        self.assertEqual(self.replay_mismatches(rows), [])

    def test_dt_1h_mutation_skew_is_seen(self):
        _, _, (rows, _) = self.run_arm("dt1h-skew", self.TABLE, trace=True,
                                       env={"FN_NATIVE_TEST_TRACE_SKEW": "1"})
        self.assertNotEqual(self.replay_mismatches(rows), [],
                            "FN_NATIVE_TEST_TRACE_SKEW makes each row take the previous outcome")

    # DT-5 ----------------------------------------------------------------
    def test_dt_5_a_small_ring_counts_its_drops(self):
        table = '\n[trace]\ncapacity = 7\nclasses = "all"\n'
        _, _, (rows, summaries) = self.run_arm("dt5", table, trace=True)
        self.assertTrue(summaries)
        last = summaries[-1]
        self.assertEqual(last["attempts"], last["recorded"] + last["dropped"] + last["sampled_out"])
        self.assertEqual(last["recorded"], 7)
        self.assertGreater(last["dropped"], 0, "the session makes more than seven traced calls")
        self.assertEqual(len(rows), 7)

    # DT-3 ----------------------------------------------------------------
    def test_dt_3_tracing_off_and_on_leave_the_octets_identical(self):
        none = self.run_arm("none", None)
        off = self.run_arm("off", self.TABLE)
        on = self.run_arm("on", self.TABLE, trace=True)
        classes = {r["class"] for r in on[2][0]}
        self.assertTrue(classes, "the on arm traced nothing")
        self.assertEqual(off[0], none[0], "client transcripts: table, tracing off")
        self.assertEqual(on[0], none[0], "client transcripts: tracing on")
        self.assertEqual(off[1], none[1], "store files: table, tracing off")
        self.assertEqual(on[1], none[1], "store files: tracing on")

    def test_dt_3_mutation_perturb_is_seen(self):
        none = self.run_arm("none-p", None)
        on = self.run_arm("on-p", self.TABLE, trace=True, env={"FN_NATIVE_TEST_TRACE_PERTURB": "1"})
        self.assertTrue(on[0] != none[0] or on[1] != none[1],
                        "an enabled trace that consumes an entropy draw must change the octets")


if __name__ == "__main__":
    unittest.main()
