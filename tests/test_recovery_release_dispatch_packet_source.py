"""Consumer-packet boundary controls, not execution of the recovery packet."""
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
from lisp_rewrite import parse, Lst, Atom


def heads(node):
    if isinstance(node, Lst):
        if node.items and isinstance(node.items[0], Atom):
            yield node.items[0].low
        for child in node.items:
            yield from heads(child)


def forbidden(source):
    calls = {h for form in parse(source).forms for h in heads(form)}
    return {h for h in calls if h in {
        "fn2-recovery-release-begin", "fn2-recovery-release-issue",
        "fn2-recovery-release-step", "fn2-allocation-release-harvest",
        "fn2-machine-observe-terminal", "fn2-recovery-machine-put-core",
    } or h.startswith("fn2-allocation-release-set-")
      or h == "fn2-checkpoint-selected-source-set-phase"}


class DispatchPacket(unittest.TestCase):
    def setUp(self):
        self.source = (ROOT / "tests/recovery-release-dispatch-support.lisp").read_text()

    def test_no_authority_or_continuation_shortcut(self):
        self.assertEqual(forbidden(self.source), set())
        for injected in ("(fn2-recovery-release-step id gen fn2-core)",
                         "(fn2-allocation-release-harvest 1 2 0 0 0 0 0 0 0 c)",
                         "(fn2-recovery-machine-put-core id (rc-auth 1) (rc-stage 13))"):
            self.assertTrue(forbidden(self.source + injected))

    def test_actual_transport_and_whole_positive_result(self):
        for call in ("(fn2-turn fn2-core)", "(fn2-cw-adapter-one 0 nil store fn2-core)",
                     "(fn2-core-wfp fn2-core)",
                     "(fn2-rp-current-unit-auth-p id ogen fn2-core)",
                     "(fn2-recovery-selected-current-p id fn2-core)"):
            self.assertIn(call, self.source)
        self.assertIn("(= (nth 1 result) 15)", self.source)
        self.assertIn("'(:missing-antecedent)", self.source)
        self.assertIn("(equal journal (fn2-rrd-journal id fn2-core))", self.source)

    def test_faults_modify_only_real_transport_or_source(self):
        for call in ("fn2-outbox-peek", "fn2-outbox-ack", "fn2-op-range",
                     "fn2-cw-write-loan", "fn2-cw-post"):
            self.assertIn(call, self.source)
        self.assertIn("(if (eq fault :wrong-opgen) (+ 1 opgen) opgen)", self.source)
        self.assertIn("(if (eq fault :short) (- length 1) length)", self.source)
        self.assertIn("(if (eq fault :short) *fn2-outcome-short* *fn2-outcome-done*)", self.source)
        self.assertIn("fn2-checkpoint-selected-source-set-generation", self.source)
        self.assertIn("(= (logand 4 (nth 1 result)) 0)", self.source)

    def test_positive_constructs_then_crashes_real_history(self):
        source = (ROOT / "tests/recovery-release-connected-unit.lisp").read_text()
        self.assertEqual(forbidden(source), set())
        for call in ("fn2-boot-start", "fn2-alloc-reserve", "fn2-alloc-commit-allocation",
                     "fn2-alloc-retire", "fn2-ccp-prefix-and-publication",
                     "fn2-allocation-release-stage", "fn2-allocation-release-submit",
                     "fn2-allocation-release-poll", "fn2-ccp-restart",
                     "fn2-rp-release-current-p", "fn2-rrd-image-packet",
                     "fn2-release-live-credit-info"):
            self.assertIn("(" + call + " ", source)
        for mode in ("clean", "wrong-opgen", "short", "stale-source"):
            self.assertIn(f"(assert-event (fn2-rrd-result-p :{mode} (fn2-rrc-test :{mode})))", source)
        self.assertIn("(put-assoc-equal :aturn 1 *fn2-ccp-profile*)", source)
        self.assertNotIn("fn2-checkpoint-working-credit-configure", source)

    def test_image_bridge_does_not_supply_expected_authentication(self):
        source = (ROOT / "tests/recovery-release-image-support.lisp").read_text()
        self.assertEqual(forbidden(source), set())
        for call in ("fn2-sim-storage-pending", "fn2-allocation-release-read-unit",
                     "fn2-rp-release-current-p", "fn2-rp-release-installation-metadata-p"):
            self.assertIn("(" + call + " ", source)
        self.assertNotIn("update-fn2-digest", source)
        self.assertNotIn("fn2-core-write", source)


if __name__ == "__main__":
    unittest.main()
