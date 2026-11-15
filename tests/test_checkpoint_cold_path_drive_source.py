"""Source controls for the actual cold-fixture transport, not a boot witness."""
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import lisp_rewrite as lr


def functions(source):
    return {m.captures["name"].low: m.node for m in
            lr.match("(defun ?name ?args ?*body)", lr.parse(source).forms)
            if isinstance(m.captures["name"], lr.Atom)}


def held_check(source):
    fn = functions(source)["fn2-ccp-epoch-fence-p"]
    for pattern in (
        "(= (fn2-machine-phase id fn2-core) *fn2-boot-state-epoch-result*)",
        "(= (fn2-machine-stage id fn2-core) 3)",
        "(= (fn2-machine-pending id fn2-core) 1)",
        "(= (fn2-machine-event-ready id fn2-core) 0)",
        "(= (fn2-ops-gen slot fn2-ops) gen)",
        "(= (fn2-ops-kind slot fn2-ops) *fn2-action-fence*)",
        "(= (fn2-ops-owner-kind slot fn2-ops) *fn2-boot-kind*)",
        "(= (fn2-ops-owner-slot slot fn2-ops) id)",
        "(= (fn2-ops-owner-gen slot fn2-ops) generation)",
    ):
        if not lr.match(pattern, [fn]):
            raise ValueError("held Fence loses actual owner/phase identity")


class Source(unittest.TestCase):
    def setUp(self):
        self.source = (ROOT / "tests/checkpoint-cold-path-drive.lisp").read_text()
        self.fns = functions(self.source)

    def test_actual_epoch_fence_only(self):
        held_check(self.source)
        with self.assertRaises(ValueError):
            held_check(self.source.replace(
                "(= (fn2-ops-owner-gen slot fn2-ops) generation)", "t", 1))

    def test_real_transport_and_restart(self):
        self.assertTrue(lr.match("(fn2-ccp-pump fn2-core fn2-sim fn2-own)", [self.fns["fn2-ccp-drive"]]))
        self.assertTrue(lr.match("(fn2-b-turn fn2-core)", [self.fns["fn2-ccp-pump"]]))
        for name in ("fn2-ccp-pump", "fn2-ccp-complete-epoch"):
            self.assertTrue(lr.match("(fn2-sim-advance-selected ?*args)", [self.fns[name]]))
            self.assertTrue(lr.match("(fn2-sim-take-prefix 1 0 fn2-core fn2-sim fn2-own)", [self.fns[name]]))
        for pattern in (
            "(fn2-sim-crash profile fn2-core fn2-sim fn2-own)",
            "(fn2-init-executor profile :null nil fn2-core)",
            "(fn2-boot-start nil image-size fn2-core)",
        ):
            self.assertTrue(lr.match(pattern, [self.fns["fn2-ccp-restart"]]))

    def test_transport_never_manufactures_authority_or_physical_returns(self):
        calls = [m.node.items[0].low for m in lr.match("(?head ?*args)", list(self.fns.values()))
                 if isinstance(m.node.items[0], lr.Atom)]
        for call in calls:
            self.assertNotIn(call, ("fn2-post-result", "fn2-post-result0", "fn2-storage-write-byte",
                                    "fn2-storage-fence-complete", "fn2-boot-put-core"))
            self.assertFalse(call.startswith(("update-fn2-alloc-", "fn2-checkpoints-put",
                                             "fn2-checkpoint-selected-source-put", "fn2-checkpoint-summary-put")), call)

    def test_failure_control_completes_the_exact_submitted_generation(self):
        fn = self.fns["fn2-ccp-complete-epoch"]
        for pattern in ("(fn2-ccp-epoch-fence-p fn2-core)", "(= taken 1)",
                        "(= (fn2-sim-gen slot fn2-sim) gen)",
                        "(= (fn2-sim-kind slot fn2-sim) *fn2-action-fence*)",
                        "(fn2-sim-advance-selected nil nil t slot fault 1 fn2-core fn2-sim fn2-own)"):
            self.assertTrue(lr.match(pattern, [fn]))

    def test_connected_fixture_calls_real_producer_and_post_death_boot(self):
        fixture = functions((ROOT / "tests/checkpoint-cold-path-unit.lisp").read_text())
        producer = fixture["fn2-ccp-prefix-and-publication"]
        self.assertEqual(len(lr.match("(fn2-commit-admit-keyed 1 0 0 0 0 fn2-core)", [producer])), 2)
        self.assertTrue(lr.match("(fn2-ccp-maintenance-entry fn2-core)", [producer]))
        body = fixture["fn2-ccp-body"]
        for pattern in (
            "(fn2-boot-start t *fn2-ccp-image-size* fn2-core)",
            "(fn2-ccp-prefix-and-publication fn2-core fn2-sim fn2-own)",
            "(fn2-ccp-restart *fn2-ccp-profile* *fn2-ccp-image-size* fn2-core fn2-sim fn2-own)",
            "(fn2-ccp-before-open-p prefix suffix fn2-core)",
            "(fn2-ccp-complete-epoch fault fn2-core fn2-sim fn2-own)",
        ):
            self.assertTrue(lr.match(pattern, [body]))

    def test_known_fixture_call_arities_match_actual_source(self):
        paths = ["tests/checkpoint-cold-path-drive.lisp", "tests/checkpoint-cold-path-unit.lisp",
                 "books/executor.lisp", "books/commit.lisp", "sim/check-recovery.lisp",
                 "sim/sim.lisp", "sim/sim-adapter-base.lisp", "sim/check-own.lisp", "sim/sim-state.lisp"]
        known = {}
        for path in paths:
            for fn in functions((ROOT / path).read_text()).values():
                args = fn.items[2]
                if isinstance(args, lr.Lst) and all(isinstance(a, lr.Atom) and not a.low.startswith('&') for a in args.items):
                    known[fn.items[1].low] = len(args.items)
        checked = 0
        for path in paths[:2]:
            for call in lr.match("(?head ?*args)", list(functions((ROOT / path).read_text()).values())):
                head = call.node.items[0]
                if isinstance(head, lr.Atom) and head.low in known:
                    self.assertEqual(len(call.node.items)-1, known[head.low], head.low)
                    checked += 1
        self.assertGreater(checked, 20)

    def test_success_and_failure_assert_raw_allocator_and_lease_outcomes(self):
        forms = lr.parse((ROOT/'tests/checkpoint-cold-path-unit.lisp').read_text()).forms
        assertions = lr.match('(assert-event ?body)', forms, deep=False)
        self.assertEqual(len(assertions), 2)
        for assertion, fault, phase, begun in zip(assertions,
                ['*fn2-fault-none*', '*fn2-fault-flush-io*'], [0, 4], [1, 0]):
            fn = assertion.node
            for pattern in [f'(fn2-ccp-test {fault})', f'(= (nth 0 facts) {phase})',
                            f'(= (nth 1 facts) {begun})', '(= (len facts) 6)',
                            '(< (+ 1 (nth 3 result)) (nth 4 result))']:
                self.assertTrue(lr.match(pattern, [fn]), pattern)
        for pattern in ['(eq (cadr result) :failed)', '(eq (nth 3 facts) :ok)',
                        '(= (nth 2 facts) (nth 5 facts))']:
            self.assertTrue(lr.match(pattern, [assertions[1].node]), pattern)


if __name__ == "__main__":
    unittest.main()
