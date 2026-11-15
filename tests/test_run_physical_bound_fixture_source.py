"""Source controls for the unexecuted actual bound-engine fixture."""
import copy
from pathlib import Path
import sys
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
from lisp_source import forms, read_sexp
ROOT = Path(__file__).resolve().parents[1]
TEXT = (ROOT / 'tests/run-physical-bound-unit.lisp').read_text()
FORMS = [read_sexp(t) for t in forms(TEXT)]


def walk(node):
    if isinstance(node, list):
        yield node
        for child in node:
            yield from walk(child)


def calls(node):
    return [n[0] for n in walk(node) if n and isinstance(n[0], str)]


def definitions(path=None):
    parsed = FORMS if path is None else [read_sexp(t) for t in forms((ROOT / path).read_text())]
    return {n[1]: n for top in parsed for n in walk(top)
            if len(n) > 2 and n[0] in ('defun', 'fn2-rpb-defun') and isinstance(n[1], str)}


def produced_ref(node):
    fields = [n for n in walk(node) if n and n[0] in [f'hash-{i}' for i in range(8)]]
    return len(fields) == 16 and all('fn2-digest-word' in calls(n) for n in fields[:8]) \
        and all('fn2-run-load-word' in calls(n) for n in fields[8:])


class PhysicalBoundFixture(unittest.TestCase):
    def setUp(self):
        self.defs = definitions()

    def test_local_production_stobjs_have_no_core_or_model_twin(self):
        state = next(n for n in FORMS if n and n[:2] == ['defconst', '*fn2-rpb-stobjs*'])[2][1]
        self.assertEqual(len(state), 16)
        self.assertEqual(len(set(state)), 16)
        self.assertTrue(all(n.startswith('fn2-') for n in state))
        self.assertNotIn('defcolumns', calls(FORMS))
        self.assertNotIn('defstobj', calls(FORMS))
        self.assertFalse(any(n.startswith('fn2-core-') for n in calls(FORMS)))
        for forbidden in ['../books/executor', '../books/assembly', '../books/run-physical-io']:
            self.assertNotIn('"' + forbidden + '"', TEXT)
        for n in walk(FORMS):
            if n and n[0] == 'fn2-rpb-mv':
                self.assertLessEqual(len(n) - 1 + len(state), 32)
        for n in FORMS:
            if n and n[0] == 'fn2-rpb-defun':
                for binding in walk(n[3]):
                    if binding and binding[0] == 'mv':
                        self.assertLessEqual(len(binding) - 1, 32)

    def test_same_actual_engine_and_observer_are_used_by_served_wrappers(self):
        self.assertIn('fn2-run-bound-issue', calls(self.defs['fn2-rpb-issue']))
        self.assertIn('fn2-run-bound-step', calls(self.defs['fn2-rpb-step']))
        self.assertIn('fn2-run-load-harvest', calls(self.defs['fn2-rpb-complete']))
        issue = definitions('books/run-physical-io.lisp')['fn2-run-load-issue']
        step = definitions('books/run-physical-step.lisp')['fn2-run-load-step']
        self.assertIn('fn2-run-bound-issue', calls(issue))
        self.assertIn('fn2-run-bound-step', calls(step))
        self.assertIn('fn2-run-load-sourcep', calls(issue))
        self.assertIn('fn2-run-load-sourcep', calls(step))
        self.assertIn('SYNTHETIC premises', TEXT)

    def test_real_producer_hashes_bind_all_words_and_corrupt_reference_is_independent(self):
        for fixture, actual in [('fn2-rpb-open', 'fn2-run-open'), ('fn2-rpb-seal-drive', 'fn2-run-seal-step'),
                                ('fn2-rpb-check', 'fn2-format-drive'), ('fn2-rpb-decoded', 'fn2-run-nth')]:
            self.assertIn(actual, calls(self.defs[fixture]))
        binding = self.defs['fn2-rpb-synthetic-bind']
        self.assertTrue(produced_ref(binding))
        damaged = copy.deepcopy(binding)
        for n in walk(damaged):
            if n and n[0] == 'fn2-digest-word':
                n[0] = 'unchecked-expected-word'
        self.assertFalse(produced_ref(damaged))
        self.assertIn('logxor', calls(binding))
        self.assertIn('fn2-run-load-boundp', calls(binding))
        for n in walk(binding):
            if n and n[0] == 'phase':
                self.assertNotIn('*fn2-run-load-phase-ready*', str(n))
                self.assertNotIn('*fn2-run-cursor-phase-header*', str(n))

    def test_completion_observes_validated_generation_before_handback_hooks_finish(self):
        complete = self.defs['fn2-rpb-complete']
        bstar = next(n for n in walk(complete) if n and n[0] == 'b*')
        names = ['fn2-outbox-peek', 'fn2-rpb-input-copy', 'fn2-outbox-ack', 'fn2-harvest-next',
                 'fn2-op-cell', 'fn2-pool-complete-in', 'fn2-b-read-pin-harvest', 'fn2-run-load-harvest', 'fn2-op-finish']
        positions = [next(i for i, n in enumerate(bstar[1]) if name in calls(n)) for name in names]
        self.assertEqual(positions, sorted(positions))
        for name in ['fn2-alloc-edge-matchesp', 'fn2-extents-outstanding-io', 'fn2-pool-input-code',
                     'fn2-pool-workspace-code', 'fn2-run-load-ops-live']:
            self.assertIn(name, calls(complete))
        bytecopy = self.defs['fn2-rpb-input-copy']
        self.assertIn('fn2-pool-read', calls(bytecopy))
        self.assertIn('fn2-pool-adapter-write', calls(bytecopy))
        core = definitions('books/core.lisp')['fn2-harvest-one']
        self.assertIn('fn2-harvest-next', calls(core))
        self.assertIn('fn2-pool-complete-in', calls(core))
        self.assertIn('fn2-core-harvest-hooks', calls(core))
        self.assertIn('fn2-op-finish', calls(core))

    def test_sixteen_reads_and_observed_verifier_header_precede_exposure(self):
        body = self.defs['fn2-rpb-body']
        for name in ['fn2-rpb-check', 'fn2-rpb-synthetic-bind', 'fn2-rpb-drive', 'fn2-rpb-decoded']:
            self.assertIn(name, calls(body))
        text = str(body)
        self.assertIn("['=', 'reads', '*fn2-storage-extent-units*']", text)
        self.assertIn('*fn2-run-load-phase-uncertain*', text)
        self.assertIn('*fn2-run-cursor-phase-miss*', text)
        self.assertIn('*fn2-none*', text)
        self.assertIn('*fn2-run-load-phase-ready*', text)
        self.assertIn('*fn2-run-cursor-phase-header*', text)
        self.assertIn('saw-header', text)
        drive = self.defs['fn2-rpb-drive']
        self.assertIn('fn2-rpb-complete', calls(drive))
        self.assertIn('*fn2-run-load-phase-header*', str(drive))
        self.assertNotIn('fn2-run-loads-set-phase', calls(drive))
        self.assertNotIn('fn2-run-cursors-set-phase', calls(drive))
        self.assertIn('(assert-event (fn2-rpb-test nil))', TEXT)
        self.assertIn('(assert-event (fn2-rpb-test t))', TEXT)
        self.assertNotIn('fn2-run-cache-install', calls(FORMS))


if __name__ == '__main__':
    unittest.main()
