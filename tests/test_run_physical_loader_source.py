"""Actual source boundary controls; no ACL2 execution or physical I/O claim."""
from pathlib import Path
import sys
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
from lisp_source import forms, read_sexp
ROOT = Path(__file__).resolve().parents[1]
FILES = tuple(ROOT / 'books' / ('run-physical-' + n + '.lisp')
              for n in ('state', 'resources', 'bound', 'bound-bind', 'source', 'harvest', 'bound-io', 'io', 'bound-step', 'step', 'release'))

def walk(x):
    if isinstance(x, list):
        yield x
        for v in x:
            yield from walk(v)

def definitions():
    return {f[1]: f for p in FILES for raw in forms(p.read_text())
            if isinstance((f := read_sexp(raw)), list) and f and f[0] == 'defun'}

def calls(f, op):
    return [x for x in walk(f[3:]) if x and x[0] == op]

def has_equality(f, lhs, rhs):
    return any(x == ['equal', lhs, rhs] for x in walk(f))

def exact_hook(f):
    return all(has_equality(f, a, b) for a, b in (
        (['fn2-run-load-ops-generation', 'opslot', 'fn2-run-load-ops'], 'opgen'),
        (['fn2-run-loads-op-slot', 'c', 'fn2-run-loads'], 'opslot'),
        (['fn2-run-loads-op-gen', 'c', 'fn2-run-loads'], 'opgen'),
        ('cell', '0'), ('evkind', '*fn2-event-read-result*'),
        ('outcome', '*fn2-outcome-done*'), ('count', '*fn2-commit-unit-bytes*')))

class PhysicalLoaderSource(unittest.TestCase):
    def setUp(self):
        self.d = definitions()

    def implementation(self, name):
        wrapper = self.d[name]
        lower = name.replace('fn2-run-load-', 'fn2-run-bound-')
        self.assertEqual(len(calls(wrapper, 'fn2-run-load-sourcep')), 1)
        call = calls(wrapper, lower)
        self.assertEqual(len(call), 1)
        self.assertEqual(call[0][1:], self.d[lower][2])
        self.assertEqual(len(calls(self.d[lower], 'fn2-run-load-boundp')), 1)
        return self.d[lower]

    def test_only_explicit_issue_queues_one_unit(self):
        issue = self.implementation('fn2-run-load-issue')
        reads = calls(issue, 'fn2-block-read-children')
        self.assertEqual(len(reads), 1)
        self.assertEqual(reads[0][4:6], ['0', '*fn2-commit-unit-bytes*'])
        self.assertFalse(calls(self.implementation('fn2-run-load-step'), 'fn2-block-read-children'))
        self.assertFalse(calls(issue, 'fn2-run-load-issue'))
        self.assertIn(['<', ['fn2-run-loads-sector', 'c', 'fn2-run-loads'],
                       '*fn2-storage-extent-units*'], list(walk(issue)))

    def test_completion_exact_and_stale_generation_control(self):
        f = self.d['fn2-run-load-harvest']
        self.assertTrue(exact_hook(f))
        self.assertFalse(calls(f, 'fn2-pool-read'))
        mutated = str(f).replace('fn2-run-loads-op-gen', 'DROPPED-op-gen')
        self.assertNotEqual(mutated, str(f))
        import copy
        bad = copy.deepcopy(f)
        for x in walk(bad):
            if x and x[0] == 'fn2-run-loads-op-gen':
                x[0] = 'DROPPED-op-gen'
        self.assertFalse(exact_hook(bad))

    def test_full_reference_and_owner_survive_yield(self):
        source = self.d['fn2-run-load-sourcep']
        self.assertEqual(calls(source, 'fn2-run-load-boundp'),
                         [['fn2-run-load-boundp', 'c', 'fn2-run-loads', 'fn2-run-cursors']])
        f = self.d['fn2-run-load-boundp']
        for load, cursor in (('unit', 'unit'), ('epoch', 'epoch'), ('allocation', 'counter'),
                             ('schema', 'schema'), ('run', 'run'), ('level', 'level'),
                             ('kind', 'okind'), ('owner', 'oslot'), ('generation', 'ogen'),
                             ('source', 'source-row'), ('tag', 'catalog-tag')):
            self.assertTrue(has_equality(f, ['fn2-run-loads-' + load, 'c', 'fn2-run-loads'],
                                         ['fn2-run-cursors-' + cursor, 'c', 'fn2-run-cursors']))
        self.assertEqual(len(calls(f, 'fn2-run-load-hash-current-p')), 1)
        self.assertEqual(len(calls(source, 'fn2-checkpoint-summary-lease-current-p')), 1)
        self.assertTrue(calls(self.d['fn2-run-load-bind'], 'fn2-checkpoint-summary-acquire'))
        self.assertTrue(calls(self.d['fn2-run-load-bind'], 'fn2-checkpoint-summary-release'))

    def test_verifier_and_real_decoder_precede_exposure(self):
        f = self.implementation('fn2-run-load-step')
        self.assertEqual(len(calls(f, 'fn2-format-run')), 1)
        verify = calls(f, 'fn2-format-run')[0]
        self.assertEqual(verify[1:3], [':page', 'nil'])
        self.assertEqual(len(calls(f, 'fn2-checkpoint-semantic-page-read-header')), 1)
        writes = calls(f, 'fn2-run-cursors-put')
        self.assertEqual(len(writes), 1)
        self.assertIn(['phase', '*fn2-run-cursor-phase-header*'], writes[0])
        self.assertFalse(calls(f, 'fn2-run-cache-install'))
        context = calls(f, 'fn2-fc-context-put')[0]
        for field in ('location', 'writer-epoch', 'allocation', 'history', 'incarnation',
                      'page-kind', 'encoded-length', 'hash', 'geometry'):
            self.assertTrue(any(isinstance(x, list) and x[0] == field for x in context))

    def test_all_or_refuse_and_pending_before_release(self):
        f = self.d['fn2-run-load-reserve']
        self.assertIn(['<=', '2', ['fn2-pool-class-countsi', 'pc', 'fn2-pool']], list(walk(f)))
        self.assertEqual(len(calls(f, 'fn2-pool-reserve')), 2)
        self.assertEqual(len(calls(f, 'fn2-pool-release')), 1)
        self.assertEqual(len(calls(f, 'fn2-run-load-admission-begin')), 1)
        source = (ROOT / 'books/run-physical-resources.lisp').read_text()
        self.assertLess(source.index('(fn2-run-load-admission-begin fn2-run-loads)'), source.index('(fn2-pool-reserve pc'))
        begin = self.d['fn2-run-load-admission-begin']
        self.assertEqual(len(calls(begin, 'update-fn2-run-loads-admissions')), 1)
        self.assertIn(['unsigned-byte-p', '60', 'next'], list(walk(begin)))
        release = self.d['fn2-run-load-release']
        self.assertTrue(has_equality(release, ['fn2-run-loads-pending', 'c', 'fn2-run-loads'], '0'))
        self.assertEqual(len(calls(release, 'fn2-pool-workspace-code')), 2)
        self.assertTrue(has_equality(release, ['fn2-run-loads-lease-mode', 'c', 'fn2-run-loads'], '*fn2-run-load-lease-mode-owned*'))
        self.assertEqual(len(calls(release, 'fn2-pool-release')), 2)
        self.assertEqual(len(calls(release, 'fn2-checkpoint-summary-release')), 1)
        accepted = [x for x in calls(release, 'member-eq') if x[1] == 'code']
        self.assertEqual(len(accepted), 2)
        self.assertTrue(all(x[2] == ['quote', [':ok', ':retired']] for x in accepted))

    def test_source_park_keeps_bytes_but_drops_exact_catalog_lease(self):
        f = self.d['fn2-run-load-park-source']
        self.assertTrue(has_equality(f, ['fn2-run-loads-lease-mode', 'c', 'fn2-run-loads'], '*fn2-run-load-lease-mode-owned*'))
        self.assertTrue(has_equality(f, ['fn2-run-loads-pending', 'c', 'fn2-run-loads'], '0'))
        self.assertEqual(len(calls(f, 'fn2-pool-workspace-code')), 2)
        self.assertEqual(len(calls(f, 'fn2-checkpoint-summary-release')), 1)
        self.assertFalse(calls(f, 'fn2-pool-release'))
        self.assertFalse(calls(f, 'fn2-pool-reset'))
        self.assertFalse(calls(f, 'fn2-pool-write'))

    def test_return_frames_match_actual_mutations_and_mv_limit(self):
        frames = {f[1]: f for p in FILES for raw in forms(p.read_text())
                  if isinstance((f := read_sexp(raw)), list) and f and f[0] == 'fn2-run-load-frames'}
        for name, frame in frames.items():
            f = (self.implementation(name) if name in ('fn2-run-load-issue', 'fn2-run-load-step') else self.d[name])
            outputs = {o[0] for o in frame[4]}
            assigned = set()
            for x in walk(f[3:]):
                if x and x[0] in ('b*', 'let', 'let*'):
                    for binding in x[1]:
                        left = binding[0]
                        names = left[1:] if isinstance(left, list) and left and left[0] == 'mv' else [left]
                        assigned.update(n for n in names if isinstance(n, str) and n.startswith('fn2-'))
            self.assertEqual(outputs, assigned, name)
            self.assertLessEqual(max(int(o[1]) for o in frame[4]) + 1, 32)
        self.assertEqual(set(frames), {'fn2-run-load-reserve', 'fn2-run-load-bind', 'fn2-run-bound-bind',
            'fn2-run-load-issue', 'fn2-run-bound-issue', 'fn2-run-load-harvest',
            'fn2-run-load-step', 'fn2-run-bound-step', 'fn2-run-load-release', 'fn2-run-load-park-source'})

if __name__ == '__main__':
    unittest.main()
