"""Actual resident release extraction and owner controls; no ACL2 execution."""
from pathlib import Path
import unittest

import lisp_rewrite as lr
import seal_release_row_rewrite as rw
import seal_release_held_rewrite as held

ROOT = Path(__file__).resolve().parents[1]
BEFORE = ROOT / 'tools/fixtures/seal-release-before.lisp'
SEALER = ROOT / 'books/sealer.lisp'


def form(source, pattern):
    matches = lr.match(pattern, lr.parse(source).forms, deep=False)
    if len(matches) != 1:
        raise ValueError(f'expected one {pattern}')
    return matches[0].node


def tree(node):
    if hasattr(node, 'low'):
        return node.low
    if hasattr(node, 'prefix'):
        return (node.prefix, tree(node.node))
    return tuple(tree(x) for x in node.items)


def check_release(source):
    row = form(source, '(defun fn2-seal-release-row ?*body)')
    wrapper = form(source, '(defun fn2-seal-release ?*body)')
    install = form(source, '(defun fn2-seal-install-run ?*body)')
    installed_provenance = ('(fn2-run-install r ?*before '
                            '(fn2-seals-okind 0 fn2-seals) '
                            '(fn2-seals-oslot 0 fn2-seals) '
                            '(fn2-seals-ogen 0 fn2-seals) fn2-run-installed)')
    if not lr.match(installed_provenance, [install]):
        raise ValueError('installed row no longer stores the run workspace owner')
    if [x.low for x in row.items[2].items] != [
            'r', 'fn2-run-installed', 'fn2-run-cache', 'fn2-pool']:
        raise ValueError('row API must take the actual cursor without sealer owner')
    for pattern in [
        '(natp r)', '(< r (fn2-run-installed-rows fn2-run-installed))',
        '(= (fn2-run-installed-state r fn2-run-installed) *fn2-run-installed-state-retired*)',
        '(= (fn2-run-installed-physical r fn2-run-installed) 1)',
        '(fn2-run-installed-ufirst r fn2-run-installed)',
        '(fn2-run-installed-ulast r fn2-run-installed)',
        '(fn2-run-cache-peek (nfix u) fn2-run-cache)',
        '(fn2-run-cache-drop (nfix u) fn2-run-cache)',
        '(fn2-pool-release-countp slot fn2-pool)',
        '(fn2-run-retired-next r fn2-run-installed)',
    ]:
        if len(lr.match(pattern, [row])) != 1:
            raise ValueError(f'actual row release lost {pattern}')
    peek = lr.match('(fn2-run-cache-peek ?*args)', [row])[0]
    drop = lr.match('(fn2-run-cache-drop ?*args)', [row])[0]
    count = lr.match('(fn2-pool-release-countp ?*args)', [row])[0]
    release = lr.match('(fn2-pool-release ?*args)', [row])
    next_row = lr.match('(fn2-run-retired-next ?*args)', [row])[0]
    physical = lr.match('(= (fn2-run-installed-physical r fn2-run-installed) 1)', [row])[0]
    accepted = lr.match('(or (eq released :ok) (eq released :retired))', [row])
    if len(release) != 1 or len(accepted) != 1 or not (
            physical.start < peek.start < count.start < release[0].start
            < accepted[0].start < drop.start < next_row.start):
        raise ValueError('bounded release effect order or physical fence changed')
    expected_release = ('(fn2-pool-release slot gen '
                        '(fn2-run-installed-okind r fn2-run-installed) '
                        '(fn2-run-installed-oslot r fn2-run-installed) '
                        '(fn2-run-installed-ogen r fn2-run-installed) fn2-pool)')
    if not lr.match(expected_release, [row]):
        raise ValueError('pool release must use installed-row owner')
    if lr.match('(fn2-seals-okind ?*args)', [row]) or lr.match('(fn2-seals-oslot ?*args)', [row]):
        raise ValueError('row release still reads mutable global sealer owner')
    if lr.match('(fn2-seal-retired-row ?*args)', [row]):
        raise ValueError('row release performs whole installed scan')
    if not lr.match('((unless (or (eq released :ok) (eq released :retired))) '
                    '(mv released fn2-run-cache fn2-pool))', [row]):
        raise ValueError('held or credit refusal must retain cache and row')
    if not lr.match('(fn2-seal-retired-row rows 0 fn2-run-installed)', [wrapper]):
        raise ValueError('ordinary sealer lost retired-row selection')
    if not lr.match('(fn2-seals-set-phase 0 *fn2-seal-phase-idle* fn2-seals)', [wrapper]):
        raise ValueError('ordinary sealer lost idle transition')
    if not lr.match('(fn2-seal-release-row r fn2-run-installed fn2-run-cache fn2-pool)', [wrapper]):
        raise ValueError('ordinary sealer bypasses bounded helper')
    if lr.match('(fn2-run-cache-drop ?*args)', [wrapper]) or lr.match('(fn2-pool-release ?*args)', [wrapper]):
        raise ValueError('ordinary sealer retains duplicate resident effects')


class Source(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.before = BEFORE.read_text()
        cls.actual = SEALER.read_text()

    def test_original_operation_extracts_exact_current_functions(self):
        overlay = '\n'.join(held.BEFORE['books/sealer.lisp'][pattern]
                            for pattern in ('(defun fn2-seal-retire ?*body)',
                                            '(fn2-seal-shape fn2-seal-retire ?*body)'))
        callers = '\n'.join(held.BEFORE['books/sealer.lisp'][pattern]
                            for pattern in held.CALLERS)
        expected, count = held.transform('books/sealer.lisp',
                                         overlay + '\n' + callers + '\n' + rw.transform(self.before))
        self.assertEqual(count, 6)
        for pattern in ['(defun fn2-seal-release-row ?*body)',
                        '(defun fn2-seal-release ?*body)',
                        '(fn2-seal-shape fn2-seal-release-row ?*body)',
                        '(fn2-seal-shape fn2-seal-release ?*body)']:
            self.assertEqual(tree(form(self.actual, pattern)), tree(form(expected, pattern)), pattern)

    def test_actual_bounded_release_and_owner(self):
        check_release(self.actual)

    def test_global_owner_mutation_refused(self):
        mutated = self.actual.replace('(fn2-run-installed-okind r fn2-run-installed)',
                                      '(fn2-seals-okind 0 fn2-seals)', 1)
        with self.assertRaisesRegex(ValueError, 'installed-row owner'):
            check_release(mutated)

    def test_physical_fence_mutation_refused(self):
        mutated = self.actual.replace('(= (fn2-run-installed-physical r fn2-run-installed) 1)',
                                      'nil', 1)
        with self.assertRaises(ValueError):
            check_release(mutated)

    def test_reintroduced_scan_refused(self):
        mutated = self.actual.replace('(u (fn2-run-installed-ufirst r fn2-run-installed))',
                                      '(u (fn2-seal-retired-row 1 r fn2-run-installed))', 1)
        with self.assertRaisesRegex(ValueError, 'ufirst|whole installed scan'):
            check_release(mutated)

    def test_old_owner_operation_fixture_is_prepared(self):
        source = (ROOT / 'tests/seal-release-row-owner-unit.lisp').read_text()
        forms = lr.parse(source).forms
        body = form(source, '(defun fn2-srr-owner-body ?*body)')
        for pattern in [
            '(fn2-pool-reserve 0 1 10 3 fn2-pool)',
            '(fn2-seals-put 0 ?*before (okind 2) (oslot 11) (ogen 4) ?*after)',
            '(fn2-pool-release slot-0 gen-0 (fn2-seals-okind 0 fn2-seals) '
            '(fn2-seals-oslot 0 fn2-seals) (fn2-seals-ogen 0 fn2-seals) fn2-pool)',
            '(fn2-seal-release-row 0 fn2-run-installed fn2-run-cache fn2-pool)',
            '(fn2-seal-release fn2-seals fn2-run-installed fn2-run-cache fn2-pool)',
        ]:
            self.assertTrue(lr.match(pattern, [body]), pattern)
        self.assertEqual(len(lr.match('(assert-event ?*body)', forms, deep=False)), 1)


if __name__ == '__main__':
    unittest.main()
