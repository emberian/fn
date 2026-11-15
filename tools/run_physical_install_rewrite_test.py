"""Source controls for the counted physical-run constructor; no ACL2 evaluation."""
from pathlib import Path
import unittest

import lisp_rewrite as lr
import run_physical_install_rewrite as rw

ROOT = Path(__file__).resolve().parents[1]
BEFORE = ROOT / 'tools/fixtures/run-physical-install-before.lisp'


def function(source, name):
    matches = lr.match(f'(defun {name} ?*body)', lr.parse(source).forms, deep=False)
    if len(matches) != 1:
        raise ValueError(f'expected one {name}')
    return matches[0].node


def tree(node, env=None):
    """Structural comparison with constructor arguments substituted at call site."""
    env = env or {}
    if isinstance(node, lr.Atom):
        return env.get(node.low, node.low)
    if isinstance(node, lr.Pre):
        return (node.prefix, tree(node.node, env))
    return tuple(tree(item, env) for item in node.items)


def fields(call):
    return {entry.items[0].low: entry.items[1] for entry in call.items[2:]}


def check_full_substitution(before, runs, apply):
    old_write, old_fields = rw.extract(before)
    constructor = function(runs, 'fn2-run-install-physical')
    actual_apply = function(apply, 'fn2-checkpoint-summary-apply-step')
    old_apply = function(rw.transform_apply(before), 'fn2-checkpoint-summary-apply-step')
    # The whole actual apply body must be the source transform of the old body.
    if tree(actual_apply) != tree(old_apply):
        raise ValueError('actual apply differs from old write extraction')
    calls = lr.match('(fn2-run-install-physical ?*args)', [actual_apply])
    if len(calls) != 1:
        raise ValueError('actual apply must call constructor once')
    if lr.match('(fn2-run-installed-put ?*args)', [actual_apply]):
        raise ValueError('apply retains direct installed-row write')
    params = constructor.items[2].items
    args = calls[0].node.items[1:]
    if len(params) != len(args):
        raise ValueError('constructor call arity changed')
    env = {param.low: tree(arg) for param, arg in zip(params, args)}
    writes = lr.match('(fn2-run-installed-put r ?*fields)', [constructor])
    if len(writes) != 1:
        raise ValueError('constructor must write one installed row')
    actual_fields = fields(writes[0].node)
    if set(actual_fields) != set(old_fields):
        raise ValueError('installed-row field set changed')
    for name in old_fields:
        if tree(actual_fields[name], env) != tree(old_fields[name].items[1]):
            raise ValueError(f'installed-row field {name} differs')
    if tree(writes[0].node.items[1], env) != tree(old_write.items[1]):
        raise ValueError('installed-row index differs')


def check_transition_class(runs, apply, retire):
    forms = lr.parse(runs).forms
    names = ('fn2-run-install-physical', 'fn2-run-install', 'fn2-run-retire',
             'fn2-run-free-physical', 'fn2-run-retired-next')
    transitions = {name: function(runs, name) for name in names}
    updates = lr.match('(update-fn2-run-installed-physical-count ?*args)', forms)
    if len(updates) != 2:
        raise ValueError('physical count must have exactly two write sites')
    expected = {
        'fn2-run-install-physical': '(update-fn2-run-installed-physical-count count fn2-run-installed)',
        'fn2-run-free-physical': '(update-fn2-run-installed-physical-count (- count 1) fn2-run-installed)',
    }
    for name, pattern in expected.items():
        if len(lr.match(pattern, [transitions[name]])) != 1:
            raise ValueError(f'{name} must own its scalar update')
    for name in names:
        if name not in expected and lr.match('(update-fn2-run-installed-physical-count ?*args)', [transitions[name]]):
            raise ValueError(f'{name} changes physical count')
        if lr.match('(fn2-run-physical-rows-from ?*args)', [transitions[name]]):
            raise ValueError(f'{name} performs served whole-row scan')
    writes = lr.match('(fn2-run-installed-put r ?*fields)', forms)
    physical = [entry for write in writes for entry in write.node.items[2:]
                if entry.items[0].low == 'physical']
    if sorted(tree(entry) for entry in physical) != sorted((('physical', '0'), ('physical', '0'), ('physical', '1'))):
        raise ValueError('physical marker has an uncounted write site')
    if len(lr.match('(fn2-run-installed-put r (state *fn2-run-installed-state-retired*) ?*fields)',
                    [transitions['fn2-run-retire']])) != 1:
        raise ValueError('retire must retain physical marker')
    if not lr.match('(= (fn2-run-installed-state r fn2-run-installed) *fn2-run-installed-state-retired*)',
                    [transitions['fn2-run-free-physical']]):
        raise ValueError('physical free must require retired row')
    if not lr.match('(= (fn2-run-installed-physical r fn2-run-installed) 1)',
                    [transitions['fn2-run-free-physical']]):
        raise ValueError('physical free must require physical row')
    if not lr.match('(unsigned-byte-p 32 count)', [transitions['fn2-run-install-physical']]):
        raise ValueError('missing count overflow fence')
    if not lr.match('(posp count)', [transitions['fn2-run-free-physical']]):
        raise ValueError('missing count underflow fence')
    if not lr.match('(= (fn2-run-installed-physical r fn2-run-installed) 0)', [transitions['fn2-run-install']]):
        raise ValueError('resident install can occupy physical free row')
    if not lr.match('((when (= (fn2-run-installed-physical r fn2-run-installed) 1)) (mv :physical fn2-run-installed))',
                    [transitions['fn2-run-retired-next']]):
        raise ValueError('retired-next can free physical row')
    model = function(runs, 'fn2-run-physical-count-consistent-p')
    if not lr.match('(fn2-run-physical-rows-from (fn2-run-installed-rows fn2-run-installed) 0 fn2-run-installed)', [model]):
        raise ValueError('logical model must sum full installed-row range')
    if lr.match('(fn2-run-physical-rows-from ?*args)', [function(apply, 'fn2-checkpoint-summary-apply-step')]):
        raise ValueError('served apply uses logical scan')
    retired = function(retire, 'fn2-checkpoint-summary-retire-row')
    if not lr.match('(fn2-run-free-physical r fn2-run-installed)', [retired]):
        raise ValueError('retirement bypasses counted free')
    if lr.match('(fn2-run-installed-put ?*args)', [retired]):
        raise ValueError('retirement writes installed row directly')


class Source(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.before = BEFORE.read_text()
        cls.runs = (ROOT / 'books/runs.lisp').read_text()
        cls.apply = (ROOT / 'books/checkpoint-summary-apply.lisp').read_text()
        cls.retire = (ROOT / 'books/checkpoint-summary-retire.lisp').read_text()

    def test_full_original_write_substitution(self):
        check_full_substitution(self.before, self.runs, self.apply)

    def test_nonfree_physical_transition_class(self):
        check_transition_class(self.runs, self.apply, self.retire)

    def test_installed_row_writes_have_one_book(self):
        owners = [path.name for path in (ROOT / 'books').glob('*.lisp')
                  if 'fn2-run-installed-put' in path.read_text()
                  or 'update-fn2-run-installed-physical-count' in path.read_text()]
        self.assertEqual(owners, ['runs.lisp'])

    def test_changed_hash_field_refused(self):
        mutated = self.runs.replace('(hash-7 hash-7)', '(hash-7 hash-6)', 1)
        with self.assertRaisesRegex(ValueError, 'hash-7'):
            check_full_substitution(self.before, mutated, self.apply)

    def test_lost_scalar_update_refused(self):
        mutated = self.runs.replace('(update-fn2-run-installed-physical-count count fn2-run-installed)',
                                    'fn2-run-installed', 1)
        with self.assertRaises(ValueError):
            check_transition_class(mutated, self.apply, self.retire)

    def test_removed_retired_next_fence_refused(self):
        mutated = self.runs.replace('((when (= (fn2-run-installed-physical r fn2-run-installed) 1)) (mv :physical fn2-run-installed))',
                                    '((when nil) (mv :physical fn2-run-installed))', 1)
        with self.assertRaises(ValueError):
            check_transition_class(mutated, self.apply, self.retire)


if __name__ == '__main__':
    unittest.main()
