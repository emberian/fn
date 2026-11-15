"""Source-only cold payload composition controls, without Lisp evaluation."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
ROOT = Path(__file__).resolve().parents[1]
OPS = {
 'fn2-boot-checkpoint-payload-begin': (['code'], ['fn2-checkpoint-payload','fn2-checkpoint-restore-reach','fn2-fields','fn2-b3','fn2-digests']),
 'fn2-boot-checkpoint-payload-target': (['code','offset','len'], ['fn2-checkpoint-payload','fn2-checkpoint-restore-reach']),
 'fn2-boot-checkpoint-payload-loaded': (['code'], ['fn2-checkpoint-payload']),
 'fn2-boot-checkpoint-payload-step': (['code'], ['fn2-checkpoint-restore-semantic','fn2-checkpoint-payload','fn2-checkpoint-restore-reach','fn2-fields','fn2-b3','fn2-digests']),
}
def projection_check(source):
    forms = lr.parse(source).forms
    for name, expected in OPS.items():
        fn = lr.match(f'(defun {name} ?*body)', forms)[0].node
        call = lr.match('(fn2-boot-cold-payload-bind ?scalars ?outputs ?body)', [fn])[0]
        got = ([x.low for x in call.captures['scalars'].items], [x.low for x in call.captures['outputs'].items])
        if got != expected or sum(map(len, got)) > 32:
            raise ValueError(f'{name}: incorrect actual mutable result projection')
def phase_check(source):
    machine = lr.match('(defmachine fn2-boot ?*body)', lr.parse(source).forms, deep=False)[0].node
    props = {machine.items[i].low: machine.items[i+1] for i in range(2, len(machine.items), 2)}
    states = [x.low for x in props[':states'].items]
    arms = [x.items[0].low for x in props[':arms'].items]
    if states != arms:
        raise ValueError('phase/arm registration differs')
    holds = {x.items[0].low: [a.low for a in x.items[1:]] for x in props[':holds'].items}
    for suffix in ('begin','load','copy','step'):
        phase = ':checkpoint-payload-' + suffix
        if phase not in states or holds.get(phase) != [':storage-window']:
            raise ValueError('missing actual owned-window custody')
def resumed_tuple_check(source):
    forms = lr.parse(source).forms
    fn = lr.match('(defun fn2-boot-checkpoint-payload-bound-p ?*body)', forms)[0].node
    # Compare actual predicates as parsed forms, not a comment/token mention.
    for field, expected in [('mode','*fn2-checkpoint-payload-mode-cold*'),
                            ('owner-kind','*fn2-boot-kind*'), ('owner-slot','id'), ('owner-gen','ogen'),
                            ('manifest-slot','mslot'), ('manifest-gen','mgen'), ('data-slot','dslot'), ('data-gen','dgen')]:
        pattern = f'(equal (fn2-checkpoint-payload-{field} 0 fn2-checkpoint-payload) {expected})'
        if not lr.match(pattern, [fn]):
            raise ValueError('missing resumed payload '+field+' binding')
class Source(unittest.TestCase):
    def test_resumed_boot_tuple_is_bound_before_copy(self):
        src = (ROOT/'books/checkpoint-restore-payload-boot.lisp').read_text()
        resumed_tuple_check(src)
        with self.assertRaises(ValueError):
            resumed_tuple_check(src.replace('(equal (fn2-checkpoint-payload-data-gen 0 fn2-checkpoint-payload) dgen)', 't', 1))
    def test_single_carrier_and_mode_specific_admission(self):
        boot = (ROOT/'books/boot-kind.lisp').read_text()
        resources = (ROOT/'books/checkpoint-metadata-resources.lisp').read_text()
        self.assertEqual(boot.count('(defcorechild fn2-core-checkpoint-payload '), 1)
        self.assertNotIn('(fn2-sealer-child fn2-core-checkpoint-payload ', resources)
        for book, mode in [('checkpoint-payload-state','live'), ('checkpoint-restore-payload','cold')]:
            src = (ROOT/'books'/(book+'.lisp')).read_text()
            self.assertIn('(fn2-checkpoint-payload-rebindablep fn2-checkpoint-payload)', src)
            self.assertIn('(mode *fn2-checkpoint-payload-mode-'+mode+'*)', src)
            self.assertIn('(equal (fn2-checkpoint-payload-mode 0 fn2-checkpoint-payload) *fn2-checkpoint-payload-mode-'+mode+'*)', src)
        harvest = (ROOT/'books/checkpoint-payload-harvest.lisp').read_text()
        self.assertIn('*fn2-checkpoint-payload-mode-live*', harvest)
        self.assertNotIn('(fn2-op-finish ', harvest)
        self.assertNotIn('(fn2-pool-release ', harvest)
    def test_actual_mutable_outputs_and_complete_phase_custody(self):
        projection_check((ROOT/'books/checkpoint-restore-payload-boot.lisp').read_text())
        phase_check((ROOT/'books/boot-kind.lisp').read_text())
    def test_readonly_input_cannot_be_promoted_to_output(self):
        src = (ROOT/'books/checkpoint-restore-payload-boot.lisp').read_text()
        mutant = src.replace('(code) (fn2-checkpoint-payload fn2-checkpoint-restore-reach fn2-fields', '(code) (fn2-checkpoints fn2-checkpoint-payload fn2-checkpoint-restore-reach fn2-fields', 1)
        with self.assertRaises(ValueError): projection_check(mutant)
    def test_missing_hold_refuses(self):
        src = (ROOT/'books/boot-kind.lisp').read_text()
        with self.assertRaises(ValueError): phase_check(src.replace('(:checkpoint-payload-load :storage-window)', '(:checkpoint-payload-load)', 1))
    def test_short_unit_uses_same_acl2_length_for_issue_and_completion(self):
        src = (ROOT/'books/boot.lisp').read_text()
        issue = src[src.index('  (:read :on-refusal'):src.index('  (:read-result\n')]
        result = src[src.index('  (:read-result\n'):src.index('  (:verify :on-refusal')]
        write = src[src.index('  (:write-result\n'):src.index('  (:read :on-refusal')]
        expected = '(if (equal row-stage 10) row-read-length 4096)'
        self.assertIn(expected, issue)
        self.assertIn(expected, result)
        self.assertNotIn(expected, write)
        self.assertIn('((equal row-stage 10) (:next :checkpoint-payload-copy))', result)
    def test_known_actual_function_call_arities(self):
        names = ('checkpoint-restore-payload', 'checkpoint-restore-payload-boot',
                 'checkpoint-payload', 'checkpoint-payload-state', 'checkpoint-payload-io',
                 'checkpoint-payload-physical', 'checkpoint-payload-physical-step',
                 'checkpoint-payload-format', 'checkpoint-payload-harvest', 'checkpoint-restore-semantic',
                 'checkpoint-restore-semantic-work', 'checkpoint-restore-reach', 'payload-workspace')
        parsed = [lr.parse((ROOT/'books'/(name+'.lisp')).read_text()).forms for name in names]
        arities = {}
        for forms in parsed:
            for m in lr.match('(defun ?name ?args ?*body)', forms):
                name, args = m.captures['name'], m.captures['args']
                if isinstance(name, lr.Atom) and isinstance(args, lr.Lst) and all(isinstance(a, lr.Atom) and not a.low.startswith('&') for a in args.items):
                    arities[name.low] = len(args.items)
        checked = 0
        for forms in parsed:
            for m in lr.match('(?*items)', forms):
                items = m.node.items
                if items and isinstance(items[0], lr.Atom) and items[0].low in arities:
                    self.assertEqual(len(items)-1, arities[items[0].low], items[0].low)
                    checked += 1
        self.assertGreater(checked, 20)
    def test_one_shared_physical_engine_and_no_premature_cursor_advance(self):
        src = (ROOT/'books/checkpoint-restore-payload.lisp').read_text()
        self.assertEqual(src.count('(fn2-checkpoint-payload-physical-step budget '), 1)
        self.assertNotIn('(fn2-am-get-', src)
        self.assertNotIn('(fn2-b3-update ', src)
        self.assertIn('(if (eq code :complete)', src)
        self.assertIn('fn2-checkpoint-restore-reach-role-payload-block', src)
        self.assertIn('fn2-checkpoint-restore-payload-current-p', src)
if __name__ == '__main__': unittest.main()
