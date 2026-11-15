"""Source-only controls for actual loader readiness in cold adoption."""
from pathlib import Path
import unittest

import lisp_rewrite as lr
import checkpoint_summary_readiness_rewrite as rw

ROOT = Path(__file__).resolve().parents[1]
BEFORE = {
    'checkpoint-summary-authority-cold.lisp': 'checkpoint-summary-readiness-cold-before.lisp',
    'checkpoint-summary-adoption.lisp': 'checkpoint-summary-readiness-adoption-before.lisp',
    'checkpoint-directory-cold.lisp': 'checkpoint-directory-readiness-before.lisp',
    'event-catalog-cold.lisp': 'event-catalog-readiness-before.lisp',
}


def function(source, name):
    matches = lr.match(f'(defun {name} ?*body)', lr.parse(source).forms)
    if len(matches) != 1:
        raise ValueError(f'expected one {name}')
    return matches[0].node


def normalized(node):
    if hasattr(node, 'low'):
        return node.low
    if hasattr(node, 'prefix'):
        return (node.prefix, normalized(node.node))
    return tuple(normalized(x) for x in node.items)


def call_args(fn, name):
    calls = lr.match(f'({name} ?*args)', [fn])
    if len(calls) != 1:
        raise ValueError(f'{fn.items[1].low} must call {name} once')
    return [x.low for x in calls[0].node.items[1:]]


def check_all_calls(sources):
    definitions = {name: function(sources[file], name)
                   for file, targets in rw.TARGETS.items() for name in targets}
    for file, targets in rw.TARGETS.items():
        for name, callee in targets.items():
            fn = definitions[name]
            formals = [x.low for x in fn.items[2].items]
            if len(formals) != len(set(formals)) or any(x not in formals for x in rw.CHILDREN):
                raise ValueError(f'{name} missing or duplicates readiness child')
            if callee and call_args(fn, callee) != [x.low for x in definitions[callee].items[2].items]:
                raise ValueError(f'{name} call does not match {callee} ABI')
            guards = lr.match('(fn2-run-load-readiness-guard)', [fn])
            if len(guards) != 1:
                raise ValueError(f'{name} lacks actual readiness child guards')
    boot = function(sources['boot.lisp'], 'fn2-boot-recovery-base')
    directory = definitions['fn2-directory-cold-base']
    if call_args(boot, 'fn2-directory-cold-base') != [x.low for x in directory.items[2].items]:
        raise ValueError('boot recovery base mismatches directory ABI')
    bindings = lr.match('(stobj-let ?bindings ?*body)', [boot])[0].captures['bindings']
    bound = [entry.items[0].low for entry in bindings.items]
    if any(x not in bound for x in rw.CHILDREN) or len(bound) != len(set(bound)):
        raise ValueError('boot recovery carrier missing child or duplicates a stobj')


def check_actual_gate(sources):
    helper = function(sources['checkpoint-summary-loader-readiness.lisp'],
                      'fn2-checkpoint-summary-loader-ready-p')
    formals = [x.low for x in helper.items[2].items]
    if formals != ['fn2-checkpoint-selected-source', *rw.CHILDREN]:
        raise ValueError('readiness helper takes an invented identity input')
    exact = ('(fn2-run-load-readiness-complete-current-p '
             '(fn2-checkpoint-selected-source-tag 0 fn2-checkpoint-selected-source) '
             '(fn2-checkpoint-selected-source-generation 0 fn2-checkpoint-selected-source) '
             '(fn2-checkpoint-selected-source-candidate 0 fn2-checkpoint-selected-source) '
             '(fn2-checkpoint-selected-source-owner-kind 0 fn2-checkpoint-selected-source) '
             '(fn2-checkpoint-selected-source-owner-slot 0 fn2-checkpoint-selected-source) '
             '(fn2-checkpoint-selected-source-owner-gen 0 fn2-checkpoint-selected-source) '
             + ' '.join(rw.CHILDREN) + ')')
    if len(lr.match(exact, [helper])) != 1:
        raise ValueError('complete-current identity must come from selected-source row 0')
    adoption = function(sources['checkpoint-summary-authority-cold.lisp'],
                        'fn2-checkpoint-summary-adoption-source-p')
    selected = lr.match('(fn2-checkpoint-selected-source-current-p ?*args)', [adoption])
    projected = lr.match('(= (fn2-checkpoint-selected-source-phase 0 fn2-checkpoint-selected-source) '
                         '*fn2-checkpoint-selected-source-phase-projected*)', [adoption])
    ready = lr.match('(fn2-checkpoint-summary-loader-ready-p ?*args)', [adoption])
    if len(selected) != 1 or len(projected) != 1 or len(ready) != 1:
        raise ValueError('adoption source lost selected/current/projected/readiness join')
    if not (selected[0].start < projected[0].start < ready[0].start):
        raise ValueError('readiness checked before selected source validation')
    if [x.low for x in ready[0].node.items[1:]] != formals:
        raise ValueError('adoption readiness call mismatches helper ABI')
    base = function(sources['checkpoint-directory-cold.lisp'], 'fn2-directory-cold-base')
    full = lr.match('(mv :full 0 0 ?epoch)', [base])
    source = lr.match('(fn2-directory-cold-source-p ?*args)', [base])
    if len(full) != 1 or len(source) != 1 or not full[0].start < source[0].start:
        raise ValueError('full genesis fallback must precede selected readiness')


def check_loader_wrappers(source):
    ready = function(source, 'fn2-checkpoint-summary-loader-ready-p')
    begin = function(source, 'fn2-checkpoint-summary-loader-begin')
    step = function(source, 'fn2-checkpoint-summary-loader-step')
    expected = ['fn2-checkpoint-selected-source', *rw.CHILDREN]
    if [x.low for x in ready.items[2].items] != expected:
        raise ValueError('current predicate has an invented identity input')
    if [x.low for x in begin.items[2].items] != expected:
        raise ValueError('begin has an invented identity input')
    if [x.low for x in step.items[2].items] != ['budget', *rw.CHILDREN]:
        raise ValueError('step has an invented source or ready input')
    complete = lr.match('(fn2-run-load-readiness-complete-current-p ?*args)', [ready])
    begin_calls = lr.match('(fn2-run-load-readiness-begin ?*args)', [begin])
    steps = lr.match('(fn2-run-load-readiness-step ?*args)', [step])
    if len(complete) != 1 or len(begin_calls) != 1 or len(steps) != 1:
        raise ValueError('wrapper must call the real readiness operations once')
    current_args = [normalized(x) for x in complete[0].node.items[1:]]
    begin_args = [normalized(x) for x in begin_calls[0].node.items[1:]]
    if current_args != begin_args or len(current_args) != 6 + len(rw.CHILDREN):
        raise ValueError('begin and current must use identical selected-source identity')
    if begin_args[6:] != list(rw.CHILDREN):
        raise ValueError('begin omits actual readiness child')
    if [normalized(x) for x in steps[0].node.items[1:]] != ['budget', *rw.CHILDREN]:
        raise ValueError('step changes the actual loader step inputs')
    for pattern in [
        '(< 0 (fn2-checkpoint-selected-source-rows fn2-checkpoint-selected-source))',
        '(= (fn2-checkpoint-selected-source-phase 0 fn2-checkpoint-selected-source) '
        '*fn2-checkpoint-selected-source-phase-projected*)',
        '(posp (fn2-checkpoint-selected-source-tag 0 fn2-checkpoint-selected-source))',
        '(posp (fn2-checkpoint-selected-source-generation 0 fn2-checkpoint-selected-source))',
        '(posp (fn2-checkpoint-selected-source-owner-gen 0 fn2-checkpoint-selected-source))',
        '(mv :source fn2-run-load-readiness)',
    ]:
        if not lr.match(pattern, [begin]):
            raise ValueError(f'begin lost selected-source gate {pattern}')
    forms = lr.parse(source).forms
    for name, answers in [
        ('fn2-checkpoint-summary-loader-begin',
         [':source', ':geometry', ':capacity', ':more']),
        ('fn2-checkpoint-summary-loader-step',
         [':yield', ':changed', ':row', ':more', ':bounds', ':operation', ':capacity', ':complete']),
    ]:
        fn = begin if name.endswith('begin') else step
        faces = lr.match(f'(defcost {name}-op ?*body)', forms, deep=False)
        if len(faces) != 1:
            raise ValueError(f'{name} lacks cost face')
        face = faces[0].node
        props = {x.low: face.items[i + 1] for i, x in enumerate(face.items[:-1])
                 if getattr(x, 'low', None) in (':child', ':answers', ':steps', ':bytes', ':descriptors', ':tables')}
        if props[':child'].low != name or [x.low for x in props[':answers'].items] != answers:
            raise ValueError(f'{name} cost answers differ from real codes')
        if [x.low for x in props[':tables'].items] != [
                'fn2-core-' + x.low[4:] for x in fn.items[2].items if x.low != 'budget']:
            raise ValueError(f'{name} cost face omits actual child')
        if (props[':steps'].low, props[':bytes'].low, props[':descriptors'].low) != (
                '*fn2-work-stage*', '0', '0'):
            raise ValueError(f'{name} cost bound changed')


def check_faces_and_preserves(sources):
    for file, targets in rw.TARGETS.items():
        forms = lr.parse(sources[file]).forms
        for name in targets:
            fn = function(sources[file], name)
            args = [x.low for x in fn.items[2].items]
            faces = lr.match(f'(defcost {name}-op ?*body)', forms, deep=False)
            if faces:
                face = faces[0].node
                i = next(i for i, x in enumerate(face.items) if getattr(x, 'low', None) == ':tables')
                tables = [x.low for x in face.items[i + 1].items]
                if tables != ['fn2-core-' + x[4:] for x in args]:
                    raise ValueError(f'{name} cost face omits actual child')
            for form in forms:
                if not getattr(form, 'items', None) or len(form.items) < 4:
                    continue
                if not getattr(form.items[0], 'low', '').endswith('-preserves'):
                    continue
                if getattr(form.items[1], 'low', None) != name:
                    continue
                if [x.low for x in form.items[2].items] != args:
                    raise ValueError(f'{name} preserves signature differs')
                i = next(i for i, x in enumerate(form.items) if getattr(x, 'low', None) == ':hyps')
                hyps = form.items[i + 1]
                for child in rw.CHILDREN:
                    for predicate in (child + 'p', child + '-wfp'):
                        if not lr.match(f'({predicate} {child})', [hyps]):
                            raise ValueError(f'{name} preserves missing {predicate}')


class Source(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.sources = {file: (ROOT / 'books' / file).read_text() for file in rw.TARGETS}
        cls.sources['boot.lisp'] = (ROOT / 'books/boot.lisp').read_text()
        cls.sources['checkpoint-summary-loader-readiness.lisp'] = (
            ROOT / 'books/checkpoint-summary-loader-readiness.lisp').read_text()

    def test_generated_class_matches_current_books(self):
        for file, targets in rw.TARGETS.items():
            before = (ROOT / 'tools/fixtures' / BEFORE[file]).read_text()
            self.assertEqual(self.sources[file], rw.transform(
                before, targets, include_helper=file == 'checkpoint-summary-authority-cold.lisp'), file)
        before = (ROOT / 'tools/fixtures/boot-recovery-base-readiness-before.lisp').read_text()
        expected = function(rw.extend_boot_recovery_base(before), 'fn2-boot-recovery-base')
        actual = function(self.sources['boot.lisp'], 'fn2-boot-recovery-base')
        self.assertEqual(normalized(actual), normalized(expected))

    def test_actual_callee_class(self):
        check_all_calls(self.sources)

    def test_selected_row_complete_current_gate(self):
        check_actual_gate(self.sources)

    def test_real_loader_wrappers_and_cost_faces(self):
        check_loader_wrappers(self.sources['checkpoint-summary-loader-readiness.lisp'])

    def test_exact_cost_and_preservation_inputs(self):
        check_faces_and_preserves(self.sources)

    def test_removed_child_call_refused(self):
        altered = dict(self.sources)
        file = 'checkpoint-summary-adoption.lisp'
        fn = function(altered[file], 'fn2-checkpoint-summary-apply-begin')
        call = lr.match('(fn2-checkpoint-summary-adoption-source-p ?*args)', [fn])[0].node
        child = call.items[-2]
        altered[file] = lr.write(altered[file], [(child.start, child.end, '')])
        with self.assertRaisesRegex(ValueError, 'ABI'):
            check_all_calls(altered)

    def test_removed_identity_component_refused(self):
        altered = dict(self.sources)
        file = 'checkpoint-summary-loader-readiness.lisp'
        altered[file] = altered[file].replace(
            '(fn2-checkpoint-selected-source-owner-gen 0 fn2-checkpoint-selected-source)', '0', 1)
        with self.assertRaisesRegex(ValueError, 'complete-current identity'):
            check_actual_gate(altered)

    def test_begin_identity_divergence_refused(self):
        source = self.sources['checkpoint-summary-loader-readiness.lisp']
        begin = function(source, 'fn2-checkpoint-summary-loader-begin')
        owner = lr.match('(fn2-checkpoint-selected-source-owner-gen 0 fn2-checkpoint-selected-source)',
                         [begin])[-1].node
        mutated = lr.write(source, [(owner.start, owner.end, '0')])
        with self.assertRaisesRegex(ValueError, 'identical selected-source identity'):
            check_loader_wrappers(mutated)


if __name__ == '__main__':
    unittest.main()
