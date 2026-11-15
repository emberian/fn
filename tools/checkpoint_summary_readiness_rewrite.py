#!/usr/bin/env python3
"""Thread the actual loader-readiness children through cold adoption callers."""
from pathlib import Path
import lisp_rewrite as lr

CHILDREN = (
    'fn2-run-load-readiness', 'fn2-run-load-geometry', 'fn2-id-decides',
    'fn2-reads', 'fn2-run-loads', 'fn2-run-cursors',
    'fn2-checkpoint-summary-leases', 'fn2-run-load-ops', 'fn2-ops',
    'fn2-fc', 'fn2-fc-context', 'fn2-b3', 'fn2-fields', 'fn2-digests', 'fn2-pool',
)
TARGETS = {
    'checkpoint-summary-authority-cold.lisp': {
        'fn2-checkpoint-summary-adoption-source-p': None,
        'fn2-checkpoint-summary-authority-cold-source-p': 'fn2-checkpoint-summary-adoption-source-p',
        'fn2-checkpoint-summary-authority-cold-begin': 'fn2-checkpoint-summary-authority-cold-source-p',
        'fn2-checkpoint-summary-authority-cold-step': 'fn2-checkpoint-summary-authority-cold-source-p',
    },
    'checkpoint-summary-adoption.lisp': {
        'fn2-checkpoint-summary-apply-begin': 'fn2-checkpoint-summary-adoption-source-p',
        'fn2-checkpoint-summary-apply-preflight': 'fn2-checkpoint-summary-adoption-source-p',
    },
    'checkpoint-directory-cold.lisp': {
        'fn2-directory-cold-source-p': 'fn2-checkpoint-summary-authority-cold-source-p',
        'fn2-directory-cold-install': 'fn2-directory-cold-source-p',
        'fn2-directory-cold-base': 'fn2-directory-cold-source-p',
    },
    'event-catalog-cold.lisp': {
        'fn2-event-catalog-cold-begin': 'fn2-directory-cold-source-p',
        'fn2-event-catalog-cold-step': 'fn2-directory-cold-source-p',
    },
}


def selected_function(source, name):
    matches = lr.match(f'(defun {name} ?*body)', lr.parse(source).forms, deep=False)
    if len(matches) != 1:
        raise ValueError(f'expected one {name}')
    return matches[0].node


def extend_function(source, fn, callee, children=CHILDREN):
    """Return nonoverlapping span edits for one guarded read-only carrier."""
    existing = [x.low for x in fn.items[2].items]
    missing = [x for x in children if x not in existing]
    if not missing:
        raise ValueError(f'{fn.items[1].low} already threaded')
    declarations = lr.match('(xargs ?*args)', [fn])
    if len(declarations) != 1:
        raise ValueError(f'{fn.items[1].low} requires one xargs declaration')
    xargs = declarations[0].node
    properties = {item.low: xargs.items[i + 1] for i, item in enumerate(xargs.items[:-1])
                  if getattr(item, 'low', None) in (':stobjs', ':guard')}
    if set(properties) != {':stobjs', ':guard'}:
        raise ValueError(f'{fn.items[1].low} requires stobj/and guard')
    stobj_list = properties[':stobjs']
    guard_and = properties[':guard']
    if guard_and.items[0].low != 'and':
        raise ValueError(f'{fn.items[1].low} requires and guard')
    stobj_existing = [x.low for x in stobj_list.items]
    if any(x not in stobj_existing for x in existing):
        raise ValueError(f'{fn.items[1].low} stobj declaration differs from formals')
    edits = [
        (fn.items[2].end - 1, fn.items[2].end - 1, ' ' + ' '.join(missing)),
        (stobj_list.end - 1, stobj_list.end - 1, ' ' + ' '.join(x for x in missing if x not in stobj_existing)),
        (guard_and.end - 1, guard_and.end - 1, '\n (fn2-run-load-readiness-guard)'),
    ]
    if callee:
        calls = lr.match(f'({callee} ?*args)', [fn])
        if len(calls) != 1:
            raise ValueError(f'{fn.items[1].low} requires one {callee} call')
        call = calls[0].node
        edits.append((call.end - 1, call.end - 1, ' ' + ' '.join(children)))
    if fn.items[1].low == 'fn2-checkpoint-summary-adoption-source-p':
        projected = lr.match(
            '(= (fn2-checkpoint-selected-source-phase 0 fn2-checkpoint-selected-source) '
            '*fn2-checkpoint-selected-source-phase-projected*)', [fn])
        if len(projected) != 1:
            raise ValueError('adoption source requires projected selected row')
        gate = '(fn2-checkpoint-summary-loader-ready-p fn2-checkpoint-selected-source '
        gate += ' '.join(children) + ')'
        edits.append((projected[0].end, projected[0].end, '\n  ' + gate))
    if fn.items[1].low == 'fn2-directory-cold-base':
        ignored = lr.match('(declare (ignore fn2-fc fn2-digests fn2-mk))', [fn])
        if len(ignored) != 1:
            raise ValueError('directory base ignore declaration changed')
        edits.append((ignored[0].start, ignored[0].end, '(declare (ignore fn2-mk))'))
    return edits


def sync_faces(source, names):
    """Derive exact defcost :tables from each current child formal list."""
    forms = lr.parse(source).forms
    edits = []
    for name in names:
        faces = lr.match(f'(defcost {name}-op ?*body)', forms, deep=False)
        if not faces:
            continue
        if len(faces) != 1:
            raise ValueError(f'multiple cost faces for {name}')
        args = selected_function(source, name).items[2].items
        tables = '(fn2-core-' + ' fn2-core-'.join(x.low[4:] for x in args) + ')'
        face = faces[0].node
        indices = [i for i, item in enumerate(face.items)
                   if getattr(item, 'low', None) == ':tables']
        if len(indices) != 1:
            raise ValueError(f'missing table face for {name}')
        node = face.items[indices[0] + 1]
        edits.append((node.start, node.end, tables))
    return lr.write(source, edits)


def extend_preserves(source, names, children=CHILDREN):
    forms = lr.parse(source).forms
    edits = []
    for form in forms:
        if not getattr(form, 'items', None) or len(form.items) < 4:
            continue
        if not getattr(form.items[0], 'low', '').endswith('-preserves'):
            continue
        if getattr(form.items[1], 'low', None) not in names:
            continue
        args = form.items[2]
        present = {x.low for x in args.items}
        missing = [x for x in children if x not in present]
        if not missing:
            raise ValueError(f'{form.items[1].low} preservation already threaded')
        edits.append((args.end - 1, args.end - 1, ' ' + ' '.join(missing)))
        positions = [i for i, item in enumerate(form.items[:-1])
                     if getattr(item, 'low', None) == ':hyps']
        if len(positions) != 1:
            raise ValueError(f'{form.items[1].low} preservation needs :hyps')
        hyps = form.items[positions[0] + 1]
        additions = []
        for child in missing:
            additions.extend((f'({child}p {child})', f'({child}-wfp {child})'))
        edits.append((hyps.end - 1, hyps.end - 1, '\n ' + ' '.join(additions)))
    return lr.write(source, edits)


def transform(source, targets, *, include_helper=False):
    forms = lr.parse(source).forms
    edits = []
    for name, callee in targets.items():
        matches = lr.match(f'(defun {name} ?*body)', forms, deep=False)
        if len(matches) != 1:
            raise ValueError(f'expected one {name}')
        edits.extend(extend_function(source, matches[0].node, callee))
    if include_helper:
        if '"checkpoint-summary-loader-readiness"' in source:
            raise ValueError('helper already included')
        layer = lr.match('(fn2-book-layer :c)', forms, deep=False)
        if len(layer) != 1:
            raise ValueError('missing C layer marker')
        edits.append((layer[0].start, layer[0].start,
                      '(include-book "checkpoint-summary-loader-readiness")\n'))
    return sync_faces(extend_preserves(lr.write(source, edits), targets), targets)


def extend_boot_recovery_base(source, children=CHILDREN):
    """Only the nested recovery-base stobj-let and its directory call."""
    matches = lr.match('(defun fn2-boot-recovery-base ?*body)', lr.parse(source).forms)
    if len(matches) != 1:
        raise ValueError('expected one nested recovery-base function')
    fn = matches[0].node
    lets = lr.match('(stobj-let ?bindings ?*body)', [fn])
    calls = lr.match('(fn2-directory-cold-base ?*args)', [fn])
    if len(lets) != 1 or len(calls) != 1:
        raise ValueError('expected one recovery-base carrier and directory call')
    bindings = lets[0].captures['bindings']
    existing = {item.items[0].low for item in bindings.items}
    missing = [child for child in children if child not in existing]
    if len(missing) != len(children) - 2:
        raise ValueError('unexpected recovery-base carrier footprint')
    binding_text = '\n              ' + '\n              '.join(
        f'({child} (fn2-core-{child[4:]} fn2-core))' for child in missing)
    edits = [(bindings.end - 1, bindings.end - 1, binding_text),
             (calls[0].end - 1, calls[0].end - 1, ' ' + ' '.join(missing))]
    return lr.write(source, edits)


if __name__ == '__main__':
    root = Path(__file__).resolve().parents[1] / 'books'
    for filename, targets in TARGETS.items():
        path = root / filename
        path.write_text(transform(path.read_text(), targets,
                                  include_helper=filename == 'checkpoint-summary-authority-cold.lisp'))
