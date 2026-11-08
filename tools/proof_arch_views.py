#!/usr/bin/env python3
"""Structural migration of the seven durability relations to symbolic views.

Every old defining formula becomes a named equivalence obligation. No theorem
statement is deleted or weakened. The shared Lisp reader owns source spans.
"""
from pathlib import Path
import argparse
import lisp_rewrite as lr

SELECT = {
    'ek': '((fn2-commit-io :columns (extent) :rows t :scalars (rows)))',
    'rk': '((fn2-commit-root :columns (installed published) :rows (:one 0) :scalars (rows)))',
    'tk': '''((fn2-machines :columns (kind slot) :rows t :scalars (rows))
             (fn2-commit :columns (phase batch-no cb-mode cb-fence-ok cb-deps-ok cb-log-ok cb-acks cb-done)
                         :rows t :scalars (rows)))''',
    'sk': '''((fn2-machines :columns (kind slot) :rows t :scalars (rows))
             (fn2-commit :scalars (rows)))''',
    'ok': '((fn2-ops :whole t))',
    'fk': '((fn2-commit :columns (cb-deps-ok cb-log-ok) :rows t))',
    'dk': '((fn2-commit :columns (cb-done) :rows t))',
}


def walk(node):
    yield node
    if isinstance(node, lr.Lst):
        for item in node.items:
            yield from walk(item)
    elif isinstance(node, lr.Pre):
        yield from walk(node.node)


def migrate(source):
    parsed = lr.parse(source)
    edits = []
    for suffix, select in SELECT.items():
        name = 'fn2-env-' + suffix
        found = lr.match('(defun-nx ' + name + ' (b a) ?body)', parsed.forms, deep=False)
        if not found:
            continue
        assert len(found) == 1, name
        m = found[0]
        body = m.captures['body']
        old = source[body.start:body.end]
        observation = '''
  :observe fn2-env-root
  :open (fn2-env-root fn2-core-commit-root fn2-commit-root-rows
         fn2-commit-root-installed fn2-commit-root-published
         fn2-commit-root-installed$ai fn2-commit-root-published$ai)''' if suffix == 'rk' else ''
        replacement = f'''(fn2-defview {name} :carrier fn2-core
  :select {select}{observation})
(defthm {name}-view-equivalence
  (equal ({name} b a) {old})
  :rule-classes nil
  :hints (("Goal" :in-theory (enable {name} fn2-ctf-dir fn2-machines-directory-keeps))))
(in-theory (enable {name}))'''
        edits.append((m.start, m.end, replacement))
    result = lr.write(source, edits)
    parsed = lr.parse(result)
    edits = []
    for form in parsed.forms:
        for node in walk(form):
            if not isinstance(node, lr.Lst):
                continue
            for left, right in zip(node.items, node.items[1:]):
                if not isinstance(left, lr.Atom) or left.low != ':in-theory':
                    continue
                theory = result[right.start:right.end]
                disabled_directory = any(
                    isinstance(item, lr.Atom) and item.low in ('fn2-ctf-dir', 'fn2-machines-directory-keeps')
                    for match in lr.match('(e/d ?enabled ?disabled)', [right])
                    for item in walk(match.captures['disabled']))
                # An explicit abstraction boundary must remain closed. Such
                # consumers need a view projection, not broader unfolding.
                if (('fn2-env-tk' in theory or 'fn2-env-sk' in theory)
                        and 'fn2-machines-directory-keeps' not in theory and not disabled_directory):
                    edits.append((right.start, right.end,
                                  "(union-theories '(fn2-ctf-dir fn2-machines-directory-keeps) " + theory + ')'))
    return lr.write(result, edits)


def lift_transports(source):
    """Replace the six identical transport schemas, checking each statement."""
    parsed = lr.parse(source)
    edits = []
    for family in ('log', 'child', 'view'):
        for invariant in ('j', 'j3'):
            name = f'fn2-env-{invariant}-{family}-transport'
            found = lr.match('(defthm ' + name + ' ?*rest)', parsed.forms, deep=False)
            if not found:
                continue
            assert len(found) == 1, name
            match = found[0]
            point = 'fn2-env-j-row' if invariant == 'j' else 'fn2-env-j3-point'
            step = ('fn2-env-' + family + '-step' if family != 'view'
                    else f'fn2-env-{invariant}-view-step')
            all_fn = f'fn2-env-{invariant}-rows'
            locality = f'fn2-env-{invariant}-{family}-locality'
            expected = lr.parse(f'(implies (and ({all_fn} keys g a) ({step} delta g a h b)) '
                                f'({all_fn} keys h b))').forms[0]
            if lr.flat(match.node.items[2]).lower() != lr.flat(expected).lower():
                raise ValueError('unexpected statement: ' + name)
            opened = ' :open (fn2-env-j3-point)' if invariant == 'j3' else ''
            replacement = (f'(fn2-pw-lift-locality {name}\n'
                           f'  :point {point} :all {all_fn} :step {step}\n'
                           f'  :locality {locality}{opened})')
            edits.append((match.start, match.end, replacement))
    return lr.write(source, edits)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('file', type=Path)
    parser.add_argument('--lifts', action='store_true', help='consolidate transport declarations')
    args = parser.parse_args()
    operation = lift_transports if args.lifts else migrate
    args.file.write_text(operation(args.file.read_text()))
