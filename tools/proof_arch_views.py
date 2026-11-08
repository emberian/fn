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
                if ('fn2-env-tk' in theory or 'fn2-env-sk' in theory) and 'fn2-machines-directory-keeps' not in theory:
                    edits.append((right.start, right.end,
                                  "(union-theories '(fn2-ctf-dir fn2-machines-directory-keeps) " + theory + ')'))
    return lr.write(result, edits)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('file', type=Path)
    args = parser.parse_args()
    args.file.write_text(migrate(args.file.read_text()))
