"""Fill concrete guards for the named restore-reach leaf class, using Lisp syntax."""
from pathlib import Path
import argparse
import lisp_rewrite as lr


def rewrite(text):
    edits = []
    for match in lr.match('(defun ?name ?args ?*body)', lr.parse(text).forms, deep=False):
        name = match.captures['name']
        if not isinstance(name, lr.Atom) or not name.low.startswith(('fn2-checkpoint-restore-reach-', 'fn2-checkpoint-restore-events-')):
            continue
        for decl in match.captures['body']:
            if not isinstance(decl, lr.Lst) or not decl.items or getattr(decl.items[0], 'low', '') != 'declare':
                continue
            for spec in decl.items[1:]:
                if not isinstance(spec, lr.Lst) or not spec.items or getattr(spec.items[0], 'low', '') != 'xargs':
                    continue
                keys = {x.low: i for i, x in enumerate(spec.items) if isinstance(x, lr.Atom)}
                if ':guard' in keys or ':stobjs' not in keys:
                    continue
                item = spec.items[keys[':stobjs'] + 1]
                tables = item.items if isinstance(item, lr.Lst) else [item]
                if not all(isinstance(x, lr.Atom) and x.low.startswith('fn2-') for x in tables):
                    raise ValueError('Require concrete named table carriers')
                guard = '(and ' + ' '.join(f'({x.text}-wfp {x.text})' for x in tables) + ')'
                edits.append((spec.end - 1, spec.end - 1, '\n  :guard ' + guard))
    return lr.write(text, edits), len(edits)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true')
    parser.add_argument('--events', action='store_true')
    parser.add_argument('--events-source', action='store_true')
    args = parser.parse_args()
    path = Path(__file__).resolve().parents[1] / ('books/checkpoint-restore-events-source.lisp' if args.events_source else ('books/checkpoint-restore-events.lisp' if args.events else 'books/checkpoint-restore-reach.lisp'))
    result, count = rewrite(path.read_text())
    print(f'{path.name}: {count} concrete guard declarations')
    if args.write:
        path.write_text(result)


def wire_boot_returns(text):
    """Extend only the exact old return class in the actual root-begin wrapper."""
    edits = []
    old = ['fn2-checkpoint-restore-reader', 'fn2-checkpoint-restore-map-control',
           'fn2-checkpoint-restore-arena-control', 'fn2-fc', 'fn2-pool']
    extra = ' fn2-checkpoint-restore-reach fn2-checkpoint-restore-reach-control'
    for found in lr.match('(defun fn2-boot-checkpoint-root-begin ?args ?*body)', lr.parse(text).forms, deep=True):
        def visit(node):
            if not isinstance(node, lr.Lst):
                return
            atoms = [x.low if isinstance(x, lr.Atom) else None for x in node.items]
            if len(atoms) in (6, 7) and atoms[-5:] == old and (len(atoms) == 6 or atoms[0] == 'mv'):
                at = node.items[-2].start
                edits.append((at, at, extra.strip() + ' '))
            for child in node.items:
                visit(child)
        for item in found.captures['body']:
            visit(item)
    return lr.write(text, edits), len(edits)
