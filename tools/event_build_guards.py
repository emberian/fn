"""Supply concrete table-shape guards to the new event builder leaf class.

Only named fn2-event-build-* / fn2-event-producer-* defuns with explicit :stobjs and no existing
:guard are eligible. Function bodies, existing guards and other books stay
unchanged; this source transformation makes no admission/proof claim.
"""
from pathlib import Path
import argparse
import lisp_rewrite as lr


def rewrite(text):
    edits = []
    for match in lr.match('(defun ?name ?args ?*body)', lr.parse(text).forms, deep=False):
        name = match.captures['name']
        if not isinstance(name, lr.Atom) or not name.low.startswith(('fn2-event-build-', 'fn2-event-producer-')):
            continue
        for decl in match.captures['body']:
            if not isinstance(decl, lr.Lst) or not decl.items or not isinstance(decl.items[0], lr.Atom) or decl.items[0].low != 'declare':
                continue
            for spec in decl.items[1:]:
                if not isinstance(spec, lr.Lst) or not spec.items or not isinstance(spec.items[0], lr.Atom) or spec.items[0].low != 'xargs':
                    continue
                keys = {x.low: i for i, x in enumerate(spec.items) if isinstance(x, lr.Atom)}
                if ':guard' in keys or ':stobjs' not in keys:
                    continue
                stobjs = spec.items[keys[':stobjs'] + 1]
                names = stobjs.items if isinstance(stobjs, lr.Lst) else [stobjs]
                if not names or not all(isinstance(x, lr.Atom) and x.low.startswith('fn2-') for x in names):
                    raise ValueError('Event builder guards require named fn2 concrete tables')
                guard = '(and ' + ' '.join(f'({x.text}-wfp {x.text})' for x in names) + ')'
                at = spec.end - 1
                edits.append((at, at, '\n  :guard ' + guard))
    return lr.write(text, edits), len(edits)


if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--write', action='store_true')
    ap.add_argument('--book', choices=('event-build', 'event-producer'), default='event-build')
    args = ap.parse_args()
    path = Path(__file__).resolve().parents[1] / f'books/{args.book}.lisp'
    result, count = rewrite(path.read_text())
    print(f'{path.name}: {count} guard declarations')
    if args.write:
        path.write_text(result)
