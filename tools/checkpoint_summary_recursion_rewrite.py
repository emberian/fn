"""Totalize the exact fixed-array recursion class in checkpoint summaries.

Each target has measure (nfix (- bound (nfix i))), exits at
(>= (nfix i) bound), and makes one self-call on (+ 1 i).  Changing only
that call to (+ 1 (nfix i)) preserves natural-index behavior and decreases
the measure even when the logical input i is negative.
"""

from pathlib import Path
import lisp_rewrite as lr


TARGETS = {
    "books/checkpoint-summary-authority-state.lisp": {
        "fn2-checkpoint-summary-authority-descriptor-p": 32,
    },
    "books/checkpoint-summary-authority-live.lisp": {
        "fn2-checkpoint-summary-live-published-hash-p": 8,
        "fn2-checkpoint-summary-authority-live-descriptor": 32,
    },
    "books/checkpoint-summary-authority-cold.lisp": {
        "fn2-checkpoint-summary-authority-cold-descriptor": 32,
    },
    "books/checkpoint-summary-catalog.lisp": {
        "fn2-checkpoint-summary-copy-descriptor": 32,
        "fn2-checkpoint-summary-descriptor-equal": 32,
    },
    "books/checkpoint-summary-leases.lisp": {
        "fn2-checkpoint-summary-source-hash-equal": 8,
    },
    "books/checkpoint-summary-live-close.lisp": {
        "fn2-checkpoint-summary-live-copy-descriptor": 32,
    },
    "books/checkpoint-summary-entry.lisp": {
        "fn2-checkpoint-summary-load-hash": 8,
    },
}


def _same(node, pattern):
    return bool(lr.match(pattern, [node], deep=False))


def _step(source, defun, name, bound):
    args = defun.items[2]
    formals = [x.low for x in args.items]
    if formals.count("i") != 1:
        raise ValueError(f"{name}: expected one formal i")
    index = formals.index("i")

    xargs = lr.match('(xargs ?*items)', [defun])
    if len(xargs) != 1:
        raise ValueError(f"{name}: expected one xargs")
    props = xargs[0].node.items
    measures = [props[j + 1] for j in range(len(props) - 1)
                if getattr(props[j], 'low', None) == ':measure']
    if len(measures) != 1 or not _same(measures[0],
                                     f'(nfix (- {bound} (nfix i)))'):
        raise ValueError(f"{name}: measure changed")

    body = defun.items[-1]
    bases = lr.match(f'(>= (nfix i) {bound})', [body])
    if len(bases) != 1:
        raise ValueError(f"{name}: base changed")
    if not (isinstance(body, lr.Lst) and len(body.items) >= 2
            and getattr(body.items[0], 'low', None) in ('if', 'or')
            and body.items[1].start == bases[0].start):
        raise ValueError(f"{name}: base is not first branch")

    calls = lr.match(f'({name} ?*arguments)', [body])
    if len(calls) != 1:
        raise ValueError(f"{name}: expected one self-call")
    actuals = calls[0].node.items[1:]
    if len(actuals) != len(formals):
        raise ValueError(f"{name}: self-call arity changed")
    old = actuals[index]
    new = '(+ 1 (nfix i))'
    if _same(old, new):
        return None
    if not _same(old, '(+ 1 i)'):
        raise ValueError(f"{name}: recursive index changed")
    return old.start, old.end, new


def rewrite(source, targets):
    forms = lr.parse(source).forms
    defs = {m.captures['name'].low: m.node
            for m in lr.match('(defun ?name ?args ?*body)', forms, deep=False)}
    edits = []
    for name, bound in targets.items():
        if name not in defs:
            raise ValueError(f"missing target: {name}")
        edit = _step(source, defs[name], name, bound)
        if edit is not None:
            edits.append(edit)
    return lr.write(source, edits), len(edits)


def main():
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true',
                        help='write the nine checked source substitutions')
    args = parser.parse_args()
    count = 0
    for file, targets in TARGETS.items():
        path = Path(file)
        source = path.read_text()
        changed, edits = rewrite(source, targets)
        if args.write and edits:
            path.write_text(changed)
        count += edits
    print(f'{count} recursive index substitutions' +
          (' written' if args.write else ' pending'))


if __name__ == '__main__':
    main()
