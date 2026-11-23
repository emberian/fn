#!/usr/bin/env python3
"""Omit the four observed conditional enum self-writes, preserving order.

Every real update still delegates to the existing column PUT macro. Equality
with the original sequence requires the typed table, WFP and valid row; this
is not a rewrite for arbitrary malformed logical lists.
"""
from pathlib import Path
from lisp_rewrite import Atom, Lst, match, parse, write
TABLE = 'fn2-cns-sources'
PUT = TABLE + '-put'
TARGETS = {
    'fn2-cns-source-issue-children': {'manifest-stage'},
    'fn2-cns-source-harvest': {'phase', 'manifest-stage'},
    'fn2-cns-source-next-children': {'manifest-stage'},
}
def transform(text):
    parsed = parse(text)
    edits = []
    count = 0
    def source(n):return text[n.start:n.end]
    def atom(n, value):return isinstance(n, Atom) and n.low == value
    alias_valid = False
    def noop(n, field, slot):
        if field == 'manifest-stage' and atom(n, 'stage'):
            if not alias_valid:
                raise ValueError('cached stage is not the actual same-row stage getter')
            return True
        return (isinstance(n, Lst) and len(n.items) == 3
                and atom(n.items[0], TABLE + '-' + field)
                and source(n.items[1]) == source(slot)
                and atom(n.items[2], TABLE))
    for found in match(None, parsed, deep=False, head='defun'):
        fn = found.node.items[1].low
        if fn not in TARGETS:continue
        alias_valid = len(match('(stage (fn2-cns-sources-manifest-stage s fn2-cns-sources))', [found.node], deep=True)) == 1
        for call in match(None, [found.node], deep=True, head=PUT):
            node = call.node
            slot = node.items[1]
            changed = 0
            bindings = []
            pending = []
            def flush():
                if pending:
                    rhs = f'({PUT} {source(slot)} ' + ' '.join(pending) + ')'
                    bindings.append(f'({TABLE} {rhs})')
                    pending.clear()
            for assignment in node.items[2:]:
                field, value = assignment.items
                def update(v):return f'({PUT} {source(slot)} ({field.text} {source(v)}))'
                rhs = None
                if field.low in TARGETS[fn] and isinstance(value, Lst):
                    parts = value.items
                    if (atom(parts[0], 'if') and len(parts) == 4
                            and noop(parts[3], field.low, slot)):
                        rhs = f'(if {source(parts[1])} {update(parts[2])} {TABLE})'
                        changed += 1
                    elif (atom(parts[0], 'cond') and parts[1:]
                          and atom(parts[-1].items[0], 't')
                          and noop(parts[-1].items[1], field.low, slot)):
                        clauses = [f'({source(b.items[0])} {update(b.items[1])})'
                                   for b in parts[1:-1]] + [f'(t {TABLE})']
                        rhs = '(cond ' + ' '.join(clauses) + ')'
                        changed += 1
                if rhs is None:
                    pending.append(source(assignment))
                else:
                    flush()
                    bindings.append(f'({TABLE} {rhs})')
            flush()
            if changed:
                replacement = '(let* (' + '\n        '.join(bindings) + ')\n   ' + TABLE + ')'
                edits.append((node.start, node.end, replacement))
                count += changed
    result = write(text, edits)
    parse(result)
    return result, count
if __name__ == '__main__':
    import argparse
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('file', type=Path)
    args = ap.parse_args()
    result, count = transform(args.file.read_text())
    if count != 4:ap.error(f'expected four original self-writes, found {count}')
    args.file.write_text(result)
