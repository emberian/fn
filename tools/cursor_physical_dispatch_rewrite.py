#!/usr/bin/env python3
"""Insert explicit physical-MISS routing at each actual D cursor C-read call.

Uses the shared structural reader; refuses missing/duplicate routing rather
than editing a nearby textual :otherwise. No ACL2 execution is involved.
"""
from __future__ import annotations
from pathlib import Path
import argparse
from lisp_rewrite import parse, match, write, Lst, Atom
OPS = {'fn2-read-lookup', 'fn2-read-next', 'fn2-read-scan-next', 'fn2-read-identity', 'fn2-read-seek-step'}
def atom(n, text):
    return isinstance(n, Atom) and n.low == text

def transform(text: str) -> tuple[str, int]:
    parsed = parse(text)
    edits = []
    for found in match('(:do ?results ?call ?*tail)', parsed.forms):
        node = found.node
        call = node.items[2]
        if not isinstance(call, Lst) or not call.items or not isinstance(call.items[0], Atom) or call.items[0].low not in OPS:
            continue
        if len(call.items) < 2:
            raise ValueError('read call has no row')
        case = next((i for i, n in enumerate(node.items) if atom(n, ':case')), None)
        if case is None or case + 1 >= len(node.items) or not isinstance(node.items[case+1], Lst):
            raise ValueError('read call has no explicit :case')
        clauses = node.items[case+1]
        if any(isinstance(c, Lst) and c.items and isinstance(c.items[0], Lst)
               and any(atom(x, ':miss') for x in c.items[0].items) for c in clauses.items):
            continue
        before = next((c.start for c in clauses.items if isinstance(c, Lst) and c.items and atom(c.items[0], ':otherwise')), clauses.end-1)
        row = text[call.items[1].start:call.items[1].end]
        edits.append((before, before, f'((:miss) (:set (load-read {row})) (:goto run-load-start))\n             '))
    return write(text, edits), len(edits)

READ_ERRORS = (':source', ':reference', ':hash', ':source-header', ':source-index', ':page-kind')
def transform_answers(text: str) -> tuple[str, int]:
    parsed=parse(text); edits=[]
    for found in match('(defcost ?name ?*tail)',parsed.forms,deep=False):
        node=found.node
        if not isinstance(node.items[1],Atom) or node.items[1].low not in OPS:
            continue
        index=next((i for i,n in enumerate(node.items) if atom(n,':answers')),None)
        if index is None or not isinstance(node.items[index+1],Lst):
            raise ValueError('read cost has no closed answer list')
        answers=node.items[index+1]
        missing=[e for e in READ_ERRORS if not any(atom(x,e) for x in answers.items)]
        if missing: edits.append((answers.end-1,answers.end-1,' '+' '.join(missing)))
    return write(text,edits),len(edits)

def transform_bundle_holds(text: str) -> tuple[str, int]:
    parsed=parse(text); edits=[]
    for found in match('(:storage-window :while (lease :held))',parsed.forms):
        edits.append((found.start,found.end,'(:storage-window :while (query-bundle :held))'))
    return write(text,edits),len(edits)

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('path',type=Path); ap.add_argument('--write',action='store_true'); ap.add_argument('--answers',action='store_true'); a=ap.parse_args()
    out,n=(transform_answers if a.answers else transform)(a.path.read_text())
    if a.write: a.path.write_text(out)
    print(f'{a.path}: {n} physical {"answer lists" if a.answers else "MISS routes"} {"updated" if a.write else "pending"}')
if __name__=='__main__': main()
