#!/usr/bin/env python3
"""Split the master's private remainder and exactly one loanable page hold.

Only the named declaration's existing storage-window holds are rewritten;
comments, strings and unrelated declarations retain their original bytes.
"""
from pathlib import Path
from lisp_rewrite import parse,match,write,Atom,Lst
LOAN_PHASES={':page-wait',':page-accept-return',':loan-uncertain'}
def rewrite(source):
    parsed=parse(source)
    hits=match('(defmachine fn2-checkpoint-master ?*body)',parsed.forms,deep=False)
    if len(hits)!=1:raise ValueError('expected one actual maintenance declaration')
    items=hits[0].node.items
    i=next(i for i,x in enumerate(items) if isinstance(x,Atom) and x.low==':holds')
    holds=items[i+1]
    if not isinstance(holds,Lst):raise ValueError('literal holds required')
    edits=[]
    for entry in holds.items:
        if not isinstance(entry,Lst) or not 2<=len(entry.items)<=3:raise ValueError('unexpected hold shape')
        phase,*resources=entry.items
        if not isinstance(phase,Atom) or not all(isinstance(x,Atom) and x.low==':storage-window' for x in resources):
            raise ValueError('only existing window holds may be split')
        expected=1 if phase.low in LOAN_PHASES else 2
        if len(resources)>expected:raise ValueError('loan phase must retain only its private remainder')
        if len(resources)<expected:edits.append((resources[-1].end,resources[-1].end,' :storage-window'))
    return write(source,edits)
if __name__=='__main__':
    path=Path(__file__).resolve().parents[1]/'books/checkpoint-master-state.lisp'
    old=path.read_text();new=rewrite(old)
    if new!=old:path.write_text(new)
    print('master page/remainder hold transformation:', 'changed' if new!=old else 'already current')
