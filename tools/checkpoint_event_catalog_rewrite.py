"""Restrict cold event scratch to stripe zero in the shared row carrier.
No Lisp evaluation. Unknown row-reader argument shapes refuse the rewrite.
"""
import lisp_rewrite as lr
ROWS='fn2-checkpoint-restore-events-work-rows'
CAPACITY='fn2-checkpoint-restore-events-work-capacity'
CARRIER='fn2-checkpoint-restore-events-work'
def scratch_capacity(source,expected):
    matches=lr.match('('+ROWS+' ?*args)',lr.parse(source).forms)
    if len(matches)!=expected: raise ValueError(f'expected {expected} scratch readers, found {len(matches)}')
    edits=[]
    for m in matches:
        n=m.node
        if len(n.items)!=2 or getattr(n.items[1],'low',None)!=CARRIER:
            raise ValueError('unknown scratch row-reader subject')
        edits.append((n.items[0].start,n.items[0].end,CAPACITY))
    return lr.write(source,edits)
def undo_capacity(source):
    edits=[]
    for m in lr.match('('+CAPACITY+' '+CARRIER+')',lr.parse(source).forms):
        n=m.node;edits.append((n.items[0].start,n.items[0].end,ROWS))
    return lr.write(source,edits)
