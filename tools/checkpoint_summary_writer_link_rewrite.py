#!/usr/bin/env python3
"""Bind live authority to the actual late-materialized packet writer request."""
from pathlib import Path
import lisp_rewrite as lr
P='fn2-checkpoint-summary-authority'
DEFERRED=[P+'-live-source-p',P+'-live-begin',P+'-live-step']
def rewrite(source):
    parsed=lr.parse(source)
    if lr.match('(defmacro fn2-checkpoint-summary-authority-live-events ?*body)',parsed.forms,deep=False):raise ValueError('already linked')
    edits=[]
    for m in lr.match('(?head ?*args)',parsed.forms):
        n=m.node
        if not n.items or not hasattr(n.items[0],'low'):continue
        h=n.items[0].low
        if h==P or h==P+'-live-source-p':
            if any(getattr(x,'low',None)=='fn2-checkpoint-source' for x in n.items):
                edits.append((n.items[-1].end,n.items[-1].end,' fn2-checkpoint-writer fn2-machines'))
        elif h=='fn2-checkpoint-publication-wfp':
            edits.append((n.end,n.end,' (fn2-checkpoint-writer-wfp fn2-checkpoint-writer) (fn2-machines-wfp fn2-machines)'))
        elif h=='fn2-core-checkpoint-summary-authority':
            edits.append((n.items[-1].end,n.items[-1].end,' fn2-core-checkpoint-writer fn2-core-machines'))
    source=lr.write(source,edits)
    fn=lr.match(f'(defun {DEFERRED[0]} ?*body)',lr.parse(source).forms,deep=False)[0].node
    edits=[]
    for field in ['owner-kind','owner-slot','owner-gen']:
        match=lr.match(f'(= (fn2-checkpoint-publication-{field} 0 fn2-checkpoint-publication) (fn2-checkpoint-source-{field} 0 fn2-checkpoint-source))',[fn])
        if len(match)!=1:raise ValueError('missing old incorrect owner equality')
        edits.append((match[0].start,match[0].end,''))
    slot=lr.match('(fn2-checkpoint-slotp c fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes)',[fn])[0].node
    request='''
        (fn2-event-producer-writer-request-p c (fn2-checkpoint-source-token 0 fn2-checkpoint-source)
         (fn2-checkpoint-source-owner-kind 0 fn2-checkpoint-source) (fn2-checkpoint-source-owner-slot 0 fn2-checkpoint-source)
         (fn2-checkpoint-source-owner-gen 0 fn2-checkpoint-source) fn2-checkpoint-writer fn2-checkpoint-publication fn2-machines)'''
    edits.append((slot.end,slot.end,request));source=lr.write(source,edits)
    forms=lr.parse(source).forms
    defs=[lr.match(f'(defun {name} ?*body)',forms,deep=False)[0].node for name in DEFERRED]
    macro='''; The actual writer machine type and requester relation materialize first.
; assembly-callbacks-c expands this after writer-events and rearm-events.
(defmacro fn2-checkpoint-summary-authority-live-events ()
 '(progn
'''+''.join(source[d.start:d.end]+'\n' for d in defs)+'))'
    source=lr.write(source,[(d.start,d.end,macro if i==0 else '') for i,d in enumerate(defs)])
    source=source.replace('(include-book "event-producer")','(include-book "event-producer")\n(include-book "event-rearm")')
    while '\n  \n' in source:source=source.replace('\n  \n','\n\n')
    return source
if __name__=='__main__':
    root=Path(__file__).resolve().parents[1]
    p=root/'books/checkpoint-summary-authority-live.lisp';p.write_text(rewrite(p.read_text()))
    p=root/'books/assembly-callbacks-c.lisp';s=p.read_text();old='(fn2-event-producer-rearm-events)';assert s.count(old)==1
    p.write_text(s.replace(old,old+'\n(fn2-checkpoint-summary-authority-live-events)'))
