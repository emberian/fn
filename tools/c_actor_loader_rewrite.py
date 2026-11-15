#!/usr/bin/env python3
"""Instrument the declared C consumer actor class; never duplicate a body."""
from pathlib import Path
from lisp_rewrite import parse, match, write, Atom, Lst
KINDS = {'fn2-txn', 'fn2-auth'}
OPS = {'fn2-identity-decide', 'fn2-successor-resolve', 'fn2-txn-group-of',
       'fn2-authority-allows', 'fn2-group-lookup', 'fn2-principal-lookup',
       'fn2-auth-find-outcome', 'fn2-auth-find-head', 'fn2-auth-find-current',
       'fn2-auth-find-grant'}
def a(x, text):
    return isinstance(x, Atom) and x.low == text

def transform(text, declarations=False):
    edits=[]; tree=parse(text)
    for found in match('(defmachine ?name ?*args)' if declarations else '(defmachine-arms ?name :declare ?*args)',tree.forms,deep=False):
        n=found.node
        if not isinstance(n.items[1],Atom) or n.items[1].low not in KINDS: continue
        edits.append((n.items[0].start,n.items[0].end,'fn2-c-actor-loader-kind' if declarations else 'fn2-c-actor-loader-arms'))
    if edits:
        book='c-actor-loader-form' if declarations else 'c-actor-loader'
        if f'(include-book "{book}")' not in text:
            layer=match('(fn2-book-layer ?x)',tree.forms,deep=False)[0].node
            edits.append((layer.start,layer.start,f'(include-book "{book}")\n'))
    return write(text,edits),len(edits)

def route(text):
    edits=[]
    for found in match('(:do ?results ?call ?*tail)',parse(text).forms):
        node=found.node; call=node.items[2]
        if not isinstance(call,Lst) or not call.items or not isinstance(call.items[0],Atom) or call.items[0].low not in OPS: continue
        ix=next((i for i,x in enumerate(node.items) if a(x,':case')),None)
        if ix is None: continue
        cases=node.items[ix+1]
        if not isinstance(cases,Lst): raise ValueError('actor C callback lacks structural case list')
        keyed=[c for c in cases.items if isinstance(c,Lst) and c.items and isinstance(c.items[0],Lst)]
        more=next((c for c in keyed if any(a(k,':more') for k in c.items[0].items)),None)
        miss=next((c for c in keyed if any(a(k,':miss') for k in c.items[0].items)),None)
        if more is not None:
            if more is miss: continue
            edits.append((more.items[0].end-1,more.items[0].end-1,' :miss'))
            if miss is not None: edits.append((miss.start,miss.end,''))
            continue
        if miss is not None: continue
        before=next((c.start for c in cases.items if isinstance(c,Lst) and c.items and a(c.items[0],':otherwise')),cases.end-1)
        edits.append((before,before,'((:miss) (:charge :bytes *fn2-c-read-step-bytes* :steps *fn2-work-transition* :runnable t))\n             '))
    return write(text,edits),len(edits)

def answers(text):
    edits=[]
    for found in match('(defcost ?name ?*tail)',parse(text).forms,deep=False):
        n=found.node
        if not isinstance(n.items[1],Atom) or n.items[1].low not in OPS: continue
        i=next((i for i,x in enumerate(n.items) if a(x,':answers')),None)
        if i is None: continue
        values=n.items[i+1]
        if isinstance(values,Lst) and not any(a(v,':miss') for v in values.items):
            edits.append((values.end-1,values.end-1,' :miss'))
    return write(text,edits),len(edits)


def lower_statuses(text):
    edits=[]
    names={'fn2-auth-lookup-step','fn2-authority-allows','fn2-cns-authority-allows'}
    for f in match('(defun ?name ?*args)',parse(text).forms):
        fn=f.node
        if not isinstance(fn.items[1],Atom) or fn.items[1].low not in names:continue
        for m in match('(member-eq lc ?x)',[fn]):
            n=m.node;old=text[n.start:n.end]
            if "'(:more :ok)" in old:edits.append((n.start,n.end,old.replace("'(:more :ok)","'(:more :miss :ok)")))
        for m in match('(if (eq c :more) :more :state)',[fn]):
            n=m.node;edits.append((n.start,n.end,"(if (member-eq c '(:more :miss)) c :state)"))
        for m in match('(case c ?*clauses)',[fn]):
            for clause in m.node.items[2:]:
                if not isinstance(clause,Lst) or not clause.items or not a(clause.items[0],':more'):continue
                edits.append((clause.items[0].start,clause.items[0].end,'(:more :miss)'))
                for ret in match('(mv :more ?*rest)',[clause]):
                    v=ret.node.items[1];edits.append((v.start,v.end,'c'))
    return write(text,edits),len(edits)

if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('path',type=Path);p.add_argument('--kind',action='store_true');p.add_argument('--write',action='store_true');args=p.parse_args()
    text=args.path.read_text();text,n=transform(text,args.kind)
    if not args.kind:
        for rewrite in (route,answers,lower_statuses):text,count=rewrite(text);n+=count
    if args.write:args.path.write_text(text)
    print(f'{args.path}: {n} scoped edits')
