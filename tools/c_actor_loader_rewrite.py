#!/usr/bin/env python3
"""Instrument the declared C consumer actor class; never duplicate a body."""
from pathlib import Path
from lisp_rewrite import parse, match, write, Atom, Lst
KINDS = {'fn2-txn', 'fn2-auth', 'fn2-cns'}
OPS = {'fn2-identity-decide', 'fn2-successor-resolve', 'fn2-txn-group-of',
       'fn2-authority-allows', 'fn2-group-lookup', 'fn2-principal-lookup',
       'fn2-auth-find-outcome', 'fn2-auth-find-head', 'fn2-auth-find-current',
       'fn2-auth-find-grant', 'fn2-cns-authority-allows'}
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
        edits.append((before,before,'((:miss) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))\n             '))
    return write(text,edits),len(edits)

if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('path',type=Path);p.add_argument('--kind',action='store_true');p.add_argument('--route',action='store_true');p.add_argument('--write',action='store_true');args=p.parse_args()
    out,n=route(args.path.read_text()) if args.route else transform(args.path.read_text(),args.kind)
    if args.write: args.path.write_text(out)
    print(f'{args.path}: {n} structural edits')

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

def cns_lease_union(text):
    edits=[]
    for found in match('(:do ?results ?call ?*tail)',parse(text).forms):
        n=found.node;call=n.items[2]
        if not isinstance(call,Lst) or not call.items or not isinstance(call.items[0],Atom) or call.items[0].low not in {'fn2-cns-lease-reserve','fn2-cns-lease-release'}: continue
        i=next((i for i,x in enumerate(n.items) if a(x,':effects')),None)
        if i is not None: edits.append((n.items[i].start,n.items[i+1].end,''))
    for found in match('(:park :pool ?class :steps ?steps)',parse(text).forms):
        edits.append((found.start,found.end,'(:set (reason *fn2-cns-reason-unavailable*)) (:goto refuse)'))
    return write(text,edits),len(edits)

def cns_commit_outputs(text):
    edits=[];tree=parse(text)
    for found in match('(:if (equal row-verb *fn2-cns-verb-register*) ?yes ?no)',tree.forms):
        yes=found.node.items[2]
        if isinstance(yes,Lst) and any(isinstance(n,Lst) and n.items and a(n.items[0],':do') and len(n.items)>1 and isinstance(n.items[1],Lst) and n.items[1].items and a(n.items[1].items[0],'ucode') for n in yes.items):
            edits.append((yes.start,yes.end,'((:set (register-check 0)) (:next :register-output) (:charge :steps *fn2-work-transition* :runnable t))'))
    for found in match('((eq cwhy :duplicate) ?*tail)',tree.forms):
        n=found.node
        if any(isinstance(x,Lst) and x.items and a(x.items[0],':do') and len(x.items)>1 and isinstance(x.items[1],Lst) and x.items[1].items and a(x.items[1].items[0],'dcode') for x in n.items):
            edits.append((n.start,n.end,'((eq cwhy :duplicate) (:set (register-check 1)) (:next :register-output) (:charge :steps *fn2-work-transition* :runnable t))'))
    for found in match('(:commit ?*tail)',tree.forms):
        n=found.node;i=next((i for i,x in enumerate(n.items) if a(x,':accepted')),None)
        if i is None:continue
        body=n.items[i+1]
        if isinstance(body,Lst) and body.items and isinstance(body.items[0],Lst) and a(body.items[0].items[0],':do'):
            call=body.items[0]
            if len(call.items)>1 and isinstance(call.items[1],Lst) and call.items[1].items and a(call.items[1].items[0],'lcode'):
                edits.append((body.start,body.end,'((:set (register-check 0)) (:next :register-output) (:charge :steps *fn2-work-transition* :runnable t))'))
    return write(text,edits),len(edits)

CNS_CONTINUATIONS={'fn2-cns-lookup-cursor','fn2-cns-decode-port','fn2-cns-item-next','fn2-cns-put-item','fn2-cns-put-article'}
def cns_continuations(text):
    edits=[];tree=parse(text)
    for found in match('(:do ?results ?call ?*tail)',tree.forms):
        n=found.node;call=n.items[2]
        if not isinstance(call,Lst) or not call.items or not isinstance(call.items[0],Atom) or call.items[0].low not in CNS_CONTINUATIONS:continue
        ix=next((i for i,x in enumerate(n.items) if a(x,':case')),None)
        clause='((:more :miss) (:charge :bytes *fn2-c-read-step-bytes* :steps *fn2-work-transition* :runnable t))'
        if ix is None:
            edits.append((n.end-1,n.end-1,'\n    :case ('+clause+')'))
        else:
            cases=n.items[ix+1]
            if not isinstance(cases,Lst):raise ValueError('CNS continuation cases malformed')
            if any(isinstance(c,Lst) and c.items and isinstance(c.items[0],Lst) and any(a(v,':miss') for v in c.items[0].items) for c in cases.items):continue
            edits.append((cases.start+1,cases.start+1,clause+'\n    '))
        accept=next((i for i,x in enumerate(n.items) if a(x,':accept')),None)
        if accept is None:edits.append((n.end-1,n.end-1,' :accept (:ok)'))
        else:
            vals=n.items[accept+1]
            if isinstance(vals,Lst):
                keep=[text[x.start:x.end] for x in vals.items if not a(x,':more') and not a(x,':miss')]
                edits.append((vals.start,vals.end,'('+' '.join(keep)+')'))
    for found in match('((eq icode :more) ?*tail)',tree.forms):
        edits.append((found.start,found.end,''))
    return write(text,edits),len(edits)
