#!/usr/bin/env python3
"""Finite source-route audit/repair for the actual CTL/CNS streaming arms.

Mirrors the relevant defcost/:do acceptance rules, not the callee behavior.
No leaf-stub execution or ACL2 admission is claimed.
"""
from pathlib import Path
import argparse
import lisp_rewrite as lr
STEP='(:more :wait :need-read :ready :complete :bad :bounds :released :handoff :stale :uncertain :covered :claim)'
FAMILY=('fn2-cns-stream-source-','fn2-ctl-stream-')
WHY={
 'fn2-cns-stream-source-step':'the following source-state dispatch handles bounded continuation, read admission, checked data/EOF, handoff and explicit fault states',
 'fn2-cns-stream-source-issue':'operation pressure retries; a refused issue enters owned-source cleanup without dropping claims',
 'fn2-cns-stream-source-open':'the following dispatch starts output only when ready, waits for transport, or cleans the retained source on refusal',
 'fn2-cns-stream-source-finish':'wait retains ownership; the following dispatch handles checked handback or a stale transport tuple',
 'fn2-cns-stream-source-next':'wait retains the source; bad closes the provisional frame; only checked EOF permits a trailer',
 'fn2-ctl-stream-reply-status':'the exact transport state selects cancellation handoff or the checked owner wake',
 'fn2-cns-lease-release':'a slot at its generation limit retires instead of returning to the free chain',
}
def head(n):return n.items[0].low if isinstance(n,lr.Lst) and n.items and isinstance(n.items[0],lr.Atom) else ''
def sym(n):return n.low if isinstance(n,lr.Atom) else ''
def walk(n):
 yield n
 if isinstance(n,lr.Lst):
  for x in n.items:yield from walk(x)
 elif isinstance(n,lr.Pre):yield from walk(n.node)
def option(n,key,start=0):
 for i in range(start,len(n.items)-1):
  if sym(n.items[i])==key:return n.items[i+1]
 return None
def codes(n):return [sym(x) for x in n.items] if isinstance(n,lr.Lst) else None
def operations(p):
 return {sym(n.items[1]):n for n in p.forms if head(n)=='defcost'}
def sites(p):
 for form in p.forms:
  if head(form)!='defmachine-arms' or len(form.items)<4:continue
  machine=sym(form.items[1]);arms=option(form,':arms')
  if arms is None:continue
  for entry in arms.items:
   for n in walk(entry):
    if head(n)==':do' and len(n.items)>2:
     name=head(n.items[2])
     if name.startswith(FAMILY) or (head(entry)==':source' and name=='fn2-cns-lease-release'):
      yield machine,name,n

def issues(source):
 p=lr.parse(source);ops=operations(p);out=[]
 for machine,name,n in sites(p):
  row=ops.get(name)
  if row is None:out.append((name,'missing defcost'));continue
  answers=codes(option(row,':answers'))
  accepted=codes(option(n,':accept',3))
  cases=option(n,':case',3);branches=[];other=False
  if cases:
   for clause in cases.items:
    if sym(clause.items[0])==':otherwise':other=True
    else:branches+=codes(clause.items[0]) or []
  # Literal source-step statuses must be declared, not hidden by open :answers T.
  if name=='fn2-cns-stream-source-step' and answers is None:out.append((name,'open source-state answers'))
  if accepted is None:accepted=[':ok'] if answers is None or ':ok' in answers else []
  if answers is not None and not other:
   missing=set(answers)-set(accepted)-set(branches)
   if missing:out.append((name,'unrouted '+','.join(sorted(missing))))
  if any(x!=':ok' for x in accepted) and (answers is None or ':ok' in answers) and option(n,':why',3) is None:
   out.append((name,'non-OK accept lacks :why'))
 return out

def inline_issue_cases(source):
 p=lr.parse(source);edits=[]
 for form in p.forms:
  for parent in walk(form):
   if not isinstance(parent,lr.Lst):continue
   for i,n in enumerate(parent.items[:-1]):
    if head(n)!=':do' or head(n.items[2])!='fn2-cns-stream-source-issue':continue
    branch=parent.items[i+1]
    if head(branch)!=':case':continue
    if i+2!=len(parent.items):raise ValueError('source issue dispatch must end its clause')
    if sym(branch.items[1])!=sym(n.items[1].items[0]):raise ValueError('source issue status mismatch')
    call=source[n.items[2].start:n.items[2].end];variables=source[n.items[1].start:n.items[1].end]
    if (len(n.items)-3)%2:raise ValueError('malformed source issue options')
    kept=[]
    for j in range(3,len(n.items),2):
     key=sym(n.items[j])
     if not key.startswith(':'):raise ValueError('malformed source issue option key')
     if key==':case':raise ValueError('source issue already has an inline case before its dispatch')
     if key!=':accept':kept.append(source[n.items[j].start:n.items[j+1].end])
    options=(' '+' '.join(kept)) if kept else ''
    clauses=' '.join(source[x.start:x.end] for x in branch.items[2:])
    edits.append((n.start,branch.end,'(:do '+variables+' '+call+options+' :accept () :case ('+clauses+'))'))
 return lr.write(source,edits)

def transform(source):
 source=inline_issue_cases(source)
 p=lr.parse(source);ops=operations(p);edits=[]
 row=ops.get('fn2-cns-stream-source-step')
 if row is not None and codes(option(row,':answers')) is None:
  a=option(row,':answers');edits.append((a.start,a.end,STEP))
  # Subsequent routing uses the exact finite list being installed.
  answers_by_name={'fn2-cns-stream-source-step':codes(lr.parse(STEP).forms[0])}
 else:answers_by_name={}
 for machine,name,n in sites(p):
  row=ops.get(name)
  if row is None:continue
  answers=answers_by_name.get(name,codes(option(row,':answers')))
  accept=option(n,':accept',3);case=option(n,':case',3);why=option(n,':why',3)
  accepted=codes(accept)
  if machine=='fn2-cns' and name in ('fn2-cns-stream-source-finish','fn2-cns-stream-source-clear'):
   desired=[':ok',':wait'] if name.endswith('finish') else [':ok']
   if accept is None:edits.append((n.end-1,n.end-1,' :accept ('+' '.join(desired)+')'))
   elif accepted!=desired:edits.append((accept.start,accept.end,'('+' '.join(desired)+')'))
   accepted=desired
   if case is None:edits.append((n.end-1,n.end-1,' :case (((:stale) (:stop :machine-phase)))'))
  elif case is None and answers:
   # These operations bind a status consumed by the following explicit
   # state dispatch. Do not steal branches from an existing inline :case.
   if accept is None:edits.append((n.end-1,n.end-1,' :accept ('+' '.join(answers)+')'))
   elif accepted!=answers:edits.append((accept.start,accept.end,'('+' '.join(answers)+')'))
   accepted=answers
  if accepted and any(x!=':ok' for x in accepted) and why is None:
   reason=WHY.get(name,'the following bounded stream dispatch waits or closes on refusal and never accepts a provisional frame as complete')
   edits.append((n.end-1,n.end-1,' :why "'+reason+'"'))
 result=lr.write(source,edits)
 if issues(result):raise ValueError(issues(result))
 return result

def main():
 ap=argparse.ArgumentParser();ap.add_argument('path',type=Path);ap.add_argument('--write',action='store_true');a=ap.parse_args()
 source=a.path.read_text();before=issues(source);result=transform(source)
 print(f'{len(before)} source-route findings; repaired={result!=source}')
 for name,reason in before:print(name+': '+reason)
 if a.write:a.path.write_text(result)
if __name__=='__main__':main()
