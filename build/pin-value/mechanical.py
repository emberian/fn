#!/usr/bin/env python3
"""Position-preserving PIN-VALUE arity transformation using the shared reader."""
from pathlib import Path
import subprocess, sys, re
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'tools'))
import lisp_rewrite as lr
ROOT = Path(__file__).resolve().parents[2]
BASE = '8c4c8c8d8'
PLAN = (ROOT/'build/pin-value/plan.txt').read_text()
ARITY = set(PLAN.splitlines()[0].split(': ',1)[1].split())
FILES = sorted(set(re.findall(r'^  [ACOWP]+\s+(\S+\.lisp)', PLAN, re.M)))
A = re.findall(r'^  A\s+(\S+)\s+(\S+)', PLAN, re.M)
def gittext(p):
 return subprocess.check_output(['git','-C',str(ROOT),'show',f'{BASE}:{p}']).decode()
def head(n):
 return n.items[0].low if isinstance(n,lr.Lst) and n.items and isinstance(n.items[0],lr.Atom) else ''
def walk(n):
 yield n
 if isinstance(n,lr.Lst):
  for x in n.items: yield from walk(x)
 elif isinstance(n,lr.Pre): yield from walk(n.node)
def definitions(parsed):
 return {n.items[1].low:n for f in parsed.forms for n in walk(f) if head(n) in ('defun','defund','def-loop','define','defun-inline')}
def formulas(parsed):
 return {n.items[1].low:n.items[2] for f in parsed.forms for n in walk(f) if head(n) in ('defthm','defthmd')}
def specs():
 out={}
 for p in FILES:
  for name,n in definitions(lr.parse(gittext(p))).items():
   if name in ARITY:
    fm=n.items[2].items
    # Keep the house arena-last convention for pure helper functions.
    pos=next((i for i,x in enumerate(fm) if isinstance(x,lr.Atom) and x.low=='fn-arena'),len(fm)) if name not in {'fn-ocfg-open','fn-ocfg-open-peer','fn-ocar-ocfg-open','fn-exp-open','fn-ocar-exp-open'} else len(fm)
    out[name]=(len(fm),pos)
 return out
SPECS=specs()
def transform(text, path):
 p=lr.parse(text); edits=[]
 for top in p.forms:
  defs=definitions(type('P',(),{'forms':[top]})())
  pure=next((n for name,n in defs.items() if name in ARITY),None)
  state=any(any(isinstance(x,lr.Atom) and x.low=='state' for x in n.items[2].items) for n in defs.values())
  is_thm=head(top)=='ocfg-r-unbound-thm' or any(head(n) in ('defthm','defthmd') for n in walk(top))
  state_formula=path=='books/owner-connection-callback-refinement.lisp' and is_thm
  arg='(fn-owner-store-profile state)' if state or state_formula else 'profile' if pure or is_thm else 'nil'
  formal_ids=set()
  for name,n in defs.items():
   formal_ids.add(id(n.items[2]))
   if name in ARITY:
    old,pos=SPECS[name]; fm=n.items[2]
    if len(fm.items)==old:
     at=fm.items[pos].start if pos<len(fm.items) else fm.end-1
     edits.append((at,at,'profile ' if pos<len(fm.items) else ' profile'))
  # Function names in theory expressions are rule-list data, not calls.
  protected=set()
  for container in walk(top):
   if not isinstance(container,lr.Lst): continue
   roots=[]
   if head(container)=='in-theory': roots=container.items[1:]
   elif head(container)=='deftheory': roots=container.items[2:]
   for i,x in enumerate(container.items[:-1]):
    if isinstance(x,lr.Atom) and x.low==':in-theory': roots.append(container.items[i+1])
   for root in roots:
    protected.update(id(x) for x in walk(root))
  for n in walk(top):
   if id(n) in protected: continue
   h=head(n)
   if h in ARITY or h.startswith('in-arena-') and h[9:] in ARITY:
    if id(n) in formal_ids: continue
    helper=h.startswith('in-arena-'); name=h[9:] if helper else h
    old,pos=SPECS[name]
    if helper: old+=0; pos=old # payload replaces the arena; profile is last
    if len(n.items)-1==old:
     idx=1+pos
     at=n.items[idx].start if idx<len(n.items) else n.end-1
     edits.append((at,at,arg+' ' if idx<len(n.items) else ' '+arg))
   if h=='bpr-lift' and n.items[1].low in ARITY:
    num=n.items[2]; old,_=SPECS[n.items[1].low]
    if int(num.text)==old-1: edits.append((num.start,num.end,str(old)))
    else: assert int(num.text)==old, (n.items[1].low,num.text)
 return lr.write(text,edits),len(edits)
def fixtures():
 cases=[('(defthm x (equal (fn-ocfg-open oc acfg) x))','(defthm x (equal (fn-ocfg-open oc acfg profile) x))'),('(defun fn-osi-host-run (oc evs fn-arena) (fn-osi-host-run oc evs fn-arena))','(defun fn-osi-host-run (oc evs profile fn-arena) (fn-osi-host-run oc evs profile fn-arena))'),("(assert-event (equal (fn-ocfg-open oc nil) x))","(assert-event (equal (fn-ocfg-open oc nil nil) x))")]
 cases.append(("(defthm x t :hints ((\"Goal\" :in-theory '(fn-ocar-ocfg-open rule1 rule2))))", "(defthm x t :hints ((\"Goal\" :in-theory '(fn-ocar-ocfg-open rule1 rule2))))"))
 cases.append(('(bpr-lift fn-osi-live-owner 6)', '(bpr-lift fn-osi-live-owner 7)'))
 cases.append(('(ocfg-r-unbound-thm sample ((car (fn-ocfg-open oc acfg))))','(ocfg-r-unbound-thm sample ((car (fn-ocfg-open oc acfg profile))))'))
 for src,want in cases:
  got,_=transform(src,'fixture'); assert got==want,(got,want)
  again,_=transform(got,'fixture'); assert again==got,(again,got)
if __name__=='__main__':
 fixtures()
 for path in FILES:
  p=ROOT/path; new,count=transform(p.read_text(),path)
  if count: p.write_text(new); print(path,count)
