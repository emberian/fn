#!/usr/bin/env python3
"""Keep existing fixture meanings while widening their explicit pin values."""
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'tools'))
import lisp_rewrite as lr
ROOT=Path(__file__).resolve().parents[2]
TARGETS={
 'tests/acl2/owner-config-tests.lisp':[
  ('*ocfg-t-stale*','(cons 0 *ocfg-t-g1*)'),
  ('*ocfg-l-completing*','(cons 0 *ocfg-t-g1*)')],
 'tests/acl2/config-owner-live-tests.lisp':[
  ('*ocl-t-forged-old-pin*','(fn-ocfg-pin-set 0 (fn-ocfg-config *ocl-t-new-open*) ?pins)')],
 'tests/acl2/login-binding-live-tests.lisp':[
  ('*lblt-oc*','(cons 5 *lblt-cfg-p*)'),
  ('*lblt-oc4*','(fn-ocfg-pin-add 2 (fn-ocfg-config *lblt-admin*) ?pins)')],
 'tests/acl2/owner-host-relation-tests.lisp':[
  ('*ohrt-stale*','(cons 77 (fn-ocfg-config *ohrt-oc*))')]}
def transform(text,targets):
 parsed=lr.parse(text);ed=[]
 for name,pattern in targets:
  ns=lr.match(None,parsed.forms,head='defconst',name=name);assert len(ns)==1,name
  matches=lr.match(pattern,[ns[0].node]);assert len(matches)<=1,(name,matches)
  for m in matches:
   n=m.node.items[2];ed.append((n.start,n.end,'(cons '+text[n.start:n.end]+' nil)'))
 return lr.write(text,ed),len(ed)
def fixtures():
 for old in ['(cons 5 cfg)','(fn-ocfg-pin-add 2 cfg pins)','(fn-ocfg-pin-set 0 cfg pins)']:
  src='(defconst *x* '+old+')\n(assert-event (equal result expected))\n'
  want=src.replace(' cfg',' (cons cfg nil)')
  got,n=transform(src,[('*x*',old)]);assert got==want and n==1
  assert transform(got,[('*x*',old)])==(got,0)
if __name__=='__main__':
 fixtures()
 for path,targets in TARGETS.items():
  p=ROOT/path;new,n=transform(p.read_text(),targets)
  if n:p.write_text(new)
  print(path,n,'fixture pin values widened')
