#!/usr/bin/env python3
"""Advisory concrete source arity/MV preflight, not ACL2 admission."""
from pathlib import Path
import lisp_rewrite as lr
ROOT=Path(__file__).resolve().parents[1]
def head(n):return n.items[0].low if isinstance(n,lr.Lst) and n.items and isinstance(n.items[0],lr.Atom) else ''
def walk(n):
 yield n
 if isinstance(n,lr.Lst):
  for x in n.items:yield from walk(x)
 elif isinstance(n,lr.Pre) and n.prefix not in ("'",'`'):yield from walk(n.node)
D={}
for p in (ROOT/'books').glob('*.lisp'):
 try:parsed=lr.parse(p)
 except lr.ReadError:continue
 for form in parsed.forms:
  for n in walk(form):
   if head(n)=='defun' and len(n.items)>2 and isinstance(n.items[1],lr.Atom) and isinstance(n.items[2],lr.Lst):D.setdefault(n.items[1].low,set()).add(len(n.items[2].items))
known={'fn2-read-value-children':2,'fn2-rd-entry-row':2,'fn2-read-octets-children':4,'fn2-run-zero':2,
 'fn2-cns-source-root-hold-children':4,'fn2-block-read-children':8,'fn2-cns-source-capture-read-children':4,
 'fn2-cns-source-capture-children':6,'fn2-pool-reset':2,'fn2-pool-truncate':2,'fn2-pool-read':2,
 'fn2-block-read-commitment-children':3,'fn2-cns-source-hash-begin':3,'fn2-cns-source-hash-update':4,
 'fn2-cns-source-hash-finish':3,'fn2-rd-copy':2,'fn2-alloc-reserve':6,'fn2-alloc-begin-epoch':2,
 'fn2-alloc-commit-allocation':2,'fn2-pool-reserve':4,'fn2-pool-write':2,
 'fn2-source-manifest-entry':10,'fn2-am-get-header':3,'fn2-block-digest-at':2,'fn2-rec-fetch':2,
 'fn2-cns-source-claim-identity':3,'fn2-block-read-done-from-children':3,'fn2-alloc-edge-drop':3,
 'fn2-cns-source-hash-update':4,'fn2-cns-source-hash-finish':3}
errors=[];calls=0;mv=0
for path in ['books/cns-source-state.lisp','books/cns-source-capture.lisp','books/cns-source-raw.lisp','tests/cns-source-capture-unit.lisp','books/cns-source-manifest.lisp','books/cns-source-retention.lisp','books/cns-source-hash.lisp','books/source-manifest-entry.lisp']:
 for form in lr.parse(ROOT/path).forms:
  if head(form)!='defun':continue
  for body in form.items[3:]:
   for n in walk(body):
    name=head(n)
    if name in D:
     calls+=1
     if len(n.items)-1 not in D[name]:errors.append((path,name,len(n.items)-1,D[name]))
    if name=='b*' and len(n.items)>1 and isinstance(n.items[1],lr.Lst):
     for binding in n.items[1].items:
      if isinstance(binding,lr.Lst) and len(binding.items)==2 and head(binding.items[0])=='mv' and head(binding.items[1]) in known:
       mv+=1;count=len(binding.items[0].items)-1;expected=known[head(binding.items[1])]
       if count!=expected:errors.append((path,'MV '+head(binding.items[1]),count,expected))
print(f'{calls} actual-definition calls / {mv} known MV bindings; findings: {errors}')
assert not errors
