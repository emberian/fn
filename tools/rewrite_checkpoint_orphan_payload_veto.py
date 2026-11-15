"""Thread canonical native/cold payload facts through the real orphan class."""
from pathlib import Path
import lisp_rewrite as lr
TABLES=('fn2-checkpoint-payload-proofs','fn2-checkpoint-bank-closures','fn2-checkpoint-publication')
NAMES=('fn2-checkpoint-owned-retirement-eligible-p','fn2-checkpoint-owned-retirement-scan')
def rewrite(text):
 p=lr.parse(text);targets=[];edits=[]
 for name in NAMES:
  for m in lr.match('(defun '+name+' ?args ?*body)',p.forms,deep=False):
   targets.append(m.captures['args'])
   for a in lr.match('(xargs ?*before :stobjs ?tables ?*after)',[m.node]):targets.append(a.captures['tables'])
  for m in lr.match('('+name+' ?*args)',p.forms):targets.append(m.node)
 # Only the actual submit recheck borrows this complete set of readonly facts.
 for m in lr.match('(stobj-let ?bindings ?outs ?body ?return)',p.forms):
  if lr.match('(fn2-checkpoint-owned-retirement-eligible-p ?*args)',[m.captures['body']]):
   b=m.captures['bindings'];present={a.items[0].low for a in b.items if isinstance(a,lr.Lst) and a.items}
   add=['('+t+' (fn2-core-'+t[4:]+' fn2-core))' for t in TABLES if t not in present]
   if add:edits.append((b.end-1,b.end-1,' '+' '.join(add)))
 for m in lr.match('(defcost fn2-checkpoint-owned-retirement-submit-op ?*args)',p.forms,deep=False):
  it=m.node.items;i=next(i for i,a in enumerate(it) if isinstance(a,lr.Atom) and a.low==':tables');b=it[i+1]
  present={a.low for a in b.items if isinstance(a,lr.Atom)};add=['fn2-core-'+t[4:] for t in TABLES if 'fn2-core-'+t[4:] not in present]
  if add:edits.append((b.end-1,b.end-1,' '+' '.join(add)))
 for node in targets:
  present={a.low for a in node.items if isinstance(a,lr.Atom)};add=[t for t in TABLES if t not in present]
  if add:edits.append((node.end-1,node.end-1,' '+' '.join(add)))
 return lr.write(text,edits),len(edits)
if __name__=='__main__':
 import argparse
 p=argparse.ArgumentParser();p.add_argument('--write',action='store_true');a=p.parse_args()
 f=Path(__file__).resolve().parents[1]/'books/checkpoint-owned-retirement.lisp';out,n=rewrite(f.read_text());print(n)
 if a.write:f.write_text(out)
