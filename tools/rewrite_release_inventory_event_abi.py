"""Extend the actual event producer/authority family with canonical inventory.
Only named declarations/calls and their emitted return/preservation class move.
"""
from pathlib import Path
import lisp_rewrite as lr
BUILD='fn2-release-inventory-build'
ADDS={name:(BUILD,) for name in (
 'fn2-event-build-frontier-header','fn2-event-build-source-step','fn2-event-build-consume-page',
 'fn2-event-producer-donep','fn2-event-producer-rearm',
 'fn2-checkpoint-summary-authority-live-source-p','fn2-checkpoint-summary-authority-live-begin',
 'fn2-checkpoint-summary-authority-live-step')}
ADDS['fn2-event-producer-step']=(BUILD,'fn2-release-evidence','fn2-release-evidence-candidates')
OLDOUTS={
 'fn2-event-producer-step':('fn2-event-build','fn2-event-read','fn2-journal-members','fn2-mk','fn2-fc','fn2-fc-context','fn2-b3','fn2-checkpoint-construction','fn2-extents','fn2-alloc-edges','fn2-fields','fn2-pool','fn2-digests','fn2-control'),
 'fn2-event-producer-rearm':('fn2-event-build','fn2-event-read','fn2-journal-members')}
FILES=('event-build','event-producer','event-rearm','event-build-kind','checkpoint-summary-authority-live')
def atoms(node):return [x.low for x in node.items if isinstance(x,lr.Atom)]
def rewrite(text):
 p=lr.parse(text);edits={}
 def add(node,strings):
  if strings:
   at=node.end-1;prior=edits.get(at,'');extra=' '.join(s for s in strings if s not in prior)
   if extra:edits[at]=prior+' '+extra
 def missing(node,names):return [n for n in names if n not in atoms(node)]
 defs={}
 for m in lr.match('(defun ?name ?args ?*body)',p.forms):
  name=m.captures['name'].low
  if name not in ADDS:continue
  defs[name]=m
  add(m.captures['args'],missing(m.captures['args'],ADDS[name]))
  tables=[]
  for q in lr.match('(xargs ?*a :stobjs ?tables ?*z)',[m.node]):
   table=q.captures['tables'];tables=atoms(table)+[x for x in ADDS[name] if x not in atoms(table)]
   add(table,missing(table,ADDS[name]))
  for q in lr.match('(xargs ?*a :guard ?guard ?*z)',[m.node]):
   g=q.captures['guard'];assert isinstance(g,lr.Lst) and g.items[0].low=='and',name
   source=text[g.start:g.end]
   add(g,['('+pred+' '+t+')' for t in tables for pred in (t+'p',t+'-wfp') if '('+pred+' '+t+')' not in source])
  if name in OLDOUTS:
   for q in lr.match('(mv ?code ?*outs)',[m.node]):
    values=q.captures['outs']
    if len(values)==len(OLDOUTS[name]) and all(isinstance(v,lr.Atom) for v in values) and [v.low for v in values]==list(OLDOUTS[name]):add(q.node,[BUILD])
 for name,extra in ADDS.items():
  for m in lr.match('('+name+' ?*args)',p.forms):add(m.node,missing(m.node,extra))
 # Actual core-borrowing unit adapters use the same canonical child. Grow
 # their binding and child-writeback tuple; do not seed a replacement state.
 for m in lr.match('(stobj-let ?bindings ?outputs ?body ?return)',p.forms):
  body=m.captures['body'];bindings=m.captures['bindings'];needed=[];mut=[]
  for name,extra in ADDS.items():
   if lr.match('('+name+' ?*args)',[body]):
    needed.extend(extra)
    if name in OLDOUTS:mut.append(BUILD)
  present=[n.items[0].low for n in bindings.items if isinstance(n,lr.Lst) and n.items and isinstance(n.items[0],lr.Atom)]
  add(bindings,['('+t+' (fn2-core-'+t[4:]+' fn2-core))' for t in dict.fromkeys(needed) if t not in present])
  add(m.captures['outputs'],missing(m.captures['outputs'],list(dict.fromkeys(mut))))
 # Explicit preservation declarations retain their output claims and grow the
 # full actual readonly typed domain, not a WFP-only forged source domain.
 for m in lr.match('(?family ?name ?args ?*rest)',p.forms):
  family=m.captures['family'];name=m.captures['name']
  if not isinstance(family,lr.Atom) or not family.low.endswith('-preserves') or not isinstance(name,lr.Atom) or name.low not in defs:continue
  n=name.low;add(m.captures['args'],missing(m.captures['args'],ADDS[n]));items=m.node.items
  tables=[]
  for q in lr.match('(xargs ?*a :stobjs ?tables ?*z)',[defs[n].node]):tables=atoms(q.captures['tables'])
  tables+= [t for t in ADDS[n] if t not in tables]
  at=next((i for i,x in enumerate(items) if isinstance(x,lr.Atom) and x.low==':hyps'),None)
  hyps=['('+pred+' '+t+')' for t in tables for pred in (t+'p',t+'-wfp')]
  if at is None:add(m.node,[':hyps ('+' '.join(hyps)+')'])
  else:
   node=items[at+1];source=text[node.start:node.end];add(node,[h for h in hyps if h not in source])
  if n in OLDOUTS:
   at=next((i for i,x in enumerate(items) if isinstance(x,lr.Atom) and x.low==':carriers'),None)
   carrier='('+BUILD+' '+str(len(OLDOUTS[n])+1)+' :prefix "-RELEASE-INVENTORY")'
   if at is None:add(m.node,[':carriers ('+carrier+')'])
   elif BUILD not in text[items[at+1].start:items[at+1].end]:add(items[at+1],[carrier])
 # Child footprints are derived from the changed lower signature; include
 # the same canonical tables in the public declaration, including readonly.
 for m in lr.match('(defcost ?name ?*rest)',p.forms):
  items=m.node.items;at=next((i for i,x in enumerate(items) if isinstance(x,lr.Atom) and x.low==':child'),None)
  if at is None or not isinstance(items[at+1],lr.Atom) or items[at+1].low not in ADDS:continue
  tables=next((items[i+1] for i,x in enumerate(items) if isinstance(x,lr.Atom) and x.low==':tables'),None)
  extra=['fn2-core-'+t[4:] for t in ADDS[items[at+1].low]]
  if tables is None:add(m.node,[':tables ('+' '.join(extra)+')'])
  else:add(tables,missing(tables,extra))
 return lr.write(text,[(at,at,value) for at,value in edits.items()]),len(edits)
if __name__=='__main__':
 import argparse
 parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
 root=Path(__file__).resolve().parents[1]
 for name in FILES:
  path=root/'books'/(name+'.lisp');out,count=rewrite(path.read_text());print(name,count)
  if args.write:path.write_text(out)
