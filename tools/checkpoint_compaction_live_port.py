"""Mechanical live-publication carrier port; preserves operation bodies/gates.

The sole authority change is ordered-source -> actual compacted production.
Readonly dependency formals/calls/core table declarations follow that signature.
"""
from pathlib import Path
import re
import lisp_rewrite as lr
FIXTURES=Path(__file__).resolve().parent/'fixtures/checkpoint-compaction/live'
NAMES=('checkpoint-summary-authority-live','checkpoint-live-catalog','checkpoint-live-cbase','checkpoint-live-install','checkpoint-live-retire','checkpoint-live-finish')
OLD='fn2-checkpoint-source';NEW='fn2-checkpoint-compaction'
EXTRA=['fn2-overlays','fn2-run-installed','fn2-checkpoint-predecessors','fn2-checkpoint-predecessor-control']
COMMON='fn2-checkpoint-compaction fn2-checkpoint-build fn2-csnapshot fn2-checkpoints '+' '.join(EXTRA)
def atom(x):return lr.emit(x,drop_comments=True)
def fnodes(source):return [m.node for m in lr.match('(defun ?name ?*body)',lr.parse(source).forms,deep=True)]
def rename(text):
 for f in ('wfp','phase','token','owner-kind','owner-slot','owner-gen'):
  text=text.replace(OLD+'-'+f,NEW+'-'+f)
 text=text.replace(OLD+'-rank',NEW+'-output-rank')
 return re.sub(r'(?<![\w-])'+OLD+r'(?![\w-])',NEW,text)
def projected_names(names):
 # If an inventory consumer already has the true compaction carrier, remove
 # the obsolete owner input rather than duplicate/alias two typed stobjs.
 result=[]
 for n in names:
  if n==OLD and NEW in names:continue
  n=NEW if n==OLD else n
  if n not in result:result.append(n)
 return result

def project_all(sources):
 if set(sources)!=set(NAMES):raise ValueError('incomplete live source family')
 for n,s in sources.items():
  if s!=(FIXTURES/(n+'.lisp')).read_text():raise ValueError('not frozen live class: '+n)
 signatures={}
 for s in sources.values():
  for f in fnodes(s):
   names=[atom(x) for x in f.items[2].items]
   if OLD in names:
    signatures[atom(f.items[1])]=names
 result={}
 for name,s in sources.items():
  changes=[]
  for f in fnodes(s):
   fname=atom(f.items[1])
   if fname not in signatures:continue
   text=s[f.start:f.end]
   # Rewrite real function applications by their original signature before
   # replacing the typed owner symbol. No arbitrary function is interpreted.
   call_changes=[]
   for target,formals in signatures.items():
    for m in lr.match('('+target+' ?*args)',lr.parse(text).forms,deep=True):
     call=m.node;args=call.items[1:]
     if len(args)!=len(formals):raise ValueError('old arity mismatch: '+target)
     actual={n:rename(text[a.start:a.end]) for n,a in zip(formals,args)}
     ordered=projected_names(formals)
     kept=[]
     for n in ordered:
      original=OLD if n==NEW and NEW not in formals else n
      kept.append(actual[original])
     for x in EXTRA:
      if x not in ordered:kept.append(x)
     call_changes.append((call.start,call.end,'('+target+' '+' '.join(kept)+')'))
   text=lr.write(text,call_changes)
   text=rename(text)
   parsed=lr.parse(text);new=fnodes(text)[0];decl=new.items[3];xargs=decl.items[1]
   stobjs=next(xargs.items[i+1] for i,x in enumerate(xargs.items[:-1]) if atom(x)==':stobjs')
   guard=next(xargs.items[i+1] for i,x in enumerate(xargs.items[:-1]) if atom(x)==':guard')
   old_formals=signatures[fname]
   names2=projected_names(old_formals)
   missing=[x for x in EXTRA if x not in names2]
   names2+=missing
   objs=projected_names([atom(x) for x in f.items[3].items[1].items[next(i+1 for i,x in enumerate(f.items[3].items[1].items[:-1]) if atom(x)==':stobjs')].items])
   objs += [x for x in EXTRA if x not in objs]
   edits=[(new.items[2].start,new.items[2].end,'('+' '.join(names2)+')'),
          (stobjs.start,stobjs.end,'('+' '.join(objs)+')'),
          (guard.end-1,guard.end-1,' '+' '.join('('+x+'-wfp '+x+')' for x in missing))]
   if OLD in old_formals and NEW in old_formals:
    duplicate=lr.match('('+NEW+'-wfp '+NEW+')',[guard],deep=True)
    if len(duplicate)!=2:raise ValueError('expected old/new guard duplicates')
    edits.append((duplicate[0].start,duplicate[0].end,''))
   text=lr.write(text,edits)
   if fname=='fn2-checkpoint-summary-authority-live-source-p':
    text=text.replace('(fn2-checkpoint-source-ownerp '+NEW+' fn2-csnapshot)',
                      '(fn2-checkpoint-compaction-produced-p '+COMMON+')')
    text=text.replace('*fn2-checkpoint-compaction-phase-done*','*fn2-checkpoint-compaction-phase-done*')
   changes.append((f.start,f.end,text))
  for m in lr.match('(defcost ?op ?*args)',lr.parse(s).forms,deep=True):
   node=m.node
   fields=node.items
   child=next((atom(fields[i+1]) for i,x in enumerate(fields[:-1]) if atom(x)==':child'),None)
   if child not in signatures:continue
   tables=next(fields[i+1] for i,x in enumerate(fields[:-1]) if atom(x)==':tables')
   names0=[atom(x) for x in tables.items]
   names1=projected_names([x.replace('fn2-core-','fn2-') for x in names0])
   names1 += [x for x in EXTRA if x not in names1]
   changes.append((tables.start,tables.end,'('+' '.join(x.replace('fn2-','fn2-core-',1) for x in names1)+')'))
  result[name]=lr.write(s,changes)
 from checkpoint_live_retire_emit import emit
 # The actual original-source retirement generator derives its ABI and gate
 # from the now-ported install producer. It remains the sole body recipe.
 result['checkpoint-live-retire']=emit(result['checkpoint-live-install'])
 return result
