"""Shared advisory classification of the actual served machine-reader emitters.

Never a runtime decision or observed ACL2 expansion. Only actual directory
INDEX-ACCESS invocations select index cost; common/kind fields use FIELD-EVENTS.
Unknown symbols are absent, so source walkers must expand or refuse them.
"""
from pathlib import Path
from lisp_source import forms,read_sexp
ID_STEPS=2
INDEX_STEPS=ID_STEPS+2
FIELD_CODE_STEPS=ID_STEPS+2*INDEX_STEPS+2
FIELD_STEPS=FIELD_CODE_STEPS+2*INDEX_STEPS+2
SNAPSHOT_STEPS=FIELD_CODE_STEPS+INDEX_STEPS
ROW_STEPS=SNAPSHOT_STEPS+INDEX_STEPS+2

def machine_reader_inventory(root=Path('.')):
 root=Path(root);indices=set();directory=set();fields={'phase'};kinds={};common=set()
 for raw in forms((root/'books/machines-a-access.lisp').read_text()):
  f=read_sexp(raw);events=[f]
  if isinstance(f,list) and f[:2]==['defmacro','fn2-machine-access-events']:
   if not(f[2]==[] and f[-1][0]=='quote' and f[-1][1][0]=='progn'):raise ValueError('unknown actual machine access emitter')
   events=f[-1][1][1:]
  for event in events:
   if isinstance(event,list) and event[:1]==['fn2-machine-index-access']:
    if len(event)!=3 or not isinstance(event[1],str):raise ValueError(('unknown INDEX-ACCESS invocation',event))
    indices.add(event[1])
 if not indices:raise ValueError('actual machine INDEX-ACCESS inventory absent')
 for raw in forms((root/'books/machines.lisp').read_text()):
  f=read_sexp(raw)
  if isinstance(f,list) and f[:2]==['defconst','*fn2-machine-common-fields*']:
   declaration=f[2]
   if not(isinstance(declaration,list) and declaration[0] in ('quote','quasiquote')):raise ValueError('unknown common fields form')
   fields.update(c[0] for c in declaration[1])
 for raw in forms((root/'books/machines.lisp').read_text()):
  f=read_sexp(raw)
  if isinstance(f,list) and f[:2]==['defconst','*fn2-machine-directory-fields*']:
   if not(isinstance(f[2],list) and f[2][0]=='list'):raise ValueError('unknown directory fields form')
   for entry in f[2][1:]:
    if not(entry[0]=='assoc-eq' and entry[1][0]=='quote'):raise ValueError('unknown directory field selection')
    directory.add(entry[1][1])
 common=set(fields)
 for path in (root/'books').glob('*.lisp'):
  for raw in forms(path.read_text()):
   f=read_sexp(raw)
   if isinstance(f,list) and f[:1]==['defmachine'] and ':fields' in f:
    declaration=f[f.index(':fields')+1]
    if not isinstance(declaration,list):raise ValueError(('nonliteral machine fields',path))
    kinds[f[1]]=common|{c[0] for c in declaration};fields.update(c[0] for c in declaration)
 result={}
 for field in fields|indices:
  kind='directory-index' if field in indices else ('directory-field' if field in directory else 'kind-field')
  base='fn2-machine-'+field
  result[base]={'class':kind,'steps':INDEX_STEPS if field in indices|directory else FIELD_STEPS}
  result[base+'-read-code']={'class':kind+'-code','steps':ID_STEPS if field in indices|directory else FIELD_CODE_STEPS}
 for kind,columns in kinds.items():
  result[kind+'-snapshot-read-code']={'class':'kind-snapshot','steps':SNAPSHOT_STEPS}
  for column in columns:
   result[kind+'-row-'+column]={'class':'kind-row-directory' if column in directory else 'kind-row','steps':SNAPSHOT_STEPS+3 if column in directory else ROW_STEPS}
 return result

def machine_reader_costs(root=Path('.')):
 return {name:row['steps'] for name,row in machine_reader_inventory(root).items()}
