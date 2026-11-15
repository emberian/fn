"""Exact composition of C-slot arena providers onto the real DRAINING protocol."""
from pathlib import Path
import hashlib,json
import lisp_rewrite as lr
import identity_arena_thread as thread
ROOT=Path(__file__).resolve().parents[1]
RECORD=ROOT/'tools/fixtures/identity-arena-draining-thread.json'
def one(s,name):
 n=lr.match('_',lr.parse(s).forms,head='defun',name=name)
 assert len(n)==1,name
 return n[0].node

def project(row):
 original=row['original'];assert hashlib.sha256(original.encode()).hexdigest()==row['sha256']
 s,n=thread.transform(original,row['file'].startswith('tests/'),set(row['targets']));assert n==row['edits']
 if row['file']=='books/sealer.lisp':
  s=s.replace('(include-book "machines-c-groups")','(include-book "machines-c-groups")\n(include-book "identity-arena-credit")',1)
  node=one(s,'fn2-seal-retire');f=s[node.start:node.end]
  for binding in ['      (gen (fn2-overlays-gen o fn2-overlays))\n','      (okind (fn2-overlays-okind o fn2-overlays))\n','      (oslot (fn2-overlays-oslot o fn2-overlays))\n','      (ogen (fn2-overlays-ogen o fn2-overlays))\n']:
   assert f.count(binding)==1;f=f.replace(binding,'')
  old='(fn2-pool-release slot gen okind oslot ogen fn2-pool)';assert f.count(old)==1
  f=f.replace(old,'(fn2-idc-arena-return o commitrows fn2-overlays fn2-pool)')
  s=s[:node.start]+f+s[node.end:]
 elif row['file']=='books/machines-c-sealer-kind.lisp':
  s=s.replace(" '(fn2-core-seals", " '(fn2-commit-table fn2-core-seals")
  s=s.replace(':tables (fn2-core-seals',':tables (fn2-commit-table fn2-core-seals')
 elif row['file']=='books/machines-c-sealer-events.lisp':
  nodes=lr.match('_',lr.parse(s).forms,deep=True,head='defun',name='fn2-sealer-step');assert len(nodes)==1;node=nodes[0].node;f=s[node.start:node.end]
  old='((fn2-seals (fn2-core-seals fn2-core))';assert f.count(old)==1
  f=f.replace(old,'((fn2-commit (fn2-commit-table fn2-core))\n                (fn2-seals (fn2-core-seals fn2-core))')
  old='(fn2-seal-step commitrows';assert f.count(old)==1;f=f.replace(old,'(fn2-seal-step (fn2-commit-rows fn2-commit)')
  s=s[:node.start]+f+s[node.end:]
 return s

def before_current(file,text):
 for row in json.loads(RECORD.read_text()):
  if row['file']==file:
   expected=project(row);assert text==expected,('unexpected C-slot/DRAINING composition',file)
   return row['original']
 return text
