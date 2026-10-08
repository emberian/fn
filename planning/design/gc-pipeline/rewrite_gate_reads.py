"""Read attachment pointers under K, then release it before entering Gate."""
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'tools'))
import lisp_rewrite as rw
from proof_repl import spans

def transform(text):
 edits=[]
 for a,b in spans(text):
  form=text[a:b]
  if '(fnn-log-pipeline-gate ' not in form or form.startswith('(defun fnn-log-pipeline-gate-read '): continue
  for hit in rw.match('_',rw.parse(form).forms,head='fnn-log-pipeline-gate',arity=1):
   node=hit.node.items[0];edits.append((a+node.start,a+node.end,'fnn-log-pipeline-gate-read'))
 return rw.write(text,edits)
assert transform('(if (fnn-log-pipeline-gate log) x y)')=='(if (fnn-log-pipeline-gate-read log) x y)'
assert transform('; (fnn-log-pipeline-gate log)\n(foo)')=='; (fnn-log-pipeline-gate log)\n(foo)'
if __name__=='__main__':
 p=ROOT/'host/native/io.lisp';p.write_text(transform(p.read_text()))
