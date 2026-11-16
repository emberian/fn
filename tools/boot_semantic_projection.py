"""Named canonical cold-semantic projection; never imports old BOOT/CORE."""
from pathlib import Path
import subprocess
DONOR='653f3ff46'
BOOKS=('checkpoint-restore-semantic-source','checkpoint-restore-semantic','checkpoint-restore-semantic-work','checkpoint-summary-catalog','checkpoint-restore-reach-core','checkpoint-restore-semantic-reach')
def project(name,text):
 if name=='checkpoint-restore-reach-core':
  import lisp_rewrite as lr
  p=lr.parse(text);edits=[]
  for n in p.forms:
   fragment=text[n.start:n.end]
   if '(include-book "checkpoint-restore-arena")' in fragment:
    edits.append((n.start,n.end,''))
   elif 'fn2-checkpoint-restore-reach-arena-consume' in fragment:
    edits.append((n.start,n.end,''))
  text=lr.write(text,edits)
 if name=='checkpoint-restore-semantic-reach':
  text=text.replace('(include-book "checkpoint-restore-reach")','(include-book "checkpoint-restore-reach-core")')
 if name=='checkpoint-restore-semantic-work':
  # This consumer references no recovery function. It needs only the exact
  # typed run/manifest decoder already provided by its other includes.
  expected='(include-book "recovery")\n'
  if text.count(expected)!=1:raise ValueError('canonical recovery include changed')
  text=text.replace(expected,'')
 return text
if __name__=='__main__':
 for name in BOOKS:
  p=Path('books/'+name+'.lisp')
  if p.exists():raise ValueError('refusing existing consumer '+str(p))
  text=subprocess.check_output(['git','show',DONOR+':books/'+('checkpoint-restore-reach' if name=='checkpoint-restore-reach-core' else name)+'.lisp'],text=True)
  p.write_text(project(name,text))
