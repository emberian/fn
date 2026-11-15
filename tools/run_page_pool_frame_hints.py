"""Keep generated run-page frame proofs in their public accessor form."""
import sys
from pathlib import Path
import lisp_rewrite as lr
TABLES=('fn2-pool','fn2-fields','fn2-run-writers','fn2-run-restarts','fn2-fc-context')
def hint(table):return " :hints ((fn2-columns-guard-hint '("+table+") nil nil world))"
def transform(text):
 parsed=lr.parse(text);edits=[]
 for table in TABLES:
  for m in lr.match('('+table+'-preserves ?*args)',parsed.forms,deep=False):
   call=text[m.start:m.end];expected=hint(table)
   if ':hints' in call:
    if expected.strip() not in call:raise ValueError('Existing proof hint requires explicit composition')
    continue
   edits.append((m.end-1,m.end-1,'\n'+expected))
 return lr.write(text,edits)
if __name__=='__main__':
 p=Path(sys.argv[1]);p.write_text(transform(p.read_text()))
