"""Require the real root1/archive cursor pair before selecting either row."""
from pathlib import Path
import sys
import lisp_rewrite as lr
GETTERS=('fn2-run-loads-rows','fn2-run-cursors-rows')
def transform(text):
 parsed=lr.parse(text);edits=[]
 for getter in GETTERS:
  for m in lr.match('(< 0 ('+getter+' ?table))',parsed.forms,deep=True):
   old=text[m.start:m.end];call=old[len('(< 0 '):-1]
   edits.append((m.start,m.end,'(fn2-b-fixed-cursor-rows-p '+call+')'))
 return lr.write(text,edits)
if __name__=='__main__':
 for name in sys.argv[1:]:
  p=Path(name);p.write_text(transform(p.read_text()))
