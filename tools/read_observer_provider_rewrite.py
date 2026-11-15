"""Canonical park dependency join; READ/CNS runtime is never rewritten."""
from pathlib import Path
import json
import lisp_rewrite as lr
DATA=json.loads((Path(__file__).parent/'fixtures/read-observer-provider-source.json').read_text())
def event(text,head,name):
 ms=lr.match('('+head+' '+name+' ?*body)',lr.parse(text).forms,deep=False)
 if len(ms)!=1:raise ValueError('one actual provider event '+name)
 return ms[0].node

def project_release(text):
 donor=DATA['release-donor'];a=event(text,'defun','fn2-run-load-park-source');b=event(donor,'defun','fn2-run-load-park-source')
 for i in (2,3):
  if text[a.items[i].start:a.items[i].end]!=donor[b.items[i].start:b.items[i].end]:raise ValueError('actual park ABI/guard changed')
 edits=[]
 if text[a.items[-1].start:a.items[-1].end]!=donor[b.items[-1].start:b.items[-1].end]:edits.append((a.items[-1].start,a.items[-1].end,donor[b.items[-1].start:b.items[-1].end]))
 if not lr.match('(defmacro fn2-run-load-park-source-mutations ?*body)',lr.parse(text).forms,deep=False):
  m=event(donor,'defmacro','fn2-run-load-park-source-mutations');edits.append((a.start,a.start,donor[m.start:m.end]+'\n'))
 return lr.write(text,edits)
if __name__=='__main__':
 p=Path(__file__).resolve().parents[1]/'books/run-physical-release.lisp';text=p.read_text();p.write_text(project_release(text))
