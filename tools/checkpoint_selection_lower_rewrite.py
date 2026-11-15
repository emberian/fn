#!/usr/bin/env python3
"""Lower the same readonly selection predicates; preserve their source bytes."""
from pathlib import Path
import lisp_rewrite as lr
GROUPS = {
 'checkpoint-recovery-census': ('anchor-bytes-p', 'descriptor-bytes-p', 'bound-p'),
 'checkpoint-selected-source': ('descriptor-p', 'HEAD', 'current-p'),
}
def names(book):
 return [('fn2-checkpoint-selected-head-p' if s == 'HEAD' else 'fn2-'+book+'-'+s) for s in GROUPS[book]]
def extract(text, book):
 nodes=[]
 for name in names(book):
  found=lr.match('(defun '+name+' ?*body)',lr.parse(text).forms,deep=False)
  if len(found)!=1: raise ValueError('expected one '+name)
  nodes.append(found[0].node)
 deps = ('origin', 'boot-config-state', 'checkpoint-recovery-census-state', 'checkpoint-recovery-evidence-state') if book == 'checkpoint-recovery-census' else ('checkpoint-recovery-census-identity', 'checkpoint-selected-source-state')
 lower='; Actual readonly identity predicates, independent of boot orchestration.\n(in-package "ACL2")\n'+''.join('(include-book "'+d+'")\n' for d in deps)+'(fn2-book-layer :b)\n\n'+'\n\n'.join(text[n.start:n.end] for n in nodes)+'\n'
 edits=[(n.start,n.end,'') for n in nodes]
 rewritten=lr.write(text,edits)
 marker='(fn2-book-layer :b)'
 if rewritten.count(marker)!=1: raise ValueError('expected one layer declaration')
 rewritten=rewritten.replace(marker,'(include-book "'+book+'-identity")\n'+marker,1)
 return rewritten,lower
if __name__ == '__main__':
 books=Path(__file__).resolve().parents[1]/'books'
 for book in GROUPS:
  upper,lower=extract((books/(book+'.lisp')).read_text(),book)
  (books/(book+'.lisp')).write_text(upper)
  (books/(book+'-identity.lisp')).write_text(lower)
 p=books/'checkpoint-projection-state.lisp'
 s=p.read_text()
 old='(include-book "checkpoint-selected-source")'
 if s.count(old)!=1: raise ValueError('expected projection operational edge')
 p.write_text(s.replace(old,'(include-book "checkpoint-selected-source-identity")'))
