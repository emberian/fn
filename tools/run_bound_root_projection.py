#!/usr/bin/env python3
"""Project actual reader leaves onto current ROOT without replacing foundations.

This structural source transformation does not evaluate ACL2 or qualify a cache.
"""
from pathlib import Path
import subprocess
import lisp_rewrite as lr
FROZEN='41a2e1dcd6e347ea45da7e5b1c5e8f6ac0a1b813'
RESOURCE='6753ec344'
def blob(ref,path):return subprocess.check_output(['git','show',ref+':'+path],text=True)
def one(s,p):
 xs=lr.match(p,lr.parse(s).forms,deep=False)
 if len(xs)!=1:raise ValueError('expected exactly one '+p)
 return xs[0].node

def boot(kind,provider):
 old=one(kind,'(defcolumns fn2-boot-config ?*body)')
 table=kind[old.start:old.end]
 field=one(kind,'(defconst *fn2-boot-group-entry-bytes* ?*body)')
 added=[]
 for name in ('fn2-boot-config-checkpoint-layout-ready','fn2-boot-config-geometry'):
  if lr.match('('+name+' ?*body)',lr.parse(table).forms,deep=True):raise ValueError('already extended '+name)
  found=lr.match('('+name+' ?*body)',lr.parse(provider).forms,deep=True)
  if len(found)!=1:raise ValueError('missing actual provider field '+name)
  n=found[0].node;added.append(provider[n.start:n.end])
 node=one(table,'(defcolumns fn2-boot-config ?*body)')
 options=list(node.items);at=next(i for i,n in enumerate(options) if n.low==':extra-fields')
 entries=options[at+1].items
 table=lr.write(table,[(entries[0].start,entries[0].start,'\n  '.join(added)+'\n  ')])
 lower='; Actual ROOT boot configuration, with the physical reader geometry fields.\n(in-package "ACL2")\n(include-book "columns")\n(include-book "profile")\n(fn2-book-layer :b)\n'+kind[field.start:field.end]+'\n'+table+'\n'
 kind=lr.write(kind,[(field.start,field.end,''),(old.start,old.end,'')])
 anchor='(include-book "machine-arms")'
 if kind.count(anchor)!=1:raise ValueError('boot include drift')
 return kind.replace(anchor,anchor+'\n(include-book "boot-config-state")'),lower

if __name__=='__main__':
 root=Path(__file__).resolve().parents[1]
 assert subprocess.check_output(['git','rev-parse','--show-toplevel'],cwd=root,text=True).strip()==str(root)
 paths=['books/run-physical-state.lisp','books/run-physical-bound.lisp','books/run-physical-bound-io.lisp','books/run-physical-bound-step.lisp','books/checkpoint-semantic-page.lisp','books/boot-geometry-state.lisp','tests/run-physical-bound-unit.lisp','tests/test_run_physical_bound_fixture_source.py']
 for path in paths:
  p=root/path
  if p.exists():raise ValueError('refuse overwrite '+path)
  p.write_text(blob(FROZEN,path))
 path='books/run-physical-resources.lisp'
 if (root/path).exists():raise ValueError('refuse overwrite resources')
 (root/path).write_text(blob(RESOURCE,path))
 path=root/'books/boot-kind.lisp'
 rewritten,lower=boot(path.read_text(),blob(FROZEN,'books/boot-config-state.lisp'))
 if (root/'books/boot-config-state.lisp').exists():raise ValueError('refuse overwrite boot state')
 path.write_text(rewritten);(root/'books/boot-config-state.lisp').write_text(lower)
