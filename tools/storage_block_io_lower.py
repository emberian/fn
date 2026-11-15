#!/usr/bin/env python3
"""Relocate the actual pinned storage primitive and its complete contracts."""
from pathlib import Path
import lisp_rewrite as lr

def one(source,pattern):
 xs=lr.match(pattern,lr.parse(source).forms,deep=False)
 if len(xs)!=1:raise ValueError('expected exactly one '+pattern)
 return xs[0].node

def selected(source):
 patterns=['(defun fn2-block-issue-identity-events ?*b)',
 '(defun fn2-pinned-block-io-children ?*b)',
 '(in-theory (disable fn2-pinned-block-io-children))',
 '(defun fn2-block-read-children ?*b)',
 '(fn2-pool-preserves fn2-block-read-children ?*b)',
 '(defun fn2-block-write-children ?*b)',
 '(fn2-pool-preserves fn2-block-write-children ?*b)']
 nodes=[one(source,p) for p in patterns]
 forms=lr.parse(source).forms
 for head,need in [('make-event',['fn2-block-issue-identity-events','fn2-issue-read-children']),
                   ('encapsulate',['fn2-pinned-block-io-children']),
                   ('make-event',['fn2-issue-wrapper-effect-events','fn2-block-read-children','fn2-block-write-children'])]:
  found=[n for n in forms if hasattr(n,'items') and n.items and n.items[0].low==head and all(x in source[n.start:n.end] for x in need)]
  if len(found)!=1:raise ValueError('expected one complete '+head+' containing '+str(need))
  nodes.append(found[0])
 nodes.sort(key=lambda n:n.start)
 if len({n.start for n in nodes})!=10:raise ValueError('overlapping primitive selection')
 return nodes

def transform(registry,resources):
 nodes=selected(registry)
 leaf='; Actual allocation-pinned block I/O and its owning contracts.\n; Registration/costs remain in machines-b; there is one runtime implementation.\n(in-package "ACL2")\n(include-book "arm-issue-effects")\n(include-book "read-pins")\n(include-book "commit-geometry")\n(include-book "std/util/bstar" :dir :system)\n(fn2-book-layer :b)\n(local (in-theory (disable tau-system)))\n\n'+'\n\n'.join(registry[n.start:n.end] for n in nodes)+'\n'
 changed=lr.write(registry,[(n.start,n.end,'(include-book "storage-block-io")' if i==0 else '') for i,n in enumerate(nodes)])
 n=one(resources,'(include-book "machines-b")')
 resources=lr.write(resources,[(n.start,n.end,'(include-book "storage-block-io")')])
 return changed,resources,leaf

if __name__=='__main__':
 books=Path(__file__).resolve().parents[1]/'books'
 if (books/'storage-block-io.lisp').exists():raise ValueError('refuse replacing an existing primitive leaf')
 resources=books/'run-physical-resources.lisp'
 resource_source=resources.read_text() if resources.exists() else '(include-book "machines-b")'
 a,b,c=transform((books/'machines-b.lisp').read_text(),resource_source)
 outputs=[(books/'machines-b.lisp',a),(books/'storage-block-io.lisp',c)]
 if resources.exists():outputs.append((resources,b))
 for p,s in outputs:p.write_text(s)
