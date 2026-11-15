#!/usr/bin/env python3
"""Move the actual boot declaration and geometry helpers without naming fields.

Replay on the integrator's current source; all new configuration fields and all
unrelated bank/recovery declarations remain intact. No ACL2 evaluation occurs.
"""
from pathlib import Path
import lisp_rewrite as lr

def one(source,pattern):
 matches=lr.match(pattern,lr.parse(source).forms,deep=False)
 if len(matches)!=1:raise ValueError('expected exactly one '+pattern)
 return matches[0].node

def move(source,patterns):
 nodes=[one(source,p) for p in patterns]
 return lr.write(source,[(n.start,n.end,'') for n in nodes]), '\n'.join(source[n.start:n.end] for n in nodes)+'\n'

def kind(source):
 rewritten,body=move(source,['(defconst *fn2-boot-group-entry-bytes* ?*body)','(defcolumns fn2-boot-config ?*body)'])
 old='(include-book "machine-arms")'
 if rewritten.count(old)!=1:raise ValueError('boot kind include drift')
 rewritten=rewritten.replace(old,old+'\n(include-book "boot-config-state")')
 state='; Actual boot configuration declaration, independent of boot orchestration.\n(in-package "ACL2")\n(include-book "columns")\n(include-book "profile")\n(fn2-book-layer :b)\n'+body
 return rewritten.rstrip()+'\n',state

def geometry(source):
 patterns=['(defun fn2-checkpoint-boot-geometry-word ?*body)',
 '(defthm fn2-checkpoint-boot-geometry-word-type ?*body)',
 '(in-theory (disable fn2-checkpoint-boot-geometry-word))',
 '(defun fn2-checkpoint-boot-geometry-copy ?*body)',
 '(defun fn2-checkpoint-boot-geometry-load ?*body)',
 '(fn2-digests-preserves fn2-checkpoint-boot-geometry-load ?*body)']
 rewritten,body=move(source,patterns)
 old='(include-book "checkpoint-publication")'
 if rewritten.count(old)!=1:raise ValueError('checkpoint boot include drift')
 rewritten=rewritten.replace(old,old+'\n(include-book "boot-geometry-state")')
 lower='; Same checked boot geometry, shared by physical readers and publication.\n(in-package "ACL2")\n(include-book "boot-config-state")\n(include-book "format-check")\n(fn2-book-layer :b)\n'+body
 return rewritten.rstrip()+'\n',lower

if __name__=='__main__':
 books=Path(__file__).resolve().parents[1]/'books'
 for old,new,transform in [('boot-kind.lisp','boot-config-state.lisp',kind),('checkpoint-boot.lisp','boot-geometry-state.lisp',geometry)]:
  rewritten,lower=transform((books/old).read_text())
  (books/old).write_text(rewritten);(books/new).write_text(lower)
