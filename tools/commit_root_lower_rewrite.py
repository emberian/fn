#!/usr/bin/env python3
"""Move the actual commit-root declaration below B registration, without edits."""
from pathlib import Path
import lisp_rewrite as lr

def transform(machines, directory):
    found=lr.match('(defcolumns fn2-commit-root ?*body)',lr.parse(machines).forms,deep=False)
    if len(found)!=1: raise ValueError('expected one actual commit-root declaration')
    n=found[0].node
    lower='; Actual commit directory carrier, independent of B registration.\n(in-package "ACL2")\n(include-book "columns")\n(fn2-book-layer :b)\n'+machines[n.start:n.end]+'\n'
    rewritten=lr.write(machines,[(n.start,n.end,'(include-book "commit-root-state")')])
    includes=lr.match('(include-book "machines-b")',lr.parse(directory).forms,deep=False)
    if len(includes)!=1: raise ValueError('expected one directory registration dependency')
    n=includes[0].node
    directory=lr.write(directory,[(n.start,n.end,'(include-book "commit-root-state")')])
    return rewritten,directory,lower

if __name__=='__main__':
    books=Path(__file__).resolve().parents[1]/'books'
    a,b,c=transform((books/'machines-b.lisp').read_text(),(books/'commit-directory.lisp').read_text())
    for name,s in [('machines-b.lisp',a),('commit-directory.lisp',b),('commit-root-state.lisp',c)]:
        (books/name).write_text(s)
