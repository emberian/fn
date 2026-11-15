"""Actual known leaf arities and explicit physical DSL call signatures only."""
from pathlib import Path
import lisp_rewrite as lr
from read_observer_rewrite import nodes,sym
import read_observer_arity_check as arity
arity.errors=[];arity.checked=0
p=lr.parse(Path('books/cursor-physical-admission.lisp').read_text())
for n in p.forms:
 if isinstance(n,lr.Lst) and len(n.items)>3 and sym(n.items[0])=='defun':
  for body in n.items[3:]:arity.visit(body)
expected={'fn2-run-page-bind':4,'fn2-run-page-step':2,'fn2-run-page-read':2,'fn2-run-page-release':4,
 'fn2-run-page-bundle-reserve':4,'fn2-read-loader-owner-op':4,'fn2-read-loader-drain-op':5,
 'fn2-read-loader-member-release-op':5,'fn2-cursor-article-query-reserve':4,'fn2-cursor-physical-count':0,
 'fn2-cursor-request-acquire':2,'fn2-cursor-request-release':2}
checked=0
for f in lr.parse(Path('books/cursor.lisp').read_text()).forms:
 for n in nodes(f):
  if isinstance(n,lr.Lst) and n.items and sym(n.items[0]) in expected:
   checked+=1
   if len(n.items)-1!=expected[sym(n.items[0])]:arity.errors.append((sym(n.items[0]),len(n.items)-1,expected[sym(n.items[0])]))
print('NNTP leaf calls:',arity.checked,'physical DSL calls:',checked,'errors:',arity.errors)
assert not arity.errors
