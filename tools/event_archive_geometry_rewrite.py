"""Replay the source-fixed/appended archive cursor class on current source.

Move actual read-count providers before their first call; preserve their ASTs.
No unrelated B state, children, allocation or C declarations are replaced.
"""
from pathlib import Path
import lisp_rewrite as lr
ROOT=Path(__file__).resolve().parents[1]
def tree(n):
 if hasattr(n,'low'):return n.low
 if hasattr(n,'prefix'):return (n.prefix,tree(n.node))
 return tuple(tree(x) for x in n.items)
def one(s,p):
 m=lr.match(p,lr.parse(s).forms,deep=False)
 if len(m)!=1:raise ValueError(p)
 return m[0].node
def machines_b(source,provider=None):
 provider=provider or (ROOT/'tools/fixtures/event-archive-geometry-provider.lisp').read_text()
 exports=lr.parse(provider).forms;actual=lr.parse(source).forms
 # A completely composed class, already before every consumer, is stable.
 present=[]
 for export in exports:
  p='('+export.items[0].low+' '+export.items[1].low+' ?*body)'
  hits=lr.match(p,actual,deep=False)
  present.append(len(hits)==1 and tree(hits[0].node)==tree(export))
 if all(present):return source
 old=one(source,'(defun fn2-b-run-cursor-rows ?*body)')
 expected=('+',('nfix',('fn2-profile-t','profile')),('*',('+','1','*fn2-b-range-source-cursors*'),('fn2-b-read-rows','profile')),'*fn2-b-seal-source-cursors*','1')
 if tree(old.items[-1])!=expected:raise ValueError('old profile cursor formula drift')
 if any(present):raise ValueError('partly installed archive class needs explicit reconciliation')
 names=['fn2-b-cursor-rows','fn2-b-cns-rows','fn2-b-auth-rows','fn2-b-read-rows']
 pats=['(defconst *fn2-b-query-read-rows* ?*body)']
 pats += ['(defun '+n+' ?*body)' for n in names]
 pats += ['(defthm '+n+'-natp ?*body)' for n in names]
 pats += ['(defthm fn2-b-read-rows-parts ?*body)',
          '(in-theory (disable fn2-b-cursor-rows fn2-b-cns-rows fn2-b-auth-rows fn2-b-read-rows))']
 nodes=[one(source,p) for p in pats]
 first=one(source,'(defconst *fn2-b-seal-source-cursors* ?*body)')
 relocated='\n'.join(source[n.start:n.end] for n in nodes)+'\n'
 edits=[(n.start,n.end,'') for n in nodes]
 edits += [(first.start,first.start,relocated),(old.start,old.end,provider.rstrip())]
 return lr.write(source,edits)
def readiness(source):
 old='''(+ (fn2-id-decides-rows fn2-id-decides) (* (+ 1 *fn2-b-range-source-cursors*) (fn2-reads-rows fn2-reads))
          *fn2-b-seal-source-cursors* 1)'''
 new='(fn2-b-run-cursor-rows-from-counts (fn2-id-decides-rows fn2-id-decides) (fn2-reads-rows fn2-reads))'
 if source.count(new)==1 and old not in source:return source
 if source.count(old)!=1:raise ValueError('runtime geometry formula drift')
 return source.replace(old,new)
if __name__=='__main__':
 for name,fn in [('machines-b',machines_b),('run-physical-readiness',readiness)]:
  p=ROOT/'books'/(name+'.lisp');p.write_text(fn(p.read_text()))
