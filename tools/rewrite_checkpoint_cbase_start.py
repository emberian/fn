#!/usr/bin/env python3
"""Extract the actual cold hold initializer for cold and live callers."""
from pathlib import Path
import re
START='      ((when (fn2-checkpoint-cbase-catalog-available-p c tag fn2-checkpoint-cbase-holds))\n'
END='      ((unless (and (fn2-checkpoint-cbase-identity-p '
def rewrite(s):
 if '(fn2-checkpoint-cbase-start 0 ' in s:return s,None
 a=s.index(START);b=s.index(END,a);old=s[a:b]
 expr=old[old.index('(let '):]
 # Drop only the b* WHEN wrapper; retain the actual sole put/mutation body.
 assert expr.endswith('fn2-alloc-edges)))\n')
 expr=expr[:-2] # remove WHEN close and newline
 expr=expr.replace('(mv :more fn2-checkpoint-cbase-holds fn2-extents fn2-alloc-edges)','(mv :more fn2-checkpoint-cbase-holds)')
 expr=re.sub(r'(\(fn2-checkpoint-summary-[\w-]+) 0 fn2-checkpoint-summary',r'\1 r fn2-checkpoint-summary',expr)
 expr=re.sub(r'\(fn2-checkpoint-cbase-summary-word ([0-7]) fn2-checkpoint-summary',r'(fn2-checkpoint-summary-descriptor-word r \1 fn2-checkpoint-summary',expr)
 inputs='fn2-checkpoint-summary fn2-ops fn2-checkpoints fn2-extents fn2-checkpoint-cbase-holds'
 helper='''; Sole actual catalog-to-hold initialization, called only after the
; cold or live constructor has established its own physical source authority.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "checkpoint-cbase-identity")
(fn2-book-layer :c)
(defun fn2-checkpoint-cbase-start (r '''+inputs+''')
 (declare (xargs :stobjs ('''+inputs+''') :guard (and '''+' '.join('('+x+'-wfp '+x+')' for x in inputs.split())+''')))
 (b* (((unless (and (natp r) (< r 2) (< r (fn2-checkpoint-summary-rows fn2-checkpoint-summary))
                    (posp (fn2-checkpoint-summary-tag r fn2-checkpoint-summary))
                    (posp (fn2-extents-rows fn2-extents)))) (mv :source fn2-checkpoint-cbase-holds))
      (c (fn2-checkpoint-summary-candidate r fn2-checkpoint-summary))
      (tag (fn2-checkpoint-summary-tag r fn2-checkpoint-summary))
      (n (fn2-extents-rows fn2-extents))
      (base (fn2-checkpoint-cbase-edge c 0 fn2-extents fn2-ops fn2-checkpoints))
      ((unless (and (unsigned-byte-p 32 base)
                    (fn2-checkpoint-cbase-catalog-available-p c tag fn2-checkpoint-cbase-holds)))
       (mv :retained fn2-checkpoint-cbase-holds)))
  '''+expr+'))\n'
 replacement=START+'''       (mv-let (code fn2-checkpoint-cbase-holds)
        (fn2-checkpoint-cbase-start 0 '''+inputs+''')
        (mv code fn2-checkpoint-cbase-holds fn2-extents fn2-alloc-edges)))
'''
 return s[:a]+replacement+s[b:],helper
if __name__=='__main__':
 p=Path('books/checkpoint-cbase-acquire.lisp');s,h=rewrite(p.read_text());p.write_text(s)
 if h:Path('books/checkpoint-cbase-start.lisp').write_text(h)
