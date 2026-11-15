#!/usr/bin/env python3
"""Bound the actual entry decoder and existing rehome loop at consumption."""
from pathlib import Path
from lisp_rewrite import parse,match,write
def rewrite_assembly(s):
 if '(defun fn2-ra-max-size-arms ' in s:return s
 helper='''(defun fn2-ra-max-size-arms (rows)
 (declare (xargs :verify-guards nil))
 (if (atom rows) nil
  (let ((layouts (fn2-decl-get :layouts (cdar rows))))
   (cons `(,(fn2-decl-get :id (cdar rows))
           (if (and (integerp lv) (< 0 lv)) ,(fn2-codec-constant (cadr layouts) "-MAX-SIZE")
             ,(fn2-codec-constant (car layouts) "-MAX-SIZE")))
         (fn2-ra-max-size-arms (cdr rows))))))
'''
 h=match('(defun fn2-ra-count-arms ?*body)',parse(s).forms,deep=False)[0];s=write(s,[(h.start,h.start,helper)])
 needle='''   (defun fn2-run-layout-keys (sid)
    (declare (xargs :guard t))
    (case sid ,@(fn2-ra-key-arms rows) (otherwise 0)))'''
 assert s.count(needle)==1
 s=s.replace(needle,needle+'''
   (defun fn2-run-layout-max-size (sid lv)
    (declare (xargs :guard t) (ignorable lv))
    (nfix (case sid ,@(fn2-ra-max-size-arms rows) (otherwise 0))))''')
 old='''         ((unless (< row (fn2-overlay-index-rows fn2-overlay-index))) (mv :bounds 0 fn2-fields)))
     (fn2-run-layout-decode'''
 new='''         ((unless (< row (fn2-overlay-index-rows fn2-overlay-index))) (mv :bounds 0 fn2-fields))
         (off (fn2-overlay-index-off row fn2-overlay-index))
         (end (min (fn2-overlays-fill o fn2-overlays)
                   (+ off (fn2-run-layout-max-size (fn2-overlays-schema o fn2-overlays) 0)))))
     (fn2-run-layout-decode'''
 assert s.count(old)==1;s=s.replace(old,new)
 old='''                            (fn2-overlay-index-off row fn2-overlay-index) (fn2-overlays-fill o fn2-overlays)'''
 assert s.count(old)==1;s=s.replace(old,'                            off end')
 return s
def rewrite_bind(s):
 old='''      ((unless (and (natp (fn2-fields-ref-off row fn2-fields)) (natp len) (unsigned-byte-p 32 off) (unsigned-byte-p 32 (+ off len))'''
 new='''      ((unless (and (natp (fn2-fields-ref-off row fn2-fields)) (natp len)
                    (fn2-run-layout-value-ok sid j len)
                    (unsigned-byte-p 32 off) (unsigned-byte-p 32 (+ off len))'''
 if new in s:return s
 assert s.count(old)==1;return s.replace(old,new)
if __name__=='__main__':
 for f,fn in [('books/runs-assemble.lisp',rewrite_assembly),('books/machines-c-bind.lisp',rewrite_bind)]:
  p=Path(f);s=p.read_text();p.write_text(fn(s))
