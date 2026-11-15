#!/usr/bin/env python3
"""Factor the actual bind-slot preparation once, preserving the atomic adapter."""
from pathlib import Path
from lisp_rewrite import parse,match,write
ROOT=Path(__file__).resolve().parents[1]
ARGS='i s b0 b event fn2-succ-slots fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool'
WRAPPER='''(defun fn2-succ-bind-slot (%s)
 (declare (xargs :stobjs (fn2-succ-slots fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
  :guard (and (fn2-succ-slots-wfp fn2-succ-slots) (fn2-id-engine-wfp fn2-id-engine)
              (fn2-overlays-wfp fn2-overlays) (fn2-overlay-index-wfp fn2-overlay-index) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool)
              (natp s) (< s (fn2-succ-slots-rows fn2-succ-slots)) (natp i) (natp b0))))
 (b* (((mv code sid fn2-id-engine fn2-overlays fn2-fields fn2-pool)
       (fn2-succ-bind-slot-prepare %s))
      ((when (eq code :skip)) (mv :ok fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
      ((mv code o fn2-id-engine fn2-overlays) (fn2-succ-target b sid (fn2-succ-slots-size s fn2-succ-slots) fn2-id-engine fn2-overlays))
      ((unless (eq code :ok)) (mv code fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool)))
  (fn2-ov-insert o (+ b0 (* *fn2-succ-block* i)) (+ b0 *fn2-idc-eb*) fn2-overlays fn2-overlay-index fn2-fields fn2-pool)))
'''%(ARGS,ARGS)
def rewrite(src):
 if '(defun fn2-succ-bind-slot-prepare ' in src:return src
 p=parse(src);m=match(None,p.forms,deep=False,head='defun',name='fn2-succ-bind-slot')[0]
 old=src[m.start:m.end];prepared=old.replace('(defun fn2-succ-bind-slot ','(defun fn2-succ-bind-slot-prepare ',1)
 prepared=prepared.replace('(declare (xargs','(declare (ignorable b fn2-overlay-index) (xargs',1)
 tail='''      ((mv c o fn2-id-engine fn2-overlays) (fn2-succ-target b sid (fn2-succ-slots-size s fn2-succ-slots) fn2-id-engine fn2-overlays))
      ((unless (eq c :ok)) (mv c fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
      ((mv c fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
       (fn2-ov-insert o entry (+ b0 *fn2-idc-eb*) fn2-overlays fn2-overlay-index fn2-fields fn2-pool)))
  (mv c fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool)))'''
 assert tail in prepared
 prepared=prepared.replace(tail,'''      )
  (mv :ok sid fn2-id-engine fn2-overlays fn2-fields fn2-pool)))''',1)
 for code in [':bounds',':ok','code2','c']:
  oldmv=f'(mv {code} fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool)'
  newmv=f'(mv {":skip" if code==":ok" else code} 0 fn2-id-engine fn2-overlays fn2-fields fn2-pool)'
  prepared=prepared.replace(oldmv,newmv)
 shape='''
(fn2-idc-fn-shape fn2-succ-bind-slot-prepare (%s)
 ((fn2-id-engine 2) (fn2-overlays 3) (fn2-fields 4) (fn2-pool 5))
 (fn2-succ-slots fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool) t
 (fn2-succ-rehome-octets fn2-succ-fill-events fn2-succ-fill-fold-events))
'''%ARGS
 return write(src,[(m.start,m.end,prepared+shape+WRAPPER.rstrip())])
if __name__=='__main__':
 path=ROOT/'books/machines-c-bind.lisp';path.write_text(rewrite(path.read_text()))
