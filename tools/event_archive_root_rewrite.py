"""Factor the actual cached archive root constructor, preserving manifest use."""
from pathlib import Path
import lisp_rewrite as lr
def transform(source):
 if '(defun fn2-event-archive-cold-start-root ' in source:return source,None
 f=lr.match('(fn2-event-archive-operation (fn2-event-archive-cold-cursor-begin ?*args) ?*body)',lr.parse(source).forms,deep=False)
 if len(f)!=1:raise ValueError('actual borrowed begin missing')
 body=f[0].node.items[-1];bindings=body.items[1].items
 starts=[i for i,b in enumerate(bindings) if lr.match('(fn2-run-cursor-start ?*args)',[b])]
 if len(starts)!=1:raise ValueError('actual cursor start drift')
 i=starts[0];kernel=bindings[i:i+3]
 if not lr.match('(fn2-run-cursors-put c ?*args)',[kernel[-1]]):raise ValueError('physical fields drift')
 text='\n      '.join(source[n.start:n.end] for n in kernel)
 replacements=[('(fn2-run-cursor-start c 10','(fn2-run-cursor-start c schema'),
  ('(fn2-event-archive-manifest-unit 1 fn2-event-archive)','unit'),
  ('(fn2-event-archive-manifest-allocation 1 fn2-event-archive)','allocation'),
  ('(fn2-event-archive-manifest-epoch 1 fn2-event-archive)','epoch'),
  ('(fn2-event-archive-checkpoint 1 fn2-event-archive)','run'),
  ('(mv code fn2-event-archive fn2-run-loads fn2-run-cursors fn2-fields)','(mv code fn2-run-cursors)')]
 for old,new in replacements:
  if text.count(old)!=1:raise ValueError('root field drift '+old)
  text=text.replace(old,new)
 if text.count(':manifest')!=8:raise ValueError('root digest class drift')
 text=text.replace(':manifest','kind')
 helper='''; One concrete root constructor for both retained manifest/member Refs.
; Callers establish the exact candidate and typed decoded source before entry.
(defun fn2-event-archive-cold-start-root (c kind base fn2-event-archive fn2-run-cursors)
 (declare (xargs :stobjs (fn2-event-archive fn2-run-cursors)
 :guard (and (fn2-event-archive-wfp fn2-event-archive) (fn2-run-cursors-wfp fn2-run-cursors))))
 (b* (((unless (and (< 1 (fn2-event-archive-rows fn2-event-archive)) (member-eq kind '(:manifest :member))))
       (mv :source fn2-run-cursors))
      (manifest (eq kind :manifest))
      (height (if manifest (fn2-event-archive-manifest-height 1 fn2-event-archive) (fn2-event-archive-member-height 1 fn2-event-archive)))
      (unit (if manifest (fn2-event-archive-manifest-unit 1 fn2-event-archive) (fn2-event-archive-member-unit 1 fn2-event-archive)))
      (epoch (if manifest (fn2-event-archive-manifest-epoch 1 fn2-event-archive) (fn2-event-archive-member-epoch 1 fn2-event-archive)))
      (allocation (if manifest (fn2-event-archive-manifest-allocation 1 fn2-event-archive) (fn2-event-archive-member-allocation 1 fn2-event-archive)))
      (schema (if manifest 10 *fn2-event-archive-schema*))
      (run (if manifest (fn2-event-archive-checkpoint 1 fn2-event-archive) (fn2-event-archive-member-last-event 1 fn2-event-archive)))
      (kind-owner (fn2-event-archive-owner-kind 1 fn2-event-archive)) (owner (fn2-event-archive-owner-slot 1 fn2-event-archive)) (gen (fn2-event-archive-owner-gen 1 fn2-event-archive))
      ((unless (and (posp height) (<= height *fn2-run-max-levels*))) (mv :bounds fn2-run-cursors))
      '''+text.replace('base kind owner gen fn2-run-cursors','base kind-owner owner gen fn2-run-cursors')+''')
  (mv :ok fn2-run-cursors)))
(fn2-run-cursors-preserves fn2-event-archive-cold-start-root (c kind base fn2-event-archive fn2-run-cursors) :position 1 :raw-rows t)
'''
 call='''((mv code fn2-run-cursors) (fn2-event-archive-cold-start-root c :manifest base fn2-event-archive fn2-run-cursors))
      '''+source[kernel[1].start:kernel[1].end]
 after=lr.write(source,[(kernel[0].start,kernel[-1].end,call)])
 anchor=lr.match('(assert-event (<= (+ *fn2-run-reader-fields* 3) 128))',lr.parse(after).forms,deep=False)[0].node
 after=lr.write(after,[(anchor.start,anchor.start,helper+'\n')])
 return after,helper
if __name__=='__main__':
 p=Path(__file__).resolve().parents[1]/'books/event-archive-cold-cursor.lisp'
 after,helper=transform(p.read_text());p.write_text(after)
