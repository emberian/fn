"""Generate exact old-source field comparisons and typed release composition.

Only source emission; ACL2 owns all identity, bounds, release and IO decisions.
"""
from pathlib import Path
import sys
sys.path.insert(0,'tools')
from checkpoint_live_old_identity import FIELDS
src=Path('books/checkpoint-live-install.lisp').read_text()
start=src.index('(defun fn2-checkpoint-live-replace-install-step ')
header=src[start:src.index('\n (declare',start)]
args=header.split(' ',2)[2].rsplit(')',1)[0].split()
base=args[1:]
extra=['fn2-overlays','fn2-run-cache','fn2-pool']
allargs=base+extra
outs=['fn2-checkpoint-summary','fn2-checkpoint-metadata-manifest','fn2-run-installed','fn2-overlays','fn2-run-cache','fn2-pool','fn2-checkpoint-cbase-holds','fn2-extents','fn2-alloc-edges']
def mv(code):return '(mv '+code+' '+' '.join(outs)+')'
oldout='fn2-checkpoint-summary fn2-checkpoint-metadata-manifest fn2-run-installed'
begin=src.index(' (b* (((unless (posp budget))',start)
end=src.index('  (stage ',begin)
gate=src[begin:end].replace(oldout,' '.join(outs))
# put readonly identity projection in a generated source mapping, never a comparator in Python.
s='''; Exact old source retirement hidden by the real exclusive publication receipt.
; No allocator FREE, new lease reservation or I/O issue occurs here. Resident
; page ownership follows the existing sealer continuation; physical catalogs
; keep promises until their existing bounded C-base drain completes.
(in-package "ACL2")
(include-book "checkpoint-live-install")
(include-book "checkpoint-cbase-release")
(fn2-book-layer :c)
(defconst *fn2-live-replace-stage-old-base* 4)
(defconst *fn2-live-replace-stage-resources* 5)
(defun fn2-checkpoint-live-old-source-p (e fn2-checkpoint-metadata-manifest fn2-overlays fn2-run-installed)
 (declare (xargs :stobjs (fn2-checkpoint-metadata-manifest fn2-overlays fn2-run-installed)
 :guard (and (fn2-checkpoint-metadata-manifest-wfp fn2-checkpoint-metadata-manifest)
             (fn2-overlays-wfp fn2-overlays) (fn2-run-installed-wfp fn2-run-installed))))
 (and (natp e) (< e (fn2-checkpoint-metadata-manifest-rows fn2-checkpoint-metadata-manifest))
  (let ((r (fn2-checkpoint-metadata-manifest-catalog-source-row e fn2-checkpoint-metadata-manifest)))
   (case (fn2-checkpoint-metadata-manifest-catalog-source-kind e fn2-checkpoint-metadata-manifest)
    (0 (and (< r (fn2-overlays-rows fn2-overlays))
        (member-equal (fn2-overlays-phase r fn2-overlays) (list *fn2-overlay-phase-active* *fn2-overlay-phase-frozen*))
        (= (fn2-overlays-schema r fn2-overlays) (fn2-checkpoint-metadata-manifest-catalog-schema e fn2-checkpoint-metadata-manifest))
        (= (fn2-overlays-seq r fn2-overlays) (fn2-checkpoint-metadata-manifest-catalog-source-order e fn2-checkpoint-metadata-manifest))
'''
over={'slot':'slot','gen':'gen','entries':'count','okind':'okind','oslot':'oslot','ogen':'ogen'}
for f,col in over.items():s+=f'        (= (fn2-overlays-{col} r fn2-overlays) (fn2-checkpoint-metadata-manifest-catalog-old-{f} e fn2-checkpoint-metadata-manifest))\n'
s+='''        ))
    (1 (and (< r (fn2-run-installed-rows fn2-run-installed))
        (= (fn2-run-installed-state r fn2-run-installed) *fn2-run-installed-state-live*)
        (= (fn2-run-installed-schema r fn2-run-installed) (fn2-checkpoint-metadata-manifest-catalog-schema e fn2-checkpoint-metadata-manifest))
        (= (fn2-run-installed-run r fn2-run-installed) (fn2-checkpoint-metadata-manifest-catalog-source-order e fn2-checkpoint-metadata-manifest))
'''
for f,_ in FIELDS:
 col={'allocation':'counter','tag':'catalog-tag'}.get(f,f)
 s+=f'        (= (fn2-run-installed-{col} r fn2-run-installed) (fn2-checkpoint-metadata-manifest-catalog-old-{f} e fn2-checkpoint-metadata-manifest))\n'
s+='''        ))
    (otherwise nil)))))
(defmacro fn2-checkpoint-live-retire-events ()
 '(progn
'''
s+='(defun fn2-checkpoint-live-replace-retire-step (budget '+' '.join(allargs)+')\n'
s+=' (declare (xargs :stobjs ('+' '.join(allargs)+') :guard (and '+' '.join('('+a+'-wfp '+a+')' for a in allargs)+')))\n'
s+=gate
s+='''  (i (fn2-checkpoint-summary-cursor 1 fn2-checkpoint-summary))
  (stage (fn2-checkpoint-summary-application-stage 1 fn2-checkpoint-summary)))
  (cond
   ((= stage *fn2-live-replace-stage-retire*)
    (b* ((limit (fn2-checkpoint-metadata-manifest-rows fn2-checkpoint-metadata-manifest))
     ((when (= i limit))
      (if (not (= (fn2-checkpoint-summary-target 1 fn2-checkpoint-summary) (fn2-checkpoint-summary-count 1 fn2-checkpoint-summary)))
       '''+mv(':coverage')+'''
       (let ((fn2-checkpoint-summary (fn2-checkpoint-summary-put 1 (application-stage *fn2-live-replace-stage-old-base*) (cursor 0) (target 0))))
        '''+mv(':more')+''')))
     ((unless (and (< i limit) (unsigned-byte-p 32 (+ 1 i)))) '''+mv(':bounds')+''')
     ((unless (= (fn2-checkpoint-metadata-manifest-catalog-token i fn2-checkpoint-metadata-manifest) (fn2-checkpoint-summary-generation 1 fn2-checkpoint-summary)))
      (let ((fn2-checkpoint-summary (fn2-checkpoint-summary-set-cursor 1 (+ 1 i) fn2-checkpoint-summary))) '''+mv(':more')+'''))
     ((unless (and (fn2-checkpoint-live-installed-p i fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-checkpoint-metadata-manifest fn2-run-installed)
                   (unsigned-byte-p 32 (+ 1 (fn2-checkpoint-summary-target 1 fn2-checkpoint-summary))))) '''+mv(':source')+''')
     (oldstage (fn2-checkpoint-metadata-manifest-catalog-old-stage i fn2-checkpoint-metadata-manifest))
     (r (fn2-checkpoint-metadata-manifest-catalog-source-row i fn2-checkpoint-metadata-manifest))
     (kind (fn2-checkpoint-metadata-manifest-catalog-source-kind i fn2-checkpoint-metadata-manifest)))
    (cond
     ((= oldstage 0)
      (b* (((unless (fn2-checkpoint-live-old-source-p i fn2-checkpoint-metadata-manifest fn2-overlays fn2-run-installed)) '''+mv(':changed')+'''))
       (if (= kind 0)
        (if (= (fn2-overlays-phase r fn2-overlays) *fn2-overlay-phase-active*)
         (mv-let (code fn2-overlays) (fn2-ov-freeze r fn2-overlays) '''+mv('(if (eq code :ok) :more code)')+''')
         (b* (((mv code fn2-overlays fn2-pool) (fn2-seal-retire r fn2-overlays fn2-pool))
              ((unless (member-eq code '(:ok :retired))) '''+mv('code')+''')
              (fn2-checkpoint-metadata-manifest (fn2-checkpoint-metadata-manifest-set-catalog-old-stage i 2 fn2-checkpoint-metadata-manifest)))
          '''+mv(':more')+'''))
        (b* (((mv code fn2-run-installed) (fn2-run-retire r fn2-run-installed))
             ((unless (eq code :ok)) '''+mv('code')+''')
             (fn2-checkpoint-metadata-manifest (fn2-checkpoint-metadata-manifest-set-catalog-old-stage i 1 fn2-checkpoint-metadata-manifest)))
         '''+mv(':more')+'''))))
     ((= oldstage 1)
      (b* (((unless (and (= kind 1) (< r (fn2-run-installed-rows fn2-run-installed)))) '''+mv(':source')+''')
           ((when (= (fn2-run-installed-state r fn2-run-installed) *fn2-run-installed-state-free*))
            (let ((fn2-checkpoint-metadata-manifest (fn2-checkpoint-metadata-manifest-set-catalog-old-stage i 2 fn2-checkpoint-metadata-manifest))) '''+mv(':more')+'''))
           ((when (= (fn2-run-installed-physical r fn2-run-installed) 1))
            (mv-let (code fn2-checkpoint-summary fn2-run-installed)
             (fn2-checkpoint-summary-row-retire-row 0 r fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-checkpoint-cbase-holds fn2-run-installed)
             '''+mv('(if (eq code :retired) :more code)')+'''))
           ((mv code fn2-run-installed fn2-run-cache fn2-pool) (fn2-seal-release-row r fn2-run-installed fn2-run-cache fn2-pool)))
       '''+mv('code')+'''))
     ((= oldstage 2)
      (let ((fn2-checkpoint-summary (fn2-checkpoint-summary-put 1 (cursor (+ 1 i)) (target (+ 1 (fn2-checkpoint-summary-target 1 fn2-checkpoint-summary)))))) '''+mv(':more')+'''))
     (t '''+mv(':state')+'''))))
   ((= stage *fn2-live-replace-stage-old-base*)
    (b* (((when (and (= (fn2-checkpoint-summary-tag 0 fn2-checkpoint-summary) 0)
                    (= (fn2-checkpoint-summary-installed 0 fn2-checkpoint-summary) 0)
                    (= (fn2-checkpoint-summary-lease-count 0 fn2-checkpoint-summary) 0)))
           (let ((fn2-checkpoint-summary (fn2-checkpoint-summary-put 1 (application-stage *fn2-live-replace-stage-resources*) (cursor 0)))) '''+mv(':resources')+'''))
         ((mv code fn2-checkpoint-summary fn2-checkpoint-cbase-holds fn2-extents fn2-alloc-edges fn2-run-installed)
          (fn2-checkpoint-cbase-row-release-step budget 0 fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-checkpoint-cbase-holds fn2-run-installed fn2-checkpoints fn2-extents fn2-ops fn2-alloc-edges))
         ((unless (eq code :released)) '''+mv('code')+''')
         (fn2-checkpoint-summary (fn2-checkpoint-summary-put 1 (application-stage *fn2-live-replace-stage-resources*) (cursor 0))))
     '''+mv(':resources')+'''))
   (t '''+mv(':state')+'''))))
))
'''
s+='(defcost fn2-checkpoint-live-replace-retire-step-op :child fn2-checkpoint-live-replace-retire-step :answers t :steps *fn2-work-stage* :bytes 64 :descriptors 0\n :tables ('+' '.join(a.replace('fn2-','fn2-core-',1) for a in allargs)+')\n :doc "Release one exact captured predecessor under the held exclusive publication receipt; no new allocation or IO.")\n'
Path('books/checkpoint-live-retire.lisp').write_text(s)
