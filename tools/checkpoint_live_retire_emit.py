"""Emit one-original-source retirement under actual durable replacement.

Dense output-rank mapping is built once from actual accepted manifest cells;
all old identities come from the original HELD inventory, never one per output.
"""
from pathlib import Path
from checkpoint_live_old_identity import FIELDS
def emit(src):
 a=src.index('(defun fn2-checkpoint-live-replace-install-step ');h=src[a:src.index('\n (declare',a)]
 base=h.split(' ',2)[2].rsplit(')',1)[0].split()[1:]
 extra=['fn2-overlays','fn2-run-cache','fn2-pool','fn2-commit','fn2-checkpoint-predecessors','fn2-checkpoint-predecessor-control','fn2-run-loads','fn2-run-cursors','fn2-checkpoint-summary-leases']
 args=list(dict.fromkeys(base+extra))
 outs=['fn2-checkpoint-summary','fn2-run-installed','fn2-overlays','fn2-run-cache','fn2-pool','fn2-checkpoint-cbase-holds','fn2-extents','fn2-alloc-edges','fn2-checkpoint-predecessors','fn2-checkpoint-predecessor-control']
 def mv(c):return '(mv '+c+' '+' '.join(outs)+')'
 b=src.index(' (b* (((unless (posp budget))',a);e=src.index('  (stage ',b)
 gate=src[b:e].replace('fn2-checkpoint-summary fn2-checkpoint-metadata-manifest fn2-run-installed',' '.join(outs))
 s='''; One original source/cleanup page per turn under actual durable replacement.
; Many original sources may share one rebuilt schema root. Mapping is a single
; manifest scan plus direct rank lookup, not an extent sweep per original.
; Empty originals require actual prepass empty proof and no fabricated root.
; Callback physical-work refinement/step charge remains unqualified pending
; component audit; declaring work-stage is not a proved body bound.
(in-package "ACL2")
(include-book "checkpoint-live-install")
(include-book "checkpoint-predecessors")
(include-book "checkpoint-cbase-release")
(include-book "checkpoint-source-loader")
(fn2-book-layer :c)
(defconst *fn2-live-replace-stage-old-base* 4)
(defconst *fn2-live-replace-stage-resources* 5)
(defun fn2-checkpoint-predecessor-retiring-p (i fn2-checkpoint-predecessors fn2-overlays fn2-run-installed)
 (declare (xargs :stobjs (fn2-checkpoint-predecessors fn2-overlays fn2-run-installed)
  :guard (and (fn2-checkpoint-predecessors-wfp fn2-checkpoint-predecessors) (fn2-overlays-wfp fn2-overlays) (fn2-run-installed-wfp fn2-run-installed))))
 (and (natp i) (< i (fn2-checkpoint-predecessors-rows fn2-checkpoint-predecessors))
  (= (fn2-checkpoint-predecessors-live i fn2-checkpoint-predecessors) 1)
  (let ((r (fn2-checkpoint-predecessors-row i fn2-checkpoint-predecessors)))
   (case (fn2-checkpoint-predecessors-kind i fn2-checkpoint-predecessors)
    (0 (and (< r (fn2-overlays-rows fn2-overlays))
         (= (fn2-checkpoint-predecessors-retire-stage i fn2-checkpoint-predecessors) 1)
         (member-equal (fn2-overlays-phase r fn2-overlays) (list *fn2-overlay-phase-frozen* *fn2-overlay-phase-draining*))
'''
 for f,actual in [('schema','schema'),('order','seq')]:s+='         (= (fn2-overlays-'+actual+' r fn2-overlays) (fn2-checkpoint-predecessors-'+f+' i fn2-checkpoint-predecessors))\n'
 for f,actual in {'slot':'slot','gen':'gen','entries':'count','okind':'okind','oslot':'oslot','ogen':'ogen'}.items():s+='         (= (fn2-overlays-'+actual+' r fn2-overlays) (fn2-checkpoint-predecessors-old-'+f+' i fn2-checkpoint-predecessors))\n'
 s+='''       ))
    (1 (and (< r (fn2-run-installed-rows fn2-run-installed))
         (= (fn2-checkpoint-predecessors-retire-stage i fn2-checkpoint-predecessors) 2)
         (= (fn2-run-installed-state r fn2-run-installed) *fn2-run-installed-state-retired*)
'''
 for f,actual in [('schema','schema'),('order','run')]:s+='         (= (fn2-run-installed-'+actual+' r fn2-run-installed) (fn2-checkpoint-predecessors-'+f+' i fn2-checkpoint-predecessors))\n'
 for f,_ in FIELDS:
  if f=='ufirst':continue
  s+='         (= (fn2-run-installed-'+{'allocation':'counter','tag':'catalog-tag'}.get(f,f)+' r fn2-run-installed) (fn2-checkpoint-predecessors-old-'+f+' i fn2-checkpoint-predecessors))\n'
 s+='''         (<= (fn2-checkpoint-predecessors-old-ufirst i fn2-checkpoint-predecessors) (fn2-run-installed-ufirst r fn2-run-installed))
         (<= (fn2-run-installed-ufirst r fn2-run-installed) (+ 1 (fn2-checkpoint-predecessors-old-ulast i fn2-checkpoint-predecessors)))
       ))
    (otherwise nil)))))
(defmacro fn2-checkpoint-live-retire-events ()
 '(progn
'''
 s+='(defun fn2-checkpoint-live-replace-retire-step (budget '+' '.join(args)+')\n'
 s+=' (declare (xargs :stobjs ('+' '.join(args)+') :guard (and '+' '.join('('+x+'-wfp '+x+')' for x in args)+')))\n'
 s+=gate
 s+='''  ((unless (and (< 0 (fn2-checkpoint-predecessor-control-rows fn2-checkpoint-predecessor-control))
   (= (fn2-checkpoint-predecessors-rows fn2-checkpoint-predecessors) (+ (fn2-overlays-rows fn2-overlays) (fn2-run-installed-rows fn2-run-installed)))
   (= (fn2-checkpoint-predecessor-control-overlay-rows 0 fn2-checkpoint-predecessor-control) (fn2-overlays-rows fn2-overlays))
   (= (fn2-checkpoint-predecessor-control-run-rows 0 fn2-checkpoint-predecessor-control) (fn2-run-installed-rows fn2-run-installed))
   (fn2-checkpoint-source-reader-detachedp fn2-run-loads fn2-run-cursors fn2-checkpoint-summary-leases)
'''
 for f,q in [('token','generation'),('candidate','candidate'),('owner-kind','owner-kind'),('owner-slot','owner-slot'),('owner-gen','owner-gen'),('cut-commit','cut-commit'),('cut-event','cut-event')]:s+='   (= (fn2-checkpoint-predecessor-control-'+f+' 0 fn2-checkpoint-predecessor-control) (fn2-checkpoint-summary-'+q+' 1 fn2-checkpoint-summary))\n'
 s+='''  )) '''+mv(':source')+''')
  (stage (fn2-checkpoint-summary-application-stage 1 fn2-checkpoint-summary))
  (phase (fn2-checkpoint-predecessor-control-phase 0 fn2-checkpoint-predecessor-control))
  (i (fn2-checkpoint-predecessor-control-cursor 0 fn2-checkpoint-predecessor-control))
  (n (fn2-checkpoint-predecessors-rows fn2-checkpoint-predecessors))
  (token (fn2-checkpoint-summary-generation 1 fn2-checkpoint-summary)))
  (cond
   ((= stage *fn2-live-replace-stage-retire*)
    (cond
     ((= phase *fn2-checkpoint-predecessor-phase-complete*)
      (if (not (and (= i n) (= (fn2-checkpoint-predecessor-control-checked 0 fn2-checkpoint-predecessor-control) (fn2-checkpoint-predecessor-control-count 0 fn2-checkpoint-predecessor-control)))) '''+mv(':coverage')+'''
       (let ((fn2-checkpoint-predecessor-control (fn2-checkpoint-predecessor-control-put 0 (phase *fn2-checkpoint-predecessor-phase-mapping*) (cursor 0) (checked 0)))) '''+mv(':more')+''')))
     ((= phase *fn2-checkpoint-predecessor-phase-mapping*)
      (b* ((limit (fn2-checkpoint-metadata-manifest-rows fn2-checkpoint-metadata-manifest))
       ((when (= i limit))
        (if (not (= (fn2-checkpoint-predecessor-control-checked 0 fn2-checkpoint-predecessor-control) (fn2-checkpoint-summary-count 1 fn2-checkpoint-summary))) '''+mv(':coverage')+'''
         (let ((fn2-checkpoint-predecessor-control (fn2-checkpoint-predecessor-control-put 0 (phase *fn2-checkpoint-predecessor-phase-retiring*) (cursor 0) (checked 0)))) '''+mv(':more')+''')))
       ((unless (and (< i limit) (unsigned-byte-p 32 (+ 1 i)))) '''+mv(':bounds')+''')
       ((unless (= (fn2-checkpoint-metadata-manifest-catalog-token i fn2-checkpoint-metadata-manifest) token))
        (let ((fn2-checkpoint-predecessor-control (fn2-checkpoint-predecessor-control-set-cursor 0 (+ 1 i) fn2-checkpoint-predecessor-control))) '''+mv(':more')+'''))
       (rank (fn2-checkpoint-metadata-manifest-catalog-rank i fn2-checkpoint-metadata-manifest))
       (at (if (posp rank) (- rank 1) n))
       (checked (+ 1 (fn2-checkpoint-predecessor-control-checked 0 fn2-checkpoint-predecessor-control)))
       ((unless (and (< at n) (unsigned-byte-p 32 checked)
        (not (= (fn2-checkpoint-predecessors-root-token at fn2-checkpoint-predecessors) token))
        (fn2-checkpoint-live-installed-p i fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-checkpoint-metadata-manifest fn2-run-installed))) '''+mv(':source')+''')
       (fn2-checkpoint-predecessors (fn2-checkpoint-predecessors-put at (root-token token) (root-extent i)
        (root-schema (fn2-checkpoint-metadata-manifest-catalog-schema i fn2-checkpoint-metadata-manifest)) (root-rank rank)))
       (fn2-checkpoint-predecessor-control (fn2-checkpoint-predecessor-control-put 0 (cursor (+ 1 i)) (checked checked))))
       '''+mv(':more')+'''))
     ((= phase *fn2-checkpoint-predecessor-phase-retiring*)
      (b* (((when (= i n))
        (if (not (= (fn2-checkpoint-predecessor-control-checked 0 fn2-checkpoint-predecessor-control) (fn2-checkpoint-predecessor-control-count 0 fn2-checkpoint-predecessor-control))) '''+mv(':coverage')+'''
         (let ((fn2-checkpoint-summary (fn2-checkpoint-summary-put 1 (application-stage *fn2-live-replace-stage-old-base*) (cursor 0) (target 0)))) '''+mv(':more')+''')))
       ((unless (and (< i n) (unsigned-byte-p 32 (+ 1 i)))) '''+mv(':bounds')+''')
       ((when (= (fn2-checkpoint-predecessors-live i fn2-checkpoint-predecessors) 0))
        (let ((fn2-checkpoint-predecessor-control (fn2-checkpoint-predecessor-control-set-cursor 0 (+ 1 i) fn2-checkpoint-predecessor-control))) '''+mv(':more')+'''))
       (rank (fn2-checkpoint-predecessors-output-rank i fn2-checkpoint-predecessors))
       (at (if (posp rank) (- rank 1) n))
       (checked (+ 1 (fn2-checkpoint-predecessor-control-checked 0 fn2-checkpoint-predecessor-control)))
       ((unless (and (= (fn2-checkpoint-predecessors-token i fn2-checkpoint-predecessors) token)
        (= (fn2-checkpoint-predecessors-ended i fn2-checkpoint-predecessors) 1)
        (= (fn2-checkpoint-predecessors-seen i fn2-checkpoint-predecessors) (fn2-checkpoint-predecessors-old-entries i fn2-checkpoint-predecessors))
        (unsigned-byte-p 32 checked)
        (if (= (fn2-checkpoint-predecessors-semantic-live i fn2-checkpoint-predecessors) 0)
         (and (= rank 0) (= (fn2-checkpoint-predecessors-old-entries i fn2-checkpoint-predecessors) 0)
              (= (fn2-checkpoint-predecessors-empty-verified i fn2-checkpoint-predecessors) 1))
         (and (< at n) (= (fn2-checkpoint-predecessors-root-token at fn2-checkpoint-predecessors) token)
          (= (fn2-checkpoint-predecessors-root-rank at fn2-checkpoint-predecessors) rank)
          (= (fn2-checkpoint-predecessors-root-schema at fn2-checkpoint-predecessors) (fn2-checkpoint-predecessors-schema i fn2-checkpoint-predecessors))
          (fn2-checkpoint-live-installed-p (fn2-checkpoint-predecessors-root-extent at fn2-checkpoint-predecessors)
           fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-checkpoint-metadata-manifest fn2-run-installed))))) '''+mv(':source')+''')
       (oldstage (fn2-checkpoint-predecessors-retire-stage i fn2-checkpoint-predecessors))
       (kind (fn2-checkpoint-predecessors-kind i fn2-checkpoint-predecessors))
       (r (fn2-checkpoint-predecessors-row i fn2-checkpoint-predecessors)))
       (cond
        ((= oldstage 0)
         (b* (((unless (fn2-checkpoint-predecessor-identity-p i fn2-checkpoint-predecessors fn2-overlays fn2-run-installed)) '''+mv(':changed')+'''))
          (if (= kind 0)
           (if (= (fn2-overlays-phase r fn2-overlays) *fn2-overlay-phase-active*)
            (b* (((mv code fn2-overlays) (fn2-ov-freeze r fn2-overlays))
                 ((unless (eq code :ok)) '''+mv('code')+''')
                 (fn2-checkpoint-predecessors (fn2-checkpoint-predecessors-set-retire-stage i 1 fn2-checkpoint-predecessors))) '''+mv(':more')+''')
            (b* (((mv code fn2-overlays fn2-pool) (fn2-seal-retire (fn2-commit-rows fn2-commit) r fn2-overlays fn2-pool))
                 ((unless (member-eq code '(:ok :retired))) '''+mv('code')+''')
                 (fn2-checkpoint-predecessors (fn2-checkpoint-predecessors-set-retire-stage i 3 fn2-checkpoint-predecessors))) '''+mv(':more')+'''))
           (b* (((mv code fn2-run-installed) (fn2-run-retire r fn2-run-installed))
                ((unless (eq code :ok)) '''+mv('code')+''')
                (fn2-checkpoint-predecessors (fn2-checkpoint-predecessors-set-retire-stage i 2 fn2-checkpoint-predecessors))) '''+mv(':more')+'''))))
        ((= oldstage 1)
         (b* (((unless (fn2-checkpoint-predecessor-retiring-p i fn2-checkpoint-predecessors fn2-overlays fn2-run-installed)) '''+mv(':changed')+''')
              ((mv code fn2-overlays fn2-pool) (fn2-seal-retire (fn2-commit-rows fn2-commit) r fn2-overlays fn2-pool))
              ((unless (member-eq code '(:ok :retired))) '''+mv('code')+''')
              (fn2-checkpoint-predecessors (fn2-checkpoint-predecessors-set-retire-stage i 3 fn2-checkpoint-predecessors))) '''+mv(':more')+'''))
        ((= oldstage 2)
         (b* (((unless (fn2-checkpoint-predecessor-retiring-p i fn2-checkpoint-predecessors fn2-overlays fn2-run-installed)) '''+mv(':changed')+''')
              ((when (= (fn2-run-installed-physical r fn2-run-installed) 1))
               (b* (((mv code fn2-checkpoint-summary fn2-run-installed)
                     (fn2-checkpoint-summary-row-retire-row 0 r fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-checkpoint-cbase-holds fn2-run-installed))
                    ((unless (eq code :retired)) '''+mv('code')+''')
                    (fn2-checkpoint-predecessors (fn2-checkpoint-predecessors-set-retire-stage i 3 fn2-checkpoint-predecessors))) '''+mv(':more')+'''))
              ((mv code fn2-run-installed fn2-run-cache fn2-pool) (fn2-seal-release-row r fn2-run-installed fn2-run-cache fn2-pool))
              ((unless (eq code :more)) '''+mv('code')+''')
              (fn2-checkpoint-predecessors (if (= (fn2-run-installed-state r fn2-run-installed) *fn2-run-installed-state-free*)
               (fn2-checkpoint-predecessors-set-retire-stage i 3 fn2-checkpoint-predecessors) fn2-checkpoint-predecessors))) '''+mv(':more')+'''))
        ((= oldstage 3)
         (let ((fn2-checkpoint-predecessor-control (fn2-checkpoint-predecessor-control-put 0 (cursor (+ 1 i)) (checked checked)))) '''+mv(':more')+'''))
        (t '''+mv(':state')+'''))))
     (t '''+mv(':state')+''')))
   ((= stage *fn2-live-replace-stage-old-base*)
    (b* (((unless (and (= phase *fn2-checkpoint-predecessor-phase-retiring*) (= i n)
     (= (fn2-checkpoint-predecessor-control-checked 0 fn2-checkpoint-predecessor-control) (fn2-checkpoint-predecessor-control-count 0 fn2-checkpoint-predecessor-control)))) '''+mv(':source')+''')
     ((mv code fn2-checkpoint-summary fn2-checkpoint-cbase-holds fn2-extents fn2-alloc-edges fn2-run-installed)
      (if (and (= (fn2-checkpoint-summary-tag 0 fn2-checkpoint-summary) 0)
               (= (fn2-checkpoint-summary-phase 0 fn2-checkpoint-summary) *fn2-checkpoint-summary-phase-idle*)
               (= (fn2-checkpoint-summary-installed 0 fn2-checkpoint-summary) 0)
               (= (fn2-checkpoint-summary-lease-count 0 fn2-checkpoint-summary) 0))
       (mv :released fn2-checkpoint-summary fn2-checkpoint-cbase-holds fn2-extents fn2-alloc-edges fn2-run-installed)
       (fn2-checkpoint-cbase-row-release-step budget 0 fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-checkpoint-cbase-holds fn2-run-installed fn2-checkpoints fn2-extents fn2-ops fn2-alloc-edges)))
     ((unless (eq code :released)) '''+mv('code')+''')
     (fn2-checkpoint-predecessor-control (fn2-checkpoint-predecessor-control-set-phase 0 *fn2-checkpoint-predecessor-phase-done* fn2-checkpoint-predecessor-control))
     (fn2-checkpoint-summary (fn2-checkpoint-summary-put 1 (application-stage *fn2-live-replace-stage-resources*) (cursor 0)))) '''+mv(':resources')+'''))
   (t '''+mv(':state')+'''))))
))
(defcost fn2-checkpoint-live-replace-retire-step-op :child fn2-checkpoint-live-replace-retire-step :answers t
 :steps *fn2-work-stage* :bytes (* 8 *fn2-commit-digest-bytes*) :descriptors 0
 :tables ('''+ ' '.join(x.replace('fn2-','fn2-core-',1) for x in args)+''')
 :doc "One actual original source/page cleanup under durable replacement; no new reserve/IO or per-source extent sweep.")
'''
 return s

if __name__ == "__main__":
 Path('books/checkpoint-live-retire.lisp').write_text(emit(Path('books/checkpoint-live-install.lisp').read_text()))
