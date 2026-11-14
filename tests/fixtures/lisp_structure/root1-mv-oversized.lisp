; Frozen shape from checkpoint-metadata-driver.lisp at91be6b87f.
; Scalarwork and helperdefinitions are omitted; exact input/output lists and
; emitted READ skeleton are retained. This is a source-parser fixture only.
(defconst *fn2-checkpoint-root1-children*
 '(fn2-checkpoint-root1 fn2-checkpoint-windows fn2-checkpoint-metadata fn2-checkpoint-source fn2-checkpoint-metadata-manifest fn2-checkpoint-retained-entry fn2-checkpoint-payload fn2-checkpoint-semantic fn2-checkpoint-semantic-work fn2-checkpoint-build fn2-csnapshot fn2-checkpoints fn2-checkpoint-construction fn2-extents fn2-alloc-edges fn2-ops fn2-control fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-page fn2-checkpoint-page-verified fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-writers fn2-run-restarts fn2-run-cursors fn2-run-paths fn2-run-cache fn2-boot-config fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))

(defmacro fn2-checkpoint-root1-mv (code)
 `(mv ,code fn2-checkpoint-root1 fn2-checkpoint-windows fn2-checkpoint-metadata fn2-checkpoint-source fn2-checkpoint-metadata-manifest fn2-checkpoint-retained-entry fn2-checkpoint-payload fn2-checkpoint-semantic fn2-checkpoint-semantic-work fn2-checkpoint-build fn2-csnapshot fn2-checkpoints fn2-checkpoint-construction fn2-extents fn2-alloc-edges fn2-ops fn2-control fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-page fn2-checkpoint-page-verified fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-writers fn2-run-restarts fn2-run-cursors fn2-run-paths fn2-run-cache fn2-boot-config fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))

(defmacro fn2-checkpoint-root1-read-mv (code)
 `(mv ,code
   (if (and (< 0 (fn2-checkpoint-root1-rows fn2-checkpoint-root1))
            (equal (fn2-checkpoint-root1-read-kind 0 fn2-checkpoint-root1) 1))
       (fn2-checkpoint-semantic-op-slot 0 fn2-checkpoint-semantic) (fn2-checkpoint-payload-op-slot 0 fn2-checkpoint-payload))
   (if (and (< 0 (fn2-checkpoint-root1-rows fn2-checkpoint-root1))
            (equal (fn2-checkpoint-root1-read-kind 0 fn2-checkpoint-root1) 1))
       (fn2-checkpoint-semantic-op-gen 0 fn2-checkpoint-semantic) (fn2-checkpoint-payload-op-gen 0 fn2-checkpoint-payload))
   ,@*fn2-checkpoint-root1-children*))

(defmacro fn2-checkpoint-root1-read-events ()
 (let ((children *fn2-checkpoint-root1-children*))
 `(progn
   (defun fn2-checkpoint-root1-read (budget kind owner gen ,@children)
    (declare (xargs :stobjs ,children :guard (and ,@(fn2-checkpoint-root1-child-hyps children))))
    (b* (((unless (and (< 0 (fn2-checkpoint-root1-rows fn2-checkpoint-root1))
                       (< 0 (fn2-checkpoint-semantic-rows fn2-checkpoint-semantic))
                       (< 0 (fn2-checkpoint-payload-rows fn2-checkpoint-payload))))
          (mv :bounds 0 0 ,@children))
         ((unless (and (natp budget) (< 0 budget))) (fn2-checkpoint-root1-read-mv :yield))
         ((unless (fn2-checkpoint-root1-ownerp (fn2-checkpoint-root1-token 0 fn2-checkpoint-root1) kind owner gen fn2-checkpoint-root1 fn2-checkpoint-windows fn2-csnapshot))
          (fn2-checkpoint-root1-read-mv :owner)))
     (cond
      ((and (equal (fn2-checkpoint-root1-phase 0 fn2-checkpoint-root1) *fn2-checkpoint-root1-phase-semantic*)
            (equal (fn2-checkpoint-root1-read-kind 0 fn2-checkpoint-root1) 1))
       (b* (((mv code fn2-checkpoint-semantic fn2-checkpoint-semantic-work fn2-checkpoint-metadata fn2-extents fn2-alloc-edges fn2-ops fn2-control fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
             (fn2-checkpoint-semantic-issue 1 fn2-checkpoint-semantic fn2-checkpoint-semantic-work fn2-checkpoint-metadata fn2-checkpoint-build fn2-csnapshot fn2-run-builds fn2-run-writers
              fn2-boot-config fn2-extents fn2-alloc-edges fn2-ops fn2-checkpoints fn2-control fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)))
        (fn2-checkpoint-root1-read-mv (if (eq code :issued) :ok code))))
      ((and (equal (fn2-checkpoint-root1-phase 0 fn2-checkpoint-root1) *fn2-checkpoint-root1-phase-payload*)
            (equal (fn2-checkpoint-root1-read-kind 0 fn2-checkpoint-root1) 2))
       (b* (((mv code fn2-checkpoint-payload fn2-pool fn2-ops fn2-control fn2-extents fn2-alloc-edges)
             (fn2-checkpoint-payload-issue 1 fn2-checkpoint-payload fn2-checkpoint-retained-entry fn2-csnapshot fn2-checkpoints fn2-fields
              fn2-extents fn2-alloc-edges fn2-pool fn2-ops fn2-control)))
        (fn2-checkpoint-root1-read-mv (if (eq code :issued) :ok code))))
      (t (fn2-checkpoint-root1-read-mv :state)))))
   (fn2-checkpoint-root1-preserves fn2-checkpoint-root1-read (budget kind owner gen ,@children)
    :hyps ,(fn2-checkpoint-root1-child-hyps children)
    :specs ,(append (fn2-checkpoint-root1-child-specs children 3)
      '(("-B3-WORDS" fn2-b3-words-length 36 :frame fn2-b3)
        ("-POOL-DATA" fn2-pool-data-length 38 :frame fn2-pool))))
   (defcost fn2-checkpoint-root1-read-op :child fn2-checkpoint-root1-read :answers t :bytes 4096 :descriptors 1
    :tables ,(fn2-checkpoint-root1-child-tables children) :effects :per-use
    :doc "Issue at most one actual authenticated root1 source read; return its retained exact operation tuple."))))
