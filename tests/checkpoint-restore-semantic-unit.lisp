; SOURCE controls over the actual binder, not a physical hash witness.
; Checked candidate/descriptor bytes and authenticated-reader phase are
; synthetic premises. Map completion/FIFO are produced by actual wire intake.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "checkpoint-restore-unit")
(include-book "../books/checkpoint-restore-semantic")
(defun fn2-crsu-body (mode fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-reader
 fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-fields fn2-pool fn2-checkpoint-restore-semantic)
 (declare (xargs :stobjs (fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-reader
 fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-fields fn2-pool fn2-checkpoint-restore-semantic) :verify-guards nil))
 (b* (((mv intake fn2-checkpoint-restore-reader fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-fields fn2-pool)
       (fn2-cru-map-body (if (eq mode :children) :children nil) fn2-checkpoint-restore-reader fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-fields fn2-pool))
      (fn2-checkpoints (fn2-checkpoints-init 2 fn2-checkpoints))
      (fn2-checkpoint-refs (fn2-checkpoint-refs-init 12 fn2-checkpoint-refs))
      (fn2-checkpoint-bytes (fn2-checkpoint-bytes-init 384 fn2-checkpoint-bytes))
      (fn2-checkpoint-restore-semantic (fn2-checkpoint-restore-semantic-init 1 fn2-checkpoint-restore-semantic))
      (fn2-checkpoints (fn2-checkpoints-put 0 (state *fn2-checkpoint-state-checked*) (anchor-mask 1)))
      (fn2-checkpoint-refs (fn2-checkpoint-refs-put 1 (storage-domain 0) (physical-unit *fn2-storage-extent-units*)
       (writer-epoch 4) (allocation 31) (page-kind *page-kind-manifest*) (encoded-length *fn2-format-page-size*)))
      ; Same slot, changed durable descriptor identity must refuse unchanged.
      (fn2-checkpoint-bytes (if (eq mode :stale) (fn2-checkpoint-bytes-set-value 0 1 fn2-checkpoint-bytes) fn2-checkpoint-bytes))
      (fn2-checkpoints (if (eq mode :cut) (fn2-checkpoints-set-cut-event 0 1 fn2-checkpoints) fn2-checkpoints))
      (fn2-checkpoint-refs (if (eq mode :epoch) (fn2-checkpoint-refs-set-writer-epoch 1 5 fn2-checkpoint-refs) fn2-checkpoint-refs))
      (fn2-checkpoint-refs (if (eq mode :allocation) (fn2-checkpoint-refs-set-allocation 1 32 fn2-checkpoint-refs) fn2-checkpoint-refs))
      (fn2-checkpoint-restore-map-control (if (eq mode :candidate)
       (fn2-checkpoint-restore-map-control-set-candidate 0 1 fn2-checkpoint-restore-map-control) fn2-checkpoint-restore-map-control))
      (slot (fn2-checkpoint-restore-reader-slot 0 fn2-checkpoint-restore-reader))
      (gen (fn2-checkpoint-restore-reader-gen 0 fn2-checkpoint-restore-reader))
      ((mv code fn2-checkpoint-restore-semantic)
       (fn2-checkpoint-restore-semantic-begin slot gen 7 0 1 fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
        fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-pool fn2-checkpoint-restore-semantic)))
  (mv (and intake
       (if (and mode (not (eq mode :children)))
        (and (not (eq code :read))
             (equal (fn2-checkpoint-restore-semantic-phase 0 fn2-checkpoint-restore-semantic) *fn2-checkpoint-restore-semantic-phase-idle*)
             (equal (fn2-checkpoint-restore-semantic-unit 0 fn2-checkpoint-restore-semantic) 0))
        (and (eq code :read)
             (equal (fn2-checkpoint-restore-semantic-unit 0 fn2-checkpoint-restore-semantic) *fn2-storage-extent-units*)
             (equal (fn2-checkpoint-restore-semantic-epoch 0 fn2-checkpoint-restore-semantic) 4)
             (equal (fn2-checkpoint-restore-semantic-allocation 0 fn2-checkpoint-restore-semantic) 31))))
   fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-reader fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-fields fn2-pool fn2-checkpoint-restore-semantic)))
(defun fn2-crsu-test (mode)
 (declare (xargs :verify-guards nil))
 (fn2-run-with-local (fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-reader fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-fields fn2-pool fn2-checkpoint-restore-semantic)
  (fn2-crsu-body mode fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-reader fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-fields fn2-pool fn2-checkpoint-restore-semantic)))
(assert-event (fn2-crsu-test nil))
(assert-event (fn2-crsu-test :stale))
(assert-event (fn2-crsu-test :cut))
(assert-event (fn2-crsu-test :epoch))
(assert-event (fn2-crsu-test :allocation))
(assert-event (fn2-crsu-test :candidate))

; Replace BOTH current descriptor and complete map at the same slot after
; successful begin. Current-map-p remains true; the in-flight source must refuse.
(defun fn2-crsu-replacement-body (fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-reader
 fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-fields fn2-pool fn2-checkpoint-restore-semantic
 fn2-fc fn2-fc-context fn2-b3 fn2-digests)
 (declare (xargs :stobjs (fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-reader
 fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-fields fn2-pool fn2-checkpoint-restore-semantic
 fn2-fc fn2-fc-context fn2-b3 fn2-digests) :verify-guards nil))
 (b* (((mv begun fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-reader
        fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-fields fn2-pool fn2-checkpoint-restore-semantic)
       (fn2-crsu-body nil fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-reader
        fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-fields fn2-pool fn2-checkpoint-restore-semantic))
      (fn2-checkpoint-bytes (fn2-checkpoint-bytes-set-value 0 1 fn2-checkpoint-bytes))
      (fn2-checkpoint-restore-map-control (update-fn2-checkpoint-restore-map-control-descriptori 0 1 fn2-checkpoint-restore-map-control))
      (current (fn2-checkpoint-restore-map-current-p fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control))
      (old (list (fn2-checkpoint-restore-semantic-phase 0 fn2-checkpoint-restore-semantic)
                 (fn2-checkpoint-restore-semantic-unit 0 fn2-checkpoint-restore-semantic)
                 (fn2-checkpoint-restore-semantic-hashi 32 fn2-checkpoint-restore-semantic)))
      ((mv code fn2-checkpoint-restore-semantic fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
       (fn2-checkpoint-restore-semantic-page 4096 0 0 fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
        fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-checkpoint-restore-semantic fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)))
  (mv (and begun current (eq code :source) (equal old (list (fn2-checkpoint-restore-semantic-phase 0 fn2-checkpoint-restore-semantic)
                     (fn2-checkpoint-restore-semantic-unit 0 fn2-checkpoint-restore-semantic)
                     (fn2-checkpoint-restore-semantic-hashi 32 fn2-checkpoint-restore-semantic))))
   fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-reader fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control
   fn2-fields fn2-pool fn2-checkpoint-restore-semantic fn2-fc fn2-fc-context fn2-b3 fn2-digests)))
(defun fn2-crsu-replacement-test ()
 (declare (xargs :verify-guards nil))
 (fn2-run-with-local (fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-reader fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control
 fn2-fields fn2-pool fn2-checkpoint-restore-semantic fn2-fc fn2-fc-context fn2-b3 fn2-digests)
  (fn2-crsu-replacement-body fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-reader fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control
   fn2-fields fn2-pool fn2-checkpoint-restore-semantic fn2-fc fn2-fc-context fn2-b3 fn2-digests)))
(assert-event (fn2-crsu-replacement-test))
