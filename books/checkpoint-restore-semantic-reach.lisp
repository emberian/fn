; Record semantic page reach only after the actual format+typed reader closes.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "checkpoint-restore-semantic")
(include-book "checkpoint-restore-reach-core")
(fn2-book-layer :c)
(defun fn2-checkpoint-restore-semantic-page-reach (budget row base fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
 fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-checkpoint-restore-semantic fn2-checkpoint-restore-reach fn2-checkpoint-restore-reach-control
 fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
 (declare (xargs :stobjs (fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control
 fn2-checkpoint-restore-semantic fn2-checkpoint-restore-reach fn2-checkpoint-restore-reach-control fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
 :guard (and (fn2-checkpoints-wfp fn2-checkpoints) (fn2-checkpoint-refs-wfp fn2-checkpoint-refs) (fn2-checkpoint-bytes-wfp fn2-checkpoint-bytes)
  (fn2-checkpoint-restore-map-wfp fn2-checkpoint-restore-map) (fn2-checkpoint-restore-map-control-wfp fn2-checkpoint-restore-map-control)
  (fn2-checkpoint-restore-semantic-wfp fn2-checkpoint-restore-semantic) (fn2-checkpoint-restore-reach-wfp fn2-checkpoint-restore-reach)
  (fn2-checkpoint-restore-reach-control-wfp fn2-checkpoint-restore-reach-control) (fn2-fc-wfp fn2-fc) (fn2-fc-context-wfp fn2-fc-context)
  (fn2-b3-wfp fn2-b3) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool) (fn2-digests-wfp fn2-digests))))
 (b* (((unless (< 0 (fn2-checkpoint-restore-semantic-rows fn2-checkpoint-restore-semantic)))
       (mv :source fn2-checkpoint-restore-semantic fn2-checkpoint-restore-reach fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))
      ((mv code fn2-checkpoint-restore-semantic fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
       (fn2-checkpoint-restore-semantic-page budget row base fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
        fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-checkpoint-restore-semantic fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))
      ((mv claimed fn2-checkpoint-restore-reach)
       (if (eq code :entries)
        (fn2-checkpoint-restore-reach-claim
         (if (equal (fn2-checkpoint-restore-semantic-source 0 fn2-checkpoint-restore-semantic) 1)
             *fn2-checkpoint-restore-reach-role-semantic-source* *fn2-checkpoint-restore-reach-role-semantic*)
         (fn2-checkpoint-restore-semantic-unit 0 fn2-checkpoint-restore-semantic)
         (fn2-checkpoint-restore-semantic-epoch 0 fn2-checkpoint-restore-semantic)
         (fn2-checkpoint-restore-semantic-allocation 0 fn2-checkpoint-restore-semantic)
         fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control
         fn2-checkpoint-restore-reach fn2-checkpoint-restore-reach-control)
        (mv :ok fn2-checkpoint-restore-reach)))
      (fn2-checkpoint-restore-semantic (if (eq claimed :ok) fn2-checkpoint-restore-semantic
       (fn2-checkpoint-restore-semantic-set-phase 0 *fn2-checkpoint-restore-semantic-phase-uncertain* fn2-checkpoint-restore-semantic))))
  (mv (if (eq claimed :ok) code claimed) fn2-checkpoint-restore-semantic fn2-checkpoint-restore-reach fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)))

(fn2-fc-shape fn2-checkpoint-restore-semantic-page-reach-shape
 (fn2-checkpoint-restore-semantic-page-reach budget row base fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
 fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-checkpoint-restore-semantic fn2-checkpoint-restore-reach fn2-checkpoint-restore-reach-control
 fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
 (and (fn2-checkpoint-restore-semanticp fn2-checkpoint-restore-semantic) (fn2-checkpoint-restore-reachp fn2-checkpoint-restore-reach) (fn2-fcp fn2-fc) (fn2-fc-contextp fn2-fc-context) (fn2-b3p fn2-b3) (fn2-fieldsp fn2-fields) (fn2-poolp fn2-pool) (fn2-digestsp fn2-digests) (and (fn2-checkpoints-wfp fn2-checkpoints) (fn2-checkpoint-refs-wfp fn2-checkpoint-refs) (fn2-checkpoint-bytes-wfp fn2-checkpoint-bytes)
  (fn2-checkpoint-restore-map-wfp fn2-checkpoint-restore-map) (fn2-checkpoint-restore-map-control-wfp fn2-checkpoint-restore-map-control)
  (fn2-checkpoint-restore-semantic-wfp fn2-checkpoint-restore-semantic) (fn2-checkpoint-restore-reach-wfp fn2-checkpoint-restore-reach)
  (fn2-checkpoint-restore-reach-control-wfp fn2-checkpoint-restore-reach-control) (fn2-fc-wfp fn2-fc) (fn2-fc-context-wfp fn2-fc-context)
  (fn2-b3-wfp fn2-b3) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool) (fn2-digests-wfp fn2-digests)))
 ((fn2-checkpoint-restore-semantic 1) (fn2-checkpoint-restore-reach 2) (fn2-fc 3) (fn2-fc-context 4) (fn2-b3 5) (fn2-fields 6) (fn2-pool 7) (fn2-digests 8)))
