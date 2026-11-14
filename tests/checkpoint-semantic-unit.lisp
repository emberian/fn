; Narrow internal queue/harvest controls. Synthetic fixtures do not establish
; the actual source binding or physical authentication needed for completion.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "../books/checkpoint-semantic-retention")
(defun fn2-checkpoint-semantic-control (fn2-extents fn2-checkpoint-semantic-work fn2-checkpoint-semantic fn2-digests)
 (declare (xargs :stobjs (fn2-extents fn2-checkpoint-semantic-work fn2-checkpoint-semantic fn2-digests) :verify-guards nil))
 (b* ((fn2-extents (fn2-alloc-init 4 fn2-extents))
      (fn2-checkpoint-semantic-work (fn2-checkpoint-semantic-work-init 4 fn2-checkpoint-semantic-work))
      (fn2-checkpoint-semantic (fn2-checkpoint-semantic-init 1 fn2-checkpoint-semantic))
      (fn2-digests (fn2-digests-init 1 fn2-digests))
      ((mv epoch-code fn2-extents) (fn2-alloc-begin-epoch 1 fn2-extents))
      ((mv reserved & e epoch allocation fn2-extents) (fn2-alloc-reserve fn2-extents))
      ((mv committed fn2-extents) (fn2-alloc-commit-allocation e epoch allocation 1 7 fn2-extents))
      ((unless (and (eq epoch-code :ok) (eq reserved :ok) (eq committed :ok)))
       (mv nil fn2-extents fn2-checkpoint-semantic-work fn2-checkpoint-semantic fn2-digests))
      (unit (* e *fn2-storage-extent-units*))
      ((mv queued fn2-checkpoint-semantic-work)
       (fn2-checkpoint-semantic-enqueue unit epoch allocation *page-kind-run-data* *fn2-run-page-size* 1 9 0 e 0 3 0
        fn2-checkpoint-semantic-work fn2-extents fn2-digests))
      ((mv duplicate fn2-checkpoint-semantic-work)
       (fn2-checkpoint-semantic-enqueue unit epoch allocation *page-kind-run-data* *fn2-run-page-size* 1 9 0 e 0 3 0
        fn2-checkpoint-semantic-work fn2-extents fn2-digests))
      ((mv stale fn2-checkpoint-semantic-work)
       (fn2-checkpoint-semantic-enqueue unit epoch (+ 1 allocation) *page-kind-run-data* *fn2-run-page-size* 1 9 0 e 0 3 0
        fn2-checkpoint-semantic-work fn2-extents fn2-digests))
      ((mv wrong-kind fn2-checkpoint-semantic-work)
       (fn2-checkpoint-semantic-enqueue unit epoch allocation *page-kind-partitioned-filter* *fn2-run-page-size* 1 9 0 e 1 0 0
        fn2-checkpoint-semantic-work fn2-extents fn2-digests))
      ((mv wrong-count fn2-checkpoint-semantic-work)
       (fn2-checkpoint-semantic-enqueue unit epoch allocation *page-kind-run-data* *fn2-run-page-size* 1 9 0 e 0 4 0
        fn2-checkpoint-semantic-work fn2-extents fn2-digests))
      (fn2-checkpoint-semantic (fn2-checkpoint-semantic-put 0 (phase *fn2-checkpoint-semantic-phase-wait*) (pending 1) (op-slot 2) (op-gen 3)))
      ((mv & fn2-checkpoint-semantic) (fn2-checkpoint-semantic-harvest 2 4 0 *fn2-event-read-result* *fn2-outcome-done* 0 4096 0 0 fn2-checkpoint-semantic))
      (ignored (and (= (fn2-checkpoint-semantic-pending 0 fn2-checkpoint-semantic) 1)
                    (= (fn2-checkpoint-semantic-phase 0 fn2-checkpoint-semantic) *fn2-checkpoint-semantic-phase-wait*)))
      ((mv & fn2-checkpoint-semantic) (fn2-checkpoint-semantic-harvest 2 3 0 *fn2-event-read-result* *fn2-outcome-done* 0 4095 0 0 fn2-checkpoint-semantic)))
  (mv (and (eq queued :ok) (eq duplicate :ok) (eq stale :reference)
           (eq wrong-kind :reference-conflict) (eq wrong-count :reference-conflict)
           (= (fn2-checkpoint-semantic-work-state e fn2-checkpoint-semantic-work) *fn2-checkpoint-semantic-work-state-pending*)
           ignored (= (fn2-checkpoint-semantic-pending 0 fn2-checkpoint-semantic) 0)
           (= (fn2-checkpoint-semantic-phase 0 fn2-checkpoint-semantic) *fn2-checkpoint-semantic-phase-uncertain*))
      fn2-extents fn2-checkpoint-semantic-work fn2-checkpoint-semantic fn2-digests)))
(defun fn2-checkpoint-semantic-control-run ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-extents
  (mv-let (ok fn2-extents)
   (with-local-stobj fn2-checkpoint-semantic-work
    (mv-let (ok fn2-extents fn2-checkpoint-semantic-work)
     (with-local-stobj fn2-checkpoint-semantic
      (mv-let (ok fn2-extents fn2-checkpoint-semantic-work fn2-checkpoint-semantic)
       (with-local-stobj fn2-digests
        (mv-let (ok fn2-extents fn2-checkpoint-semantic-work fn2-checkpoint-semantic fn2-digests)
         (fn2-checkpoint-semantic-control fn2-extents fn2-checkpoint-semantic-work fn2-checkpoint-semantic fn2-digests)
         (mv ok fn2-extents fn2-checkpoint-semantic-work fn2-checkpoint-semantic)))
       (mv ok fn2-extents fn2-checkpoint-semantic-work)))
     (mv ok fn2-extents))) ok)))
(assert-event (fn2-checkpoint-semantic-control-run))
