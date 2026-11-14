(in-package "ACL2")
(include-book "../books/checkpoint-publication")

; Source fixtures awaiting allocation/admission. These drive the same concrete
; harvest callback registered on the publication child. They do not inject host
; booleans or claim a real issued-operation/fence witness.
(defun fn2-checkpoint-publication-harvest-test-body (fn2-checkpoint-publication)
 (declare (xargs :stobjs fn2-checkpoint-publication :verify-guards nil))
 (b* ((fn2-checkpoint-publication (fn2-checkpoint-publication-init 1 fn2-checkpoint-publication))
      (fn2-checkpoint-publication (fn2-checkpoint-publication-put 0
        (phase *fn2-checkpoint-publication-phase-wait-first*) (op-slot 5) (op-gen 7)))
      ((mv stale fn2-checkpoint-publication)
       (fn2-checkpoint-publication-harvest 5 6 0 *fn2-event-write-result* *fn2-outcome-done* 0 4096 0 0 fn2-checkpoint-publication))
      ((unless (and (eq stale :ok)
                     (equal (fn2-checkpoint-publication-phase 0 fn2-checkpoint-publication)
                            *fn2-checkpoint-publication-phase-wait-first*)))
       (mv nil fn2-checkpoint-publication))
      ((mv done fn2-checkpoint-publication)
       (fn2-checkpoint-publication-harvest 5 7 0 *fn2-event-write-result* *fn2-outcome-done* 0 4096 0 0 fn2-checkpoint-publication))
      ((unless (and (eq done :ok)
                     (equal (fn2-checkpoint-publication-phase 0 fn2-checkpoint-publication)
                            *fn2-checkpoint-publication-phase-write-second*)))
       (mv nil fn2-checkpoint-publication))
      ; A short physical completion must retain uncertainty, never permit fence.
      (fn2-checkpoint-publication (fn2-checkpoint-publication-put 0
        (phase *fn2-checkpoint-publication-phase-wait-second*) (op-slot 6) (op-gen 9)))
      ((mv short fn2-checkpoint-publication)
       (fn2-checkpoint-publication-harvest 6 9 0 *fn2-event-write-result* *fn2-outcome-done* 0 4095 0 0 fn2-checkpoint-publication)))
  (mv (and (eq short :ok)
           (equal (fn2-checkpoint-publication-phase 0 fn2-checkpoint-publication)
                  *fn2-checkpoint-publication-phase-uncertain*)) fn2-checkpoint-publication)))
(defun fn2-checkpoint-publication-harvest-test ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-checkpoint-publication
  (mv-let (answer fn2-checkpoint-publication)
   (fn2-checkpoint-publication-harvest-test-body fn2-checkpoint-publication) answer)))
(assert-event (fn2-checkpoint-publication-harvest-test))

; The previous minimum-size layout cannot hold this bootstrap + four-bank
; reservation. All four anchors are distinct and before the epoch pair.
(assert-event (mv-let (code off) (fn2-checkpoint-anchor-offset 0 (* 4096 7) 1 1)
                (and (eq code :geometry) (equal off 0))))
(assert-event (and (fn2-checkpoint-image-sizep (* 4096 12) 1 1)
                   (equal (fn2-checkpoint-bootstrap-unit 1 1) 5)
                   (equal (fn2-checkpoint-anchor-unit 0 1 1) 6)
                   (equal (fn2-checkpoint-anchor-unit 3 1 1) 9)))
