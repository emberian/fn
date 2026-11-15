; The table below is an explicit synthetic private fact, not authenticated
; checkpoint admission. This tests the readonly tuple comparator's complete
; typed antecedent; only actual journal-step can produce served consumed facts.
; No boot/reader phase is seeded and no inventory/recovery acceptance is claimed.
(in-package "ACL2")
(include-book "../books/checkpoint-restore-events-source")
(include-book "column-snapshot-support")
(make-event (cons 'progn (fn2-test-column-snapshot-events 'fn2-checkpoint-restore-events-work (w state))))
(defun fn2-ejf-body (fn2-checkpoint-restore-events-work)
 (declare (xargs :stobjs fn2-checkpoint-restore-events-work :verify-guards nil))
 (b* ((fn2-checkpoint-restore-events-work (fn2-checkpoint-restore-events-work-init 8 fn2-checkpoint-restore-events-work))
      (fn2-checkpoint-restore-events-work (fn2-checkpoint-restore-events-work-put 3
       (generation 11) (commit 17) (first 29) (members 3) (extent 3)
       (epoch 19) (allocation 23) (journal-history 41) (journal-incarnation 43) (consumed 1)))
      (typed (and (fn2-checkpoint-restore-events-workp fn2-checkpoint-restore-events-work)
                  (fn2-checkpoint-restore-events-work-wfp fn2-checkpoint-restore-events-work)))
      (before (fn2-test-table-snapshot-fn2-checkpoint-restore-events-work fn2-checkpoint-restore-events-work))
      (exact (fn2-checkpoint-restore-events-journal-tuple-p 3 11 17 30 19 23 41 43 fn2-checkpoint-restore-events-work))
      (bounds (and (fn2-checkpoint-restore-events-journal-tuple-p 3 11 17 29 19 23 41 43 fn2-checkpoint-restore-events-work)
                   (fn2-checkpoint-restore-events-journal-tuple-p 3 11 17 31 19 23 41 43 fn2-checkpoint-restore-events-work)
                   (not (fn2-checkpoint-restore-events-journal-tuple-p 3 11 17 28 19 23 41 43 fn2-checkpoint-restore-events-work))
                   (not (fn2-checkpoint-restore-events-journal-tuple-p 3 11 17 32 19 23 41 43 fn2-checkpoint-restore-events-work))))
      (refused (and (not (fn2-checkpoint-restore-events-journal-tuple-p 3 12 17 30 19 23 41 43 fn2-checkpoint-restore-events-work))
                    (not (fn2-checkpoint-restore-events-journal-tuple-p 3 11 18 30 19 23 41 43 fn2-checkpoint-restore-events-work))
                    (not (fn2-checkpoint-restore-events-journal-tuple-p 3 11 17 30 20 23 41 43 fn2-checkpoint-restore-events-work))
                    (not (fn2-checkpoint-restore-events-journal-tuple-p 3 11 17 30 19 24 41 43 fn2-checkpoint-restore-events-work))
                    (not (fn2-checkpoint-restore-events-journal-tuple-p 3 11 17 30 19 23 47 43 fn2-checkpoint-restore-events-work))
                    (not (fn2-checkpoint-restore-events-journal-tuple-p 3 11 17 30 19 23 41 47 fn2-checkpoint-restore-events-work))))
      (frame (equal before (fn2-test-table-snapshot-fn2-checkpoint-restore-events-work fn2-checkpoint-restore-events-work)))
      (fn2-checkpoint-restore-events-work (fn2-checkpoint-restore-events-work-set-consumed 3 0 fn2-checkpoint-restore-events-work))
      (unconsumed (not (fn2-checkpoint-restore-events-journal-tuple-p 3 11 17 30 19 23 41 43 fn2-checkpoint-restore-events-work)))
      ; A typed upper-stripe catalog row is not a cold consumed-prefix fact.
      (fn2-checkpoint-restore-events-work (fn2-checkpoint-restore-events-work-put 8
       (generation 11) (commit 17) (first 29) (members 3) (extent 8)
       (epoch 19) (allocation 23) (journal-history 41) (journal-incarnation 43) (consumed 1)))
      (upper (not (fn2-checkpoint-restore-events-journal-tuple-p 8 11 17 30 19 23 41 43 fn2-checkpoint-restore-events-work)))
      (fn2-checkpoint-restore-events-work (fn2-checkpoint-restore-events-work-put 3 (extent 4) (consumed 1)))
      (wrong-index (not (fn2-checkpoint-restore-events-journal-tuple-p 3 11 17 30 19 23 41 43 fn2-checkpoint-restore-events-work)))
      (fn2-checkpoint-restore-events-work (fn2-checkpoint-restore-events-work-put 0
       (generation 11) (commit 1) (first 1) (members 1) (extent 0)
       (epoch 19) (allocation 23) (journal-history 41) (journal-incarnation 43) (consumed 1)))
      (first-event (and (fn2-checkpoint-restore-events-journal-tuple-p 0 11 1 1 19 23 41 43 fn2-checkpoint-restore-events-work)
                        (not (fn2-checkpoint-restore-events-journal-tuple-p 0 11 1 0 19 23 41 43 fn2-checkpoint-restore-events-work)))))
  (mv (and typed exact bounds refused frame unconsumed upper wrong-index first-event) fn2-checkpoint-restore-events-work)))
(defun fn2-ejf-test ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-checkpoint-restore-events-work
  (mv-let (answer fn2-checkpoint-restore-events-work) (fn2-ejf-body fn2-checkpoint-restore-events-work) answer)))
(assert-event (fn2-ejf-test))
