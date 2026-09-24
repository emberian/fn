; Reached topic history across the actual Store crash/recover and open paths.
(in-package "ACL2")
(include-book "../../books/topic-history-recovery-invariants")
(include-book "consumer-topic-store-tests")
(include-book "std/testing/must-fail" :dir :system)

(assert-event (not (equal (fn-sn-topic *cts-admitted*)
                          (fn-th-prefix-state :ok 0 nil nil nil nil nil))))
(make-event `(defconst *thr-crashed*
               ',(fn-sn-crash *cts-admitted* :old :absent)))
(assert-event (equal (fn-sf-phase (fn-sn-files *thr-crashed*)) :replaying))
(assert-event (equal (fn-sn-topic *thr-crashed*)
                     (fn-th-prefix-state :ok 0 nil nil nil nil nil)))
(make-event `(defconst *thr-recovered* ',(fn-sn-recover *thr-crashed*)))
(assert-event (equal (fn-sf-phase (fn-sn-files *thr-recovered*)) :recovering))
(assert-event (equal (fn-sn-topic *thr-recovered*)
                     (fn-th-prefix-project
                      (fn-sf-records (fn-sn-files *thr-recovered*)))))
(assert-event (equal (fn-sn-topic *thr-recovered*)
                     (fn-sn-topic *cts-admitted*)))
(assert-event (equal (fn-sn-topic *cts-reopened*)
                     (fn-th-prefix-project
                      (fn-sf-records (fn-sn-files *cts-reopened*)))))

; Without a valid crash choice, the actual transition is a no-op and retains
; the nonempty live topic projection rather than resetting it.
(assert-event (not (fn-sf-crash-choicep :old :sideways)))
(must-fail
 (assert-event
  (equal (fn-sn-topic (fn-sn-crash *cts-admitted* :old :sideways))
         (fn-th-prefix-state :ok 0 nil nil nil nil nil))))

; A refused observed open has no recovered state or historical projection.
(assert-event
 (not (fn-sn-open-okp
       (fn-sn-open-observed '(:not-a-group) 32 8
                            (fn-sf-records (fn-sn-files *cts-admitted*))))))
(must-fail
 (assert-event
  (equal (fn-sn-topic
          (fn-sn-open-state
           (fn-sn-open-observed '(:not-a-group) 32 8
                                (fn-sf-records (fn-sn-files *cts-admitted*)))))
         (fn-th-prefix-project
          (fn-sf-records (fn-sn-files *cts-admitted*))))))
