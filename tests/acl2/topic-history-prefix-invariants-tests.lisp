(in-package "ACL2")
(include-book "../../books/topic-history-prefix-invariants")
(include-book "topic-history-prefix-tests")
(include-book "std/testing/must-fail" :dir :system)

; A real topic report has an earlier accepted T10 source and key snapshot,
; but remains inadmissible without a root anchor. This is not a syntax,
; sequence, or verifier failure.
(defconst *sti-unanchored-before*
  (fn-th-prefix-state :ok 11 (list *tha-snapshot*)
                      (list *thad-event*) nil *thla-install* nil))
(assert-event (fn-th-topic-eventp *thad-report-event*))
(assert-event (equal (fn-th-at 1 *sti-unanchored-before*)
                     (fn-store-event-sequence *thad-report-event*)))
(assert-event
 (equal (fn-th-at 0
                  (fn-th-prefix-step *sti-unanchored-before*
                                     *thad-report-event*))
        :fault))
(must-fail
 (assert-event
  (equal (fn-th-at 0
                   (fn-th-prefix-step *sti-unanchored-before*
                                      *thad-report-event*))
         :ok)))
