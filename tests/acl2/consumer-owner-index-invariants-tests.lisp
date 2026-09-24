; The actual owner poll agrees with the exact historical list on a committed
; article, but a stale derived index changes its observable answer.
(in-package "ACL2")
(include-book "../../books/consumer-owner-index-invariants")
(include-book "consumer-owner-local-tests")
(include-book "std/testing/must-fail" :dir :system)

(assert-event (fn-ceis-relatedp *colt-after-article*))
(assert-event
 (equal (fn-col-poll (fn-own-start *colt-after-article* 2) *colt-id*)
        (fn-col-poll-list-reference
         (fn-own-start *colt-after-article* 2) *colt-id*)))

(defconst *coit-stale-index*
  (fn-sn-with-event-index *colt-after-article* nil))
(assert-event (not (fn-ceis-relatedp *coit-stale-index*)))
(assert-event
 (not (equal (fn-col-poll (fn-own-start *coit-stale-index* 2) *colt-id*)
             (fn-col-poll-list-reference
              (fn-own-start *coit-stale-index* 2) *colt-id*))))
(must-fail
 (defthm coit-caller-equality-needs-derived-index-relation
   (equal (fn-col-poll o consumer)
          (fn-col-poll-list-reference o consumer))))
