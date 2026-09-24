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

; The shared scope selector refuses an ACK beyond the committed frontier on
; both the indexed caller and the historical-list reference.  This malformed
; owner is outside the Store relation but exposes a decision drift if the
; proof-only reference reimplements an older, weaker scope check.
(defconst *coit-bad-ack-store*
  (let* ((store *colt-after-article*)
         (s (fn-sn-consumer store))
         (entries (fn-cp-nth 5 s))
         (bad (update-nth 7 (1+ (fn-cp-nth 3 s)) (car entries))))
    (fn-sn-with-consumer store
                         (update-nth 5 (cons bad (cdr entries)) s))))
(assert-event
 (equal (fn-col-poll (fn-own-start *coit-bad-ack-store* 2) *colt-id*)
        '(:refused :scope)))
(assert-event
 (equal (fn-col-poll-list-reference
         (fn-own-start *coit-bad-ack-store* 2) *colt-id*)
        '(:refused :scope)))

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
