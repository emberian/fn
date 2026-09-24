; The actual owner poll agrees with the exact historical list on a committed
; article, but a stale derived index changes its observable answer.
(in-package "ACL2")
(include-book "../../books/consumer-owner-index-invariants")
(include-book "consumer-owner-local-tests")
(include-book "std/testing/must-fail" :dir :system)

(assert-event (fn-ceis-relatedp *colt-after-article*))
(assert-event (fn-snt-relation *colt-after-article*))
(assert-event
 (let* ((store *colt-after-article*)
        (files (fn-sn-files store)))
   (and (fn-ceis-relatedp store)
        (not (member-eq (fn-sf-phase files)
                        '(:replaying :fault)))
        (fn-sf-statep files))))
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
 (and (fn-sf-statep (fn-sn-files *coit-stale-index*))
      (not (member-eq
            (fn-sf-phase (fn-sn-files *coit-stale-index*))
            '(:replaying :fault)))))
(assert-event
 (not (equal (fn-col-poll (fn-own-start *coit-stale-index* 2) *colt-id*)
             (fn-col-poll-list-reference
              (fn-own-start *coit-stale-index* 2) *colt-id*))))
(must-fail
 (assert-event
  (equal (fn-col-poll (fn-own-start *coit-stale-index* 2) *colt-id*)
         (fn-col-poll-list-reference
          (fn-own-start *coit-stale-index* 2) *colt-id*))))

; The phase premise matters because the maintained index relation is
; intentionally vacuous in :fault/:replaying, when poll is not served.
(defconst *coit-fault-files*
  (let ((files (fn-sn-files *colt-after-article*)))
    (fn-sf-make :fault (fn-sf-frontier files) nil
                (fn-sf-records files) nil nil
                (fn-sf-successes files) 0)))
(defconst *coit-fault-stale-index*
  (fn-sn-with-event-index
   (fn-sn-update *colt-after-article* *coit-fault-files*
                 (fn-sn-node *colt-after-article*))
   nil))
(assert-event (fn-ceis-relatedp *coit-fault-stale-index*))
(assert-event
 (fn-sf-statep (fn-sn-files *coit-fault-stale-index*)))
(must-fail
 (assert-event
  (equal (fn-col-poll (fn-own-start *coit-fault-stale-index* 2) *colt-id*)
         (fn-col-poll-list-reference
          (fn-own-start *coit-fault-stale-index* 2) *colt-id*))))
