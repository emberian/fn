; The actual owner poll agrees with the exact historical list on a committed
; article, but a stale derived index changes its observable answer.
(in-package "ACL2")
(include-book "../../books/consumer-owner-index-invariants")
(include-book "consumer-owner-local-tests")
(include-book "must-fail-checked")

; lane history-columns-3: the readers take the history stobj fn-hist.
(defun fn-col-poll-hx (o consumer hist)
  ; fn-col-poll over a history stobj loaded with HIST (R holds when HIST is the history it reads).
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-hist
    (mv-let (ans fn-hist)
      (let ((fn-hist (fn-hist-load (true-list-fix hist) 0 fn-hist)))
        (mv (fn-col-poll o consumer fn-hist) fn-hist))
      ans)))

; lane history-columns-3: the readers take the history stobj fn-hist.
(defun fn-col-poll-h (o consumer)
  ; fn-col-poll over a history stobj loaded with the history it reads (R holds by construction).
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-hist
    (mv-let (ans fn-hist)
      (let ((fn-hist (fn-hist-load (true-list-fix (fn-sf-records (fn-sn-files (fn-own-store o)))) 0 fn-hist)))
        (mv (fn-col-poll o consumer fn-hist) fn-hist))
      ans)))


(assert-event (fn-snt-relation *colt-after-article*))

(assert-event
 (equal (fn-col-poll-h (fn-own-start *colt-after-article* 2) *colt-id*)
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
 (equal (fn-col-poll-h (fn-own-start *coit-bad-ack-store* 2) *colt-id*)
        '(:refused :scope)))
(assert-event
 (equal (fn-col-poll-list-reference
         (fn-own-start *coit-bad-ack-store* 2) *colt-id*)
        '(:refused :scope)))

;; Without R (lane history-columns-3: the store node's event index is
;; retired): the poll read through a history stobj that is NOT the Store's
;; history (empty) answers differently from the list reference.
(defconst *coit-owner* (fn-own-start *colt-after-article* 2))
(assert-event (consp (fn-sf-records (fn-sn-files (fn-own-store *coit-owner*)))))
(assert-event
 (not (equal (fn-col-poll-hx *coit-owner* *colt-id* nil)
             (fn-col-poll-list-reference *coit-owner* *colt-id*))))
(assert-event
 (equal (fn-col-poll-h *coit-owner* *colt-id*)
        (fn-col-poll-list-reference *coit-owner* *colt-id*)))
(must-fail-checked
 (assert-event
  (equal (fn-col-poll-hx *coit-owner* *colt-id* nil)
         (fn-col-poll-list-reference *coit-owner* *colt-id*))))
