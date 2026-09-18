; Executable commit-record replay scenarios.  These records are logical inputs,
; not a byte persistence or signature test.
(in-package "ACL2")
(include-book "../../books/replay")

(defconst *replay-groups* '("fn.letters" "fn.test"))
(defconst *replay-payload-a* '(72 105 13 10))
(defconst *replay-payload-b* '(66 13 10))
(defconst *replay-r0*
  (fn-record-make 0 0 9 "<a@example.invalid>" *replay-payload-a*
                  *replay-groups* "archive-a" "content-a" "release-a" 5))
; txid 1 represents a known abort; contiguous journal sequence 1 commits txid 2.
(defconst *replay-r1*
  (fn-record-make 1 2 9 "<b@example.invalid>" *replay-payload-b*
                  '("fn.letters") "archive-b" "content-b" "release-b" 3))
(assert-event (fn-record-p *replay-r0*))
(assert-event (fn-record-p *replay-r1*))

(defconst *replay-ok* (fn-replay *replay-groups* 10 (list *replay-r0* *replay-r1*)))
(assert-event (fn-replay-okp *replay-ok*))
(assert-event (equal (fn-replay-result-sequence *replay-ok*) 2))
(assert-event (equal (len (fn-state-articles
                           (fn-node-acceptance (fn-replay-result-node *replay-ok*))))
                     2))
(assert-event (equal (fn-retain-reserved
                      (fn-node-retention (fn-replay-result-node *replay-ok*))) 8))
(assert-event (equal (fn-state-next-txid
                      (fn-node-acceptance (fn-replay-result-node *replay-ok*))) 3))

; Duplicate, out-of-order, and gap sequences fail at the last good prefix.
(defconst *replay-duplicate* (fn-replay *replay-groups* 10 (list *replay-r0* *replay-r0*)))
(assert-event (fn-replay-faultp *replay-duplicate*))
(assert-event (equal (fn-replay-result-sequence *replay-duplicate*) 1))
(assert-event (equal (len (fn-state-articles
                           (fn-node-acceptance
                            (fn-replay-result-node *replay-duplicate*)))) 1))
(defconst *replay-gap*
  (fn-replay *replay-groups* 10
             (list (fn-record-make 1 0 9 "<a@example.invalid>" *replay-payload-a*
                                   *replay-groups* "archive-a" "content-a" "release-a" 5))))
(assert-event (fn-replay-faultp *replay-gap*))
(assert-event (equal (fn-replay-result-sequence *replay-gap*) 0))
(defconst *replay-improper-tail*
  (fn-replay *replay-groups* 10 (cons *replay-r0* 17)))
(assert-event (fn-replay-faultp *replay-improper-tail*))
(assert-event (equal (fn-replay-result-sequence *replay-improper-tail*) 1))

; Capacity, malformed subject, and a transaction-id reuse/refusal fault rather
; than silently dropping a claimed committed record.
(defconst *replay-over-capacity*
  (fn-replay *replay-groups* 4 (list *replay-r0*)))
(assert-event (fn-replay-faultp *replay-over-capacity*))
(assert-event (equal (fn-replay-result-sequence *replay-over-capacity*) 0))
(assert-event (equal (len (fn-state-articles
                           (fn-node-acceptance
                            (fn-replay-result-node *replay-over-capacity*)))) 0))
(defconst *replay-bad-subject*
  (fn-replay *replay-groups* 10
             (list (fn-record-make 0 0 9 "<a@example.invalid>" *replay-payload-a*
                                   *replay-groups* "archive-a" nil "release-a" 5))))
(assert-event (fn-replay-faultp *replay-bad-subject*))
(assert-event (equal (fn-replay-result-reason *replay-bad-subject*) :invalid-record))
(defconst *replay-txid-reuse*
  (fn-replay *replay-groups* 10
             (list *replay-r0*
                   (fn-record-make 1 0 9 "<b@example.invalid>" *replay-payload-b*
                                   '("fn.letters") "archive-b" "content-b" "release-b" 3))))
(assert-event (fn-replay-faultp *replay-txid-reuse*))
(assert-event (equal (fn-replay-result-sequence *replay-txid-reuse*) 1))
