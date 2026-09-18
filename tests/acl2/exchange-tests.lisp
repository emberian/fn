; Four-node carried-media scenarios for the pure exchange fact-set model.

(in-package "ACL2")
(include-book "../../books/exchange")

(defconst *fn-exchange-policy*
  (fn-exchange-make-policy '(1) '("alice" "relay" "archive")))

(defconst *fn-exchange-a*
  (fn-exchange-make-fact 1 :object "<a@example.invalid>" "sha256:a"
                         "alice-node" "inc-a" 1 "alice"))
(defconst *fn-exchange-a-duplicate*
  (fn-exchange-make-fact 1 :object "<a@example.invalid>" "sha256:a"
                         "alice-node" "inc-a" 1 "alice"))
(defconst *fn-exchange-a-conflict*
  (fn-exchange-make-fact 1 :object "<a@example.invalid>" "sha256:other"
                         "relay-node" "inc-r" 9 "relay"))
(defconst *fn-exchange-b*
  (fn-exchange-make-fact 1 :object "<b@example.invalid>" "sha256:b"
                         "alice-node" "inc-a" 2 "alice"))
(defconst *fn-exchange-statement*
  (fn-exchange-make-fact 1 :statement "<a@example.invalid>" "sha256:receipt"
                         "relay-node" "inc-r" 10 "relay"))
(defconst *fn-exchange-unknown*
  (fn-exchange-make-fact 99 :object "<u@example.invalid>" "sha256:u"
                         "unknown-node" "inc-u" 1 "relay"))

(assert-event (fn-exchange-validatep *fn-exchange-a* *fn-exchange-policy*))
(assert-event (not (fn-exchange-validatep *fn-exchange-unknown*
                                             *fn-exchange-policy*)))
(assert-event
 (not (equal (fn-exchange-content-id *fn-exchange-a*)
             (fn-exchange-origin-event-id *fn-exchange-a*))))

; Node A writes portable facts.  B receives a duplicate/reordered carried batch.
(defconst *fn-exchange-node-a*
  (fn-exchange-ingest (fn-exchange-initial-state 8)
                      (list *fn-exchange-a* *fn-exchange-b*)
                      *fn-exchange-policy*))
(defconst *fn-exchange-node-b*
  (fn-exchange-ingest (fn-exchange-initial-state 8)
                      (list *fn-exchange-b* *fn-exchange-a-duplicate* *fn-exchange-a*)
                      *fn-exchange-policy*))
(assert-event (fn-exchange-statep *fn-exchange-node-a*))
(assert-event (fn-exchange-statep *fn-exchange-node-b*))
(assert-event
 (fn-exchange-set-equiv (fn-exchange-facts *fn-exchange-node-a*)
                        (fn-exchange-facts *fn-exchange-node-b*)))

; C obtains A's facts from B, in a different order.  D gets one item directly
; and the other later by carried media.  All four observe the same fact set.
(defconst *fn-exchange-node-c*
  (fn-exchange-ingest (fn-exchange-initial-state 8)
                      (fn-exchange-facts *fn-exchange-node-b*)
                      *fn-exchange-policy*))
(defconst *fn-exchange-node-d-first*
  (fn-exchange-ingest (fn-exchange-initial-state 8)
                      (list *fn-exchange-a*) *fn-exchange-policy*))
(defconst *fn-exchange-node-d*
  (fn-exchange-ingest *fn-exchange-node-d-first*
                      (list *fn-exchange-b* *fn-exchange-a-duplicate*)
                      *fn-exchange-policy*))
(assert-event
 (fn-exchange-set-equiv (fn-exchange-facts *fn-exchange-node-a*)
                        (fn-exchange-facts *fn-exchange-node-c*)))
(assert-event
 (fn-exchange-set-equiv (fn-exchange-facts *fn-exchange-node-a*)
                        (fn-exchange-facts *fn-exchange-node-d*)))

; Duplicates are observable-set idempotent, including a replay at full capacity.
(defconst *fn-exchange-full*
  (fn-exchange-ingest (fn-exchange-initial-state 1)
                      (list *fn-exchange-a*) *fn-exchange-policy*))
(assert-event
 (equal (fn-exchange-ingest *fn-exchange-full* (list *fn-exchange-a*)
                            *fn-exchange-policy*)
        *fn-exchange-full*))

; Unknown schema has no transition, and unaffordable atomic input is refused
; with its prior committed fact set untouched.
(assert-event
 (equal (fn-exchange-ingest *fn-exchange-node-a* (list *fn-exchange-unknown*)
                            *fn-exchange-policy*)
        *fn-exchange-node-a*))
(defconst *fn-exchange-small*
  (fn-exchange-ingest (fn-exchange-initial-state 1)
                      (list *fn-exchange-a*) *fn-exchange-policy*))
(assert-event
 (equal (fn-exchange-ingest *fn-exchange-small*
                            (list *fn-exchange-b* *fn-exchange-statement*)
                            *fn-exchange-policy*)
        *fn-exchange-small*))

; Conflicting evidence survives and produces a deterministic local conflict
; status; it does not select a winner by arrival time.
(defconst *fn-exchange-conflicted*
  (fn-exchange-ingest *fn-exchange-node-a* (list *fn-exchange-a-conflict*)
                      *fn-exchange-policy*))
(assert-event (equal (fn-exchange-message-status "<a@example.invalid>"
                                                (fn-exchange-facts *fn-exchange-node-a*))
                     :single))
(assert-event (equal (fn-exchange-message-status "<a@example.invalid>"
                                                (fn-exchange-facts *fn-exchange-conflicted*))
                     :conflict))
(assert-event (member-equal *fn-exchange-a* (fn-exchange-facts *fn-exchange-conflicted*)))
(assert-event (member-equal *fn-exchange-a-conflict*
                            (fn-exchange-facts *fn-exchange-conflicted*)))
