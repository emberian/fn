; Regression vectors for actual immutable-fact ingest and finite traces.

(in-package "ACL2")
(include-book "../../books/exchange-invariants")

(defconst *fn-exchange-inv-alice-policy*
  (fn-exchange-make-policy '(1) '("alice")))
(defconst *fn-exchange-inv-relay-policy*
  (fn-exchange-make-policy '(1) '("relay")))

(defconst *fn-exchange-inv-a*
  (fn-exchange-make-fact 1 :object "<ia@example.invalid>" "sha256:ia"
                         "alice-node" "inc-a" 1 "alice"))
(defconst *fn-exchange-inv-b*
  (fn-exchange-make-fact 1 :object "<ib@example.invalid>" "sha256:ib"
                         "alice-node" "inc-a" 2 "alice"))
(defconst *fn-exchange-inv-a-conflict*
  (fn-exchange-make-fact 1 :object "<ia@example.invalid>" "sha256:other"
                         "relay-node" "inc-r" 7 "alice"))
(defconst *fn-exchange-inv-unknown*
  (fn-exchange-make-fact 9 :object "<iu@example.invalid>" "sha256:iu"
                         "alice-node" "inc-a" 3 "alice"))
(defconst *fn-exchange-inv-unauthorized*
  (fn-exchange-make-fact 1 :object "<ix@example.invalid>" "sha256:ix"
                         "mallory-node" "inc-m" 1 "mallory"))

; A duplicate in an admitted batch has no extra capacity charge.  The vector
; also checks the actual state constructor remains within its finite bound.
(defconst *fn-exchange-inv-base*
  (fn-exchange-ingest (fn-exchange-initial-state 3)
                      (list *fn-exchange-inv-a*)
                      *fn-exchange-inv-alice-policy*))
(defconst *fn-exchange-inv-duplicate-batch-result*
  (fn-exchange-ingest *fn-exchange-inv-base*
                      (list *fn-exchange-inv-b*
                            *fn-exchange-inv-b*
                            *fn-exchange-inv-a*)
                      *fn-exchange-inv-alice-policy*))
(assert-event (fn-exchange-statep *fn-exchange-inv-duplicate-batch-result*))
(assert-event
 (equal (len (fn-exchange-facts *fn-exchange-inv-duplicate-batch-result*)) 2))
(assert-event
 (equal (len (fn-exchange-new-facts
              (list *fn-exchange-inv-b* *fn-exchange-inv-b* *fn-exchange-inv-a*)
              (fn-exchange-facts *fn-exchange-inv-base*)))
        1))

; Valid conflicting objects stay together and result in the local conflict
; status.  The model does not choose a winner.
(defconst *fn-exchange-inv-conflicted*
  (fn-exchange-ingest *fn-exchange-inv-base*
                      (list *fn-exchange-inv-a-conflict*)
                      *fn-exchange-inv-alice-policy*))
(assert-event
 (equal (fn-exchange-message-status "<ia@example.invalid>"
                                    (fn-exchange-facts *fn-exchange-inv-conflicted*))
        :conflict))
(assert-event (member-equal *fn-exchange-inv-a*
                            (fn-exchange-facts *fn-exchange-inv-conflicted*)))
(assert-event (member-equal *fn-exchange-inv-a-conflict*
                            (fn-exchange-facts *fn-exchange-inv-conflicted*)))

; Unknown schemas and unauthorized provenance reject their entire batches.
(assert-event
 (equal (fn-exchange-ingest *fn-exchange-inv-base*
                            (list *fn-exchange-inv-unknown* *fn-exchange-inv-b*)
                            *fn-exchange-inv-alice-policy*)
        *fn-exchange-inv-base*))
(assert-event
 (equal (fn-exchange-ingest *fn-exchange-inv-base*
                            (list *fn-exchange-inv-unauthorized* *fn-exchange-inv-b*)
                            *fn-exchange-inv-alice-policy*)
        *fn-exchange-inv-base*))

; A finite fixed-policy trace keeps every accepted fact despite replay.
(defconst *fn-exchange-inv-trace*
  (fn-exchange-ingest-trace
   (fn-exchange-initial-state 3)
   (list (list *fn-exchange-inv-a*)
         (list *fn-exchange-inv-b*)
         (list *fn-exchange-inv-a*))
   *fn-exchange-inv-alice-policy*))
(assert-event (fn-exchange-statep *fn-exchange-inv-trace*))
(assert-event (member-equal *fn-exchange-inv-a*
                            (fn-exchange-facts *fn-exchange-inv-trace*)))
(assert-event (member-equal *fn-exchange-inv-b*
                            (fn-exchange-facts *fn-exchange-inv-trace*)))

; On the second actual call the authority changes: b is valid under the first
; policy but refused under the relay-only policy.  The first accepted fact
; remains, and no prefix of the refused batch can appear.
(defconst *fn-exchange-inv-policy-trace*
  (fn-exchange-policy-ingest-trace
   (fn-exchange-initial-state 3)
   (list (list *fn-exchange-inv-a*) (list *fn-exchange-inv-b*))
   (list *fn-exchange-inv-alice-policy* *fn-exchange-inv-relay-policy*)))
(assert-event (fn-exchange-statep *fn-exchange-inv-policy-trace*))
(assert-event (member-equal *fn-exchange-inv-a*
                            (fn-exchange-facts *fn-exchange-inv-policy-trace*)))
(assert-event (not (member-equal *fn-exchange-inv-b*
                                 (fn-exchange-facts *fn-exchange-inv-policy-trace*))))

; Capacity makes sequential arrival order observable.  This is an intentional
; counterexample to any claim that merge commutativity alone makes all bounded
; admission schedules converge: each first batch fills the one-fact state and
; the other valid singleton is atomically refused.
(defconst *fn-exchange-inv-a-then-b*
  (fn-exchange-ingest
   (fn-exchange-ingest (fn-exchange-initial-state 1)
                       (list *fn-exchange-inv-a*)
                       *fn-exchange-inv-alice-policy*)
   (list *fn-exchange-inv-b*)
   *fn-exchange-inv-alice-policy*))
(defconst *fn-exchange-inv-b-then-a*
  (fn-exchange-ingest
   (fn-exchange-ingest (fn-exchange-initial-state 1)
                       (list *fn-exchange-inv-b*)
                       *fn-exchange-inv-alice-policy*)
   (list *fn-exchange-inv-a*)
   *fn-exchange-inv-alice-policy*))
(assert-event
 (not (fn-exchange-set-equiv (fn-exchange-facts *fn-exchange-inv-a-then-b*)
                             (fn-exchange-facts *fn-exchange-inv-b-then-a*))))
