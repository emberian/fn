; Exchange test book: four-node carried-media scenarios, the guard-world audit,
; malformed logical-input regressions, ingest and trace regression vectors, and
; the teeth of the conflicting-evidence keystone.
;
; Folded from exchange-tests, exchange-guards-tests, exchange-invariants-tests
; and exchange-teeth-tests (2026-09-19).  Every negative case is a concrete
; violating value that ACL2 evaluates.  A call outside a guard is made under
; `with-guard-checking :none'.
(in-package "ACL2")
(include-book "../../books/exchange-invariants")

; -----------------------------------------------------------------------------
; Guard world.  Admissibility and ingest carry `fn-exchange-statep'; records
; and set operations are total.
(assert-event (equal (symbol-class 'fn-exchange-schema (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-exchange-schema nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-exchange-kind (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-exchange-kind nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-exchange-message-id (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-exchange-message-id nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-exchange-content-id (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-exchange-content-id nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-exchange-origin (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-exchange-origin nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-exchange-incarnation (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-exchange-incarnation nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-exchange-sequence (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-exchange-sequence nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-exchange-provenance (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-exchange-provenance nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-exchange-make-fact (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-exchange-make-fact nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-exchange-fact-shapep (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-exchange-fact-shapep nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-exchange-kindp (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-exchange-kindp nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-exchange-origin-event-id (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-exchange-origin-event-id nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-exchange-factp (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-exchange-factp nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-exchange-string-listp (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-exchange-string-listp nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-exchange-no-duplicatesp (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-exchange-no-duplicatesp nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-exchange-policy-schemas (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-exchange-policy-schemas nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-exchange-policy-authorizations (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-exchange-policy-authorizations nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-exchange-make-policy (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-exchange-make-policy nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-exchange-policy-shapep (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-exchange-policy-shapep nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-exchange-policyp (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-exchange-policyp nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-exchange-known-schemap (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-exchange-known-schemap nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-exchange-authorizedp (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-exchange-authorizedp nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-exchange-validatep (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-exchange-validatep nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-exchange-batch-validp (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-exchange-batch-validp nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-exchange-add-fact (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-exchange-add-fact nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-exchange-merge (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-exchange-merge nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-exchange-subsetp (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-exchange-subsetp nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-exchange-set-equiv (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-exchange-set-equiv nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-exchange-capacity (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-exchange-capacity nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-exchange-facts (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-exchange-facts nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-exchange-make-state (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-exchange-make-state nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-exchange-state-shapep (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-exchange-state-shapep nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-exchange-fact-listp (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-exchange-fact-listp nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-exchange-statep (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-exchange-statep nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-exchange-initial-state (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-exchange-initial-state nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-exchange-new-facts (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-exchange-new-facts nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-exchange-admissible-batchp (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-exchange-admissible-batchp nil (w state)) '(fn-exchange-statep s)))
(assert-event (equal (symbol-class 'fn-exchange-ingest (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-exchange-ingest nil (w state)) '(fn-exchange-statep s)))
(assert-event (equal (symbol-class 'fn-exchange-object-for-messagep (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-exchange-object-for-messagep nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-exchange-any-object-for-messagep (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-exchange-any-object-for-messagep nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-exchange-conflicting-with-contentp (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-exchange-conflicting-with-contentp nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-exchange-conflicting-messagep (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-exchange-conflicting-messagep nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-exchange-message-status (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-exchange-message-status nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-exchange-ingest-trace (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-exchange-ingest-trace nil (w state)) '(fn-exchange-statep s)))
(assert-event (equal (symbol-class 'fn-exchange-policy-ingest-trace (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-exchange-policy-ingest-trace nil (w state)) '(fn-exchange-statep s)))

(assert-event (equal (fn-exchange-schema 7) nil))
(assert-event (equal (fn-exchange-kind '(1 . 7)) nil))
(assert-event (equal (fn-exchange-provenance #c(1 2)) nil))
(assert-event (equal (fn-exchange-origin-event-id '(1 :object . tail)) '(nil nil nil)))
(assert-event (not (fn-exchange-factp '(1 :object . tail))))
(assert-event (not (fn-exchange-policyp '((1 . tail) ("auth")))))
(assert-event (fn-exchange-no-duplicatesp '(a . tail)))
(assert-event (not (fn-exchange-no-duplicatesp '(a a . tail))))
; Preserve member-equal's exact suffix result, including dotted suffixes.
(assert-event (equal (fn-exchange-known-schemap 1 '((1 . tail) nil)) '(1 . tail)))
(assert-event (equal (fn-exchange-authorizedp "auth" '(nil ("auth" . tail)))
                     '("auth" . tail)))
(assert-event (not (fn-exchange-authorizedp "auth" 7)))
(assert-event (equal (fn-exchange-add-fact 'a 7) '(a . 7)))
(assert-event (equal (fn-exchange-merge '(a b . tail) 7) '(b a . 7)))
(assert-event (fn-exchange-subsetp '(a . tail) '(a . rest)))
(assert-event (fn-exchange-set-equiv 7 'tail))
(assert-event (equal (fn-exchange-new-facts '(a a b . tail) 7) '(a b)))
(assert-event (not (fn-exchange-validatep 7 7)))
(assert-event (not (fn-exchange-batch-validp '(7 . tail) 7)))
(assert-event (not (fn-exchange-statep '(#c(1 2) nil))))
; The :logic body of ingest is total: a non-state is returned unchanged.
(assert-event
 (with-guard-checking :none
  (equal (fn-exchange-ingest '(#c(1 2) nil) '(bad . tail) 7) '(#c(1 2) nil))))
(assert-event
 (with-guard-checking :none (equal (fn-exchange-ingest 7 '(bad . tail) 7) 7)))
(assert-event (equal (fn-exchange-message-status "m" '(7 . tail)) :absent))
(assert-event (equal (fn-exchange-message-status
                      "m" '((bad :object "m" "a") 7
                            (bad :object "m" "b") . tail)) :conflict))

(defconst *exg-policy* (fn-exchange-make-policy '(1) '("auth")))
(defconst *exg-empty* (fn-exchange-initial-state 1))
(defconst *exg-fact*
  (fn-exchange-make-fact 1 :object "m" "content" "origin" "incarnation" 0 "auth"))
; Reject the entire improper batch after its valid first fact, preserving the
; exact empty store.  A proper batch still takes the original successful path.
(assert-event (equal (fn-exchange-ingest *exg-empty* (cons *exg-fact* 7) *exg-policy*)
                     *exg-empty*))
(assert-event (equal (fn-exchange-ingest *exg-empty* (list *exg-fact*) '(bad . tail))
                     *exg-empty*))
(assert-event (equal (fn-exchange-facts
                      (fn-exchange-ingest *exg-empty* (list *exg-fact*) *exg-policy*))
                     (list *exg-fact*)))

; -----------------------------------------------------------------------------
; Four-node carried-media scenarios for the pure exchange fact-set model.

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

; -----------------------------------------------------------------------------
; Regression vectors for actual immutable-fact ingest and finite traces.

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

; -----------------------------------------------------------------------------
; Teeth for the exchange conflicting-evidence keystone.
;
; `fn-exchange-admitted-ingest-retains-conflicting-evidence' is the theorem
; behind OBJ-001's "preserve conflicting evidence": an admitted batch carrying
; an object whose Message-ID collides with a stored object leaves both pieces
; of evidence, and says nothing about a winner.  Six hypotheses; three enable
; the conclusion and three scope it.  The three that enable it get teeth.

; A reachable, non-degenerate witness: two facts that agree on the Message-ID
; and disagree on the content identity, origin node, incarnation and sequence.
; Neither fact dominates the other on any ordering the model has, which is the
; point of refusing to select a winner.
(defconst *exch-teeth-policy*
  (fn-exchange-make-policy '(1) '("alice" "relay" "archive")))

(defconst *exch-teeth-a*
  (fn-exchange-make-fact 1 :object "<a@example.invalid>" "sha256:a"
                         "alice-node" "inc-a" 1 "alice"))
(defconst *exch-teeth-b*
  (fn-exchange-make-fact 1 :object "<b@example.invalid>" "sha256:b"
                         "alice-node" "inc-a" 2 "alice"))
(defconst *exch-teeth-conflict*
  (fn-exchange-make-fact 1 :object "<a@example.invalid>" "sha256:other"
                         "relay-node" "inc-r" 9 "relay"))
(defconst *exch-teeth-outside*
  (fn-exchange-make-fact 1 :statement "<c@example.invalid>" "sha256:receipt"
                         "relay-node" "inc-r" 10 "relay"))
(defconst *exch-teeth-unknown*
  (fn-exchange-make-fact 99 :object "<u@example.invalid>" "sha256:u"
                         "unknown-node" "inc-u" 1 "relay"))

(defconst *exch-teeth-store*
  (fn-exchange-ingest (fn-exchange-initial-state 8)
                      (list *exch-teeth-a* *exch-teeth-b*)
                      *exch-teeth-policy*))
(defconst *exch-teeth-batch* (list *exch-teeth-conflict*))

(assert-event (fn-exchange-statep *exch-teeth-store*))
(assert-event (member-equal *exch-teeth-a* (fn-exchange-facts *exch-teeth-store*)))
(assert-event
 (fn-exchange-admissible-batchp *exch-teeth-store* *exch-teeth-batch*
                                *exch-teeth-policy*))

; The two facts collide on the Message-ID and agree on nothing else.
(assert-event
 (fn-exchange-object-for-messagep "<a@example.invalid>" *exch-teeth-a*))
(assert-event
 (fn-exchange-object-for-messagep "<a@example.invalid>" *exch-teeth-conflict*))
(assert-event
 (not (equal (fn-exchange-content-id *exch-teeth-a*)
             (fn-exchange-content-id *exch-teeth-conflict*))))
(assert-event
 (not (equal (fn-exchange-origin-event-id *exch-teeth-a*)
             (fn-exchange-origin-event-id *exch-teeth-conflict*))))

; Both survive the admitted batch: this is the keystone at the witness.
(defconst *exch-teeth-after*
  (fn-exchange-ingest *exch-teeth-store* *exch-teeth-batch* *exch-teeth-policy*))
(assert-event (fn-exchange-statep *exch-teeth-after*))
(assert-event (member-equal *exch-teeth-a* (fn-exchange-facts *exch-teeth-after*)))
(assert-event (member-equal *exch-teeth-conflict* (fn-exchange-facts *exch-teeth-after*)))

; Teeth.  The statement is
;   (implies (and (fn-exchange-admissible-batchp s batch policy)          ; H1
;                 (member-equal stored (fn-exchange-facts s))             ; H2
;                 (member-equal incoming batch)                           ; H3
;                 (fn-exchange-object-for-messagep message-id stored)     ; H4
;                 (fn-exchange-object-for-messagep message-id incoming)   ; H5
;                 (not (equal (fn-exchange-content-id stored)
;                             (fn-exchange-content-id incoming))))        ; H6
;            (and (member-equal stored (fn-exchange-facts (fn-exchange-ingest ...)))
;                 (member-equal incoming (fn-exchange-facts (fn-exchange-ingest ...)))))

; H1, admissibility, dropped.  A batch that carries an unauthorised schema is
; refused atomically, so the incoming fact is not retained -- and neither is a
; prefix of the batch, which is the other half of what refusal means here.
(defconst *exch-teeth-bad-batch* (list *exch-teeth-conflict* *exch-teeth-unknown*))
(assert-event
 (not (fn-exchange-admissible-batchp *exch-teeth-store* *exch-teeth-bad-batch*
                                     *exch-teeth-policy*)))
(assert-event
 (not (member-equal *exch-teeth-conflict*
                    (fn-exchange-facts
                     (fn-exchange-ingest *exch-teeth-store* *exch-teeth-bad-batch*
                                         *exch-teeth-policy*)))))

; H2, the stored fact being stored, dropped.  A fact in neither the state nor
; the batch is not in the result: ingest adds the batch, not the universe.
(assert-event
 (not (member-equal *exch-teeth-outside* (fn-exchange-facts *exch-teeth-store*))))
(assert-event
 (not (member-equal *exch-teeth-outside* (fn-exchange-facts *exch-teeth-after*))))

; H3, the incoming fact being in the batch, dropped.  Same shape, other side:
; an admissible batch does not admit a fact it does not carry.
(assert-event (not (member-equal *exch-teeth-outside* *exch-teeth-batch*)))
(assert-event
 (not (member-equal *exch-teeth-outside* (fn-exchange-facts *exch-teeth-after*))))

; H4, H5 and H6 -- the two object-for-message tests and the content-identity
; disagreement -- have no teeth, and none is forged.  They scope the claim
; rather than enable it: the conclusion follows from H1 to H3 alone, because
; `fn-exchange-ingest' retains every stored fact and adds every batch fact
; whatever their Message-IDs are.  Dropping them yields a theorem that is still
; true and no longer about conflicting evidence, which is why they are there.
