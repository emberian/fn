; Teeth for the exchange conflicting-evidence keystone.
;
; `fn-exchange-admitted-ingest-retains-conflicting-evidence'
; (books/exchange-invariants.lisp:131) is the theorem behind OBJ-001's
; "preserve conflicting evidence": an admitted batch carrying an object whose
; Message-ID collides with a stored object leaves both pieces of evidence, and
; says nothing about a winner.  Six hypotheses; three enable the conclusion and
; three scope it.  The three that enable it get teeth.

(in-package "ACL2")
(include-book "../../books/exchange-invariants")
(include-book "std/testing/must-fail" :dir :system)

; -----------------------------------------------------------------------------
; A reachable, non-degenerate witness.
;
; Two facts that agree on the Message-ID and disagree on the content identity,
; origin node, incarnation and sequence.  A witness whose two facts differed
; only in the content identity would not separate "both kept" from "the newer
; one kept": here neither fact dominates the other on any ordering the model
; has, which is the point of refusing to select a winner.

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

; -----------------------------------------------------------------------------
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

(local
 (must-fail
  (defthm exch-teeth-retains-without-admissibility
    (and (member-equal *exch-teeth-a*
                       (fn-exchange-facts
                        (fn-exchange-ingest *exch-teeth-store* *exch-teeth-bad-batch*
                                            *exch-teeth-policy*)))
         (member-equal *exch-teeth-conflict*
                       (fn-exchange-facts
                        (fn-exchange-ingest *exch-teeth-store* *exch-teeth-bad-batch*
                                            *exch-teeth-policy*)))))))

; H2, the stored fact being stored, dropped.  A fact in neither the state nor
; the batch is not in the result: ingest adds the batch, not the universe.
(assert-event
 (not (member-equal *exch-teeth-outside* (fn-exchange-facts *exch-teeth-store*))))

(local
 (must-fail
  (defthm exch-teeth-retains-without-stored-fact
    (and (member-equal *exch-teeth-outside* (fn-exchange-facts *exch-teeth-after*))
         (member-equal *exch-teeth-conflict* (fn-exchange-facts *exch-teeth-after*))))))

; H3, the incoming fact being in the batch, dropped.  Same shape, other side:
; an admissible batch does not admit a fact it does not carry.
(assert-event (not (member-equal *exch-teeth-outside* *exch-teeth-batch*)))

(local
 (must-fail
  (defthm exch-teeth-retains-without-incoming-in-batch
    (and (member-equal *exch-teeth-a* (fn-exchange-facts *exch-teeth-after*))
         (member-equal *exch-teeth-outside* (fn-exchange-facts *exch-teeth-after*))))))

; H4, H5 and H6 -- the two object-for-message tests and the content-identity
; disagreement -- have no teeth, and none is forged.  They scope the claim
; rather than enable it: the conclusion follows from H1 to H3 alone, because
; `fn-exchange-ingest' retains every stored fact and adds every batch fact
; whatever their Message-IDs are.  Dropping them yields a theorem that is still
; true and no longer about conflicting evidence, which is why they are there.
; Recorded as a finding in HANDOFF.md.
