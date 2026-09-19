; Teeth for the node install keystone.
;
; The 2026-09-18 review §5: "The node install step discharges its hard premises
; from the invariant rather than assuming them (books/node-invariants.lisp:70-101).
; This is the opposite of hypothesis smuggling."  That is
; `fn-node-install-stage-preserves-state', and it has exactly two hypotheses.
; Both are given teeth here.

(in-package "ACL2")
(include-book "../../books/node-invariants")
(include-book "std/testing/must-fail" :dir :system)

; -----------------------------------------------------------------------------
; A reachable, non-degenerate witness.
;
; A node with a committed article, a committed archive pin, a published binding
; that relates the two, and a second transaction staged on top.  The archive
; subject is deliberately not the Message-ID, so a witness that conflated them
; would not satisfy the binding clause.

(defconst *node-teeth-groups* '("fn.letters" "fn.test"))
(defconst *node-teeth-payload* '(72 105 13 10))
(defconst *node-teeth-empty* (fn-node-initial-state *node-teeth-groups* 12))

(defconst *node-teeth-prepared*
  (fn-node-prepare *node-teeth-empty* 9 "<a@example.invalid>" *node-teeth-payload*
                   *node-teeth-groups* "archive-a" "content-a" "release-a" 5))
(defconst *node-teeth-committed*
  (fn-node-complete *node-teeth-prepared* 0 9 :durable))
(defconst *node-teeth-staged-again*
  (fn-node-prepare *node-teeth-committed* 9 "<b@example.invalid>"
                   '(66 121 101 13 10) '("fn.letters")
                   "archive-b" "content-b" "release-b" 4))

(assert-event (fn-node-statep *node-teeth-empty*))
(assert-event (fn-node-statep *node-teeth-prepared*))
(assert-event (fn-node-statep *node-teeth-committed*))
(assert-event (fn-node-statep *node-teeth-staged-again*))

; Non-degenerate: a committed article, a committed pin, a binding, and a stage.
(assert-event
 (equal (len (fn-state-articles (fn-node-acceptance *node-teeth-committed*))) 1))
(assert-event
 (equal (len (fn-retain-pins (fn-node-retention *node-teeth-committed*))) 1))
(assert-event (equal (len (fn-node-bindings *node-teeth-committed*)) 1))
(assert-event (null (fn-node-stage *node-teeth-committed*)))
(assert-event (consp (fn-node-stage *node-teeth-staged-again*)))

; The archive subject is not the Message-ID: the binding relates three distinct
; identities rather than repeating one.
(assert-event
 (not (equal (fn-node-stage-msgid (fn-node-stage *node-teeth-staged-again*))
             (fn-node-stage-subject (fn-node-stage *node-teeth-staged-again*)))))
(assert-event
 (not (equal (fn-node-stage-subject (fn-node-stage *node-teeth-staged-again*))
             (fn-node-stage-id (fn-node-stage *node-teeth-staged-again*)))))

; The keystone's own construction, at the witness, is a node state.
(assert-event
 (fn-node-statep
  (fn-node-make-state
   (fn-install-pending (fn-node-acceptance *node-teeth-staged-again*))
   (fn-node-stage-retention (fn-node-stage *node-teeth-staged-again*))
   nil
   (cons (fn-node-make-binding
          (fn-node-stage-msgid (fn-node-stage *node-teeth-staged-again*))
          (fn-node-stage-subject (fn-node-stage *node-teeth-staged-again*))
          (fn-node-stage-id (fn-node-stage *node-teeth-staged-again*)))
         (fn-node-bindings *node-teeth-staged-again*)))))

; -----------------------------------------------------------------------------
; Teeth for `fn-node-install-stage-preserves-state'
;   (implies (and (fn-node-statep s) (consp (fn-node-stage s)))
;            (fn-node-statep (fn-node-make-state
;                             (fn-install-pending (fn-node-acceptance s))
;                             (fn-node-stage-retention (fn-node-stage s)) nil
;                             (cons (fn-node-make-binding ...) (fn-node-bindings s)))))

; Hypothesis 1, `(fn-node-statep s)', dropped.  Replace the acceptance
; component of the staged witness with a non-state.  The stage survives, so the
; second hypothesis still holds, and the published acceptance component is not
; a state.
(defconst *node-teeth-forged*
  (fn-node-make-state 7
                      (fn-node-retention *node-teeth-staged-again*)
                      (fn-node-stage *node-teeth-staged-again*)
                      (fn-node-bindings *node-teeth-staged-again*)))
(assert-event (not (fn-node-statep *node-teeth-forged*)))
(assert-event (consp (fn-node-stage *node-teeth-forged*)))

(local
 (must-fail
  (defthm node-teeth-install-without-node-statep
    (fn-node-statep
     (fn-node-make-state
      (fn-install-pending (fn-node-acceptance *node-teeth-forged*))
      (fn-node-stage-retention (fn-node-stage *node-teeth-forged*))
      nil
      (cons (fn-node-make-binding
             (fn-node-stage-msgid (fn-node-stage *node-teeth-forged*))
             (fn-node-stage-subject (fn-node-stage *node-teeth-forged*))
             (fn-node-stage-id (fn-node-stage *node-teeth-forged*)))
            (fn-node-bindings *node-teeth-forged*)))))))

; Hypothesis 2, `(consp (fn-node-stage s))', dropped.  The committed witness is
; a node state with nothing staged; installing an absent stage publishes an
; article with a NIL Message-ID and a retention component taken from NIL.
(assert-event (fn-node-statep *node-teeth-committed*))
(assert-event (not (consp (fn-node-stage *node-teeth-committed*))))

(local
 (must-fail
  (defthm node-teeth-install-without-a-stage
    (fn-node-statep
     (fn-node-make-state
      (fn-install-pending (fn-node-acceptance *node-teeth-committed*))
      (fn-node-stage-retention (fn-node-stage *node-teeth-committed*))
      nil
      (cons (fn-node-make-binding
             (fn-node-stage-msgid (fn-node-stage *node-teeth-committed*))
             (fn-node-stage-subject (fn-node-stage *node-teeth-committed*))
             (fn-node-stage-id (fn-node-stage *node-teeth-committed*)))
            (fn-node-bindings *node-teeth-committed*)))))))
