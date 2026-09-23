; Node test book: executable acceptance-plus-retention scenarios, the teeth of
; the node install keystone, and finite traces through the dispatcher.
;
; Folded from node-tests, node-teeth-tests and node-traces-tests (2026-09-19).
; Every negative case is a concrete violating value that ACL2 evaluates.  A
; call outside a transition's guard is made under `with-guard-checking :none'.
(in-package "ACL2")
(include-book "../../books/node-traces")

; The three node transitions, the matching test, the dispatcher and the fold
; carry `fn-node-statep'; the stage recognizer carries the committed ledger's.
(assert-event (equal (guard 'fn-node-prepare nil (w state)) '(fn-node-statep s)))
(assert-event (equal (guard 'fn-node-complete nil (w state)) '(fn-node-statep s)))
(assert-event (equal (guard 'fn-node-recover nil (w state)) '(fn-node-statep s)))
(assert-event (equal (guard 'fn-node-pending-matchesp nil (w state)) '(fn-node-statep s)))
(assert-event (equal (guard 'fn-node-stagep nil (w state)) '(fn-retain-statep committed)))
(assert-event (equal (guard 'fn-node-step nil (w state)) '(fn-node-statep s)))
(assert-event (equal (guard 'fn-node-trace nil (w state)) '(fn-node-statep s)))
(assert-event (equal (guard 'fn-node-statep nil (w state)) ''t))
(assert-event (equal (guard 'fn-node-stage nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-node-trace (w state)) :common-lisp-compliant))

; -----------------------------------------------------------------------------
; Executable integration scenarios for acceptance plus retention.

(defconst *node-groups* '("fn.letters" "fn.test"))
(defconst *node-payload* '(72 105 13 10))
(defconst *node-empty* (fn-node-initial-state *node-groups* 8))
(assert-event (fn-node-statep *node-empty*))

; A resource refusal changes neither the acceptance nor retention component.
(assert-event
 (equal (fn-node-prepare *node-empty* 9 "<a@example.invalid>" *node-payload*
                         *node-groups* "archive-a" "content-a" "release-a" 9 841000000)
        *node-empty*))

; The successful preparation stages both sides but publishes neither groups nor
; a committed archive pin.  The archive subject is not the Message-ID.
(defconst *node-prepared*
  (fn-node-prepare *node-empty* 9 "<a@example.invalid>" *node-payload*
                   *node-groups* "archive-a" "content-a" "release-a" 5 841000000))
(assert-event (fn-node-statep *node-prepared*))
(assert-event (equal (fn-state-articles
                      (fn-node-acceptance *node-prepared*)) nil))
(assert-event (equal (fn-retain-reserved
                      (fn-node-retention *node-prepared*)) 0))
(assert-event (equal (fn-retain-reserved
                      (fn-node-stage-retention (fn-node-stage *node-prepared*)))
                     5))
(assert-event
 (equal (fn-node-stage-subject (fn-node-stage *node-prepared*)) "content-a"))

; The reservation blocks competing work before durable completion.
(assert-event
 (equal (fn-node-prepare *node-prepared* 9 "<b@example.invalid>" *node-payload*
                         '("fn.letters") "archive-b" "content-b" "release-b" 4 841000000)
        *node-prepared*))

; Wrong transaction/generation cannot publish either component.
(assert-event
 (equal (fn-node-complete *node-prepared* 1 9 :durable) *node-prepared*))
(assert-event
 (equal (fn-node-complete *node-prepared* 0 10 :durable) *node-prepared*))

; A caller cannot swap a content subject into the staged prospective retention
; state: the correlated stage is not a node state and therefore cannot publish.
; The completion call is outside the guard, so it runs in the logic.
(defconst *node-subject-mismatch*
  (fn-node-make-state
   (fn-node-acceptance *node-prepared*)
   (fn-node-retention *node-prepared*)
   (fn-node-make-stage "<a@example.invalid>" 9 "archive-a" "other-content"
                       "release-a" 5
                       (fn-node-stage-retention (fn-node-stage *node-prepared*)))
   (fn-node-bindings *node-prepared*)))
(assert-event (not (fn-node-statep *node-subject-mismatch*)))
(assert-event
 (with-guard-checking :none
  (equal (fn-node-complete *node-subject-mismatch* 0 9 :durable)
         *node-subject-mismatch*)))

; Matching durable completion publishes both local memberships atomically and
; commits exactly the staged pin.
(defconst *node-committed* (fn-node-complete *node-prepared* 0 9 :durable))
(assert-event (fn-node-statep *node-committed*))
(assert-event (fn-statep (fn-node-acceptance *node-committed*)))
(assert-event (fn-retain-statep (fn-node-retention *node-committed*)))
(assert-event (equal (len (fn-state-articles
                           (fn-node-acceptance *node-committed*)) ) 1))
(assert-event (equal (fn-retain-reserved
                      (fn-node-retention *node-committed*)) 5))
(assert-event (equal (len (fn-retain-pins
                           (fn-node-retention *node-committed*))) 1))
(assert-event (equal (fn-node-stage *node-committed*) nil))

; A lost success/retry is a duplicate and cannot allocate another pin.
(assert-event
 (equal (fn-node-prepare *node-committed* 9 "<a@example.invalid>" *node-payload*
                         *node-groups* "archive-retry" "other-subject"
                         "other-release" 1 841000000)
        *node-committed*))

; A known abort releases the staged capacity and consumes the acceptance txid.
(defconst *node-abort-prepared*
  (fn-node-prepare *node-committed* 9 "<b@example.invalid>" *node-payload*
                   '("fn.letters") "archive-b" "content-b" "release-b" 2 841000000))
(defconst *node-aborted* (fn-node-complete *node-abort-prepared* 1 9 :aborted))
(assert-event (equal (fn-retain-reserved (fn-node-retention *node-aborted*)) 5))
(assert-event (equal (fn-state-next-txid (fn-node-acceptance *node-aborted*)) 2))
(assert-event (equal (fn-node-stage *node-aborted*) nil))

; An indeterminate result fences both ordinary submission and finalization;
; recovery alone chooses whether to promote or discard the staged archive pin.
(defconst *node-uncertain-prepared*
  (fn-node-prepare *node-aborted* 9 "<b@example.invalid>" *node-payload*
                   '("fn.letters") "archive-b" "content-b" "release-b" 2 841000000))
(defconst *node-uncertain*
  (fn-node-complete *node-uncertain-prepared* 2 9 :indeterminate))
(assert-event (equal (fn-state-fenced (fn-node-acceptance *node-uncertain*)) t))
(assert-event (consp (fn-node-stage *node-uncertain*)))
(assert-event
 (equal (fn-node-prepare *node-uncertain* 9 "<c@example.invalid>" *node-payload*
                         '("fn.test") "archive-c" "content-c" "release-c" 1 841000000)
        *node-uncertain*))
(defconst *node-recovered-absent*
  (fn-node-recover *node-uncertain* 2 9 :absent))
(assert-event (fn-node-statep *node-recovered-absent*))
(assert-event (equal (fn-retain-reserved
                      (fn-node-retention *node-recovered-absent*)) 5))
(assert-event (equal (fn-node-stage *node-recovered-absent*) nil))

; The committed recovery branch installs both the article and the exact staged
; archive pin, never a caller-supplied mismatch.
(defconst *node-recovered-committed*
  (fn-node-recover *node-uncertain* 2 9 :committed))
(assert-event (fn-node-statep *node-recovered-committed*))
(assert-event (equal (len (fn-state-articles
                           (fn-node-acceptance *node-recovered-committed*))) 2))
(assert-event (equal (fn-retain-reserved
                      (fn-node-retention *node-recovered-committed*)) 7))
(assert-event (equal (fn-retain-obligation-subject
                      (fn-retain-find-id
                       "archive-b"
                       (fn-retain-pins
                        (fn-node-retention *node-recovered-committed*))))
                     "content-b"))

; Recognizer boundaries: the two proposals exist together, and each committed
; article has its own charged archive obligation and unique Message-ID binding.
(assert-event
 (not (fn-node-statep
       (fn-node-make-state (fn-node-acceptance *node-prepared*)
                           (fn-node-retention *node-prepared*) nil nil))))
(assert-event
 (not (fn-node-statep
       (fn-node-make-state (fn-node-acceptance *node-empty*)
                           (fn-node-retention *node-empty*)
                           (fn-node-stage *node-prepared*) nil))))
(assert-event
 (not (fn-node-statep
       (fn-node-make-state
        (fn-node-acceptance *node-recovered-committed*)
        (fn-node-retention *node-recovered-committed*) nil
        (list (fn-node-make-binding "<a@example.invalid>" "content-a" "archive-a")
              (fn-node-make-binding "<b@example.invalid>" "content-a" "archive-a"))))))
(assert-event
 (not (fn-node-statep
       (fn-node-make-state
        (fn-node-acceptance *node-committed*)
        (fn-node-retention *node-committed*) nil
        (append (fn-node-bindings *node-committed*)
                (fn-node-bindings *node-committed*))))))
(assert-event
 (not (fn-node-statep
       (fn-node-make-state
        (fn-node-acceptance *node-empty*)
        (fn-node-retention *node-empty*) nil
        (list (fn-node-make-binding "<orphan@example.invalid>" "content" "pin"))))))
(assert-event
 (not (fn-node-binding-listp
       (list (fn-node-make-binding "<same>" "content-a" "archive-a")
             (fn-node-make-binding "<same>" "content-b" "archive-b")))))
(assert-event
 (not (fn-node-binding-listp
       (list (fn-node-make-binding "<a>" "content-a" "same-pin")
             (fn-node-make-binding "<b>" "content-a" "same-pin")))))

; -----------------------------------------------------------------------------
; Teeth for the node install keystone.
;
; The 2026-09-18 review §5: "The node install step discharges its hard premises
; from the invariant rather than assuming them.  This is the opposite of
; hypothesis smuggling."  That is `fn-node-install-stage-preserves-state', and
; it has exactly two hypotheses.  Both are given teeth here.

; A reachable, non-degenerate witness: a node with a committed article, a
; committed archive pin, a published binding that relates the two, and a second
; transaction staged on top.  The archive subject is deliberately not the
; Message-ID, so a witness that conflated them would not satisfy the binding
; clause.
(defconst *node-teeth-groups* '("fn.letters" "fn.test"))
(defconst *node-teeth-payload* '(72 105 13 10))
(defconst *node-teeth-empty* (fn-node-initial-state *node-teeth-groups* 12))

(defconst *node-teeth-prepared*
  (fn-node-prepare *node-teeth-empty* 9 "<a@example.invalid>" *node-teeth-payload*
                   *node-teeth-groups* "archive-a" "content-a" "release-a" 5 841000000))
(defconst *node-teeth-committed*
  (fn-node-complete *node-teeth-prepared* 0 9 :durable))
(defconst *node-teeth-staged-again*
  (fn-node-prepare *node-teeth-committed* 9 "<b@example.invalid>"
                   '(66 121 101 13 10) '("fn.letters")
                   "archive-b" "content-b" "release-b" 4 841000000))

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
(assert-event
 (not (fn-node-statep
       (fn-node-make-state
        (fn-install-pending (fn-node-acceptance *node-teeth-forged*))
        (fn-node-stage-retention (fn-node-stage *node-teeth-forged*))
        nil
        (cons (fn-node-make-binding
               (fn-node-stage-msgid (fn-node-stage *node-teeth-forged*))
               (fn-node-stage-subject (fn-node-stage *node-teeth-forged*))
               (fn-node-stage-id (fn-node-stage *node-teeth-forged*)))
              (fn-node-bindings *node-teeth-forged*))))))

; Hypothesis 2, `(consp (fn-node-stage s))', dropped.  The committed witness is
; a node state with nothing staged; installing an absent stage publishes an
; article with a NIL Message-ID and a retention component taken from NIL.
(assert-event (fn-node-statep *node-teeth-committed*))
(assert-event (not (consp (fn-node-stage *node-teeth-committed*))))
(assert-event
 (not (fn-node-statep
       (fn-node-make-state
        (fn-install-pending (fn-node-acceptance *node-teeth-committed*))
        (fn-node-stage-retention (fn-node-stage *node-teeth-committed*))
        nil
        (cons (fn-node-make-binding
               (fn-node-stage-msgid (fn-node-stage *node-teeth-committed*))
               (fn-node-stage-subject (fn-node-stage *node-teeth-committed*))
               (fn-node-stage-id (fn-node-stage *node-teeth-committed*)))
              (fn-node-bindings *node-teeth-committed*))))))

; -----------------------------------------------------------------------------
; Executable finite traces over the abstract composite node machine.  These
; assertions exercise refusal, retry, stale completion, indeterminate fencing,
; recovery, and malformed-event rejection.  No disk or host result is inferred.

(defconst *node-trace-groups* '("fn.letters" "fn.test"))
(defconst *node-trace-payload* '(72 105 13 10))
(defconst *node-trace-empty* (fn-node-initial-state *node-trace-groups* 16))

(defconst *node-trace-first-prepare*
  '(:prepare 9 "<a@example.invalid>" (72 105 13 10)
             ("fn.letters" "fn.test") "archive-a" "content-a" "release-a" 5 841000000))
(defconst *node-trace-after-first-prepare*
  (fn-node-step *node-trace-empty* *node-trace-first-prepare*))

; Structural rejection happens before any node transition is selected.
(assert-event (fn-node-statep *node-trace-empty*))
(assert-event (fn-node-prepare-eventp *node-trace-first-prepare*))
(assert-event (consp (fn-node-stage *node-trace-after-first-prepare*)))
(assert-event
 (equal (fn-pending-msgid
         (fn-state-pending
          (fn-node-acceptance *node-trace-after-first-prepare*)))
        "<a@example.invalid>"))
(assert-event
 (equal (fn-node-stage-id (fn-node-stage *node-trace-after-first-prepare*))
        "archive-a"))
(assert-event (not (fn-node-eventp '(:unknown 1 2 3))))
(assert-event (not (fn-node-eventp '(:complete "not-a-txid" 0 :durable))))
(assert-event (not (fn-node-eventp '(:prepare 0 "<bad>" (not-octets)
                                     ("fn.letters") "id" "subject" "e" 1 841000000))))
(assert-event (equal (fn-node-step *node-trace-empty* '(:unknown 1 2 3))
                     *node-trace-empty*))
(assert-event (equal (fn-node-step *node-trace-empty*
                                   '(:complete "not-a-txid" 0 :durable))
                     *node-trace-empty*))

; A complete trace includes an attempted competing prepare, stale completion,
; durable and indeterminate outcomes, fenced refusal, both recovery outcomes,
; abort, retry, and durable completion.  The first article is then used as an
; old binding while later transactions exercise the remaining branches.
(defconst *node-trace-events*
  '((:prepare 9 "<a@example.invalid>" (72 105 13 10)
              ("fn.letters" "fn.test") "archive-a" "content-a" "release-a" 5 841000000)
    (:prepare 9 "<b@example.invalid>" (72 105 13 10)
              ("fn.letters") "archive-b" "content-b" "release-b" 2 841000000)
    (:complete 99 9 :durable)
    (:complete 0 9 :durable)
    (:prepare 9 "<c@example.invalid>" (72 105 13 10)
              ("fn.test") "archive-c" "content-c" "release-c" 1 841000000)
    (:complete 1 9 :indeterminate)
    (:recover 1 9 :absent)
    (:prepare 9 "<b@example.invalid>" (72 105 13 10)
              ("fn.letters") "archive-b" "content-b" "release-b" 2 841000000)
    (:complete 99 9 :durable)
    (:complete 2 9 :indeterminate)
    (:prepare 9 "<d@example.invalid>" (72 105 13 10)
              ("fn.test") "archive-d" "content-d" "release-d" 1 841000000)
    (:complete 99 9 :durable)
    (:recover 2 9 :committed)
    (:prepare 9 "<d@example.invalid>" (72 105 13 10)
              ("fn.test") "archive-d" "content-d" "release-d" 1 841000000)
    (:complete 3 9 :aborted)
    (:prepare 9 "<d@example.invalid>" (72 105 13 10)
              ("fn.test") "archive-d" "content-d" "release-d" 1 841000000)
    (:complete 4 9 :durable)))

(defconst *node-trace-result*
  (fn-node-trace *node-trace-empty* *node-trace-events*))

(assert-event (fn-node-statep *node-trace-result*))
(assert-event (equal (len (fn-state-articles
                           (fn-node-acceptance *node-trace-result*)))
                       3))
(assert-event (equal (len (fn-retain-pins
                           (fn-node-retention *node-trace-result*)))
                       3))
(assert-event (equal (fn-state-next-txid
                     (fn-node-acceptance *node-trace-result*))
                     5))
(assert-event (equal (fn-node-stage *node-trace-result*) nil))
(assert-event (equal (fn-state-fenced
                      (fn-node-acceptance *node-trace-result*))
                     nil))

; The recognizer inherited from acceptance and retention establishes that all
; committed memberships remain below their watermarks and each article has its
; own archive binding/pin.  The trace theorem additionally preserves the old
; binding set from any valid prefix.
(assert-event
 (fn-node-articles-have-archive-bindingsp
  (fn-state-articles (fn-node-acceptance *node-trace-result*))
  (fn-node-bindings *node-trace-result*)
  (fn-retain-pins (fn-node-retention *node-trace-result*))))
(assert-event (equal (fn-node-find-binding "<a@example.invalid>"
                                           (fn-node-bindings *node-trace-result*))
                     (fn-node-make-binding "<a@example.invalid>"
                                           "content-a" "archive-a")))
(assert-event (equal (fn-node-find-binding "<b@example.invalid>"
                                           (fn-node-bindings *node-trace-result*))
                     (fn-node-make-binding "<b@example.invalid>"
                                           "content-b" "archive-b")))

; A valid prefix's old article/archive binding remains present through an
; arbitrary suffix containing malformed, stale, and refusal events.
(defconst *node-trace-prefix*
  (fn-node-trace *node-trace-empty*
                 '((:prepare 9 "<a@example.invalid>" (72 105 13 10)
                             ("fn.letters") "archive-a" "content-a" "release-a" 3 841000000)
                   (:complete 0 9 :durable))))
(defconst *node-trace-suffix*
  '((:bogus)
    (:complete 88 9 :durable)
    (:prepare 9 "<bad-group@example.invalid>" (72 105)
              ("fn.missing") "archive-bad" "content-bad" "release-bad" 2 841000000)
    (:prepare 9 "<b@example.invalid>" (72 105)
              ("fn.test") "archive-b" "content-b" "release-b" 2 841000000)
    (:complete 1 9 :indeterminate)
    (:recover 1 9 :absent)))
(defconst *node-trace-prefix-suffix*
  (fn-node-trace *node-trace-prefix* *node-trace-suffix*))

(assert-event (fn-node-statep *node-trace-prefix*))
(assert-event (fn-node-statep *node-trace-prefix-suffix*))
(assert-event
 (fn-node-bindings-subsetp (fn-node-bindings *node-trace-prefix*)
                           (fn-node-bindings *node-trace-prefix-suffix*)))
(assert-event (equal (fn-node-find-binding "<a@example.invalid>"
                                           (fn-node-bindings *node-trace-prefix-suffix*))
                     (fn-node-make-binding "<a@example.invalid>"
                                           "content-a" "archive-a")))

; An improper event tail is still rejected by the step and the finite fold
; stops at the atom; no malformed tail is interpreted as an operation.
(assert-event (equal (fn-node-trace *node-trace-empty* '((:unknown) . bad))
                     *node-trace-empty*))
