; Executable finite traces over the abstract composite node machine.
; These assertions exercise refusal, retry, stale completion, indeterminate
; fencing, recovery, and malformed-event rejection.  No disk or host result is
; inferred by this book.
(in-package "ACL2")
(include-book "../../books/node-traces")

(defconst *node-trace-groups* '("fn.letters" "fn.test"))
(defconst *node-trace-payload* '(72 105 13 10))
(defconst *node-trace-empty* (fn-node-initial-state *node-trace-groups* 16))

(defconst *node-trace-first-prepare*
  '(:prepare 9 "<a@example.invalid>" (72 105 13 10)
             ("fn.letters" "fn.test") "archive-a" "content-a" "release-a" 5))
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
                                     ("fn.letters") "id" "subject" "e" 1))))
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
              ("fn.letters" "fn.test") "archive-a" "content-a" "release-a" 5)
    (:prepare 9 "<b@example.invalid>" (72 105 13 10)
              ("fn.letters") "archive-b" "content-b" "release-b" 2)
    (:complete 99 9 :durable)
    (:complete 0 9 :durable)
    (:prepare 9 "<c@example.invalid>" (72 105 13 10)
              ("fn.test") "archive-c" "content-c" "release-c" 1)
    (:complete 1 9 :indeterminate)
    (:recover 1 9 :absent)
    (:prepare 9 "<b@example.invalid>" (72 105 13 10)
              ("fn.letters") "archive-b" "content-b" "release-b" 2)
    (:complete 99 9 :durable)
    (:complete 2 9 :indeterminate)
    (:prepare 9 "<d@example.invalid>" (72 105 13 10)
              ("fn.test") "archive-d" "content-d" "release-d" 1)
    (:complete 99 9 :durable)
    (:recover 2 9 :committed)
    (:prepare 9 "<d@example.invalid>" (72 105 13 10)
              ("fn.test") "archive-d" "content-d" "release-d" 1)
    (:complete 3 9 :aborted)
    (:prepare 9 "<d@example.invalid>" (72 105 13 10)
              ("fn.test") "archive-d" "content-d" "release-d" 1)
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
                             ("fn.letters") "archive-a" "content-a" "release-a" 3)
                   (:complete 0 9 :durable))))
(defconst *node-trace-suffix*
  '((:bogus)
    (:complete 88 9 :durable)
    (:prepare 9 "<bad-group@example.invalid>" (72 105)
              ("fn.missing") "archive-bad" "content-bad" "release-bad" 2)
    (:prepare 9 "<b@example.invalid>" (72 105)
              ("fn.test") "archive-b" "content-b" "release-b" 2)
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
