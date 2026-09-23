; Replay test book: executable commit-record replay scenarios, the guard-world
; audit and malformed logical-input regressions.
;
; Folded from replay-tests and replay-guards-tests (2026-09-19).  These
; records are logical inputs, not a byte persistence or signature test.  A
; call outside a guard is made under `with-guard-checking :none'.
(in-package "ACL2")
(include-book "../../books/replay")
(include-book "../../books/codec-attach")

; -----------------------------------------------------------------------------
; Guard world.  `fn-node-statep' is carried: the advance, the one-record step
; and the loop take it as their guard; the entry point checks it once.
(assert-event (equal (symbol-class 'fn-replay-result-kind (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-replay-result-kind nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-replay-result-node (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-replay-result-node nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-replay-result-sequence (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-replay-result-sequence nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-replay-result-reason (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-replay-result-reason nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-replay-ok (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-replay-ok nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-replay-fault (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-replay-fault nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-replay-okp (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-replay-okp nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-replay-faultp (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-replay-faultp nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-replay-advance-txid (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-replay-advance-txid nil (w state)) '(fn-node-statep node)))
(assert-event (equal (symbol-class 'fn-replay-advance-okp (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-replay-advance-okp nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-replay-apply-record (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-replay-apply-record nil (w state))
                     '(if (fn-node-statep node) (true-listp record) 'nil)))
(assert-event (equal (symbol-class 'fn-replay-loop (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-replay-loop nil (w state)) '(fn-node-statep node)))
(assert-event (equal (symbol-class 'fn-replay (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-replay nil (w state)) ''t))

(defconst *rg-node* (fn-node-initial-state '("fn.test") 10))
(assert-event (equal (fn-replay-result-kind 7) nil))
(assert-event (equal (fn-replay-result-node '(:ok . 7)) nil))
(assert-event (equal (fn-replay-result-sequence '(:ok 7 . tail)) nil))
(assert-event (equal (fn-replay-result-reason #c(1 2)) nil))
(assert-event (not (fn-replay-okp 7)))
(assert-event (not (fn-replay-faultp '(:fault . 7))))
; The :logic bodies are total: a non-state is returned unchanged or refused.
(assert-event (with-guard-checking :none (equal (fn-replay-advance-txid 7 4) 7)))
(assert-event (equal (fn-replay-advance-txid *rg-node* #c(1 2)) *rg-node*))
(assert-event (not (fn-replay-advance-okp '(a . b) 0)))
(assert-event (with-guard-checking :none (equal (fn-replay-apply-record 7 nil) nil)))
(assert-event (equal (fn-replay-apply-record *rg-node* '(0 0 bad)) nil))
(assert-event
 (with-guard-checking :none
  (equal (fn-replay-loop 7 '(bad . tail) #c(0 1))
         (fn-replay-fault 7 #c(0 1) :invalid-initial-node))))
(assert-event (equal (fn-replay-loop *rg-node* '(7 bad . tail) 0)
                     (fn-replay-fault *rg-node* 0 :invalid-record)))
(assert-event (equal (fn-replay-loop *rg-node* 7 0)
                     (fn-replay-fault *rg-node* 0 :improper-record-list)))
; Preserve the existing total logical behavior for an arbitrary caller's
; expected-sequence value; the public entry point always initializes it to 0.
(assert-event (equal (fn-replay-loop *rg-node* nil #c(0 1))
                     (fn-replay-ok *rg-node* #c(0 1))))
(assert-event (not (fn-replay-okp (fn-replay-loop *rg-node* nil #c(0 1)))))
(assert-event (equal (fn-replay-result-reason (fn-replay 7 10 nil))
                     :invalid-initial-node))
(assert-event (equal (fn-replay-result-reason (fn-replay '("fn.test") #c(0 1) nil))
                     :invalid-initial-node))

; -----------------------------------------------------------------------------
; Executable commit-record replay scenarios.

(defconst *replay-groups* '("fn.letters" "fn.test"))
(defconst *replay-payload-a* '(72 105 13 10))
(defconst *replay-payload-b* '(66 13 10))
(defconst *replay-r0*
  (fn-record-make 0 0 9 "<a@example.invalid>" *replay-payload-a*
                  *replay-groups* "archive-a" "content-a" "release-a" 5 :legacy))
; txid 1 represents a known abort; contiguous journal sequence 1 commits txid 2.
(defconst *replay-r1*
  (fn-record-make 1 2 9 "<b@example.invalid>" *replay-payload-b*
                  '("fn.letters") "archive-b" "content-b" "release-b" 3 :legacy))
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
                                   *replay-groups* "archive-a" "content-a" "release-a" 5 :legacy))))
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
                                   *replay-groups* "archive-a" nil "release-a" 5 :legacy))))
(assert-event (fn-replay-faultp *replay-bad-subject*))
(assert-event (equal (fn-replay-result-reason *replay-bad-subject*) :invalid-record))
(defconst *replay-txid-reuse*
  (fn-replay *replay-groups* 10
             (list *replay-r0*
                   (fn-record-make 1 0 9 "<b@example.invalid>" *replay-payload-b*
                                   '("fn.letters") "archive-b" "content-b" "release-b" 3 :legacy))))
(assert-event (fn-replay-faultp *replay-txid-reuse*))
(assert-event (equal (fn-replay-result-sequence *replay-txid-reuse*) 1))
