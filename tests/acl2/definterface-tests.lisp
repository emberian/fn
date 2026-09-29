; Teeth for books/definterface.lisp.
;
;   1. Declarations the world confirms: a guard-verified entry with kind
;      conjuncts and a direct keystone; a :program entry with an exempt
;      formal and a keystone about a function it runs (:via); a stobj
;      creator as an extraction root.  The table records each.
;   2. One refusal per world check, each under must-fail: the wrong class,
;      kinds that differ from the guard's (missing one, extra one, wrong
;      order), an :exempt formal the guard kinds or that is no formal, a
;      keystone that is no theorem, that does not call the entry, whose
;      :via function the entry never runs, and an entry that is no
;      function.
;   3. One refusal per malformed form (fn-di-refusal).
;   4. :raw-with (D40): the accepted raw dispatch and one refusal per check.

(in-package "ACL2")
(include-book "../../books/definterface")
(include-book "../../books/payload-kinds") ; *fn-entry-guard-kinds*
(include-book "must-fail-checked")

(defun fn-dit-f (n tag octets)
  (declare (xargs :guard (and (natp n) (fn-cbor-octet-listp octets) (< n 5)
                              (symbolp tag))))
  (list n tag octets))

(defthm fn-dit-f-keeps-n
  (equal (car (fn-dit-f n tag octets)) n))

(defthm fn-dit-unrelated
  (equal (len (list x)) 1))

(defun fn-dit-g (payload)
  (declare (xargs :mode :program))
  (fn-dit-f 1 :x payload))

(defstobj fn-dit-st (fn-dit-fld :type integer :initially 0))

; ---------------------------------------------------------------------------
; 1. Accepted.

(definterface fn-dit-f
  :class :common-lisp-compliant
  :kinds ((n natp) (tag symbolp) (octets fn-cbor-octet-listp))
  :keystones (fn-dit-f-keeps-n))

(definterface fn-dit-g
  :class :program
  :exempt ((payload "a test: the body passes it on to a guarded entry"))
  :keystones ((fn-dit-f-keeps-n :via fn-dit-f)))

(definterface create-fn-dit-st
  :class :common-lisp-compliant
  :root :extract-extra)

(assert-event
 (equal (table-alist 'fn-interfaces (w state))
        '((create-fn-dit-st :class :common-lisp-compliant :root :extract-extra)
          (fn-dit-g :class :program
                    :exempt ((payload "a test: the body passes it on to a guarded entry"))
                    :keystones ((fn-dit-f-keeps-n :via fn-dit-f)))
          (fn-dit-f :class :common-lisp-compliant
                    :kinds ((n natp) (tag symbolp) (octets fn-cbor-octet-listp))
                    :keystones (fn-dit-f-keeps-n)))))

; The kinds are the host entry guard's: position order, the conjunct (< n 5)
; (not a unary kind) left to ACL2.
(assert-event
 (equal (fn-di-world-kinds 'fn-dit-f (w state))
        '((n natp) (tag symbolp) (octets fn-cbor-octet-listp))))

; A one-form wrapper delegates its decision to the function it is exactly a
; call of (:delegates, lane decision-keystones-2): accepted when the body is
; the callee applied to the wrapper's formals.
(defun fn-dit-w (n tag octets)
  (declare (xargs :guard (and (natp n) (fn-cbor-octet-listp octets) (< n 5)
                              (symbolp tag))))
  (fn-dit-f n tag octets))

(definterface fn-dit-w
  :class :common-lisp-compliant
  :kinds ((n natp) (tag symbolp) (octets fn-cbor-octet-listp))
  :delegates fn-dit-f)

; ---------------------------------------------------------------------------
; 2. The world refutes.

; :delegates: fn-dit-g's body applies fn-dit-f to constants, not to its own
; formals, so its decision is not fn-dit-f's by definition.
(assert-event (fn-di-problem 'fn-dit-g '(:class :program
                     :exempt ((payload "a test: the body passes it on to a guarded entry"))
                     :delegates fn-dit-f) (w state)))
(must-fail-checked (definterface fn-dit-g :class :program
                     :exempt ((payload "a test: the body passes it on to a guarded entry"))
                     :delegates fn-dit-f)
                   :unchecked "definterface's refusal is its claim; the assert-event above names the world check")

; :delegates a name that is no function of the world.
(assert-event (fn-di-problem 'fn-dit-w '(:class :common-lisp-compliant
                     :kinds ((n natp) (tag symbolp) (octets fn-cbor-octet-listp))
                     :delegates fn-dit-no-such-function) (w state)))
(must-fail-checked (definterface fn-dit-w :class :common-lisp-compliant
                     :kinds ((n natp) (tag symbolp) (octets fn-cbor-octet-listp))
                     :delegates fn-dit-no-such-function)
                   :unchecked "definterface's refusal is its claim; the assert-event above names the world check")

(assert-event (fn-di-problem 'fn-dit-f '(:class :program
                     :kinds ((n natp) (tag symbolp) (octets fn-cbor-octet-listp))) (w state)))
(must-fail-checked (definterface fn-dit-f :class :program
                     :kinds ((n natp) (tag symbolp) (octets fn-cbor-octet-listp)))
                   :unchecked "definterface's refusal is its claim; the assert-event above names the world check")

(assert-event (fn-di-problem 'fn-dit-f '(:class :common-lisp-compliant
                     :kinds ((n natp) (octets fn-cbor-octet-listp))) (w state)))
(must-fail-checked (definterface fn-dit-f :class :common-lisp-compliant
                     :kinds ((n natp) (octets fn-cbor-octet-listp)))
                   :unchecked "definterface's refusal is its claim; the assert-event above names the world check")

(assert-event (fn-di-problem 'fn-dit-f '(:class :common-lisp-compliant
                     :kinds ((n natp) (tag symbolp) (octets fn-cbor-octet-listp)
                             (octets fn-payload-handle-p))) (w state)))
(must-fail-checked (definterface fn-dit-f :class :common-lisp-compliant
                     :kinds ((n natp) (tag symbolp) (octets fn-cbor-octet-listp)
                             (octets fn-payload-handle-p)))
                   :unchecked "definterface's refusal is its claim; the assert-event above names the world check")

(assert-event (fn-di-problem 'fn-dit-f '(:class :common-lisp-compliant
                     :kinds ((tag symbolp) (n natp) (octets fn-cbor-octet-listp))) (w state)))
(must-fail-checked (definterface fn-dit-f :class :common-lisp-compliant
                     :kinds ((tag symbolp) (n natp) (octets fn-cbor-octet-listp)))
                   :unchecked "definterface's refusal is its claim; the assert-event above names the world check")

(assert-event (fn-di-problem 'fn-dit-f '(:class :common-lisp-compliant
                     :kinds ((n natp) (tag symbolp) (octets fn-cbor-octet-listp))
                     :exempt ((octets "the guard kinds it"))) (w state)))
(must-fail-checked (definterface fn-dit-f :class :common-lisp-compliant
                     :kinds ((n natp) (tag symbolp) (octets fn-cbor-octet-listp))
                     :exempt ((octets "the guard kinds it")))
                   :unchecked "definterface's refusal is its claim; the assert-event above names the world check")

(assert-event (fn-di-problem 'fn-dit-f '(:class :common-lisp-compliant
                     :kinds ((n natp) (tag symbolp) (octets fn-cbor-octet-listp))
                     :exempt ((bytes "no such formal"))) (w state)))
(must-fail-checked (definterface fn-dit-f :class :common-lisp-compliant
                     :kinds ((n natp) (tag symbolp) (octets fn-cbor-octet-listp))
                     :exempt ((bytes "no such formal")))
                   :unchecked "definterface's refusal is its claim; the assert-event above names the world check")

(assert-event (fn-di-problem 'fn-dit-f '(:class :common-lisp-compliant
                     :kinds ((n natp) (tag symbolp) (octets fn-cbor-octet-listp))
                     :keystones (fn-dit-no-such-theorem)) (w state)))
(must-fail-checked (definterface fn-dit-f :class :common-lisp-compliant
                     :kinds ((n natp) (tag symbolp) (octets fn-cbor-octet-listp))
                     :keystones (fn-dit-no-such-theorem))
                   :unchecked "definterface's refusal is its claim; the assert-event above names the world check")

(assert-event (fn-di-problem 'fn-dit-f '(:class :common-lisp-compliant
                     :kinds ((n natp) (tag symbolp) (octets fn-cbor-octet-listp))
                     :keystones (fn-dit-unrelated)) (w state)))
(must-fail-checked (definterface fn-dit-f :class :common-lisp-compliant
                     :kinds ((n natp) (tag symbolp) (octets fn-cbor-octet-listp))
                     :keystones (fn-dit-unrelated))
                   :unchecked "definterface's refusal is its claim; the assert-event above names the world check")

(assert-event (fn-di-problem 'fn-dit-g '(:class :program
                     :keystones ((fn-payload-handle-p-is-natp :via fn-payload-handle-p))) (w state)))
(must-fail-checked (definterface fn-dit-g :class :program
                     :keystones ((fn-payload-handle-p-is-natp :via fn-payload-handle-p)))
                   :unchecked "definterface's refusal is its claim; the assert-event above names the world check")

(assert-event (fn-di-problem 'fn-dit-no-such-function '(:class :program) (w state)))
(must-fail-checked (definterface fn-dit-no-such-function :class :program)
                   :unchecked "definterface's refusal is its claim; the assert-event above names the world check")

; ---------------------------------------------------------------------------
; 3. Malformed forms.

; :delegates takes a function name.
(assert-event (equal (fn-di-refusal 'fn-dit-w '(:class :common-lisp-compliant :delegates 3))
                     '(:bad-delegates 3)))
(assert-event (equal (fn-di-refusal 'fn-dit-w '(:class :common-lisp-compliant :delegates nil))
                     '(:bad-delegates nil)))

(assert-event (equal (car (fn-di-refusal 'fn-dit-f '(:class :logic)))
                     :bad-class))
(assert-event (equal (car (fn-di-refusal 'fn-dit-f '(:class :program :root t)))
                     :bad-root))
(assert-event (equal (fn-di-refusal 'fn-dit-f '(:class :program :guard t))
                     '(:unknown-keyword :guard)))
(assert-event (equal (car (fn-di-refusal 'fn-dit-f '(:class :program :exempt ((x "")))))
                     :bad-exempt))
(assert-event (equal (car (fn-di-refusal 'fn-dit-f '(:class :program
                                                     :exempt ((x "a") (x "b")))))
                     :duplicate-exempt))
(assert-event (equal (car (fn-di-refusal 'fn-dit-f '(:class :program :kinds (x))))
                     :bad-kinds))
(assert-event (equal (car (fn-di-refusal 'fn-dit-f '(:class :program
                                                     :keystones ((k :by f)))))
                     :bad-keystones))
(assert-event (equal (car (fn-di-refusal 'fn-dit-f '(:class :program :direct "")))
                     :bad-direct))
(must-fail-checked (definterface fn-dit-f :class :program :root t)
                   :unchecked "definterface's malformed-form refusal is its claim")

; ---------------------------------------------------------------------------
; 4. :raw-with (D40, lane depth-debt-9): raw dispatch of a guard-verified entry
; whose guard carries an invariant over a stobj.  The invariant conjunct
; (fn-dit-positivep fn-dit-st) is what the entry guard never evaluates; the
; named theorems are the bridge (the carried relation concludes it) and the
; per-transition preservation stated over the carried relation.

(defun fn-dit-positivep (fn-dit-st)
  (declare (xargs :stobjs fn-dit-st))
  (< 0 (fn-dit-fld fn-dit-st)))

(defun fn-dit-relationp (fn-dit-st)
  (declare (xargs :stobjs fn-dit-st))
  (and (< 0 (fn-dit-fld fn-dit-st)) (< (fn-dit-fld fn-dit-st) 1000000)))

(defun fn-dit-r (n fn-dit-st)
  (declare (xargs :stobjs fn-dit-st
                  :guard (and (natp n) (fn-dit-positivep fn-dit-st))))
  (update-fn-dit-fld (+ n (fn-dit-fld fn-dit-st)) fn-dit-st))

(defun fn-dit-k (n)
  (declare (xargs :guard (natp n)))
  n)

(defthm fn-dit-relation-positive
  (implies (fn-dit-relationp fn-dit-st)
           (fn-dit-positivep fn-dit-st)))

(defthm fn-dit-r-keeps-relation
  (implies (and (natp n) (< n 1) (fn-dit-relationp fn-dit-st))
           (fn-dit-relationp (fn-dit-r n fn-dit-st))))

(defthm fn-dit-r-keeps-positive
  (implies (and (natp n) (fn-dit-positivep fn-dit-st))
           (fn-dit-positivep (fn-dit-r n fn-dit-st))))

; Accepted: the preservation theorem concludes the actual entry guard over
; this entry on its full guard domain; the bridge also names the relation.
(definterface fn-dit-r
  :class :common-lisp-compliant
  :kinds ((n natp))
  :raw-with (fn-dit-relation-positive fn-dit-r-keeps-positive))

(assert-event
 (equal (cdr (assoc-eq 'fn-dit-r (table-alist 'fn-interfaces (w state))))
        '(:class :common-lisp-compliant :kinds ((n natp))
          :raw-with (fn-dit-relation-positive fn-dit-r-keeps-positive))))

; The invariant conjuncts are the guard's minus the kind checks; their heads
; are the tree's predicates.
(assert-event
 (equal (fn-di-invariant-heads
         (fn-di-invariant-conjuncts
          (fn-di-conjuncts (getpropc 'fn-dit-r 'guard *t* (w state)))
          (getpropc 'fn-dit-r 'formals nil (w state))
          (getpropc 'fn-dit-r 'stobjs-in nil (w state))
          (fn-di-guard-kinds (w state))
          (w state))
         (w state))
        '(fn-dit-positivep)))

; A negative conclusion mentions the predicate but establishes its failure.
(defthm fn-dit-zero-is-not-positive
  (implies (equal (fn-dit-fld fn-dit-st) 0)
           (not (fn-dit-positivep fn-dit-st))))
(assert-event
 (fn-di-problem 'fn-dit-r
  '(:class :common-lisp-compliant :kinds ((n natp))
    :raw-with (fn-dit-zero-is-not-positive fn-dit-r-keeps-relation)) (w state)))
(must-fail-checked
 (definterface fn-dit-r :class :common-lisp-compliant :kinds ((n natp))
  :raw-with (fn-dit-zero-is-not-positive fn-dit-r-keeps-relation))
 :unchecked "a negative conclusion cannot establish the skipped guard")

; Reachable positive witness: establish the entire retained entry domain
; and assert the conclusion after a nontrivial increment.
(defun fn-dit-raw-positive-witness ()
  (declare (xargs :guard t))
  (with-local-stobj fn-dit-st
    (mv-let (answer fn-dit-st)
      (let* ((fn-dit-st (update-fn-dit-fld 1 fn-dit-st))
             (before (and (natp 7) (fn-dit-positivep fn-dit-st)))
             (fn-dit-st (fn-dit-r 7 fn-dit-st)))
        (mv (and before (fn-dit-positivep fn-dit-st)
                 (equal (fn-dit-fld fn-dit-st) 8)) fn-dit-st))
      answer)))
(assert-event (fn-dit-raw-positive-witness))

(defun fn-dit-other-r (fn-dit-st)
  (declare (xargs :stobjs fn-dit-st :guard (fn-dit-positivep fn-dit-st)))
  fn-dit-st)
(defthm fn-dit-other-r-keeps-positive
  (implies (fn-dit-positivep fn-dit-st)
           (fn-dit-positivep (fn-dit-other-r fn-dit-st))))
(assert-event
 (fn-di-problem 'fn-dit-r
  '(:class :common-lisp-compliant :kinds ((n natp))
    :raw-with (fn-dit-relation-positive fn-dit-other-r-keeps-positive)) (w state)))
(must-fail-checked
 (definterface fn-dit-r :class :common-lisp-compliant :kinds ((n natp))
  :raw-with (fn-dit-relation-positive fn-dit-other-r-keeps-positive))
 :unchecked "the preservation theorem is about a different entry")

; Stronger premises do not justify the full entry domain.
(defthm fn-dit-r-keeps-positive-under-extra-bound
  (implies (and (natp n) (< n 1) (fn-dit-positivep fn-dit-st))
           (fn-dit-positivep (fn-dit-r n fn-dit-st))))
(assert-event
 (fn-di-problem 'fn-dit-r
  '(:class :common-lisp-compliant :kinds ((n natp))
    :raw-with (fn-dit-relation-positive fn-dit-r-keeps-positive-under-extra-bound))
  (w state)))
(must-fail-checked
 (definterface fn-dit-r :class :common-lisp-compliant :kinds ((n natp))
  :raw-with (fn-dit-relation-positive fn-dit-r-keeps-positive-under-extra-bound))
 :unchecked "the stronger bound is absent from the actual entry guard")

; An invariant bridge alone says nothing about this entry's transition.
(assert-event
 (fn-di-problem 'fn-dit-r
  '(:class :common-lisp-compliant :kinds ((n natp))
    :raw-with (fn-dit-relation-positive)) (w state)))
(must-fail-checked
 (definterface fn-dit-r :class :common-lisp-compliant :kinds ((n natp))
  :raw-with (fn-dit-relation-positive))
 :unchecked "the bridge lacks the actual entry subject")

; Refused: a theorem that is not in the world.
(assert-event (fn-di-problem 'fn-dit-r '(:class :common-lisp-compliant :kinds ((n natp))
                     :raw-with (fn-dit-relation-positive fn-dit-no-such-theorem)) (w state)))
(must-fail-checked (definterface fn-dit-r :class :common-lisp-compliant :kinds ((n natp))
                     :raw-with (fn-dit-relation-positive fn-dit-no-such-theorem))
                   :unchecked "definterface's refusal is its claim; the assert-event above names the world check")

; Refused: no named theorem concludes the invariant conjunct's head (the
; preservation theorem alone is over the relation, never the guard).
(assert-event (fn-di-problem 'fn-dit-r '(:class :common-lisp-compliant :kinds ((n natp))
                     :raw-with (fn-dit-r-keeps-relation)) (w state)))
(must-fail-checked (definterface fn-dit-r :class :common-lisp-compliant :kinds ((n natp))
                     :raw-with (fn-dit-r-keeps-relation))
                   :unchecked "definterface's refusal is its claim; the assert-event above names the world check")

; Refused: a named theorem about nothing of the guard's argument.
(assert-event (fn-di-problem 'fn-dit-r '(:class :common-lisp-compliant :kinds ((n natp))
                     :raw-with (fn-dit-relation-positive fn-dit-unrelated)) (w state)))
(must-fail-checked (definterface fn-dit-r :class :common-lisp-compliant :kinds ((n natp))
                     :raw-with (fn-dit-relation-positive fn-dit-unrelated))
                   :unchecked "definterface's refusal is its claim; the assert-event above names the world check")

; Refused: a guard conjunct over a host-passed argument ((< n 5) of fn-dit-f)
; -- nothing carried establishes a per-call argument.
(assert-event (fn-di-problem 'fn-dit-f '(:class :common-lisp-compliant
                     :kinds ((n natp) (tag symbolp) (octets fn-cbor-octet-listp))
                     :keystones (fn-dit-f-keeps-n)
                     :raw-with (fn-dit-f-keeps-n)) (w state)))
(must-fail-checked (definterface fn-dit-f :class :common-lisp-compliant
                     :kinds ((n natp) (tag symbolp) (octets fn-cbor-octet-listp))
                     :keystones (fn-dit-f-keeps-n)
                     :raw-with (fn-dit-f-keeps-n))
                   :unchecked "definterface's refusal is its claim; the assert-event above names the world check")

; Refused: a guard of kind checks alone -- raw dispatch would skip nothing.
(assert-event (fn-di-problem 'fn-dit-k '(:class :common-lisp-compliant :kinds ((n natp))
                     :raw-with (fn-dit-r-keeps-positive)) (w state)))
(must-fail-checked (definterface fn-dit-k :class :common-lisp-compliant :kinds ((n natp))
                     :raw-with (fn-dit-r-keeps-positive))
                   :unchecked "definterface's refusal is its claim; the assert-event above names the world check")

; Refused: a :program entry (no guard verification, no faithful raw execution).
(assert-event (fn-di-problem 'fn-dit-g '(:class :program
                     :exempt ((payload "a test: the body passes it on to a guarded entry"))
                     :raw-with (fn-dit-relation-positive)) (w state)))
(must-fail-checked (definterface fn-dit-g :class :program
                     :exempt ((payload "a test: the body passes it on to a guarded entry"))
                     :raw-with (fn-dit-relation-positive))
                   :unchecked "definterface's refusal is its claim; the assert-event above names the world check")

; Malformed: :raw-with takes a non-empty list of names.
(assert-event (equal (car (fn-di-refusal 'fn-dit-r '(:class :common-lisp-compliant :raw-with nil)))
                     :bad-raw-with))
(assert-event (equal (car (fn-di-refusal 'fn-dit-r '(:class :common-lisp-compliant
                                                     :raw-with fn-dit-relation-positive)))
                     :bad-raw-with))
