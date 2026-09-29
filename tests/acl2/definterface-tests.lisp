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
