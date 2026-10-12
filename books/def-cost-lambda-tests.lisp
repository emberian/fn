; Lambda-bound unknown costs must be closed over the entry's formals.
; These zero-accounted bounds were false before the collector substituted
; lambda actuals.  The nested case also charges an unknown call in an actual.
(in-package "ACL2")
(include-book "def-cost")

(encapsulate
  (((fn-clt-leaf *) => *))
  (local (defun fn-clt-leaf (x) x)))

(defun fn-clt-single (xs)
  (declare (xargs :guard t :verify-guards nil))
  (let ((tail (cdr xs)))
    (fn-clt-leaf tail)))

(defun fn-clt-nested (xs)
  (declare (xargs :guard t :verify-guards nil))
  (let ((tail (cdr xs)))
    (let ((value (fn-clt-leaf tail)))
      (fn-clt-leaf value))))

; Exercise the refusal through the real declaration validator using a
; malformed body in a COPY of the world; never install that body in ACL2.
(assert-event
 (mv-let (problem route cost un sizes bound)
   (fn-cost-problem
    'fn-clt-single '(:visits 0 :unaccounted (fn-clt-leaf))
    (putprop 'fn-clt-single 'unnormalized-body '(fn-clt-leaf escaped) (w state)))
   (declare (ignore route cost un sizes bound))
   (equal problem
          (msg "~x0: unaccounted cost terms ~x1 have free variables outside formals ~x2"
               'fn-clt-single
               '((fn-cost-unaccounted 'fn-clt-leaf (list escaped)))
               '(xs)))))

; Pin the collected terms and the callee names independently: substituting
; the bound arguments must not alter the :unaccounted name equality check.
(assert-event
 (mv-let (problem route rcost bcost un)
   (fn-cost-derive 'fn-clt-single (w state))
   (declare (ignore route rcost))
   (and (null problem) (equal un '(fn-clt-leaf))
        (consp (car bcost))
        (equal (fn-cost-unaccounted-terms bcost)
               '((fn-cost-unaccounted 'fn-clt-leaf (list (cdr xs))))))))

(assert-event
 (mv-let (problem route rcost bcost un)
   (fn-cost-derive 'fn-clt-nested (w state))
   (declare (ignore route rcost))
   (and (null problem) (equal un '(fn-clt-leaf))
        (consp (car bcost))
        (equal (fn-cost-unaccounted-terms bcost)
               '((fn-cost-unaccounted 'fn-clt-leaf (list (cdr xs)))
                 (fn-cost-unaccounted 'fn-clt-leaf
                                      (list (fn-clt-leaf (cdr xs)))))))))

(def-cost fn-clt-single :visits 0 :unaccounted (fn-clt-leaf))
(def-cost fn-clt-nested :visits 0 :unaccounted (fn-clt-leaf))

(assert-event
 (and (equal (all-vars (getpropc 'fn-clt-single-visits-bound 'theorem nil (w state)))
             '(xs))
      (equal (all-vars (getpropc 'fn-clt-nested-visits-bound 'theorem nil (w state)))
             '(xs))))
(def-cost-check fn-clt-single)
(def-cost-check fn-clt-nested)

; Countermodels of the OLD generated theorems, not attachments. Interpret
; the unconstrained leaf as the identity, as its encapsulate witness does.
; Interpret its unknown cost as 1000 only at the argument (b), zero elsewhere.
; This satisfies the sole constraint on fn-cost-unaccounted: natural-valued.
(local
 (defun fn-clt-cost-model (f args)
   (if (and (equal f 'fn-clt-leaf) (equal args '((b)))) 1000 0)))
(local
 (defthm fn-clt-cost-model-natp
   (natp (fn-clt-cost-model f args))
   :rule-classes :type-prescription))

; XS=(a b), free TAIL=NIL: old LHS=1000 > RHS=0; fixed RHS=1000.
(assert-event
 (let* ((xs '(a b)) (tail nil)
        (actual-tail (cdr xs))
        (lhs (fn-clt-cost-model 'fn-clt-leaf (list actual-tail)))
        (old-rhs (fn-clt-cost-model 'fn-clt-leaf (list tail)))
        (new-rhs (fn-clt-cost-model 'fn-clt-leaf (list (cdr xs)))))
   (and (equal (list lhs old-rhs new-rhs) '(1000 0 1000))
        (> lhs old-rhs) (<= lhs new-rhs))))

; XS=(a b), free TAIL=VALUE=NIL, identity leaf: two calls at (b).
; Old LHS=2000 > RHS=0; fixed RHS=2000 includes the actual's own call.
(assert-event
 (let* ((xs '(a b)) (tail nil) (value nil)
        (actual-tail (cdr xs)) (actual-value actual-tail)
        (lhs (+ (fn-clt-cost-model 'fn-clt-leaf (list actual-tail))
                (fn-clt-cost-model 'fn-clt-leaf (list actual-value))))
        (old-rhs (+ (fn-clt-cost-model 'fn-clt-leaf (list tail))
                    (fn-clt-cost-model 'fn-clt-leaf (list value))))
        (new-rhs (+ (fn-clt-cost-model 'fn-clt-leaf (list (cdr xs)))
                    (fn-clt-cost-model 'fn-clt-leaf (list (cdr xs))))))
   (and (equal (list lhs old-rhs new-rhs) '(2000 0 2000))
        (> lhs old-rhs) (<= lhs new-rhs))))
