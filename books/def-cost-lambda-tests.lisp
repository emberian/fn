; Tests for simultaneous lambda substitution, nested/shadowed/MV-LET bindings,
; and one unknown-cost summand per occurrence in both visits and conses bounds.
; Pin collected terms, generated bounds, callee-name sets and closure refusals.
; Concrete natural-valued cost models refute the former substitution and
; multiplicity bugs without attaching the constrained functions.
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

; The same escaped-variable refusal applies to the conses dimension, even
; when the function already has a visits row. This world copy is not installed.
(assert-event
 (mv-let (problem route cost un sizes bound)
   (fn-cost-problem-dimension
    'fn-clt-single '(:conses 0 :cons-unaccounted (fn-clt-leaf))
    (putprop 'fn-clt-single 'unnormalized-body '(fn-clt-leaf escaped) (w state))
    :conses)
   (declare (ignore route cost un sizes bound))
   (equal problem
          (msg "~x0: unaccounted cost terms ~x1 have free variables outside formals ~x2"
               'fn-clt-single
               '((fn-cost-unaccounted-conses 'fn-clt-leaf (list escaped)))
               '(xs)))))

(defmacro fn-clt-terms (fn dimension names expected)
  `(assert-event
    (mv-let (problem route rcost bcost un)
      (fn-cost-derive-dimension ',fn (w state) ,dimension)
      (declare (ignore route rcost))
      (and (null problem)
           (subsetp-eq un ',names) (subsetp-eq ',names un)
           (equal (fn-cost-unaccounted-terms bcost) ',expected)))))

; Separate lambda applications execute the same unknown call twice.
(defun fn-clt-twice (xs)
  (declare (xargs :guard t :verify-guards nil))
  (cons (let ((x (cdr xs))) (fn-clt-leaf x))
        (let ((y (cdr xs))) (fn-clt-leaf y))))
(fn-clt-terms fn-clt-twice :visits (fn-clt-leaf)
  ((fn-cost-unaccounted 'fn-clt-leaf (list (cdr xs)))
   (fn-cost-unaccounted 'fn-clt-leaf (list (cdr xs)))))
(fn-clt-terms fn-clt-twice :conses (fn-clt-leaf)
  ((fn-cost-unaccounted-conses 'fn-clt-leaf (list (cdr xs)))
   (fn-cost-unaccounted-conses 'fn-clt-leaf (list (cdr xs)))))
(def-cost fn-clt-twice :visits 0 :unaccounted (fn-clt-leaf)
  :conses 1 :cons-unaccounted (fn-clt-leaf))
(def-cost-check fn-clt-twice)

; Pin the emitted RHS too: the route/body merge and the teeth row must not
; collapse the two occurrences after the collector has retained them.
(defmacro fn-clt-bound-terms (name expected)
  `(assert-event
    (equal
     (fn-cost-unaccounted-terms
      (caddr (cadr (fn-cost-get :claim
                    (cdr (assoc-eq ',name (table-alist 'fn-teeth-owed (w state))))))))
     ',expected)))
(fn-clt-bound-terms fn-clt-twice-visits-bound
  ((fn-cost-unaccounted 'fn-clt-leaf (list (cdr xs)))
   (fn-cost-unaccounted 'fn-clt-leaf (list (cdr xs)))))
(fn-clt-bound-terms fn-clt-twice-conses-bound
  ((fn-cost-unaccounted-conses 'fn-clt-leaf (list (cdr xs)))
   (fn-cost-unaccounted-conses 'fn-clt-leaf (list (cdr xs)))))

; Identity leaf, XS=(a b), unknown visits/conses cost 1000 at (b).
; Before the bag fix: visits 2000 <= 1000 and conses 2001 <= 1001 are false.
; After: the two RHS summands give equality in each dimension.
(assert-event
 (let* ((u (fn-clt-cost-model 'fn-clt-leaf (list (cdr '(a b)))))
        (visits (+ u u)) (conses (+ 1 u u)))
   (and (equal (list visits u conses (+ 1 u)) '(2000 1000 2001 1001))
        (> visits u) (> conses (+ 1 u))
        (<= visits (+ u u)) (<= conses (+ 1 u u)))))

; Inner X shadows outer X: substitution must compose from the inside out.
(defun fn-clt-shadow (xs)
  (declare (xargs :guard t :verify-guards nil))
  (let ((x (cdr xs)))
    (let ((x (cdr x)))
      (fn-clt-leaf x))))
(fn-clt-terms fn-clt-shadow :visits (fn-clt-leaf)
  ((fn-cost-unaccounted 'fn-clt-leaf (list (cdr (cdr xs))))))
(def-cost fn-clt-shadow :visits 0 :unaccounted (fn-clt-leaf))

; Simultaneous A/B substitution must not rewrite an inserted actual again.
(defun fn-clt-swap (a b)
  (declare (xargs :guard t :verify-guards nil))
  ((lambda (a b) (cons (fn-clt-leaf a) (fn-clt-leaf b))) b a))
(fn-clt-terms fn-clt-swap :visits (fn-clt-leaf)
  ((fn-cost-unaccounted 'fn-clt-leaf (list b))
   (fn-cost-unaccounted 'fn-clt-leaf (list a))))
(def-cost fn-clt-swap :visits 0 :unaccounted (fn-clt-leaf))

; MV-LET binds the complete multiple-value result, then its projections.
(defun fn-clt-values (xs)
  (declare (xargs :guard t))
  (mv xs xs))
(defun fn-clt-mv (xs)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (a b) (fn-clt-values xs)
    (cons (fn-clt-leaf a) (fn-clt-leaf b))))
(fn-clt-terms fn-clt-mv :visits (mv-nth fn-clt-leaf)
  ((fn-cost-unaccounted 'mv-nth (list '0 (fn-clt-values xs)))
   (fn-cost-unaccounted 'mv-nth (list '1 (fn-clt-values xs)))
   (fn-cost-unaccounted 'fn-clt-leaf (list (mv-nth '0 (fn-clt-values xs))))
   (fn-cost-unaccounted 'fn-clt-leaf (list (mv-nth '1 (fn-clt-values xs))))))
(def-cost fn-clt-mv :visits 0 :unaccounted (mv-nth fn-clt-leaf))
(def-cost-check fn-clt-shadow)
(def-cost-check fn-clt-swap)
(def-cost-check fn-clt-mv)

; Exercise route/body concatenation independently: each side contributes U.
; Inspect generated events only; do not install these synthetic cost rows.
(defmacro fn-clt-route-body-bag (dimension)
  `(assert-event
    (let* ((u (list (fn-cost-unknown-name ,dimension) ''fn-clt-leaf '(list xs)))
           (events (fn-cost-events-dimension 'fn-clt-single nil :served
                     (cons u u) '(fn-clt-leaf) nil ''0 (w state) ,dimension))
           (statement (caddr (assoc-eq 'defthm (cdr events)))))
      (equal (fn-cost-unaccounted-terms statement) (list u u)))))
(fn-clt-route-body-bag :visits)
(fn-clt-route-body-bag :conses)

; Both IF arms contribute, even when the terms are identical. Summing them
; over-approximates either chosen branch because unknown costs are natural.
(assert-event
 (let ((u '(fn-cost-unaccounted 'fn-clt-leaf (list xs))))
   (equal (fn-cost-unaccounted-terms (list 'if 'flag u u)) (list u u))))
(assert-event
 (let ((u '(fn-cost-unaccounted-conses 'fn-clt-leaf (list xs))))
   (equal (fn-cost-unaccounted-terms (list 'if 'flag u u)) (list u u))))
