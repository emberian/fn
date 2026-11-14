; Canonical/domain composition fixture. This does not claim served-root coverage.
(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)

(defun fn2-tv-bump (x)
  (declare (xargs :guard (integerp x)))
  (+ x 1))

(defthm fn2-tv-bump-preserves-integer-domain
  (implies (integerp x) (integerp (fn2-tv-bump x))))

(defun fn2-tv-twice-bump (x)
  (declare (xargs :guard (integerp x)))
  (let ((y (fn2-tv-bump x)))
    (fn2-tv-bump y)))

; These are the exact canonical bodies/guards decoded by the Lean fixture,
; checked against the admitted functions rather than an emitter's summary.
(assert-event
 (and (equal (getpropc 'fn2-tv-bump 'unnormalized-body :missing (w state))
             '(binary-+ x '1))
      (equal (getpropc 'fn2-tv-twice-bump 'unnormalized-body :missing (w state))
             '((lambda (y) (fn2-tv-bump y)) (fn2-tv-bump x)))
      (equal (getpropc 'fn2-tv-bump 'guard :missing (w state)) '(integerp x))
      (equal (getpropc 'fn2-tv-twice-bump 'guard :missing (w state)) '(integerp x))))

(defevaluator fn2-tv-domain-eval fn2-tv-domain-eval-list
  ((binary-+ x y) (fn2-tv-bump x)))

(defthm fn2-tv-bump-canonical-body
  (equal (fn2-tv-domain-eval '(binary-+ x '1) (list (cons 'x x)))
         (fn2-tv-bump x)))

(defthm fn2-tv-twice-bump-canonical-body
  (equal (fn2-tv-domain-eval '((lambda (y) (fn2-tv-bump y)) (fn2-tv-bump x))
                            (list (cons 'x x)))
         (fn2-tv-twice-bump x)))

(defthm fn2-tv-composed-domain-and-result
  (implies (integerp x)
           (and (integerp (fn2-tv-bump x))
                (integerp (fn2-tv-twice-bump x))
                (equal (fn2-tv-twice-bump x) (+ (+ x 1) 1)))))

(defthm fn2-tv-domain-positive
  (and (integerp 4)
       (integerp (fn2-tv-bump 4))
       (equal (fn2-tv-bump 4) 5)
       (integerp (fn2-tv-twice-bump 4))
       (equal (fn2-tv-twice-bump 4) 6))
  :rule-classes nil)

; Concrete counterexamples, not a failed proof search, support these controls.
(defthm fn2-tv-domain-and-callee-controls
  (and (not (integerp nil))
       (not (equal 4 (fn2-tv-bump 4))))
  :rule-classes nil)

(must-fail (defthm fn2-tv-false-domain (integerp nil) :rule-classes nil))
(must-fail (defthm fn2-tv-false-callee (equal 4 (fn2-tv-bump 4)) :rule-classes nil))

; The integer-only primitive model has an actual hypothesis-removal witness:
; logical ACL2 addition completes NIL to zero, but this admitted model refuses it.
(defun fn2-tv-integer-add-model (x y)
  (declare (xargs :guard t))
  (if (and (integerp x) (integerp y)) (+ x y) :unsupported))

(defthm fn2-tv-add-guarded-correspondence
  (implies (and (integerp x) (integerp y))
           (equal (fn2-tv-integer-add-model x y) (+ x y))))

(defthm fn2-tv-add-domain-removal-control
  (and (equal (fn2-tv-integer-add-model nil 1) :unsupported)
       (equal (fn2-tv-bump nil) 1)
       (not (equal (fn2-tv-integer-add-model nil 1) (fn2-tv-bump nil))))
  :rule-classes nil)
