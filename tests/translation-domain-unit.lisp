; Canonical/domain composition fixture. This does not claim served-root coverage.
(in-package "ACL2")
(include-book "../books/translation-validation")
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
 (and (equal (fn2-tv-property 'fn2-tv-bump 'unnormalized-body (w state))
             '(binary-+ x '1))
      (equal (fn2-tv-property 'fn2-tv-twice-bump 'unnormalized-body (w state))
             '((lambda (y) (fn2-tv-bump y)) (fn2-tv-bump x)))
      (equal (fn2-tv-property 'fn2-tv-bump 'guard (w state)) '(integerp x))
      (equal (fn2-tv-property 'fn2-tv-twice-bump 'guard (w state)) '(integerp x))))

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
       (equal (fn2-tv-twice-bump 4) 6)))

; Concrete counterexamples, not a failed proof search, support these controls.
(defthm fn2-tv-domain-and-callee-controls
  (and (not (integerp nil))
       (not (equal 4 (fn2-tv-bump 4)))))

(must-fail (defthm fn2-tv-false-domain (integerp nil)))
(must-fail (defthm fn2-tv-false-callee (equal 4 (fn2-tv-bump 4))))
