; Constraint semantics are tested independently of core/codec machinery.
(in-package "ACL2")
(include-book "../sim/envelope-output")
(defun fn2-envelope-output-resume-check (constraints peer cut)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-envelope-output-state
  (mv-let (ok fn2-envelope-output-state)
   (let* ((fn2-envelope-output-state (fn2-envelope-output-init constraints peer fn2-envelope-output-state))
          (fn2-envelope-output-state (fn2-envelope-output-run cut fn2-envelope-output-state))
          (fn2-envelope-output-state
           (fn2-envelope-output-run (fn2-envelope-output-budget constraints peer) fn2-envelope-output-state)))
    (mv (and (equal (fn2-eo-phase fn2-envelope-output-state) 10)
             (fn2-eo-result fn2-envelope-output-state)) fn2-envelope-output-state)) ok)))
(assert-event
 (and (fn2-envelope-output-matches-p '((:exact 3) (:exact 1 2)) '(1 2 3))
      (not (fn2-envelope-output-matches-p '((:exact 3) (:exact 1 2)) '(1 2)))
      (fn2-envelope-output-matches-p '((:prefix 3 4) (:exact 1 2)) '(1 2))
      (fn2-envelope-output-matches-p '((:prefix 3 4) (:exact 1 2)) '(1 2 3))
      (fn2-envelope-output-matches-p '((:prefix 3 4) (:exact 1 2)) '(1 2 3 4))
      (not (fn2-envelope-output-matches-p '((:prefix 3 4) (:exact 1 2)) '(1 2 4)))
      (not (fn2-envelope-output-matches-p '((:prefix 3 4) (:exact 1 2)) '(1 2 3 4 5)))))
; Both ambiguous cases are necessary: always taking zero or always taking the
; longest uncertain prefix is wrong. The general path evaluates rows instead.
(assert-event
 (and (fn2-envelope-output-matches-p '((:exact 1) (:prefix 1)) '(1))
      (fn2-envelope-output-matches-p '((:exact 1 2) (:prefix 1)) '(1 1 2))
      (fn2-envelope-output-matches-p '((:exact 2) (:prefix 1) (:prefix 1)) '(1 2))
      (not (fn2-envelope-output-matches-p '((:exact 2) (:prefix 1) (:prefix 1)) '(1 3 2)))
      (fn2-envelope-output-resume-check '((:exact 1 2) (:prefix 1)) '(1 1 2) 7)
      (fn2-envelope-output-resume-check '((:prefix 3 4) (:exact 1 2)) '(1 2 3) 3)))
; Malformed observations and constraint storage must fail in every path.
(assert-event
 (and (not (fn2-envelope-output-matches-p '((:exact 1) (:prefix 1)) '(1 . 7)))
      (not (fn2-envelope-output-matches-p '((:exact 1) (:prefix 1)) '(256)))
      (not (fn2-envelope-output-matches-p '((:prefix 1 . 7)) nil))
      (not (fn2-envelope-output-matches-p '((:prefix 1 256)) nil))
      (not (fn2-envelope-output-matches-p '((:bogus 1)) '(1)))
      (not (fn2-envelope-output-matches-p '((:exact 1) . 7) '(1)))
      (not (fn2-envelope-output-matches-p '(7) nil))))
(defun fn2-envelope-output-reinit-check ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-envelope-output-state
  (mv-let (ok fn2-envelope-output-state)
   (let* ((fn2-envelope-output-state
           (fn2-envelope-output-init '((:exact 1 2) (:prefix 1)) '(1 1 2) fn2-envelope-output-state))
          (fn2-envelope-output-state (fn2-envelope-output-run 25 fn2-envelope-output-state))
          (mid-dp (member-equal (fn2-eo-phase fn2-envelope-output-state) '(4 5 6 7 8 9)))
          (fn2-envelope-output-state (fn2-envelope-output-init '((:exact 9)) '(9) fn2-envelope-output-state))
          (fn2-envelope-output-state (fn2-envelope-output-run 100 fn2-envelope-output-state))
          (good (and mid-dp (equal (fn2-eo-phase fn2-envelope-output-state) 10)
                     (fn2-eo-result fn2-envelope-output-state)))
          (fn2-envelope-output-state (fn2-envelope-output-init '((:exact 9)) '(9 . bad) fn2-envelope-output-state))
          (fn2-envelope-output-state (fn2-envelope-output-run 100 fn2-envelope-output-state)))
    (mv (and good (equal (fn2-eo-phase fn2-envelope-output-state) 10)
             (not (fn2-eo-result fn2-envelope-output-state))) fn2-envelope-output-state)) ok)))
(assert-event (fn2-envelope-output-reinit-check))

(defun fn2-envelope-output-spec-controls (cases)
 (declare (xargs :verify-guards nil))
 (if (atom cases) t
  (and (equal (fn2-envelope-output-matches-p (caar cases) (cadar cases))
              (fn2-envelope-output-language-p (reverse (caar cases)) (cadar cases)))
       (fn2-envelope-output-spec-controls (cdr cases)))))
(assert-event
 (fn2-envelope-output-spec-controls
  '((((:exact 1 2)) (1 2)) (((:exact 1 2)) (1))
    (((:exact 1) (:prefix 1)) (1)) (((:exact 1) (:prefix 1)) (1 1))
    (((:exact 1 2) (:prefix 1)) (1 1 2)) (((:exact 1 2) (:prefix 1)) (1 2))
    (((:exact 2) (:prefix 1) (:prefix 1)) (2))
    (((:exact 2) (:prefix 1) (:prefix 1)) (1 2))
    (((:exact 2) (:prefix 1) (:prefix 1)) (1 1 2))
    (((:exact 2) (:prefix 1) (:prefix 1)) (1 3 2)))))
