(in-package "ACL2")
(include-book "../../books/group-number-source-key")
(include-book "../../books/group-number-source-stage")

(defun fn-tgna-assign-run (fuel c)
  (declare (xargs :guard (natp fuel) :measure (nfix fuel)))
  (if (or (zp fuel) (not (fn-gns-assign-cursorp c))
          (member-eq (fn-gns-at 0 c) '(:done :refused))) c
    (fn-tgna-assign-run (1- fuel) (fn-gns-assign-step c))))
(defun fn-tgna-stage-run (fuel c)
  (declare (xargs :guard (natp fuel) :measure (nfix fuel)))
  (if (or (zp fuel) (not (fn-gns-stage-cursorp c))
          (member-eq (fn-gns-at 0 c) '(:done :refused))) c
    (fn-tgna-stage-run (1- fuel) (fn-gns-stage-step c))))
(defun fn-tgna-group-run (fuel c)
  (declare (xargs :guard (natp fuel) :measure (nfix fuel)))
  (if (or (zp fuel) (not (fn-gns-group-cursorp c))
          (member-eq (fn-gns-at 0 c) '(:done :refused))) c
    (fn-tgna-group-run (1- fuel) (fn-gns-group-step c))))
(defun fn-tgna-number-run (fuel c)
  (declare (xargs :guard (natp fuel) :measure (nfix fuel)))
  (if (or (zp fuel) (not (fn-gns-number-cursorp c))
          (member-eq (fn-gns-at 0 c) '(:done :refused))) c
    (fn-tgna-number-run (1- fuel) (fn-gns-number-step c))))
(defconst *tgna-root* (fn-gns-group-set "a" 0 0 (fn-gns-group-value 7 nil) nil))
(defconst *tgna-groups* '("a" "b" "a"))
(defconst *tgna-assigned*
  (fn-tgna-assign-run 100 (fn-gns-assign-begin *tgna-groups* *tgna-root* :held '(19 . 0) 0 :registered-id)))
; Complete antecedents and conclusion of the terminal denotation theorem.
(assert-event
 (and (fn-gns-assign-cursorp *tgna-assigned*)
      (eq (fn-gns-at 0 *tgna-assigned*) :done)
      (equal (fn-gns-at 5 (fn-gns-assign-result *tgna-assigned*))
             (fn-gns-assign-denotation *tgna-assigned*))
      (equal (fn-gns-at 5 *tgna-assigned*) '(("a" . 8) ("b" . 1) ("a" . 8)))
      (equal (fn-gns-at 10 *tgna-assigned*) 9)
      (equal (fn-gns-at 7 *tgna-assigned*) :held)
      (equal (fn-gns-at 8 *tgna-assigned*) '(19 . 0))
      (equal (fn-gns-at 9 *tgna-assigned*) 0)
      (equal (fn-gns-at 11 *tgna-assigned*) :registered-id)))
; Every live action preserves denotation and source authority scalars.
(assert-event
 (let* ((c (fn-gns-assign-begin *tgna-groups* *tgna-root* :held '(19 . 0) 0 :registered-id))
        (n (fn-gns-assign-step c)))
   (and (fn-gns-assign-cursorp c) (not (eq (fn-gns-at 0 c) :refused))
        (or (not (consp (fn-gns-at 1 c))) (stringp (car (fn-gns-at 1 c))))
        (equal (fn-gns-assign-denotation n) (fn-gns-assign-denotation c))
        (equal (fn-gns-at 7 n) (fn-gns-at 7 c))
        (equal (fn-gns-at 8 n) (fn-gns-at 8 c))
        (equal (fn-gns-at 9 n) (fn-gns-at 9 c))
        (equal (fn-gns-at 11 n) (fn-gns-at 11 c))
        (<= (fn-gns-at 10 c) (fn-gns-at 10 n))
        (<= (fn-gns-at 10 n) (+ 2 (fn-gns-at 10 c))))))
(defconst *tgna-staged* (fn-tgna-stage-run 300
  (fn-gns-stage-begin (fn-gns-at 5 *tgna-assigned*) 0 *tgna-root*)))
(assert-event
 (and (fn-gns-stage-cursorp *tgna-staged*) (eq (fn-gns-at 0 *tgna-staged*) :done)
      (equal (fn-gns-at 2 *tgna-staged*)
             (fn-gns-memberships-root (fn-gns-at 5 *tgna-assigned*) 0 *tgna-root*))
      (equal (fn-gns-group-value-high (fn-gns-group-get "a" 0 0 (fn-gns-at 2 *tgna-staged*))) 8)
      (equal (fn-gns-group-value-high (fn-gns-group-get "b" 0 0 (fn-gns-at 2 *tgna-staged*))) 1)
      (equal (fn-gns-group-get "a" 0 0 *tgna-root*) (fn-gns-group-value 7 nil))))
; Selected root and high are projected from one terminal; ordinal zero survives.
(assert-event
 (let* ((c (fn-tgna-group-run 20 (fn-gns-group-begin "a" (fn-gns-at 2 *tgna-staged*))))
        (n (fn-tgna-number-run 10
             (fn-gns-number-begin 8 (fn-gns-at 1 (fn-gns-group-selected-result c)) 1))))
   (and (fn-gns-group-cursorp c) (eq (fn-gns-at 0 c) :done)
        (equal (fn-gns-group-selected-result c)
          (list :number-root (fn-gns-group-value-root
            (fn-gns-group-get (fn-gns-at 1 c) (fn-gns-at 2 c) (fn-gns-at 3 c) (fn-gns-at 4 c)))))
        (equal (fn-gns-group-high-result c) '(:high 8))
        (equal (fn-gns-number-result n) '(:ordinal 0)))))
; Mutation, separately labelled: invalid group refuses before any assignment.
(assert-event
 (let ((c (fn-tgna-assign-run 3 (fn-gns-assign-begin '(7) *tgna-root* :held '(19 . 0) 0 :registered-id))))
   (and (fn-gns-assign-cursorp c) (eq (fn-gns-at 0 c) :refused)
        (equal (fn-gns-at 10 c) 0) (equal (fn-gns-at 2 c) *tgna-root*))))
; Profile-independent number width: a stored high beyond 31 bits is unchanged.
(assert-event
 (let* ((r (fn-gns-group-set "a" 0 0 (fn-gns-group-value 1099511627776 nil) nil))
        (c (fn-tgna-assign-run 40 (fn-gns-assign-begin '("a") r :held '(19 . 0) 0 :registered-id))))
   (and (fn-gns-assign-cursorp c) (eq (fn-gns-at 0 c) :done)
        (equal (fn-gns-at 5 c) '(("a" . 1099511627777))))))
; Hypothesis removal for the terminal theorem: omitted :done, no other premises.
(assert-event
 (let ((c (fn-gns-assign-begin '("a") *tgna-root* :held '(19 . 0) 0 :registered-id)))
   (and (not (eq (fn-gns-at 0 c) :done))
        (not (equal (fn-gns-at 5 (fn-gns-assign-result c))
                     (fn-gns-assign-denotation c))))))
; Hypothesis removal for step refinement: retained cursor invariant holds,
; omitted next-group string condition fails and the conclusion fails.
(assert-event
 (let ((c (fn-gns-assign-begin '(7) nil :held '(19 . 0) 0 :registered-id)))
   (and (fn-gns-assign-cursorp c)
        (not (implies (eq (fn-gns-at 0 c) :next)
               (or (not (consp (fn-gns-at 1 c))) (stringp (car (fn-gns-at 1 c))))))
        (not (equal (fn-gns-assign-denotation (fn-gns-assign-step c))
                     (fn-gns-assign-denotation c))))))
; Corrupted-state hypothesis removal is a logical witness outside execution
; guards. It retains the next-group premise, violates child done-position
; invariant, and affirmatively refutes the one-step denotation conclusion.
(defthm fn-tgna-step-invariant-hypothesis-removal
 (let ((c (list :group '("a") *tgna-root* nil nil nil
                (list :done "a" 0 0 *tgna-root* 0)
                :held '(19 . 0) 0 0 :registered-id)))
   (and (not (fn-gns-assign-cursorp c))
        (implies (eq (fn-gns-at 0 c) :next)
          (or (not (consp (fn-gns-at 1 c))) (stringp (car (fn-gns-at 1 c)))))
        (not (equal (fn-gns-assign-denotation (fn-gns-assign-step c))
                     (fn-gns-assign-denotation c)))))
 :rule-classes nil)
