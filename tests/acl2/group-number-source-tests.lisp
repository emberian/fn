; SCN-1052. Reachable low-level persistent-root fixtures, not publication proof.
(in-package "ACL2")
(include-book "../../books/group-number-source-key")
(include-book "../../books/group-number-source-stage")

(defun fn-tgns-update-run (fuel c)
  (declare (xargs :guard (natp fuel) :measure (nfix fuel)))
  (if (or (zp fuel) (not (fn-gns-update-cursorp c))
          (member-eq (fn-gns-at 0 c) '(:done :refused))) c
    (fn-tgns-update-run (1- fuel) (fn-gns-update-step c))))
(defun fn-tgns-group-run (fuel c)
  (declare (xargs :guard (natp fuel) :measure (nfix fuel)))
  (if (or (zp fuel) (not (fn-gns-group-cursorp c))
          (not (eq (fn-gns-at 0 c) :walking))) c
    (fn-tgns-group-run (1- fuel) (fn-gns-group-step c))))
(defun fn-tgns-number-run (fuel c)
  (declare (xargs :guard (natp fuel) :measure (nfix fuel)))
  (if (or (zp fuel) (not (fn-gns-number-cursorp c))
          (not (eq (fn-gns-at 0 c) :walking))) c
    (fn-tgns-number-run (1- fuel) (fn-gns-number-step c))))
(defconst *tgns-n0* (fn-tgns-update-run 20 (fn-gns-update-begin :number 3 nil '(:ordinal 0))))
(defconst *tgns-n1* (fn-tgns-update-run 100 (fn-gns-update-begin :number 1099511627776
                                                              (fn-gns-at 5 *tgns-n0*) '(:ordinal 1))))
(defconst *tgns-g0* (fn-tgns-update-run 100 (fn-gns-update-begin :group "a" nil (fn-gns-at 5 *tgns-n0*))))
(defconst *tgns-g1* (fn-tgns-update-run 100 (fn-gns-update-begin :group "ab" (fn-gns-at 5 *tgns-g0*)
                                                              (fn-gns-at 5 *tgns-n1*))))
(assert-event (and (fn-gns-update-cursorp *tgns-n0*) (fn-gns-update-cursorp *tgns-n1*)
                   (equal (fn-gns-at 0 *tgns-n1*) :done)
                   (equal (fn-gns-at 8 *tgns-n1*) 41)
                   (equal (fn-gns-at 9 *tgns-n1*) 40)
                   (equal (fn-gns-at 10 *tgns-n1*) 81)))
; No fixed31 ceiling; zero ordinal, holes and captured count fence.
(assert-event
 (and (equal (fn-gns-number-result (fn-tgns-number-run 10 (fn-gns-number-begin 3 (fn-gns-at 5 *tgns-n1*) 2))) '(:ordinal 0))
      (equal (fn-gns-number-result (fn-tgns-number-run 50 (fn-gns-number-begin 1099511627776 (fn-gns-at 5 *tgns-n1*) 2))) '(:ordinal 1))
      (equal (fn-gns-number-result (fn-tgns-number-run 50 (fn-gns-number-begin 1099511627776 (fn-gns-at 5 *tgns-n1*) 1))) '(:missing))
      (equal (fn-gns-number-result (fn-tgns-number-run 10 (fn-gns-number-begin 4 (fn-gns-at 5 *tgns-n1*) 2))) '(:missing))
      (equal (fn-gns-number-result (fn-tgns-number-run 50 (fn-gns-number-begin 1099511627776 (fn-gns-at 5 *tgns-n0*) 2))) '(:missing))))
; Distinct prefix groups and immutable older root.
(assert-event
 (and (equal (fn-gns-group-result (fn-tgns-group-run 20 (fn-gns-group-begin "a" (fn-gns-at 5 *tgns-g1*))))
             (list :number-root (fn-gns-at 5 *tgns-n0*)))
      (equal (fn-gns-group-result (fn-tgns-group-run 20 (fn-gns-group-begin "ab" (fn-gns-at 5 *tgns-g1*))))
             (list :number-root (fn-gns-at 5 *tgns-n1*)))
      (equal (fn-gns-group-result (fn-tgns-group-run 20 (fn-gns-group-begin "ab" (fn-gns-at 5 *tgns-g0*)))) '(:number-root nil))))
; Literal antecedent+conclusion: group and number step lookup keystones.
(assert-event
 (let ((c (fn-gns-group-begin "ab" (fn-gns-at 5 *tgns-g1*))))
   (and (fn-gns-group-cursorp c)
        (equal (fn-gns-group-get (fn-gns-at 1 (fn-gns-group-step c)) (fn-gns-at 2 (fn-gns-group-step c))
                                 (fn-gns-at 3 (fn-gns-group-step c)) (fn-gns-at 4 (fn-gns-group-step c)))
               (fn-gns-group-get (fn-gns-at 1 c) (fn-gns-at 2 c) (fn-gns-at 3 c) (fn-gns-at 4 c))))))
(assert-event
 (let ((c (fn-gns-number-begin 3 (fn-gns-at 5 *tgns-n1*) 2)))
   (and (fn-gns-number-cursorp c)
        (equal (fn-gnix-get (fn-gns-at 1 (fn-gns-number-step c)) (fn-gns-at 2 (fn-gns-number-step c)))
               (fn-gnix-get (fn-gns-at 1 c) (fn-gns-at 2 c))))))
; Literal update-denotation and allocation bound, descent+terminal+rebuild.
(assert-event
 (let* ((c (fn-gns-update-begin :group "a" (fn-gns-at 5 *tgns-g1*) :new))
        (n (fn-gns-update-step c)))
   (and (fn-gns-update-cursorp c) (fn-gns-update-cursorp n)
        (equal (fn-gns-update-denotation n) (fn-gns-update-denotation c))
        (<= (fn-gns-at 8 c) (fn-gns-at 8 n))
        (<= (fn-gns-at 8 n) (1+ (fn-gns-at 8 c)))
        (<= (fn-gns-at 10 n) (+ 2 (fn-gns-at 10 c))))))
(assert-event
 (and (fn-gns-update-cursorp *tgns-n1*) (eq (fn-gns-at 0 *tgns-n1*) :done)
      (not (fn-gns-at 6 *tgns-n1*))
      (equal (fn-gns-at 5 *tgns-n1*) (fn-gns-update-denotation *tgns-n1*))))

; Literal generic-group get/set: same key, distinct key, and prefix key.
(assert-event
 (and (or (stringp "a") (stringp "ab"))
      (equal (fn-gns-group-get "a" 0 0 (fn-gns-group-set "ab" 0 0 :new (fn-gns-at 5 *tgns-g0*)))
             (if (equal "a" "ab") :new (fn-gns-group-get "a" 0 0 (fn-gns-at 5 *tgns-g0*))))
      (or (stringp "ab") (stringp "ab"))
      (equal (fn-gns-group-get "ab" 0 0 (fn-gns-group-set "ab" 0 0 :new (fn-gns-at 5 *tgns-g0*))) :new)))
; Hypothesis-removal: both non-string equal keys. Other premises: none.
(defthm fn-tgns-group-get-of-set-hypothesis-removal
 (and (not (or (stringp 7) (stringp 7)))
      (not (equal (fn-gns-group-get 7 0 0 (fn-gns-group-set 7 0 0 :new nil))
                  (if (equal 7 7) :new (fn-gns-group-get 7 0 0 nil)))))
 :rule-classes nil)
; Literal done result refinements at completed nonempty group/ordinal zero.
(assert-event
 (let ((c (fn-tgns-group-run 20 (fn-gns-group-begin "a" (fn-gns-at 5 *tgns-g0*)))))
   (and (fn-gns-group-cursorp c) (eq (fn-gns-at 0 c) :done)
        (equal (fn-gns-group-result c)
               (list :number-root (fn-gns-group-get (fn-gns-at 1 c) (fn-gns-at 2 c)
                                                    (fn-gns-at 3 c) (fn-gns-at 4 c)))))))
(assert-event
 (let* ((c (fn-tgns-number-run 10 (fn-gns-number-begin 3 (fn-gns-at 5 *tgns-n0*) 1)))
        (v (fn-gnix-get (fn-gns-at 1 c) (fn-gns-at 2 c))))
   (and (fn-gns-number-cursorp c) (eq (fn-gns-at 0 c) :done)
        (true-listp v) (= (len v) 2) (eq (fn-gns-at 0 v) :ordinal)
        (natp (fn-gns-at 1 v)) (< (fn-gns-at 1 v) (fn-gns-at 3 c))
        (equal (fn-gns-number-result c) v))))

(defun fn-tgns-stage-run (fuel c)
  (declare (xargs :guard (natp fuel) :measure (nfix fuel)))
  (if (or (zp fuel) (not (fn-gns-stage-cursorp c))
          (member-eq (fn-gns-at 0 c) '(:done :refused))) c
    (fn-tgns-stage-run (1- fuel) (fn-gns-stage-step c))))
(defconst *tgns-assigned* '(("a" . 3) ("ab" . 1099511627776)))
(defconst *tgns-staged* (fn-tgns-stage-run 300 (fn-gns-stage-begin *tgns-assigned* 0 nil)))
; Literal staged-fold result and one-action semantic/copy refinement.
(assert-event
 (and (fn-gns-stage-cursorp *tgns-staged*) (eq (fn-gns-at 0 *tgns-staged*) :done)
      (equal (fn-gns-at 2 *tgns-staged*) (fn-gns-memberships-root *tgns-assigned* 0 nil))
      (equal (fn-gns-stage-result *tgns-staged*)
             (list :staged (fn-gns-stage-denotation *tgns-staged*) 0
                   (fn-gns-at 7 *tgns-staged*) (fn-gns-at 8 *tgns-staged*)
                   (fn-gns-at 9 *tgns-staged*)))))
(assert-event
 (let* ((c (fn-gns-stage-begin *tgns-assigned* 0 nil)) (next (fn-gns-stage-step c)))
   (and (fn-gns-stage-cursorp c)
        (equal (fn-gns-stage-denotation next) (fn-gns-stage-denotation c))
        (<= (fn-gns-stage-copied-nodes c) (fn-gns-stage-copied-nodes next))
        (<= (fn-gns-stage-copied-nodes next) (1+ (fn-gns-stage-copied-nodes c))))))
(assert-event
 (let ((c (fn-tgns-stage-run 300 (fn-gns-stage-begin '(("a" . 0)) 0 nil))))
   (and (fn-gns-stage-cursorp c) (eq (fn-gns-at 0 c) :refused)
        (equal (fn-gns-at 2 c) nil) (equal (fn-gns-stage-copied-nodes c) 0))))
