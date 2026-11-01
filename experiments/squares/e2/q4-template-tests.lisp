; E2 pass 2: the same formula generator rejects count-only correspondence.
; False generated formulas are evaluated, not inferred from a failed proof.
(in-package "ACL2")
(include-book "q4-square")

(defconst *sq-q4-count-contract*
  '(:relation rs-count2-rel :admissible (rs-h-ok rs-h-ok)
    :step (rs-h-step rs-h-step) :recognizer rs-eventp
    :observation (rs-h-count2-obs rs-h-count2-obs)
    :fold (rs-h-fold rs-h-fold)))

(make-event
 (value
  `(progn
     (defun sq-q4-count-generated-step (h s e)
       (declare (xargs :verify-guards nil))
       ,(sq-fs-formula :read *sq-q4-count-contract*))
     (defun sq-q4-count-generated-composition (h s j q)
       (declare (xargs :verify-guards nil))
       ,(sq-fs-formula :composition *sq-q4-count-contract*)))))

; The complete antecedent is true, and each complete generated implication
; is false at the original tooth-1 pair and suffix. Both are evaluated.
(defun sq-q4-template-negative ()
 (declare (xargs :verify-guards nil))
 (and (rs-h-ok *rs-s1*) (rs-h-ok *rs-s2*)
      (rs-count2-rel *rs-s1* *rs-s2*)
      (rs-eventp '(:read 1)) (eq (car '(:read 1)) :read)
      (not (sq-q4-count-generated-step *rs-s1* *rs-s2* '(:read 1)))
      (not (sq-q4-count-generated-composition
            *rs-s1* *rs-s2* *rs-suffix* '(:count 2)))))

(assert-event (sq-q4-template-negative))

; A proof for the strong contract cannot be borrowed by this generated weak
; statement. The refusal is the envelope's translated-formula equality check.
(make-event
 (value
  `(must-fail
    (defsquare sq-q4-count-control
      :template :fold-summary
      :cases-from '(:read)
      :bindings
      (list (cons :read
                  (list :id 'sq-q4-count-control-read :schema :g1
                        :vars (sq-fs-vars :read)
                        :formula (sq-fs-formula :read *sq-q4-count-contract*)
                        :proof '(:proved sq-q4-generated-read)
                        :unused-roles '((:contract :observation) (:contract :fold))
                        :teeth '(:positive sq-q4-positive
                                 :negative sq-q4-negative))))
      :contract ,*sq-q4-count-contract*
      :sides (:left rs-h-step :right rs-h-step)))))

(assert-event
 (and (not (assoc-eq 'sq-q4-count-control-read
                     (table-alist 'sq-squares (w state))))
      (not (assoc-eq 'sq-q4-count-control
                     (table-alist 'sq-coverage (w state))))))

; An existing but unused declared relation is refused even without a proof.
; Keep the generated strong statement and change only its declaration role.
(make-event
 (value
  `(must-fail
    (defsquare sq-q4-role-divergence
      :template :fold-summary :cases-from '(:read)
      :bindings
      (list (cons :read
                  (sq-put :id 'sq-q4-role-divergence-read
                    (sq-put :proof '(:owed)
                      (cdar (sq-q4-bindings '(:read) *sq-q4-contract*))))))
      :contract ,(sq-put :relation 'rs-count2-rel *sq-q4-contract*)
      :sides (:left rs-h-step :right rs-s-step))
    :with-output-off nil)))

(assert-event
 (and (not (assoc-eq 'sq-q4-role-divergence-read
                     (table-alist 'sq-squares (w state))))
      (not (assoc-eq 'sq-q4-role-divergence
                     (table-alist 'sq-coverage (w state))))))
