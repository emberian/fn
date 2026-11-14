; Bind the recursive Lean pilot to live ACL2 logical bodies and admitted measure.
; This is a leaf bridge fixture, not a current served-root coverage claim.
(in-package "ACL2")

(assert-event
 (and
  (equal (getpropc 'member-eq-exec 'formals :missing (w state)) '(x lst))
  (equal (getpropc 'member-eq-exec 'unnormalized-body :missing (w state))
         '(if (endp lst) 'nil
              (if (eq x (car lst)) lst (member-eq-exec x (cdr lst)))))
  (equal (getpropc 'member-eq-exec 'guard :missing (w state))
         '(if (symbolp x) (true-listp lst) (symbol-listp lst)))
  (equal (access justification (getpropc 'member-eq-exec 'justification nil (w state)) :measure)
         '(acl2-count lst))
  (equal (getpropc 'endp 'unnormalized-body :missing (w state)) '(atom x))
  (equal (getpropc 'atom 'unnormalized-body :missing (w state)) '(not (consp x)))
  (equal (getpropc 'not 'unnormalized-body :missing (w state)) '(if p 'nil 't))
  (equal (getpropc 'eq 'unnormalized-body :missing (w state)) '(equal x y))))

(defthm fn2-member-exec-pilot-decreases
 (implies (consp lst) (< (acl2-count (cdr lst)) (acl2-count lst)))
 :rule-classes nil)

(defthm fn2-member-exec-pilot-domain-preserved
 (implies (and (symbolp x) (true-listp lst) (consp lst))
          (and (symbolp x) (true-listp (cdr lst))))
 :rule-classes nil)

(defthm fn2-member-exec-pilot-positive
 (and (symbolp :ok) (true-listp '(:more :ok))
      (equal (member-eq-exec :ok '(:more :ok)) '(:ok)))
 :rule-classes nil)

(defthm fn2-member-exec-pilot-no-decrease-control
 (not (< (acl2-count '(:more :ok)) (acl2-count '(:more :ok))))
 :rule-classes nil)
