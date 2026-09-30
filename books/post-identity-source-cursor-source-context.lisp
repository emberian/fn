; Unchanged proof-only virtual-source context and incoming agent span abstraction.
(in-package "ACL2")
(include-book "post-identity-source-cursor-refinement")

(defun fn-psc-source-contextp (c incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (and (true-listp c) (equal (len c) 24) (stringp (fn-psc-get msgid c))
      (member-eq (fn-psc-get mode c) '(:source-incoming :source-held))
      (true-listp incoming) (true-listp (fn-psc-model-source c incoming held))
      (equal (fn-psc-get n c) (len (fn-psc-model-source c incoming held)))
      (natp (fn-psc-get agent-start c)) (natp (fn-psc-get agent-end c))
      (<= (fn-psc-get agent-start c) (fn-psc-get agent-end c))
      (<= (fn-psc-get agent-end c) (len incoming))))

(defun fn-psc-model-retained-agent (c incoming)
 (declare (xargs :guard t :verify-guards nil))
 (fn-inj-take (- (fn-psc-get agent-end c) (fn-psc-get agent-start c))
             (nthcdr (fn-psc-get agent-start c) incoming)))

(in-theory (disable fn-psc-source-contextp fn-psc-model-retained-agent))
