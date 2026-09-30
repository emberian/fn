; Explicit terminal corollary for the captured controller's scalar result branch.
(in-package "ACL2")
(include-book "post-identity-source-cursor-agent")

(defthm fn-psc-agent-completion-is-done-unfolds
 (implies (fn-psc-agent-statep c incoming)
  (equal (fn-psc-get phase (fn-psc-model-agent-complete c incoming)) :done))
 :hints (("Goal" :do-not-induct t :use fn-psc-agent-result-is-bounded
  :in-theory (union-theories '(fn-psc-agent-resultp fn-psc-result)
                              (theory 'minimal-theory)))))
