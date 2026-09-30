(in-package "ACL2")
(include-book "../../books/bp-handoff-symbol-domain")
(include-book "bp-handoff-producer-shape-tests")

; The complete positive is the actual delivery producer's returned handoff.
(defconst *bphsd-produced*
 (mv-let (ok held handoff)
  (fn-bpah-apply-delivery *fn-bphsp-record* (list *fn-bphsp-held*))
  (declare (ignore ok held)) handoff))
(assert-event (and (consp *bphsd-produced*)
 (fn-bphs-handoffp *bphsd-produced*)
 (fn-bphs-symbol-domain-p *bphsd-produced*)))
(assert-event (and (fn-bphs-handoffs-p (list *bphsd-produced*))
 (fn-bphs-symbol-domain-p (list *bphsd-produced*))))
; Corrupted data removes the only antecedent and falsifies the conclusion.
(assert-event (and (not (fn-bphs-handoffp :unknown-checkpoint-symbol))
 (not (fn-bphs-symbol-domain-p :unknown-checkpoint-symbol))))
(assert-event (and (not (fn-bphs-handoffs-p '(:unknown-checkpoint-symbol)))
 (not (fn-bphs-symbol-domain-p '(:unknown-checkpoint-symbol)))))
