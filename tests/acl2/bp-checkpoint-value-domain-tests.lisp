; Strict full-value domain, actual returned producer positives and removals.
(in-package "ACL2")
(include-book "../../books/bp-checkpoint-value-domain")
(include-book "bp-held-family-source-tests")
(include-book "bp-handoff-symbol-domain-tests")
(defconst *bpcvt-held* (fn-bpn-nth 2 *bphgf-applied*))
(defconst *bpcvt-held-list* (fn-bpn-nth 1 *bphgf-applied*))
(defconst *bpcvt-handoffs* (list *bphsd-produced*))
(defconst *bpcvt-checkpoint* (fn-bpnr-checkpoint 1 *bpcvt-held-list* *bpcvt-handoffs* (cons 0 1) 8 0))
; Both handoff theorem positives affirm the complete actual producer row.
(assert-event (and (consp *bphsd-produced*) (fn-bphs-handoffp *bphsd-produced*) (fn-bpcv-valuep *bphsd-produced*)))
(assert-event (and (fn-bphs-handoffs-p *bpcvt-handoffs*) (fn-bpcv-valuep *bpcvt-handoffs*)))
(assert-event (and (not (fn-bphs-handoffp :unknown-handoff)) (not (fn-bpcv-valuep :unknown-handoff))))
(assert-event (and (not (fn-bphs-handoffs-p '(:unknown-handoff))) (not (fn-bpcv-valuep '(:unknown-handoff)))))
; Actual family result is the complete held-row/list positive.
(assert-event (and (equal (car *bphgf-applied*) :ready) (fn-bphs-held-sourcep *bpcvt-held*) (fn-bphg-held-auxp *bpcvt-held*) (fn-bpcv-valuep *bpcvt-held*)))
(assert-event (and (fn-bphs-held-sourcesp *bpcvt-held-list*) (fn-bphg-held-auxsp *bpcvt-held-list*) (fn-bpcv-valuep *bpcvt-held-list*)))
; Corrupted source principal, retaining the full auxiliary premise.
(defconst *bpcvt-source-corrupt* (bphgft-corrupt-principal *fn-bphsp-held*))
(assert-event (and (not (fn-bphs-held-sourcep *bpcvt-source-corrupt*)) (fn-bphg-held-auxp *bpcvt-source-corrupt*) (not (fn-bpcv-valuep *bpcvt-source-corrupt*))))
(assert-event (and (not (fn-bphs-held-sourcesp (list *bpcvt-source-corrupt*))) (fn-bphg-held-auxsp (list *bpcvt-source-corrupt*)) (not (fn-bpcv-valuep (list *bpcvt-source-corrupt*)))))
; Corrupted auxiliary, retaining the full actual received-source premise.
(defconst *bpcvt-aux-corrupt* (update-nth 5 :unknown-submission *fn-bphsp-held*))
(assert-event (and (fn-bphs-held-sourcep *bpcvt-aux-corrupt*) (not (fn-bphg-held-auxp *bpcvt-aux-corrupt*)) (not (fn-bpcv-valuep *bpcvt-aux-corrupt*))))
(assert-event (and (fn-bphs-held-sourcesp (list *bpcvt-aux-corrupt*)) (not (fn-bphg-held-auxsp (list *bpcvt-aux-corrupt*))) (not (fn-bpcv-valuep (list *bpcvt-aux-corrupt*)))))
; Complete checkpoint antecedent and conclusion over actual producer outputs.
(assert-event (and (fn-bpnr-checkpointp *bpcvt-checkpoint*) (fn-bphs-held-sourcesp (fn-bpnr-checkpoint-held *bpcvt-checkpoint*)) (fn-bphg-held-auxsp (fn-bpnr-checkpoint-held *bpcvt-checkpoint*)) (fn-bphs-handoffs-p (fn-bpnr-checkpoint-handoffs *bpcvt-checkpoint*)) (fn-bpcv-valuep *bpcvt-checkpoint*)))
; Each checkpoint hypothesis is removed with every other one affirmed.
(assert-event (let ((ck (update-nth 0 :foreign-root *bpcvt-checkpoint*))) (and (not (fn-bpnr-checkpointp ck)) (fn-bphs-held-sourcesp (fn-bpnr-checkpoint-held ck)) (fn-bphg-held-auxsp (fn-bpnr-checkpoint-held ck)) (fn-bphs-handoffs-p (fn-bpnr-checkpoint-handoffs ck)) (not (fn-bpcv-valuep ck)))))
(assert-event (let ((ck (fn-bpnr-checkpoint 1 (list *bpcvt-source-corrupt*) *bpcvt-handoffs* nil 8 0))) (and (fn-bpnr-checkpointp ck) (not (fn-bphs-held-sourcesp (fn-bpnr-checkpoint-held ck))) (fn-bphg-held-auxsp (fn-bpnr-checkpoint-held ck)) (fn-bphs-handoffs-p (fn-bpnr-checkpoint-handoffs ck)) (not (fn-bpcv-valuep ck)))))
(assert-event (let ((ck (fn-bpnr-checkpoint 1 (list *bpcvt-aux-corrupt*) *bpcvt-handoffs* nil 8 0))) (and (fn-bpnr-checkpointp ck) (fn-bphs-held-sourcesp (fn-bpnr-checkpoint-held ck)) (not (fn-bphg-held-auxsp (fn-bpnr-checkpoint-held ck))) (fn-bphs-handoffs-p (fn-bpnr-checkpoint-handoffs ck)) (not (fn-bpcv-valuep ck)))))
(assert-event (let ((ck (fn-bpnr-checkpoint 1 *bpcvt-held-list* '(:foreign-handoff) nil 8 0))) (and (fn-bpnr-checkpointp ck) (fn-bphs-held-sourcesp (fn-bpnr-checkpoint-held ck)) (fn-bphg-held-auxsp (fn-bpnr-checkpoint-held ck)) (not (fn-bphs-handoffs-p (fn-bpnr-checkpoint-handoffs ck))) (not (fn-bpcv-valuep ck)))))
; Unsupported codec leaf families cannot belong to the strict typed grammar.
(assert-event (and (not (fn-bpcv-valuep 'acl2::foreign-symbol)) (not (fn-bpcv-valuep 'common-lisp::car)) (not (fn-bpcv-valuep "foreign-string")) (not (fn-bpcv-valuep #\A)) (not (fn-bpcv-valuep -1))))
