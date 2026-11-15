(in-package "ACL2")
(include-book "machines-b")
(include-book "checkpoint-bank-closure-kind")
(include-book "checkpoint-bank-protection")
(fn2-book-layer :b)
(defcorechild fn2-core-checkpoint-bank-protection fn2-checkpoint-bank-protection
 :init (fn2-checkpoint-bank-protection-init (if (fn2-profile-get :image-boot profile) 1 0) fn2-checkpoint-bank-protection)
 :why "Actual bounded restoration cursor for all four independently retained anchor closures; no evidence-only completion flag.")
(defcost fn2-checkpoint-bank-protection-op :child fn2-checkpoint-bank-protection-step :answers t
 :tables (fn2-core-checkpoint-selected-source fn2-core-boot-config fn2-core-checkpoints fn2-core-checkpoint-refs fn2-core-checkpoint-bytes fn2-core-origin fn2-core-checkpoint-recovery-evidence fn2-core-checkpoint-recovery-census fn2-core-checkpoint-restore-map fn2-core-checkpoint-restore-map-control fn2-core-checkpoint-restore-reach-control fn2-core-checkpoint-projection fn2-core-ops fn2-core-extents fn2-core-checkpoint-publication fn2-core-checkpoint-bank-closures fn2-core-checkpoint-bank-protection fn2-core-alloc-edges)
 :doc "Restore one exact retained physical anchor reach claim under the selected recovery freeze; identity conflicts retain closure and refuse.")
