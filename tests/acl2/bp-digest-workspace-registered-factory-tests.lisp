; Actual registered source/storage trajectory with deliberately seeded intent.
; No installed allowance or native constructor permission follows.
(in-package "ACL2")
(include-book "bp-controller-checkpoint-payload-directory-tests")
(set-verify-guards-eagerness 0)
(defun bpdfr-fixture-prefix (job fuel)
 (declare (xargs :guard (natp fuel) :measure (nfix fuel)))
 (if (or (zp fuel) (not (eq (fn-bpn-nth 6 job) :emit))) job
  (bpdfr-fixture-prefix (fn-bpn-nth 0 (fn-bpck-emit-step job)) (1- fuel))))

