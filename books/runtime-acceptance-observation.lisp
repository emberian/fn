; Actual read-only admission observation for the production acceptance driver.
; Scalar mode/epoch/activity is diagnostic, never proof of a qualified family.
(in-package "ACL2")
(include-book "runtime-operation-source")
(defun fn-owner-runtime-acceptance-observe (kind fn-page-read-pool state)
 (declare (xargs :stobjs (fn-page-read-pool state) :guard t))
 (mv-let (word family)
  (fn-owner-runtime-operation-source kind fn-page-read-pool state)
  (mv word (fn-prl-nth 6 family)
      (fn-prp-alloc-mode fn-page-read-pool)
      (fn-prp-alloc-epoch fn-page-read-pool)
      (fn-prp-alloc-occupied fn-page-read-pool)
      (fn-prp-alloc-allocated fn-page-read-pool)
      (fn-prp-alloc-active-turns fn-page-read-pool))))
