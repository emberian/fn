; Startup funding depends on launcher/profile books; ordinary lease adapters do not.
(in-package "ACL2")
(include-book "../books/cold-read-bootstrap")
(include-book "page-read-host")

; Install exactly the plan whose constructor capacities the native startup
; will consume. Additional live row/output bookkeeping remains supplied by
; the joined representation contract; it is not inferred from these maps.
(defun fn-owner-page-read-bootstrap (policy profile runtime bookkeeping fd-bookkeeping fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (let ((plan (fn-crb-start-plan policy profile runtime)))
    (if (not (equal (fn-crv-nth 0 plan) :admitted))
        (mv (fn-crv-nth 1 plan) nil fn-page-read-pool)
      (mv-let (word fn-page-read-pool)
        (fn-owner-page-read-install-baseline
         (fn-crv-nth 1 plan) (fn-crv-nth 2 plan) bookkeeping fd-bookkeeping
         (fn-crv-nth 4 policy) fn-page-read-pool)
        (mv word (and (equal word :installed) plan) fn-page-read-pool)))))

