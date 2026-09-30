(in-package "ACL2")
(include-book "payload-view-lease")
; The same actual STATE global used by the snapshot lifecycle adapter.
(defun fn-owner-query-payload-ledger (state)
  (declare (xargs :stobjs state))
  (if (f-boundp-global 'fn-owner-payload-view state)
      (f-get-global 'fn-owner-payload-view state)
    (fn-pvl-seed)))
