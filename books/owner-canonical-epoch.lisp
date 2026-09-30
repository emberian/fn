; Read-only process epoch coordinate, independent of canonical size ancestry.
(in-package "ACL2")
(include-book "state-globals")

(defun fn-owner-canonical-epoch (state)
  (declare (xargs :stobjs state :guard t))
  (if (boundp-global 'fn-owner-canonical-epoch state)
      (f-get-global 'fn-owner-canonical-epoch state) 0))

