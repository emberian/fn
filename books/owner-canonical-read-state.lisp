(in-package "ACL2")
(include-book "state-globals")

(defun fn-owner-canonical-state (state)
  (declare (xargs :stobjs state :guard t))
  (and (boundp-global 'fn-owner-canonical-state state)
       (f-get-global 'fn-owner-canonical-state state)))
