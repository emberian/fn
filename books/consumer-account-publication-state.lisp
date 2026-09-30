; Sole unchanged read-only accessor, factored from consumer-account-state.
; Installer/fence/reset establishes the carried relation; absence is NIL.
(in-package "ACL2")
(defun fn-owner-account-root-state (state)
  (declare (xargs :stobjs state :guard t))
  (and (boundp-global 'fn-owner-account-root-state state)
       (f-get-global 'fn-owner-account-root-state state)))
(in-theory (disable fn-owner-account-root-state))
