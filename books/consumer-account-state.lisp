; Read-only accessor for the sole owner-maintained account publication.
; The installer/fence/reset owner establishes its carried relation. Absence
; returns nil, never a fabricated empty ready account configuration.
(in-package "ACL2")
(include-book "consumer-account-auth")

(defun fn-owner-account-root-state (state)
  (declare (xargs :stobjs state :guard t))
  (and (boundp-global 'fn-owner-account-root-state state)
       (f-get-global 'fn-owner-account-root-state state)))

(in-theory (disable fn-owner-account-root-state))
