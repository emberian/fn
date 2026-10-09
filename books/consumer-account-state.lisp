; Read-only accessor for the sole owner-maintained account publication.
; The installer/fence/reset owner establishes its carried relation. Absence
; returns nil, never a fabricated empty ready account configuration.
(in-package "ACL2")
(include-book "owner-authority-state")
(include-book "consumer-account-availability")

(defun fn-owner-account-root-state (state)
  (declare (xargs :stobjs state :guard t))
  (fn-oauth-get :root (fn-ost-authority state)))

(in-theory (disable fn-owner-account-root-state))
