; Read only the sole metadata4 installed by actual authority publication.
; The owner producer maintains CP7 correspondence; this accessor establishes
; neither that relation nor canonical funding/readiness. Absence is unavailable.
(in-package "ACL2")
(include-book "owner-authority-state")

(defun fn-owner-account-carries-read (state)
  (declare (xargs :stobjs state :guard t))
  (fn-oauth-get :carries (fn-ost-authority state)))

(in-theory (disable fn-owner-account-carries-read))
