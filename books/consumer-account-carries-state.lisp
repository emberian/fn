; Read only the sole metadata4 installed by actual authority publication.
; The owner producer maintains CP7 correspondence; this accessor establishes
; neither that relation nor canonical funding/readiness. Absence is unavailable.
(in-package "ACL2")

(defun fn-owner-account-carries-read (state)
  (declare (xargs :stobjs state :guard t))
  (and (boundp-global 'fn-owner-account-carries state)
       (f-get-global 'fn-owner-account-carries state)))

(in-theory (disable fn-owner-account-carries-read))
