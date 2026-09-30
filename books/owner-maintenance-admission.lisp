; The shared retirement fence for new owner maintenance/capture jobs.
(in-package "ACL2")

(defun fn-ort-maintenance-action (retiringp)
  (declare (xargs :guard t))
  (if retiringp :skip :admit))

(in-theory (disable fn-ort-maintenance-action))
