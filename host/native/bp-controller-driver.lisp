;;; Token-only native BP foundation consumer. Not included/activated until the
;;; physical owner installs the guarded registry dispatcher and canonical pool
;;; envelope. No diagnostic fnn-call or native CURRENT fallback.
(in-package "ACL2")

(defun fnn-bps-registered-foundation-step (controller event fuel)
  "The core installs CURRENT before exposing effects; caller executes I/O
only after this function has released the shared registry/pool mutex."
  (multiple-value-bind (status effects remaining registry)
      (sb-thread:with-mutex (*fnn-extent-lock*)
        (fnn-core-bp-controller-values fn-owner-bp-controller-step
                                       controller event fuel))
    (declare (ignore registry))
    (values status effects remaining)))
