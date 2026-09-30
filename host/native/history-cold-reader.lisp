;;; Actual cold-codec/authenticated-page adapter. The child controller is
;;; frozen by its owner while this core mapping waits; no host offset/serial.
(in-package "ACL2")

(defun fnn-hsr-cold-begin (handle source resource)
  (fnn-core 'fn-ocb-begin handle source resource))

(defun fnn-hsr-cold-step (service root maintenance reader mapping
                         current-source current-child)
  "One actual reader action for the authoritative current child demand.
Return verdict and the next outer mapping. :SUPPLY carries the core-selected
pool position and observed scalar byte; the child owner performs supply."
  (let ((cursor mapping))
    (when (eq (fnn-core 'fn-omk-at 0 cursor) :idle)
      (destructuring-bind (word next)
          (fnn-call 'fn-ocb-request cursor current-child)
        (setq cursor next)
        (unless (eq word :waiting)
          (return-from fnn-hsr-cold-step (values word cursor)))))
    (let ((demand (fnn-core 'fn-ocb-demand cursor)))
      (unless (and (consp demand) (eq (first demand) :need-byte))
        (return-from fnn-hsr-cold-step (values demand cursor)))
      (multiple-value-bind (answer observation)
          (fnn-hsr-source-step service root maintenance reader current-source demand)
        (if (eq answer :ready)
            (destructuring-bind (word next)
                (fnn-call 'fn-ocb-complete cursor current-source current-child observation)
              (values word next))
          (values answer cursor))))))
