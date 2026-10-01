;;; Preconstructed image baseline; no served constructor or synthetic grant.
(in-package "ACL2")
(defstruct (fnn-runtime-bootstrap
            (:constructor %make-fnn-runtime-bootstrap) (:copier nil))
  pool observation admit phase)
(defvar *fnn-runtime-bootstrap* nil)
(defun fnn-runtime-bootstrap-image-prepare ()
  "Run only while constructing the image, before SAVE-LISP-AND-DIE."
  (when *fnn-runtime-bootstrap*
    (error "runtime bootstrap image preparation repeated"))
  (setq *fnn-runtime-bootstrap*
        (%make-fnn-runtime-bootstrap
         :pool (fnn-live-page-read-pool)
         :observation (make-fnn-runtime-collection)
         :admit (fnn-fixed-raw-callback 'fn-owner-runtime-bootstrap-admit)
         :phase :saved)))
(defun fnn-runtime-bootstrap-entry ()
  "Single-thread entry before crypto, normalization, TLS and logger workers."
  (let ((binding *fnn-runtime-bootstrap*))
    (unless binding
      (fnn-fixed-callback-fail 'fn-owner-runtime-bootstrap-admit
                               :missing-image-baseline nil))
    (unless (eq (fnn-runtime-bootstrap-phase binding) :saved)
      (fnn-fixed-callback-fail 'fn-owner-runtime-bootstrap-admit
                               :bootstrap-already-attempted nil))
    ; Unknown collection/callback outcome cannot be retried on this carrier.
    (setf (fnn-runtime-bootstrap-phase binding) :uncertain)
    ; The live accessor caches its result, so check both it and the actual
    ; registry association. A substituted registry must refuse before sampling.
    (unless (and (eq (fnn-runtime-bootstrap-pool binding)
                     (fnn-live-page-read-pool))
                 (eq (fnn-runtime-bootstrap-pool binding)
                     (cdr (assoc 'fn-page-read-pool
                                 (user-stobj-alist *the-live-state*)))))
      (setf (fnn-runtime-bootstrap-phase binding) :registry-mismatch)
      (return-from fnn-runtime-bootstrap-entry
        (values :runtime-registry-mismatch :fenced)))
    ; No qualified launch capsule/participant acknowledgement is installed yet.
    ; Call the actual negative core boundary before any geometry observation.
    (multiple-value-bind (word outcome pool)
        (fnn-core-mv 'fn-owner-runtime-bootstrap-admit
          (funcall (fnn-runtime-bootstrap-admit binding)
                   :qualification-request nil nil nil
                   (fnn-runtime-bootstrap-pool binding)))
      (setf (fnn-runtime-bootstrap-pool binding) pool
            (fnn-runtime-bootstrap-phase binding) word)
      (values word outcome))))
(defun fnn-runtime-bootstrap-startup ()
  "Earliest saved-image entry; only accepted may return to facility startup."
  (let ((outcome :fenced))
    (handler-case
        (if (and *fnn-runtime-bootstrap*
                 (eq (fnn-runtime-bootstrap-phase *fnn-runtime-bootstrap*)
                     :startup-accepted))
            ; XL-TOPLEVEL and the raw native entry share one process attempt.
            ; Successful reuse still checks the live registry association.
            (when (and (eq (fnn-runtime-bootstrap-pool *fnn-runtime-bootstrap*)
                           (fnn-live-page-read-pool))
                       (eq (fnn-runtime-bootstrap-pool *fnn-runtime-bootstrap*)
                           (cdr (assoc 'fn-page-read-pool
                                       (user-stobj-alist *the-live-state*)))))
              (setq outcome :accepted))
          (multiple-value-bind (word class) (fnn-runtime-bootstrap-entry)
            (declare (ignore word))
            (setq outcome class)
            (when (eq class :accepted)
              (setf (fnn-runtime-bootstrap-phase *fnn-runtime-bootstrap*)
                    :startup-accepted))))
      ; Do not render the condition or enter general startup cleanup.
      (serious-condition () (setq outcome :fenced)))
    (unless (eq outcome :accepted)
      (sb-ext:exit :code (fnn-core 'fn-outcome-code outcome) :abort t))
    :accepted))
(defun fnn-runtime-bootstrap-production-entry ()
  "Consume the earliest accepted process entry exactly once before facilities."
  ; Direct raw entry performs the earliest attempt here. The extracted
  ; trampoline has already performed it; STARTUP validates the SAME registry.
  (fnn-runtime-bootstrap-startup)
  (unless (and *fnn-runtime-bootstrap*
               (eq (fnn-runtime-bootstrap-phase *fnn-runtime-bootstrap*)
                   :startup-accepted))
    (sb-ext:exit :code (fnn-core 'fn-outcome-code :fenced) :abort t))
  (setf (fnn-runtime-bootstrap-phase *fnn-runtime-bootstrap*) :production-entered)
  :accepted)
