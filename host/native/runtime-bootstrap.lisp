;;; Preconstructed image baseline; no served constructor or synthetic grant.
(in-package "ACL2")
(defstruct (fnn-runtime-bootstrap
            (:constructor %make-fnn-runtime-bootstrap) (:copier nil))
  pool observation admit phase participants image-policy slots construct source-install fault prs-install profile-envelope)
(defvar *fnn-runtime-bootstrap* nil)
(defun fnn-runtime-bootstrap-live-slots ()
 (or (cdr (assoc 'fn-allocation-turn-slots (user-stobj-alist *the-live-state*)))
     (fnn-fixed-callback-fail 'fn-owner-runtime-ats-construct-internal
                              :missing-image-turn-slots nil)))
(defun fnn-runtime-bootstrap-image-prepare ()
  "Run only while constructing the image, before SAVE-LISP-AND-DIE."
  (when *fnn-runtime-bootstrap*
    (error "runtime bootstrap image preparation repeated"))
  (setq *fnn-runtime-bootstrap*
        (%make-fnn-runtime-bootstrap
         :pool (fnn-live-page-read-pool)
         :observation (make-fnn-runtime-collection)
         :admit (fnn-fixed-raw-callback 'fn-owner-runtime-bootstrap-admit)
         :phase :saved
         :participants cl-user::*fnn-runtime-participants*
         :image-policy cl-user::*fnn-runtime-image-policy*
         :slots (fnn-runtime-bootstrap-live-slots)
         :construct (fnn-fixed-raw-callback 'fn-owner-runtime-ats-construct-internal)
         :source-install (fnn-fixed-raw-callback
                           'fn-owner-runtime-operation-binding-install-internal)
         :fault (fnn-fixed-raw-callback 'fn-owner-runtime-bootstrap-fence-internal)
         :prs-install (fnn-fixed-raw-callback 'fn-owner-recovery-prs-install)
         :profile-envelope *fnn-runtime-profile-envelope-binding*)))
(defun fnn-runtime-bootstrap-installation-failure (binding reason)
 (multiple-value-bind (word pool)
     (fnn-core-mv 'fn-owner-runtime-bootstrap-fence-internal
       (funcall (fnn-runtime-bootstrap-fault binding)
                (fnn-runtime-bootstrap-pool binding)))
  (declare (ignore word))
  (when pool (setf (fnn-runtime-bootstrap-pool binding) pool))
  (values reason :fenced (fnn-runtime-bootstrap-pool binding))))
(defun fnn-runtime-bootstrap-install-turns (binding)
 "Publish source, virgin PRS baseline and actual executor slots while BOOT is closed."
 (let ((returned nil))
  (unwind-protect
   (multiple-value-prog1
    (multiple-value-bind (source-word next-state)
        (fnn-core-mv 'fn-owner-runtime-operation-binding-install-internal
          (funcall (fnn-runtime-bootstrap-source-install binding)
                   (fnn-runtime-bootstrap-pool binding) *the-live-state*))
     (when next-state (setf *the-live-state* next-state))
     (cond
      ((not (and next-state (eq source-word :runtime-operation-binding-installed)))
       (fnn-runtime-bootstrap-installation-failure
         binding :runtime-operation-installation-unavailable))
      (t
       (multiple-value-bind (prs-word next-pool)
           (fnn-core-mv 'fn-owner-recovery-prs-install
             (funcall (fnn-runtime-bootstrap-prs-install binding)
                      (fnn-runtime-bootstrap-pool binding) *the-live-state*))
        (when next-pool (setf (fnn-runtime-bootstrap-pool binding) next-pool))
        (if (not (and next-pool (eq prs-word :recovery-prs-installed)))
            (fnn-runtime-bootstrap-installation-failure
              binding :runtime-recovery-prs-unavailable)
         (multiple-value-bind (word slots)
             (fnn-core-mv 'fn-owner-runtime-ats-construct-internal
               (funcall (fnn-runtime-bootstrap-construct binding)
                        (fnn-runtime-bootstrap-slots binding)
                        (fnn-runtime-bootstrap-pool binding)))
          (when slots (setf (fnn-runtime-bootstrap-slots binding) slots))
          (if (and (eq word :constructed)
                   (eq slots (fnn-runtime-bootstrap-live-slots))
                   (eq (fnn-runtime-bootstrap-pool binding)
                       (fnn-live-page-read-pool)))
              (values :runtime-bootstrap-installed :accepted
                      (fnn-runtime-bootstrap-pool binding))
            (fnn-runtime-bootstrap-installation-failure
              binding :runtime-turn-installation-unavailable))))))))
    (setf returned t))
   (unless returned
    (fnn-runtime-bootstrap-installation-failure
      binding :runtime-turn-installation-uncertain)))))
(defun fnn-runtime-bootstrap-observe-and-install (binding)
 "Only the real qualifier reaches this single locked no-GC initial sample."
 (let ((observation (fnn-runtime-bootstrap-observation binding)) (returned nil))
  (unwind-protect
   (multiple-value-prog1
    (progn
     (setf (fnn-runtime-collection-status observation) :uncertain)
     (fnn-runtime-geometry-into observation)
     (setf (fnn-runtime-collection-status observation) :completed)
     (multiple-value-bind (word outcome pool)
         (fnn-core-mv 'fn-owner-runtime-bootstrap-admit
           (funcall (fnn-runtime-bootstrap-admit binding)
                    (fnn-runtime-collection-status observation)
                    (fnn-runtime-collection-dynamic-pages observation)
                    (fnn-runtime-collection-page-octets observation)
                    (fnn-runtime-collection-dynamic-reservation observation)
                    (fnn-runtime-bootstrap-pool binding)))
      (when pool (setf (fnn-runtime-bootstrap-pool binding) pool))
      (if (eq outcome :accepted)
          (fnn-runtime-bootstrap-install-turns binding)
        (values word outcome pool))))
    (setf returned t))
   (unless returned
    (fnn-runtime-bootstrap-installation-failure
      binding :runtime-bootstrap-observation-uncertain)))))
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
                                 (user-stobj-alist *the-live-state*))))
                 (eq (fnn-runtime-bootstrap-slots binding)
                     (fnn-runtime-bootstrap-live-slots)))
      (setf (fnn-runtime-bootstrap-phase binding) :registry-mismatch)
      (return-from fnn-runtime-bootstrap-entry
        (values :runtime-registry-mismatch :fenced)))
    ; Actual saved policy identity and parked acknowledgement precede the core
    ; qualification boundary. Neither observation grants allocation authority.
    (multiple-value-bind (word outcome pool)
        (cl-user::fnn-with-runtime-participants-bootstrap
          ((fnn-runtime-bootstrap-participants binding)
           (fnn-runtime-bootstrap-pool binding))
          (multiple-value-bind (policy-word policy)
              (cl-user::fnn-runtime-image-policy-bootstrap-status
                (fnn-runtime-bootstrap-pool binding)
                (fnn-runtime-bootstrap-participants binding))
            (if (and (eq policy-word :image-policy-closed)
                     policy
                     (eq policy (fnn-runtime-bootstrap-image-policy binding)))
                (multiple-value-bind (profile-word profile-binding)
                    (fnn-runtime-profile-envelope-live-binding
                      (fnn-runtime-bootstrap-pool binding) policy)
                  (if (and (eq profile-word :profile-envelope-available)
                           profile-binding
                           (eq profile-binding
                               (fnn-runtime-bootstrap-profile-envelope binding)))
                (multiple-value-bind (admit-word admit-outcome admit-pool)
                    (fnn-core-mv 'fn-owner-runtime-bootstrap-admit
                      (funcall (fnn-runtime-bootstrap-admit binding)
                               :qualification-request nil nil nil
                               (fnn-runtime-bootstrap-pool binding)))
                  (when admit-pool
                    (setf (fnn-runtime-bootstrap-pool binding) admit-pool))
                  (cond ((eq admit-outcome :qualified)
                         (fnn-runtime-bootstrap-observe-and-install binding))
                        ((eq admit-outcome :accepted)
                         (fnn-runtime-bootstrap-installation-failure
                           binding :runtime-bootstrap-qualification-protocol))
                        (t (values admit-word admit-outcome admit-pool))))
                    (values :runtime-profile-envelope-unavailable :fenced)))
              (values :runtime-image-policy-unavailable :fenced))))
      ; A participant refusal returns no pool MV: retain the SAME original.
      (when pool (setf (fnn-runtime-bootstrap-pool binding) pool))
      (setf (fnn-runtime-bootstrap-phase binding) word)
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
