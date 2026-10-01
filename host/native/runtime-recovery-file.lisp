;;; One early, pre-service scheduling quantum. No controller/target creator,
;;; supplied ticket, budget or decoded-ready result is accepted here.
(in-package "ACL2")

(defun fnn-recovery-profile-retain-effects (bootstrap slots pool)
  (when slots (setf (fnn-runtime-bootstrap-slots bootstrap) slots))
  (when pool (setf (fnn-runtime-bootstrap-pool bootstrap) pool))
  (unless (and slots pool)
    (fnn-runtime-bootstrap-installation-failure bootstrap :recovery-missing-effects)))

(defun fnn-recovery-profile-quantum (bootstrap binding fuel)
  "Core chooses one effect and its exact target span. Keep actual FD rooted."
  (let ((controller (fnn-runtime-profile-envelope-binding-controller binding)))
    (multiple-value-bind (word effect left next-controller pool slots)
        (fnn-core-mv 'fn-owner-page-file-open-step
          (funcall (fnn-fixed-raw-callback 'fn-owner-page-file-open-step)
                   fuel controller (fnn-runtime-profile-envelope-binding-buffer binding)
                   (fnn-runtime-bootstrap-pool bootstrap)
                   (fnn-runtime-bootstrap-slots bootstrap) *the-live-state*))
      (setf controller next-controller)
      (fnn-recovery-profile-retain-effects bootstrap slots pool)
      (unless (eq controller (fnn-runtime-profile-envelope-binding-controller binding))
        (return-from fnn-recovery-profile-quantum
          (fnn-runtime-bootstrap-installation-failure bootstrap :recovery-controller-replaced)))
      (if (member word '(:file-open :file-read :file-close))
          (multiple-value-bind (io-word count retained-fd)
              (fnn-recovery-profile-perform effect binding)
            (declare (ignore retained-fd)) ; Already stored INSIDE primitive.
            (multiple-value-bind (observed next-controller)
                (fnn-core-mv 'fn-owner-page-file-open-observe
                  (funcall (fnn-fixed-raw-callback 'fn-owner-page-file-open-observe)
                           (second effect) (third effect) (fourth effect) io-word count
                           controller pool slots))
              (setf controller next-controller)
              (unless (eq controller (fnn-runtime-profile-envelope-binding-controller binding))
                (return-from fnn-recovery-profile-quantum
                  (fnn-runtime-bootstrap-installation-failure bootstrap :recovery-observe-replaced)))
              (cond
                ((eq observed :file-observation-uncertain)
                 (fnn-runtime-bootstrap-installation-failure bootstrap observed))
                ((eq observed :file-closed-retained)
                 ; Drop the temporary native effect. The controller/decoded
                 ; result/source/claim remain rooted and charged: no PRS return.
                 (setf effect nil)
                 (multiple-value-bind (finished next-slots next-pool)
                     (fnn-core-mv 'fn-ats-finish-owned
                       (funcall (fnn-runtime-bootstrap-recovery-turn-finish bootstrap)
                         (fnn-core 'fn-pfo-slot controller)
                         (fnn-core 'fn-pfo-turn controller) slots pool))
                   (fnn-recovery-profile-retain-effects bootstrap next-slots next-pool)
                   (if (eq finished :left)
                       (values observed (fnn-core 'fn-pfo-result controller) left)
                     (fnn-runtime-bootstrap-installation-failure bootstrap finished))))
                (t (values observed nil left)))))
        ; A profile result is a held intermediate result, never acceptance.
        (values word nil left)))))

(defun fnn-recovery-profile-start (path)
  "Start only from the actual completed image bootstrap and saved binding.
Source refusal does not create a controller, copy bytes or perform file I/O."
  (let ((bootstrap *fnn-runtime-bootstrap*))
    (unless (and bootstrap (eq (fnn-runtime-bootstrap-phase bootstrap) :accepted))
      (return-from fnn-recovery-profile-start (values :recovery-bootstrap-unavailable nil)))
    (sb-thread:with-recursive-lock (*fnn-extent-lock*)
      (multiple-value-bind (binding-word binding)
          (fnn-runtime-profile-envelope-live-binding
           (fnn-runtime-bootstrap-pool bootstrap) (fnn-runtime-bootstrap-image-policy bootstrap))
        (unless (and (eq binding-word :profile-envelope-available)
                     (eq binding (fnn-runtime-bootstrap-profile-envelope bootstrap)))
          (return-from fnn-recovery-profile-start
            (values :recovery-image-binding-unavailable nil)))
        (multiple-value-bind (word slot nonce slots pool)
            (fnn-core-mv 'fn-owner-recovery-file-turn-begin
              (funcall (fnn-runtime-bootstrap-recovery-turn-begin bootstrap)
                       path (fnn-runtime-bootstrap-slots bootstrap)
                       (fnn-runtime-bootstrap-pool bootstrap) *the-live-state*))
          (fnn-recovery-profile-retain-effects bootstrap slots pool)
          (unless (eq word :prepaid)
            ; Before-slot unavailable is definite. Other unfinished entry
            ; outcomes retain/fence; closeout does not invent a cleanup join.
            (return-from fnn-recovery-profile-start
              (if (eq word :recovery-operation-unavailable) (values word nil)
                (fnn-runtime-bootstrap-installation-failure bootstrap word))))
          (multiple-value-bind (begun controller next-slots)
              (fnn-core-mv 'fn-owner-page-file-open-begin
                (funcall (fnn-fixed-raw-callback 'fn-owner-page-file-open-begin)
                         path slot nonce (fnn-runtime-profile-envelope-binding-controller binding)
                         (fnn-runtime-profile-envelope-binding-buffer binding) pool slots *the-live-state*))
            (when next-slots (setf (fnn-runtime-bootstrap-slots bootstrap) next-slots))
            (unless (and next-slots (eq begun :recovery-file-ready)
                         (eq controller (fnn-runtime-profile-envelope-binding-controller binding)))
              (return-from fnn-recovery-profile-start
                (fnn-runtime-bootstrap-installation-failure bootstrap begun)))
            (fnn-recovery-profile-quantum bootstrap binding 1)))))))

(defun fnn-recovery-profile-next ()
  "Resume the actual retained controller; do not enter a second ATS ticket."
  (let ((bootstrap *fnn-runtime-bootstrap*))
    (unless (and bootstrap (eq (fnn-runtime-bootstrap-phase bootstrap) :accepted))
      (return-from fnn-recovery-profile-next (values :recovery-bootstrap-unavailable nil)))
    (sb-thread:with-recursive-lock (*fnn-extent-lock*)
      (multiple-value-bind (word binding)
          (fnn-runtime-profile-envelope-live-binding
            (fnn-runtime-bootstrap-pool bootstrap) (fnn-runtime-bootstrap-image-policy bootstrap))
        (if (and (eq word :profile-envelope-available)
                 (eq binding (fnn-runtime-bootstrap-profile-envelope bootstrap)))
            (fnn-recovery-profile-quantum bootstrap binding 1)
          (values :recovery-image-binding-unavailable nil))))))
