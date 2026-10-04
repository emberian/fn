;;; Image-owned grammar workspace. This is not a Store profile or PRS grant.
(in-package "ACL2")

(defstruct (fnn-runtime-profile-envelope-binding
             (:constructor %fnn-runtime-profile-envelope-binding
                 (pool envelope buffer workspace source image &optional controller))
             (:copier nil))
  (pool nil :read-only t)
  (envelope nil :read-only t)
  (buffer nil :read-only t)
  (workspace nil :read-only t)
  (source nil :read-only t)
  (image nil :read-only t)
  (controller nil :read-only t)
  ;; Actual native OPEN custody lives in this preconstructed SAME binding.
  ;; Constructor arguments and immutable source associations remain unchanged.
  (fd nil)
  (io-phase :uninstalled))

(defvar *fnn-runtime-profile-envelope-binding* nil)

(defun fnn-runtime-profile-envelope-image-prepare (pool image-policy)
  "Construct once in the isolated builder, before bootstrap ImagePrepare.
ACL2 supplies every dimension. SOURCE is the actual selected compiled entry;
IMAGE is the actual saved policy object, with final artifact hashes external."
  (when *fnn-runtime-profile-envelope-binding*
    (error "runtime-profile-envelope-repeated"))
  (unless (and (eq pool (fnn-live-page-read-pool))
               image-policy
               (eq image-policy cl-user::*fnn-runtime-image-policy*))
    (error "runtime-profile-envelope-association-unavailable"))
  (let* ((buffer (cdr (assoc 'fn-recovery-profile-buffer
                             (user-stobj-alist *the-live-state*))))
         (controller (cdr (assoc 'fn-page-file-open
                                 (user-stobj-alist *the-live-state*))))
         (source (fnn-raw-dispatch-callback 'fn-recovery-profile-envelope))
         (envelope (fnn-core 'fn-recovery-profile-envelope)))
    (unless buffer
      (error "runtime-profile-envelope-buffer-unavailable"))
    (unless controller
      (error "runtime-profile-envelope-controller-unavailable"))
    (unless (compiled-function-p source)
      (error "runtime-profile-envelope-source-uncompiled"))
    (setf *fnn-runtime-profile-envelope-binding*
          (%fnn-runtime-profile-envelope-binding
           pool envelope buffer (svref buffer *fn-rpf-bytesi*)
           source image-policy controller))))

(defun fnn-runtime-profile-envelope-live-binding (pool image-policy)
  "Read the retained actual workspace; never construct in a runtime entry."
  (let ((binding *fnn-runtime-profile-envelope-binding*))
    (if (and binding
             (eq pool (fnn-runtime-profile-envelope-binding-pool binding))
             (eq image-policy (fnn-runtime-profile-envelope-binding-image binding))
             (eq image-policy cl-user::*fnn-runtime-image-policy*)
             (eq (fnn-runtime-profile-envelope-binding-buffer binding)
                 (cdr (assoc 'fn-recovery-profile-buffer
                             (user-stobj-alist *the-live-state*))))
             (eq (fnn-runtime-profile-envelope-binding-controller binding)
                 (cdr (assoc 'fn-page-file-open
                             (user-stobj-alist *the-live-state*))))
             (fnn-runtime-profile-envelope-binding-controller binding)
             (eq (fnn-runtime-profile-envelope-binding-workspace binding)
                 (svref (fnn-runtime-profile-envelope-binding-buffer binding)
                        *fn-rpf-bytesi*))
             (eq (fnn-runtime-profile-envelope-binding-source binding)
                 (fnn-raw-dispatch-callback 'fn-recovery-profile-envelope)))
        (values :profile-envelope-available binding)
      (values :profile-envelope-unavailable nil))))
