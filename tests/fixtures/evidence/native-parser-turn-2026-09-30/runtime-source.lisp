(defstruct (fnn-owner-receiver-turn-runtime
             (:constructor %make-fnn-owner-receiver-turn-runtime))
  provider capacity-token current turn turn-start copy-next copy-ack fence limits parser)

(defun fnn-owner-receiver-turn-runtime-make
    (token current turn-start copy-next copy-ack fence limits &optional parser)
  (%make-fnn-owner-receiver-turn-runtime
   :capacity-token token :current current :turn-start turn-start
   :copy-next copy-next :copy-ack copy-ack :fence fence :limits limits :parser parser))

(defun fnn-owner-receiver-current-startup
    (service demand limits current creator turn-creator
             reserve-callback allocation-callback install-callback
             turn-start-callback next-callback ack-callback fence-callback current-fence-callback pool
             &optional parser-callback)
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (when (fnn-owner-service-receiver-runtime service)
      (fnn-fixed-callback-fail 'fn-owner-rx-current-reserve
                               :receiver-startup-already-retained nil))
    (handler-case
        (progn
    (setf (fnn-owner-service-receiver-runtime service) current)
    (multiple-value-bind (word token current1 pool1)
        (fnn-core-mv 'fn-owner-rx-current-reserve
          (funcall reserve-callback demand current pool))
      (setf (fnn-owner-service-receiver-runtime service) current1)
      (unless (eq word :admitted)
        (return-from fnn-owner-receiver-current-startup (values word nil pool1)))
      (multiple-value-bind (allocation current2 pool2)
          (fnn-core-mv 'fn-owner-rx-current-allocation-begin
            (funcall allocation-callback token current1 pool1))
        (setf (fnn-owner-service-receiver-runtime service) current2)
        (unless (eq allocation :allocate)
          (fnn-fixed-callback-fail 'fn-owner-rx-current-allocation-begin
                                   :receiver-allocation-incomplete allocation))
        (let ((runtime (fnn-owner-receiver-turn-runtime-make
                        token current2 turn-start-callback next-callback
                        ack-callback fence-callback limits parser-callback)))
          (setf (fnn-owner-service-receiver-runtime service) runtime)
          (let ((provider (fnn-core-mv 'create-fn-rx-provider (funcall creator))))
            (setf (fnn-owner-receiver-turn-runtime-provider runtime) provider)
            (setf (fnn-owner-receiver-turn-runtime-turn runtime)
                  (fnn-core-mv 'create-fn-receiver-turn (funcall turn-creator)))
            (multiple-value-bind (installed provider1 turn1 current3 pool3)
                (fnn-core-mv 'fn-owner-rx-current-install
                  (funcall install-callback token provider
                           (fnn-owner-receiver-turn-runtime-turn runtime)
                           current2 pool2))
              (setf (fnn-owner-receiver-turn-runtime-provider runtime) provider1
                    (fnn-owner-receiver-turn-runtime-turn runtime) turn1
                    (fnn-owner-receiver-turn-runtime-current runtime) current3)
              (unless (eq installed :installed)
                (fnn-fixed-callback-fail 'fn-owner-rx-current-install
                                         :receiver-install-incomplete installed))
              (values installed runtime pool3)))))))
      (serious-condition (cause)
        ;; The control owns any token even if reserve escaped before returning
        ;; it. Fence that actual control, then any constructed provider. A
        ;; fence escape must reach the enclosing shared fail-stop boundary.
        (let* ((retained (fnn-owner-service-receiver-runtime service))
               (runtimep (fnn-owner-receiver-turn-runtime-p retained))
               (controller (if runtimep
                               (fnn-owner-receiver-turn-runtime-current retained)
                             retained)))
          (multiple-value-bind (ignored fenced pool1)
              (fnn-core-mv 'fn-owner-rx-current-fence-current
                (funcall current-fence-callback controller pool))
            (declare (ignore ignored pool1))
            (if runtimep
                (setf (fnn-owner-receiver-turn-runtime-current retained) fenced)
              (setf (fnn-owner-service-receiver-runtime service) fenced)))
          (when (and runtimep (fnn-owner-receiver-turn-runtime-provider retained))
            (fnn-core-mv 'fn-rxp-fence
              (funcall fence-callback
                       (fnn-owner-receiver-turn-runtime-capacity-token retained)
                       (fnn-owner-receiver-turn-runtime-provider retained)))))
        (error cause)))))
