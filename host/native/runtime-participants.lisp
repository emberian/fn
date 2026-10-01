;;;; Isolated selected-SBCL prototype. Not an installed allowance or image claim.
(in-package "CL-USER")

(defstruct (fnn-runtime-participants
             (:constructor %fnn-runtime-participants (pool original original-stop)))
  pool original original-stop
  (lock (sb-thread:make-mutex :name "runtime-participants"))
  (changed (sb-thread:make-waitqueue :name "runtime-participants"))
  parked shutdown active active-owner fault)

(defvar *fnn-runtime-participants* nil)
(defvar *fnn-runtime-participant-barrier* nil)

(defun fnn-runtime-finalizer-entry ()
  ;; This entry precedes the original runner's rehash, hooks, compiler and users.
  ;; The unbounded original batch is deliberately not an admitted callback.
  (let ((gate *fnn-runtime-participants*))
    (unless gate (error "runtime-participant-unavailable"))
    (sb-thread:with-mutex ((fnn-runtime-participants-lock gate))
      (setf (fnn-runtime-participants-parked gate) t)
      (sb-thread:condition-broadcast (fnn-runtime-participants-changed gate))
      (loop until (fnn-runtime-participants-shutdown gate)
            do (sb-thread:condition-wait
                (fnn-runtime-participants-changed gate)
                (fnn-runtime-participants-lock gate)))
      (setf (fnn-runtime-participants-parked gate) nil))))

(defun fnn-runtime-finalizer-stop-entry ()
  ;; Normal quit/error exit also joins this worker, not only image DEINIT.
  ;; Wake before entering the original C stop/join implementation.
  (let ((gate *fnn-runtime-participants*))
    (unless gate (error "runtime-participant-unavailable"))
    (sb-thread:with-mutex ((fnn-runtime-participants-lock gate))
      (when (fnn-runtime-participants-active gate)
        (error "runtime-participant-active"))
      (setf (fnn-runtime-participants-shutdown gate) t)
      (sb-thread:condition-broadcast (fnn-runtime-participants-changed gate)))
    (funcall (fnn-runtime-participants-original-stop gate))))

(defun fnn-runtime-participants-install-for-image (pool)
  (when *fnn-runtime-participants* (error "runtime-participant-already-installed"))
  (let ((original (symbol-function 'sb-impl::run-pending-finalizers))
        (original-stop (symbol-function 'sb-impl::finalizer-thread-stop)))
    (unless (and (compiled-function-p original)
                 (compiled-function-p original-stop))
      (error "runtime-participant-uncompiled"))
    ;; Only an isolated image-build process may call this function.
    (sb-thread::with-system-mutex (sb-thread::*make-thread-lock*)
      (sb-impl::finalizer-thread-stop))
    (let ((gate (%fnn-runtime-participants pool original original-stop)))
      (setf *fnn-runtime-participants* gate)
      (sb-ext:without-package-locks
        (setf (symbol-function 'sb-impl::run-pending-finalizers)
              #'fnn-runtime-finalizer-entry
              (symbol-function 'sb-impl::finalizer-thread-stop)
              #'fnn-runtime-finalizer-stop-entry))
      (sb-impl::finalizer-thread-start)
      gate)))

(defmacro fnn-with-runtime-participants-parked ((gate pool) &body body)
  (let ((g (gensym "PARTICIPANTS")))
    `(let ((,g ,gate))
     (when (or (eq *fnn-runtime-participant-barrier* ,g)
               (eq sb-thread:*current-thread* sb-impl::*finalizer-thread*)
               (eq sb-thread:*current-thread*
                   (fnn-runtime-participants-active-owner ,g)))
       (error "runtime-participant-reentrant"))
     (sb-thread:with-mutex ((fnn-runtime-participants-lock ,g))
       (unless (and (eq (symbol-function 'sb-impl::run-pending-finalizers)
                       #'fnn-runtime-finalizer-entry)
                    (eq (symbol-function 'sb-impl::finalizer-thread-stop)
                        #'fnn-runtime-finalizer-stop-entry)
                    (eq ,pool (fnn-runtime-participants-pool ,g))
                    (not (fnn-runtime-participants-shutdown ,g))
                    (not (fnn-runtime-participants-fault ,g)))
         (error "runtime-participant-unavailable"))
       (loop until (and (fnn-runtime-participants-parked ,g)
                        (not (fnn-runtime-participants-active ,g)))
             do (when (or (fnn-runtime-participants-shutdown ,g)
                          (fnn-runtime-participants-fault ,g))
                  (error "runtime-participant-unavailable"))
                (sb-thread:condition-wait
                 (fnn-runtime-participants-changed ,g)
                 (fnn-runtime-participants-lock ,g)))
       (when (or (fnn-runtime-participants-shutdown ,g)
                 (fnn-runtime-participants-fault ,g))
         (error "runtime-participant-unavailable"))
       (let ((*fnn-runtime-participant-barrier* ,g)) ,@body)))))

(defmacro fnn-with-runtime-participants-bootstrap ((gate pool) &body body)
  ;; The earliest escrow suffix never waits or retries for an acknowledgment.
  ;; A successful body returns its exact multiple values while SAME lock holds.
  (let ((g (gensym "BOOT-GATE")) (p (gensym "BOOT-POOL"))
        (attempt (gensym "BOOT-ATTEMPT")))
    `(sb-sys:without-interrupts
       (let ((,g ,gate) (,p ,pool))
       (block ,attempt
         (unless (typep ,g 'fnn-runtime-participants)
           (return-from ,attempt (values :participant-unavailable :fenced)))
         (when (or (sb-thread:holding-mutex-p
                    (fnn-runtime-participants-lock ,g))
                   (eq *fnn-runtime-participant-barrier* ,g)
                   (eq sb-thread:*current-thread* sb-impl::*finalizer-thread*)
                   (eq sb-thread:*current-thread*
                       (fnn-runtime-participants-active-owner ,g)))
           (return-from ,attempt (values :participant-reentrant :fenced)))
         (sb-thread:with-mutex ((fnn-runtime-participants-lock ,g) :wait-p nil)
           (unless (and (eq (symbol-function 'sb-impl::run-pending-finalizers)
                            #'fnn-runtime-finalizer-entry)
                        (eq (symbol-function 'sb-impl::finalizer-thread-stop)
                            #'fnn-runtime-finalizer-stop-entry)
                        (eq ,p (fnn-runtime-participants-pool ,g))
                        (not (fnn-runtime-participants-shutdown ,g))
                        (not (fnn-runtime-participants-fault ,g)))
             (return-from ,attempt (values :participant-unavailable :fenced)))
           (unless (and (fnn-runtime-participants-parked ,g)
                        (not (fnn-runtime-participants-active ,g)))
             (return-from ,attempt (values :participant-not-ready :refused)))
           (let ((*fnn-runtime-participant-barrier* ,g))
             (return-from ,attempt (progn ,@body))))
         (values :participant-not-ready :refused))))))

(defun fnn-runtime-participants-stop-and-join (gate)
  ;; Wake the Lisp barrier before requesting the C worker's stop and real join.
  (sb-thread:with-mutex ((fnn-runtime-participants-lock gate))
    (when (fnn-runtime-participants-active gate)
      (error "runtime-participant-active"))
    (setf (fnn-runtime-participants-shutdown gate) t)
    (sb-thread:condition-broadcast (fnn-runtime-participants-changed gate)))
  (sb-thread::with-system-mutex (sb-thread::*make-thread-lock*)
    (sb-impl::finalizer-thread-stop))
  ;; A stopped gate refuses until the genuine image init starts its worker.
  (setf (fnn-runtime-participants-parked gate) nil)
  gate)

(defstruct (fnn-runtime-cleanup-binding
             (:constructor %fnn-runtime-cleanup-binding
                 (gate subject claim body complete fence)))
  (gate nil :read-only t) (subject nil :read-only t)
  (claim nil :read-only t) (body nil :read-only t)
  (complete nil :read-only t) (fence nil :read-only t)
  receipt)

(defun fnn-runtime-participant-cleanup-one (binding)
  ;; Binding construction is image-private. CLAIM is the actual core admission;
  ;; no arbitrary pending finalizer, hook, or compiler batch is opened by it.
  (let ((gate (fnn-runtime-cleanup-binding-gate binding)))
    (when (eq *fnn-runtime-participant-barrier* gate)
      (return-from fnn-runtime-participant-cleanup-one :unavailable))
    (sb-thread:with-mutex ((fnn-runtime-participants-lock gate))
      (unless (and (fnn-runtime-participants-parked gate)
                   (not (fnn-runtime-participants-active gate))
                   (not (fnn-runtime-participants-fault gate))
                   (not (fnn-runtime-participants-shutdown gate)))
        (return-from fnn-runtime-participant-cleanup-one :unavailable))
      (setf (fnn-runtime-participants-active gate) t
            (fnn-runtime-participants-active-owner gate) sb-thread:*current-thread*))
    (let ((definite nil) (fenced nil))
      (unwind-protect
         (handler-case
             (multiple-value-bind (word receipt)
                 (funcall (fnn-runtime-cleanup-binding-claim binding)
                          (fnn-runtime-cleanup-binding-subject binding))
               ;; Retain any returned custody before discriminating the word.
               (setf (fnn-runtime-cleanup-binding-receipt binding) receipt)
               (case word
                 (:refused (setf definite t)
                           (return-from fnn-runtime-participant-cleanup-one :refused))
                 (:unavailable (setf definite t)
                               (return-from fnn-runtime-participant-cleanup-one :unavailable))
                 (:admitted (unless receipt (error "runtime-participant-missing-receipt")))
                 (otherwise (error "runtime-participant-claim-uncertain")))
               (funcall (fnn-runtime-cleanup-binding-body binding))
               (unless (eq :completed
                           (funcall (fnn-runtime-cleanup-binding-complete binding) receipt))
                 (error "runtime-participant-completion-uncertain"))
               (setf definite t)
               ;; Logical completion does not reclaim this retained receipt.
               :completed)
           (serious-condition (cause)
             (sb-thread:with-mutex ((fnn-runtime-participants-lock gate))
               (setf (fnn-runtime-participants-fault gate) cause))
             (setf fenced t)
             (funcall (fnn-runtime-cleanup-binding-fence binding)
                      (fnn-runtime-cleanup-binding-receipt binding) cause)
             (error cause)))
        (unwind-protect
             (unless (or definite fenced)
               (sb-thread:with-mutex ((fnn-runtime-participants-lock gate))
                 (setf (fnn-runtime-participants-fault gate) :nonlocal-escape))
               (funcall (fnn-runtime-cleanup-binding-fence binding)
                        (fnn-runtime-cleanup-binding-receipt binding) :nonlocal-escape))
          (sb-thread:with-mutex ((fnn-runtime-participants-lock gate))
            (setf (fnn-runtime-participants-active gate) nil
                  (fnn-runtime-participants-active-owner gate) nil)
            (sb-thread:condition-broadcast
             (fnn-runtime-participants-changed gate))))))))

(defun fnn-runtime-participants-save-hook ()
  ;; SAVE-LISP-AND-DIE's official DEINIT owns the actual C stop and join.
  ;; Wake the parked Lisp entry so that DEINIT can perform that join.
  (let ((gate *fnn-runtime-participants*))
    (sb-thread:with-mutex ((fnn-runtime-participants-lock gate))
      (when (fnn-runtime-participants-active gate)
        (error "runtime-participant-active"))
      (setf (fnn-runtime-participants-shutdown gate) t)
      (sb-thread:condition-broadcast (fnn-runtime-participants-changed gate)))))

(defun fnn-runtime-participants-init-hook ()
  ;; Selected SBCL documents INIT-HOOKS before non-user finalizer thread birth.
  (let ((gate *fnn-runtime-participants*))
    (setf (fnn-runtime-participants-shutdown gate) nil
          (fnn-runtime-participants-parked gate) nil
          (fnn-runtime-participants-active gate) nil
          (fnn-runtime-participants-active-owner gate) nil)))

(defun fnn-runtime-participants-register-image-hooks ()
  ;; Hook ordering is unspecified. This finite prototype cannot qualify other
  ;; image callbacks, which could allocate or start workers before the barrier.
  (unless (and (every (lambda (hook)
                        (eq hook 'fnn-runtime-participants-save-hook))
                      sb-ext:*save-hooks*)
               (every (lambda (hook)
                        (or (eq hook 'fnn-runtime-participants-init-hook)
                            (eq hook 'fnn-runtime-image-policy-restore)))
                      sb-ext:*init-hooks*))
    (error "runtime-participant-image-hooks-unavailable"))
  (pushnew 'fnn-runtime-participants-save-hook sb-ext:*save-hooks*)
  (pushnew 'fnn-runtime-participants-init-hook sb-ext:*init-hooks*))

(defun fnn-runtime-system-finalizer-one (scratch)
  ;; Exact one-action system target from the selected runner. No user finalizer,
  ;; hook, compiler batch, or original runner is called by this entry.
  (sb-vm::immobile-code-dealloc-1 scratch))

(defun %fnn-runtime-system-cleanup-binding (gate subject claim complete fence)
  ;; Image-private construction; scratch and closure are retained baseline.
  ;; CLAIM must resolve the qualified unit for this exact target, or refuse.
  (unless (compiled-function-p
           (symbol-function 'sb-vm::immobile-code-dealloc-1))
    (error "runtime-system-cleanup-unavailable"))
  (let ((scratch (list 0)))
    (%fnn-runtime-cleanup-binding
     gate subject claim
     (lambda () (fnn-runtime-system-finalizer-one scratch))
     complete fence)))
