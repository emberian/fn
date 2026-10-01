;;;; Image-build/restore only. A callback exclusion is not an allocation tariff.
(in-package "CL-USER")
(eval-when (:compile-toplevel :load-toplevel :execute) (require :sb-sprof))
(defparameter *fnn-runtime-bootstrap-ordinary-signals*
  (list sb-unix:sighup sb-unix:sigint sb-unix:sigquit sb-unix:sigterm
        sb-unix:sigpipe sb-unix:sigalrm sb-unix:sigprof
        sb-unix:sigusr1 sb-unix:sigwinch))
(defstruct (fnn-runtime-image-policy
             (:constructor %fnn-runtime-image-policy (pool participants)))
  pool participants (phase :building))
(defvar *fnn-runtime-image-policy* nil)
(defun fnn-runtime-image-policy-platform-p ()
  (and (member :linux *features*) (member :x86-64 *features*)
       (member :sb-thread *features*) (not (member :sb-safepoint *features*))
       (not (member :address-sanitizer *features*))))
(defun fnn-runtime-image-policy-signal-default-p (signal)
  ;; Exact selected TARGET-SIGNAL implementation documents this table read.
  ;; Reserved SIGURG/SIGUSR2/SIGVTALRM and memory-fault handlers are untouched.
  (eql 0 (sb-sys:sap-ref-lispobj
          (sb-sys:foreign-symbol-sap "lisp_sig_handlers" t)
          (ash signal sb-vm:word-shift))))
(defun fnn-runtime-image-policy-allocator-profiler-off-p ()
  (zerop (sb-alien:extern-alien "gencgc_alloc_profiler" sb-alien:int)))
(defun fnn-runtime-image-policy-source-quiet-p ()
  ;; Cold inventory before the heap sample; not a served-path revalidation.
  (and (not sb-sprof::*profiling*)
       (fnn-runtime-image-policy-allocator-profiler-off-p)
       (null sb-impl::*active-processes*)
       (null (sb-ext:list-all-timers))
       (every (lambda (thread)
                (or (eq thread sb-thread:*current-thread*)
                    (eq thread sb-impl::*finalizer-thread*)))
              (sb-thread:list-all-threads))))
(defun fnn-runtime-image-policy-restore ()
  (let ((policy *fnn-runtime-image-policy*))
    (when policy (setf (fnn-runtime-image-policy-phase policy) :uncertain))
    (unless (and policy (fnn-runtime-image-policy-platform-p)
                 (eq (fnn-runtime-image-policy-participants policy)
                     *fnn-runtime-participants*)
                 (eq (fnn-runtime-image-policy-pool policy)
                     (fnn-runtime-participants-pool *fnn-runtime-participants*))
                 (fnn-runtime-image-policy-source-quiet-p))
      (error "runtime-image-policy-unavailable"))
    ;; Default termination cannot run an application Lisp callback. These
    ;; dispositions remain installed through the bootstrap mask EXIT.
    (dolist (signal *fnn-runtime-bootstrap-ordinary-signals*)
      (sb-sys:enable-interrupt signal :default))
    (unless (every #'fnn-runtime-image-policy-signal-default-p
                   *fnn-runtime-bootstrap-ordinary-signals*)
      (error "runtime-image-policy-disposition-unavailable"))
    (setf (fnn-runtime-image-policy-phase policy) :closed)
    policy))
(defun fnn-runtime-image-policy-prepare (pool participants)
  (when *fnn-runtime-image-policy* (error "runtime-image-policy-repeated"))
  (unless (and participants (eq participants *fnn-runtime-participants*)
               (eq pool (fnn-runtime-participants-pool participants)))
    (error "runtime-image-policy-association-unavailable"))
  (setf *fnn-runtime-image-policy* (%fnn-runtime-image-policy pool participants))
  (fnn-runtime-image-policy-restore))

(defun fnn-runtime-image-policy-bootstrap-status (pool participants)
  ;; Observation of the exact image-private object, not a qualification flag.
  (let ((policy *fnn-runtime-image-policy*))
    (if (and policy (eq (fnn-runtime-image-policy-phase policy) :closed)
             (eq pool (fnn-runtime-image-policy-pool policy))
             (eq participants (fnn-runtime-image-policy-participants policy))
             (eq participants *fnn-runtime-participants*)
             (fnn-runtime-image-policy-allocator-profiler-off-p)
             (every #'fnn-runtime-image-policy-signal-default-p
                    *fnn-runtime-bootstrap-ordinary-signals*))
        (values :image-policy-closed policy)
      (values :image-policy-unavailable nil))))
(defun fnn-runtime-image-policy-register-image-hook ()
  (unless *fnn-runtime-image-policy* (error "runtime-image-policy-missing"))
  (pushnew 'fnn-runtime-image-policy-restore sb-ext:*init-hooks*))
