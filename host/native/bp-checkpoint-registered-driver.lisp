;;; Dormant actual registered-prefix caller. The installer must establish
;;; selected BODY/stage authority before publishing these guarded callbacks.
;;; No constructor/callback installer or generic interpreter fallback here.
(in-package "ACL2")
(defvar *fnn-bpck-prefix-next-callback* nil)
(defvar *fnn-bpck-prefix-observe-callback* nil)
(defvar *fnn-bpck-close-next-callback* nil)
(defvar *fnn-bpck-close-observe-callback* nil)
(defvar *fnn-bpck-cancelled-observe-callback* nil)

(defstruct (fnn-bpck-registered-io (:constructor %make-fnn-bpck-registered-io))
  controller job-token stage action fd (close-result :closed) (outcome :idle)
  (action-lock (sb-thread:make-mutex)) (source-result :returned)
  status failure core-failure)

(defun fnn-bps-registered-checkpoint-record (controller stage)
  ;; A compiled callback is a role, not a per-job constructor claim. The
  ;; genuine registered claim/creator gate is not installed yet. Refuse before
  ;; constructing the record/mutex or looking up any registry object.
  (declare (ignore controller stage))
  (fnn-fault "the guarded per-job BP native holder allocator is not installed"))

(defun fnn-bps-registered-checkpoint-prefix-turn (record fuel)
  "One prepare/primitive or observation join. RECORD remains caller-visible.
No native CURRENT, checkpoint job or digest stobj is authoritative here."
  (when (fnn-bpck-registered-io-core-failure record)
    (return-from fnn-bps-registered-checkpoint-prefix-turn record))
  ;; One primitive/result owner per record. A concurrent scheduler quantum
  ;; never joins the placeholder :unknown while the primitive is still running.
  ;; This lock is distinct from the semantic extent lock and is never waited on.
  (sb-thread:with-mutex ((fnn-bpck-registered-io-action-lock record) :wait-p nil)
   (when (fnn-bpck-registered-io-core-failure record)
    (return-from fnn-bps-registered-checkpoint-prefix-turn record))
   (setf (fnn-bpck-registered-io-source-result record) :running)
   (unwind-protect
    (handler-case
      (if (fnn-bpck-registered-io-action record)
          ;; An already attempted primitive is never repeated, even if its
          ;; core observation fails or cancellation/recovery races this turn.
          (let ((callback *fnn-bpck-prefix-observe-callback*)
                (action (fnn-bpck-registered-io-action record)))
            (unless callback (fnn-fault "registered BP observation callback unavailable"))
            (sb-thread:with-mutex (*fnn-extent-lock*)
              (multiple-value-bind (word left registry)
                  (funcall callback (fnn-bpck-registered-io-controller record)
                           (second action) (third action)
                           (fnn-bpck-registered-io-outcome record) fuel
                           (fnn-live-bp-controller-registry))
                (declare (ignore left registry))
                (setf (fnn-bpck-registered-io-status record) word)
                (case word
                  ((:observed :uncertain :close-observed :close-uncertain)
                   (setf (fnn-bpck-registered-io-action record) nil
                         (fnn-bpck-registered-io-outcome record) :idle))
                  (:yield nil)
                  (otherwise
                   (setf (fnn-bpck-registered-io-core-failure record) word))))))
          (let ((callback *fnn-bpck-prefix-next-callback*) (action nil))
            (unless callback (fnn-fault "registered BP prefix callback unavailable"))
            (sb-thread:with-mutex (*fnn-extent-lock*)
              (multiple-value-bind (word effect left registry)
                  (funcall callback (fnn-bpck-registered-io-controller record)
                           (fnn-bpck-registered-io-job-token record) fuel
                           (fnn-live-bp-controller-registry))
                (declare (ignore left registry))
                (setf (fnn-bpck-registered-io-status record) word)
                (when (eq word :action-prepared)
                  ;; Retain exact core action BEFORE leaving the lock/I/O.
                  (setf action effect
                        (fnn-bpck-registered-io-action record) effect
                        (fnn-bpck-registered-io-outcome record) :unknown))))
            (when action
              ;; Filesystem effects occur after releasing the semantic lock.
              (handler-case
                  (progn
                    (case (fourth action)
                      (:open
                       (setf (fnn-bpck-registered-io-close-result record) :uncertain)
                       (setf (fnn-bpck-registered-io-fd record)
                             (fnn-open (fnn-bpck-registered-io-stage record)
                                       (logior sb-posix:o-rdwr sb-posix:o-creat
                                               sb-posix:o-excl +fnn-o-nofollow+) #o600)
                             (fnn-bpck-registered-io-close-result record) :open))
                      (:close
                       ;; Detach before CLOSE. Unknown close is never retried,
                       ;; and detached NIL never establishes definite return.
                       (let ((closing (fnn-bpck-registered-io-fd record)))
                        (cond
                         (closing
                          (setf (fnn-bpck-registered-io-fd record) nil
                                (fnn-bpck-registered-io-close-result record) :uncertain)
                          (fnn-close closing)
                          (setf (fnn-bpck-registered-io-close-result record) :closed))
                         ((eq (fnn-bpck-registered-io-close-result record) :closed) nil)
                         (t (fnn-fault "detached BP descriptor has uncertain close custody")))))
                      (:emit (fnn-write-all (fnn-bpck-registered-io-fd record)
                                           (sixth action)))
                      (otherwise (fnn-fault "unrecognized registered prefix I/O action")))
                    (setf (fnn-bpck-registered-io-outcome record) :ok))
                (error (condition)
                  (setf (fnn-bpck-registered-io-failure record) condition
                        (fnn-bpck-registered-io-outcome record) :unknown))))))
    (error (condition)
      (setf (fnn-bpck-registered-io-core-failure record) condition)))
    (setf (fnn-bpck-registered-io-source-result record) :returned)))
  record)

(defun fnn-bps-registered-checkpoint-close-turn (record fuel)
  "One retained registered close action/result. No release is performed."
  (unless (and *fnn-bpck-close-next-callback* *fnn-bpck-close-observe-callback*)
    (fnn-fault "guarded registered BP close callbacks unavailable"))
  (let ((*fnn-bpck-prefix-next-callback* *fnn-bpck-close-next-callback*)
        (*fnn-bpck-prefix-observe-callback* *fnn-bpck-close-observe-callback*))
    (fnn-bps-registered-checkpoint-prefix-turn record fuel)))

(defun fnn-bps-registered-checkpoint-cancelled-result-turn (record fuel)
  "Join an already attempted primitive after cancellation; perform no I/O."
  (unless *fnn-bpck-cancelled-observe-callback*
    (fnn-fault "guarded registered BP cancelled observation callback unavailable"))
  (sb-thread:with-mutex ((fnn-bpck-registered-io-action-lock record) :wait-p nil)
   (let ((action (fnn-bpck-registered-io-action record)))
    (when action
     ;; The retained core result callback is also a source/alias action. Do not
     ;; advertise definite return while that callback still owns its borrow.
     (setf (fnn-bpck-registered-io-source-result record) :running)
     (unwind-protect
      (handler-case
       (sb-thread:with-mutex (*fnn-extent-lock*)
        (multiple-value-bind (word left registry)
         (funcall *fnn-bpck-cancelled-observe-callback*
          (fnn-bpck-registered-io-controller record) (second action) (third action)
          (fnn-bpck-registered-io-outcome record) fuel
          (fnn-live-bp-controller-registry))
         (declare (ignore left registry))
         (setf (fnn-bpck-registered-io-status record) word)
         (case word
          ((:cancelled-observed :cancelled-uncertain)
           ;; Only the exact registered settlement can retire this result.
           ;; No descriptor, stage, or ledger debt is inferred released.
           (setf (fnn-bpck-registered-io-action record) nil
                 (fnn-bpck-registered-io-outcome record) :idle
                 (fnn-bpck-registered-io-core-failure record) nil))
          (:yield nil)
          (otherwise (setf (fnn-bpck-registered-io-core-failure record) word)))))
       (error (condition)
        (setf (fnn-bpck-registered-io-core-failure record) condition)))
      (setf (fnn-bpck-registered-io-source-result record) :returned)))))
  record)
