;;; Dormant actual registered-prefix caller. The installer must establish
;;; selected BODY/stage authority before publishing these guarded callbacks.
;;; No constructor/callback installer or generic interpreter fallback here.
(in-package "ACL2")
(defvar *fnn-bpck-prefix-next-callback* nil)
(defvar *fnn-bpck-prefix-observe-callback* nil)

(defstruct (fnn-bpck-registered-io (:constructor %make-fnn-bpck-registered-io))
  controller stage action fd (close-result :closed) (outcome :idle)
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
                  ((:observed :uncertain)
                   (setf (fnn-bpck-registered-io-action record) nil
                         (fnn-bpck-registered-io-outcome record) :idle))
                  (:yield nil)
                  (otherwise
                   (setf (fnn-bpck-registered-io-core-failure record) word))))))
          (let ((callback *fnn-bpck-prefix-next-callback*) (action nil))
            (unless callback (fnn-fault "registered BP prefix callback unavailable"))
            (sb-thread:with-mutex (*fnn-extent-lock*)
              (multiple-value-bind (word effect left registry)
                  (funcall callback (fnn-bpck-registered-io-controller record) fuel
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
