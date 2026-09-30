;;; One bounded BP checkpoint source/I/O turn. The creator is called only
;;; after admission; its caller retains RECORD before the first effect.
;;; Turns execute outside the owner/BP semantic mutex. The caller rejoins each
;;; observed result under its epoch/token fence before scheduling another.
(in-package "ACL2")

(defstruct (fnn-bpck-io (:constructor %make-fnn-bpck-io))
  stage job digest-state control fd (close-result :closed)
  (source-result :returned) failure core-failure)

(defun fnn-bps-checkpoint-digest-call (record name &rest arguments)
  (apply #'fnn-call name
         (append arguments (list (fnn-bpck-io-digest-state record)))))

(defun fnn-bps-checkpoint-open-job (stage job digest-state)
  "Retain this record before any I/O; no stage is created by this constructor."
  (%make-fnn-bpck-io :stage stage :job job :digest-state digest-state
                   :control (fnn-core 'fn-bpck-io-begin job)))

(defun fnn-bps-checkpoint-observe (record word)
  (setf (fnn-bpck-io-control record)
        (fnn-core 'fn-bpck-io-step (fnn-bpck-io-control record) word)))

(defun fnn-bps-checkpoint-turn (record)
  "Perform one source action or primitive and always return the same record.
Every condition leaves caller-visible stage, descriptor and close evidence.
No turn loops over the job; cancellation prevents scheduling the next turn,
then closes/settles the retained stage before any charge can be refunded."
  ;; A failed core observation cannot authorize another filesystem turn.
  ;; Keep the record/FD charged for recovery; do not synthesize a core state.
  (when (fnn-bpck-io-core-failure record)
    (return-from fnn-bps-checkpoint-turn record))
  (setf (fnn-bpck-io-source-result record) :running)
  (unwind-protect
       (handler-case
           (let ((job (fnn-bpck-io-job record)))
             (case (fnn-core 'fn-bpck-io-action
                             (fnn-bpck-io-control record) job)
               (:open
                (setf (fnn-bpck-io-fd record)
                      (fnn-open (fnn-bpck-io-stage record)
                                (logior sb-posix:o-rdwr sb-posix:o-creat
                                        sb-posix:o-excl +fnn-o-nofollow+) #o600)
                      (fnn-bpck-io-close-result record) :open
                      (fnn-bpck-io-job record)
                      (fnn-core 'fn-bpck-stage-observation job :created))
                (fnn-bps-checkpoint-observe record :ok))
               (:emit
                (let ((answer (fnn-core 'fn-bpck-emit-step job)))
                  ;; Retain the new source position before the write attempt.
                  (setf (fnn-bpck-io-job record) (first answer))
                  (fnn-write-all (fnn-bpck-io-fd record) (second answer))
                  (fnn-bps-checkpoint-observe record :ok)))
               (:prefix-end
                (fnn-bps-checkpoint-observe
                 record (if (eq (fnn-core 'fn-bpck-write-action job) :digest)
                            :prefix-end :error)))
               (:digest-start
                (fnn-bps-checkpoint-observe
                 record (if (eq (first (fnn-bps-checkpoint-digest-call
                                        record 'fn-bpck-digest-start job)) :started)
                            :ok :error)))
               (:digest
                (let ((action (first (fnn-bps-checkpoint-digest-call
                                      record 'fn-bpck-digest-action job))))
                  (case (first action)
                    (:read
                     (let ((octets (fnn-log-pread (fnn-bpck-io-fd record)
                                                 (second action) (third action))))
                       (fnn-bps-checkpoint-observe
                        record (if (member (first (fnn-bps-checkpoint-digest-call
                                                   record 'fn-bpck-digest-step job
                                                   (fnn-octet-list octets)))
                                           '(:continue :done)) :ok :error))))
                    (:advance
                     (fnn-bps-checkpoint-observe
                      record (if (member (first (fnn-bps-checkpoint-digest-call
                                                 record 'fn-bpck-digest-step job nil))
                                         '(:continue :done)) :ok :error)))
                    (:trailer (fnn-bps-checkpoint-observe record :trailer-ready))
                    (otherwise (fnn-bps-checkpoint-observe record :error)))))
               (:trailer
                (let ((action (first (fnn-bps-checkpoint-digest-call
                                      record 'fn-bpck-digest-action job))))
                  (unless (eq (first action) :trailer)
                    (fnn-fault "BP checkpoint trailer action changed"))
                  (fnn-posix () (sb-posix:lseek
                                 (fnn-bpck-io-fd record)
                                 (fnn-core 'fn-bpck-prefix-end job)
                                 sb-posix:seek-set))
                  (fnn-write-all (fnn-bpck-io-fd record) (second action))
                  (fnn-bps-checkpoint-observe record :ok)))
               (:barrier
                (fnn-fsync-file (fnn-bpck-io-fd record))
                (fnn-bps-checkpoint-observe record :ok))
               (:close
                (let ((closing (fnn-bpck-io-fd record)))
                  ;; Detach before close; its ambiguous result is never retried.
                  (setf (fnn-bpck-io-fd record) nil
                        (fnn-bpck-io-close-result record) :uncertain)
                  (when closing (fnn-close closing))
                  (setf (fnn-bpck-io-close-result record) :closed)
                  (fnn-bps-checkpoint-observe record :ok)))
               (:done nil)
               (otherwise (fnn-bps-checkpoint-observe record :error))))
         (error (condition)
           (setf (fnn-bpck-io-failure record) condition)
           (handler-case
               (progn
                 (setf (fnn-bpck-io-job record)
                       (fnn-core 'fn-bpck-stage-observation
                                 (fnn-bpck-io-job record) :ambiguous))
                 (fnn-bps-checkpoint-observe record :error))
             (error (core-condition)
               ;; Both conditions and the actual FD/source position remain
               ;; visible even when the core cannot record the I/O outcome.
               (setf (fnn-bpck-io-core-failure record) core-condition)))))
    (setf (fnn-bpck-io-source-result record) :returned))
  record)

(defun fnn-bps-checkpoint-cancel (record)
  "Stop future source turns after the active turn has returned.
This requests a retained close turn; it does not delete staging or refund.
The scheduler must call it only after joining the active action."
  (unless (fnn-bpck-io-core-failure record)
    (handler-case (fnn-bps-checkpoint-observe record :cancel)
      (error (condition)
        (setf (fnn-bpck-io-failure record) condition
              (fnn-bpck-io-core-failure record) condition))))
  record)
