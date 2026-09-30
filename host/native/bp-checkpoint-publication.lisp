;;; One bounded publication action per scheduled turn, after retained writer return.
;;; Unactivated until actual indexed grant, epoch/token fence and installed disk
;;; transfer are joined. No whole checkpoint encoding or filesystem loop.
(in-package "ACL2")

(defstruct (fnn-bpck-publication (:constructor %make-fnn-bpck-publication))
  root directory stage final job control fd (close-result :closed)
  (source-result :returned) failure core-failure)

(defun fnn-bps-checkpoint-publication-open (root directory stage final writer)
  "The caller retains this record before scheduling any publication effect."
  (%make-fnn-bpck-publication
   :root root :directory directory :stage stage :final final
   :job (fnn-bpck-io-job writer)
   :control (fnn-core 'fn-bpck-publication-begin
                       (fnn-bpck-io-job writer) (fnn-bpck-io-control writer)
                       (fnn-bpck-io-source-result writer)
                       (fnn-bpck-io-close-result writer)
                       (and (fnn-bpck-io-failure writer) t)
                       (and (fnn-bpck-io-core-failure writer) t))))

(defun fnn-bps-checkpoint-publication-observe (record word)
  (let ((answer (fnn-core 'fn-bpck-publication-observe
                          (fnn-bpck-publication-job record)
                          (fnn-bpck-publication-control record) word)))
    (setf (fnn-bpck-publication-control record) (first answer)
          (fnn-bpck-publication-job record) (second answer))))

(defun fnn-bps-checkpoint-publication-turn (record)
  "Return the retained record after one bounded action, including every condition.
A failure or failed core observation retains the private/published uncertainty
and its charge. This driver never deletes a stage or refunds installed disk."
  (when (fnn-bpck-publication-core-failure record)
    (return-from fnn-bps-checkpoint-publication-turn record))
  (setf (fnn-bpck-publication-source-result record) :running)
  (unwind-protect
       (handler-case
           (let ((action (fnn-core 'fn-bpck-publication-action
                                    (fnn-bpck-publication-control record)
                                    (fnn-bpck-publication-close-result record))))
             (case action
               (:make-directory
                (fnn-mkdir (fnn-bpck-publication-directory record) #o700))
               ((:open-generation :open-root)
                (setf (fnn-bpck-publication-fd record)
                      (fnn-open (if (eq action :open-generation)
                                    (fnn-bpck-publication-directory record)
                                  (fnn-bpck-publication-root record))
                                (logior sb-posix:o-rdonly +fnn-o-directory+
                                        +fnn-o-nofollow+))
                      (fnn-bpck-publication-close-result record) :open))
               (:barrier (fnn-fsync-file (fnn-bpck-publication-fd record)))
               (:close
                (let ((closing (fnn-bpck-publication-fd record)))
                  (setf (fnn-bpck-publication-fd record) nil
                        (fnn-bpck-publication-close-result record) :uncertain)
                  (fnn-close closing)
                  (setf (fnn-bpck-publication-close-result record) :closed)))
               (:replace
                (fnn-replace (fnn-bpck-publication-stage record)
                             (fnn-bpck-publication-final record)))
               (:fence
                (fnn-bps-checkpoint-publication-observe record :error)
                (return-from fnn-bps-checkpoint-publication-turn record))
               (:done (return-from fnn-bps-checkpoint-publication-turn record))
               (otherwise (fnn-fault "Invalid checkpoint publication action")))
             (fnn-bps-checkpoint-publication-observe record :ok))
         (error (condition)
           (setf (fnn-bpck-publication-failure record) condition)
           (handler-case
               (fnn-bps-checkpoint-publication-observe record :error)
             (error (core-condition)
               (setf (fnn-bpck-publication-core-failure record) core-condition)))))
    (setf (fnn-bpck-publication-source-result record) :returned))
  record)
