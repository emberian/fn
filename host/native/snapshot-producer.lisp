; The actual captured source portion of the online snapshot job.  Loaded
; after owner and history-auth-reader.  Publication remains the same job's
; next phase; this module never routes a cheap capture into the old eager
; twelve-field checkpoint writer.
(in-package "ACL2")

(defstruct (fnn-snapshot-job (:constructor %make-fnn-snapshot-job))
  service capture root maintenance payload-view source reader provider
  observation completion (phase :source) outcome
  (action-lock (sb-thread:make-mutex :name "snapshot action"))
  (returned :returned) (stage :none))

(defun fnn-snapshot-job-open (service captured root maintenance payload-view)
  "The caller holds the owner mutex and has admitted maintenance, acquired
ROOT, captured the Store and acquired PAYLOAD-VIEW in that order.  Borrow
that immutable source; no records accessor or history materializer is used."
  (%make-fnn-snapshot-job
   :service service :capture captured :root root :maintenance maintenance
   :payload-view payload-view :source (fnn-snapshot-source-begin captured)))

(defun %fnn-snapshot-job-source-step (job)
  "One source/provider/auth-reader action. A row is offered once, with its
current source identity and parser-size completion; an opaque Store is never
compared or traversed to decide whether a completion belongs to this job."
  (let ((source (fnn-snapshot-job-source job)))
    (case (fnn-snapshot-job-phase job)
      (:source
       (let ((answer (fnn-core 'fn-osrc-tick source nil)))
         (case (first answer)
           (:yield (setf (fnn-snapshot-job-source job) (second answer)) :yield)
           (:row
            (setf (fnn-snapshot-job-source job) (fifth answer))
            answer)
           (:done (setf (fnn-snapshot-job-phase job) :source-done) answer)
           (:need-row
            (let* ((handle (third answer)) (token (fourth answer))
                   (provider (fnn-core 'fn-obp-begin handle token
                                       (fnn-snapshot-job-maintenance job))))
              (unless (fnn-snapshot-job-reader job)
                (multiple-value-bind (word reader)
                    (fnn-hsr-source-begin
                     (fnn-core 'fn-hrs-h-rec handle) token
                     (sb-thread:with-mutex
                         ((fnn-owner-service-lock (fnn-snapshot-job-service job)))
                       (fnn-snapshot-source-root-ticket
                        (fnn-snapshot-job-service job) (fnn-snapshot-job-root job)))
                     (fnn-snapshot-job-maintenance job))
                  (unless (eq word :idle)
                    (fnn-refuse-io "snapshot source reader refused: ~a" word))
                  (setf (fnn-snapshot-job-reader job) reader)))
              (setf (fnn-snapshot-job-source job) (fifth answer)
                    (fnn-snapshot-job-provider job) provider
                    (fnn-snapshot-job-phase job) :provider)
              :yield))
           (otherwise answer))))
      (:provider
       (let ((answer (fnn-core 'fn-obp-tick (fnn-snapshot-job-provider job)
                               (fnn-snapshot-job-observation job))))
         (setf (fnn-snapshot-job-observation job) nil)
         (case (first answer)
           (:yield (setf (fnn-snapshot-job-provider job) (second answer)) :yield)
           (:need-byte
            (multiple-value-bind (word observation)
                (fnn-hsr-source-step
                 (fnn-snapshot-job-service job) (fnn-snapshot-job-root job)
                 (fnn-snapshot-job-maintenance job) (fnn-snapshot-job-reader job)
                 (fnn-core 'fn-osrc-token source)
                 (fnn-core 'fn-obp-demand (fnn-snapshot-job-provider job)))
              ; Supplying this octet is a separate scheduling action. Reader
              ; output carries no vector alias, only the protected scalar.
              (when (eq word :ready)
                (setf (fnn-snapshot-job-observation job) observation))
              word))
           (:decoded
            (let ((row (fnn-core 'fn-osrc-tick source
                                 (list :decoded (second answer) (third answer)))))
              (setf (fnn-snapshot-job-completion job) (fourth answer))
              (when (eq (first row) :row)
                (setf (fnn-snapshot-job-source job) (fifth row)
                      (fnn-snapshot-job-provider job) nil
                      (fnn-snapshot-job-phase job) :source))
              row))
           (otherwise answer))))
      (:source-done '(:done))
      (otherwise '(:refused :source-phase)))))

(defun fnn-snapshot-job-source-step (job)
  "The action mutex covers the actual synchronous I/O return. Cleanup
cannot observe a timeout as a join or race a still-executing source step."
  (sb-thread:with-mutex ((fnn-snapshot-job-action-lock job))
    (setf (fnn-snapshot-job-returned job) :running)
    (unwind-protect
         (handler-case (%fnn-snapshot-job-source-step job)
           (fnn-snapshot-read-not-issued (condition)
             (setf (fnn-snapshot-job-outcome job) :refused)
             (error condition))
           (error (condition)
             (setf (fnn-snapshot-job-outcome job) :uncertain)
             (error condition)))
      (setf (fnn-snapshot-job-returned job) :returned))))

(defun fnn-snapshot-job-release-source (job)
  "Only after the executing source action has actually returned/joined.
Release every reader alias first, then its exact root-file incarnation.
An exception leaves the job's remaining leases for recovery/definite cleanup."
  (let ((reader (fnn-snapshot-job-reader job)))
    (when reader
      ; This is cancellation/terminal joined cleanup, not ordinary page
      ; replacement. The reader first fences the current digest/byte phase.
      (let ((settled (fnn-hsr-source-cancel-returned
                      reader (fnn-snapshot-job-outcome job))))
        (unless (member settled '(:released :closed))
          (fnn-fault "snapshot reader cleanup retains ownership: ~a" settled)))
      (setf (fnn-snapshot-job-reader job) nil)))
  (when (fnn-snapshot-job-root job)
    (fnn-snapshot-source-root-release (fnn-snapshot-job-service job)
                                      (fnn-snapshot-job-root job))
    (setf (fnn-snapshot-job-root job) nil))
  :source-released)

(defun fnn-snapshot-job-cleanup (job)
  "Settle a returned source job in ownership order. Staged effects, when
present, must already have a definite deleted/published core observation.
Every field is cleared only after its actual release succeeds; failures
retain the rest of the job for retry or recovery."
  (sb-thread:with-mutex ((fnn-snapshot-job-action-lock job))
    (let ((word (fnn-core 'fn-osj-cleanup-word
                          (fnn-snapshot-job-returned job)
                          (fnn-snapshot-job-stage job))))
      (unless (eq (first word) :release)
        (return-from fnn-snapshot-job-cleanup word))
      (fnn-snapshot-job-release-source job)
      (let ((service (fnn-snapshot-job-service job)))
        (sb-thread:with-mutex ((fnn-owner-service-lock service))
          (when (fnn-snapshot-job-payload-view job)
            (let ((released (fnn-snapshot-payload-view-release
                             (fnn-snapshot-job-payload-view job) :joined)))
              (unless (eq (first released) :released)
                (return-from fnn-snapshot-job-cleanup released)))
            (setf (fnn-snapshot-job-payload-view job) nil))
          (when (fnn-snapshot-job-capture job)
            (let ((released (fnn-core-state
                             'fn-owner-osn-release
                             (fnn-core 'fn-osj-capture-ticket (fnn-snapshot-job-capture job)))))
              (unless (eq (first released) :released)
                (return-from fnn-snapshot-job-cleanup released)))
            (setf (fnn-snapshot-job-capture job) nil))))
      (when (fnn-snapshot-job-maintenance job)
        (let ((settled (fnn-core-page-read-pool
                        'fn-owner-maintenance-release (fnn-snapshot-job-maintenance job))))
          (unless (eq (first settled) :released)
            (return-from fnn-snapshot-job-cleanup settled))
          (setf (fnn-snapshot-job-maintenance job) nil)))
      (setf (fnn-snapshot-job-source job) nil
            (fnn-snapshot-job-provider job) nil
            (fnn-snapshot-job-observation job) nil
            (fnn-snapshot-job-completion job) nil
            (fnn-snapshot-job-phase job) :released)
      '(:released))))

(defun fnn-owner-snapshot-capture (service maintenance)
  "MAINTENANCE is an already admitted, operation-derived demand. Recheck
its exact live ledger binding before acquiring a root or capture. This
operational fence does not claim the complete rescue reserve is installed."
  (let ((captured nil) (root nil) (view nil) (job nil))
    (unwind-protect
         (fnn-owner-gated (service :control)
           (let ((plan (fnn-core 'fn-osj-resource-word
                                (fnn-snapshot-source-context) maintenance)))
             (unless (eq (first plan) :capture)
               (fnn-refuse-io "snapshot capture refused: ~a" (second plan)))
             (unless (eq (first (fnn-core-page-read-pool
                                'fn-owner-maintenance-grow maintenance '(0 0 0 0 0))) :grown)
               (fnn-refuse-io "snapshot maintenance lease is not live"))
             (when (second plan)
               (setq root (fnn-snapshot-source-root-acquire service (second plan) maintenance)))
             (setq captured (fnn-core-state 'fn-owner-osn-capture))
             (unless (eq (first captured) :captured)
               (fnn-refuse-io "snapshot capture refused: ~a" (second captured)))
             (multiple-value-bind (word holder)
                 (fnn-snapshot-payload-view-acquire service maintenance)
               (unless (eq word :acquired)
                 (fnn-refuse-io "snapshot payload view refused: ~a" word))
               (setq view holder))
             (setq job (fnn-snapshot-job-open service captured root maintenance view))
             job))
      ; No worker exists yet on this refusal path. The owner gate has
      ; returned before these cleanup calls acquire it again.
      (unless job
        (when root (fnn-snapshot-source-root-release service root))
        (when captured
          (sb-thread:with-mutex ((fnn-owner-service-lock service))
            (when view (fnn-snapshot-payload-view-release view :joined))
            (when (eq (first captured) :captured)
              (fnn-core-state 'fn-owner-osn-release
                              (fnn-core 'fn-osj-capture-ticket captured)))))))))
