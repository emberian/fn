; The actual captured source portion of the online snapshot job.  Loaded
; after owner and history-auth-reader.  Publication remains the same job's
; next phase; this module never routes a cheap capture into the old eager
; twelve-field checkpoint writer.
(in-package "ACL2")

(defstruct (fnn-snapshot-job (:constructor %make-fnn-snapshot-job))
  service capture root maintenance canonical payload-view source reader provider
  observation completion log-position (log-phase :unfrozen) (phase :source) outcome
  census pending-row cold-mapping (pipeline-phase :census) writer key-cursor remapper
  (action-lock (sb-thread:make-mutex :name "snapshot action"))
  (returned :returned) (stage :none) account-publication hpi-stage initial-source initial-reader-token)
(defun fnn-snapshot-job-open (service captured root maintenance payload-view)
  "The caller holds the owner mutex and has admitted maintenance, acquired
ROOT, captured the Store and acquired PAYLOAD-VIEW in that order.  Borrow
that immutable source; no records accessor or history materializer is used."
  (%make-fnn-snapshot-job
   :service service :capture captured :root root :maintenance maintenance
   :payload-view payload-view :source (fnn-snapshot-source-begin captured)))


(defun %fnn-snapshot-recovery-job-open
    (service begun root maintenance payload-view)
  "Internal constructor after the actual operation allowance and root/view
acquisitions. BEGUN is the one returned fn-owner-recovery-census-begin packet;
it is not a supplied capture/ready tuple. Startup keeps its no-writer interval
until measurement/seal or definite joined cleanup. This source entry does not
install the still-missing INITIAL factory or publication capability."
  (destructuring-bind (word source collector) begun
    (unless (eq word :census)
      (fnn-refuse-io "recovery census begin unavailable: ~a" word))
    (%make-fnn-snapshot-job
     :service service :capture nil :root root :maintenance maintenance
     :payload-view payload-view :source source :canonical collector
     :remapper (fnn-core 'fn-omk-at 2 collector)
     :census (fnn-core 'fn-omk-at 3 collector))))

(defun fnn-snapshot-recovery-census-step (job)
  "One action of the existing source/remap/census pipeline, followed by the
actual retained collector offer/readout. The startup caller retains exclusive
Store custody; source-token checks alone cannot prove same-count nonmutation.
A lost token leaves every root and lease held. There is no writer restart here."
  (sb-thread:with-mutex ((fnn-snapshot-job-action-lock job))
    (let* ((service (fnn-snapshot-job-service job))
           (current (sb-thread:with-mutex ((fnn-owner-service-lock service))
                      (fnn-core-state 'fn-owner-recovery-census-current
                                      (fnn-snapshot-job-canonical job)))))
      (unless (eq (first current) :current)
        (return-from fnn-snapshot-recovery-census-step current))
      ; The core terminal transition is single-use. Retain its collector;
      ; calling the core readout again returns :pending, never a new result.
      (when (eq (fnn-core 'fn-omk-at 0 (fnn-snapshot-job-canonical job)) :measured)
        (return-from fnn-snapshot-recovery-census-step '(:retained :measured)))
      (setf (fnn-snapshot-job-returned job) :running)
      (unwind-protect
           (handler-case
               (let* ((action (%fnn-snapshot-job-source-step job))
                      (terminal (and (consp action) (eq (first action) :census-complete)))
                      (retained
                       (sb-thread:with-mutex ((fnn-owner-service-lock service))
                         (if terminal
                             (fnn-core-state 'fn-owner-recovery-census-readout
                              (fnn-snapshot-job-canonical job)
                              (fnn-snapshot-job-source job)
                              (fnn-snapshot-job-remapper job)
                              (fnn-snapshot-job-census job))
                           (fnn-core-state 'fn-owner-recovery-census-offer
                            (fnn-snapshot-job-canonical job)
                            (fnn-snapshot-job-source job)
                            (fnn-snapshot-job-remapper job)
                            (fnn-snapshot-job-census job))))))
                 (cond
                   ((eq (first retained) :retained)
                    (setf (fnn-snapshot-job-canonical job) (second retained))
                    action)
                   ((eq (first retained) :measured)
                    (setf (fnn-snapshot-job-canonical job) (third retained))
                    retained)
                   (t
                    ; Actual source steps may already have returned I/O.
                    ; Refusal cannot erase their held buffer or current root.
                    (setf (fnn-snapshot-job-phase job) :recovery-required
                          (fnn-snapshot-job-outcome job) :uncertain)
                    retained)))
             (fnn-snapshot-read-not-issued (condition)
               (setf (fnn-snapshot-job-outcome job) :refused)
               (error condition))
             (error (condition)
               (setf (fnn-snapshot-job-outcome job) :uncertain)
               (error condition)))
        (setf (fnn-snapshot-job-returned job) :returned)))))

(defun %fnn-snapshot-job-row-step (job)
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
                (let ((root-ticket
                        (sb-thread:with-mutex
                            ((fnn-owner-service-lock (fnn-snapshot-job-service job)))
                          (fnn-snapshot-source-root-ticket
                           (fnn-snapshot-job-service job) (fnn-snapshot-job-root job)))))
                  (multiple-value-bind (word reader receipt)
                      (if (fnn-snapshot-job-initial-source job)
                          (sb-thread:with-mutex
                              ((fnn-owner-service-lock (fnn-snapshot-job-service job)))
                            (fnn-snapshot-initial-reader-begin
                             (fnn-snapshot-job-service job)
                             (fnn-snapshot-job-initial-source job)
                             (fnn-snapshot-job-maintenance job) token root-ticket))
                        (fnn-hsr-source-begin
                         (fnn-core 'fn-hrs-h-rec handle) token root-ticket
                         (fnn-snapshot-job-maintenance job)))
                    (unless (eq word :idle)
                      (fnn-refuse-io "snapshot source reader refused: ~a" word))
                    ; Keep the core-issued custody token before exposing reader.
                    (setf (fnn-snapshot-job-initial-reader-token job) receipt
                          (fnn-snapshot-job-reader job) reader))))
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

(defun %fnn-snapshot-job-census-begin (job)
  (unless (fnn-snapshot-job-census job)
    (let ((source (fnn-snapshot-job-source job)))
      (setf (fnn-snapshot-job-census job)
            (fnn-core 'fn-hct-begin (fnn-core 'fn-osrc-at 3 source)
                      (fnn-core 'fn-osrc-at 10 source)
                      (fnn-snapshot-job-maintenance job)))
      (unless (fnn-snapshot-job-remapper job)
        (setf (fnn-snapshot-job-remapper job)
              (fnn-core 'fn-osm-begin (fnn-core 'fn-osrc-token source)))))))

(defun %fnn-snapshot-job-remap-row (job row)
  (destructuring-bind (word mapped next)
      (fnn-call 'fn-osm-prepare-row (fnn-snapshot-job-remapper job) row)
    (setf (fnn-snapshot-job-remapper job) next)
    (values word mapped)))

(defun %fnn-snapshot-job-census-cold-step (job current-child)
  "The actual census emitted CURRENT-CHILD; completion cannot invent one."
  (let* ((source (fnn-snapshot-job-source job))
         (token (fourth (fnn-snapshot-job-pending-row job))))
    (unless (fnn-snapshot-job-cold-mapping job)
      (setf (fnn-snapshot-job-cold-mapping job)
            (fnn-hsr-cold-begin (fnn-core 'fn-osrc-at 5 source) token
                                (fnn-snapshot-job-maintenance job))))
    (multiple-value-bind (word mapping)
        (fnn-hsr-cold-step (fnn-snapshot-job-service job)
                          (fnn-snapshot-job-root job)
                          (fnn-snapshot-job-maintenance job)
                          (fnn-snapshot-job-reader job)
                          (fnn-snapshot-job-cold-mapping job)
                          token current-child)
      (setf (fnn-snapshot-job-cold-mapping job) mapping)
      (if (and (consp word) (eq (first word) :supply))
          (destructuring-bind (verdict census)
              (fnn-call 'fn-hct-supply (fnn-snapshot-job-census job)
                        (second word) (third word))
            (setf (fnn-snapshot-job-census job) census)
            verdict)
        word))))

(defun %fnn-snapshot-job-key-begin (job)
  (let* ((row (fnn-snapshot-job-pending-row job))
         (answer (fnn-core 'fn-omk-begin (third row)
                           (fnn-core 'fn-osj-capture-image-salt
                                     (fnn-snapshot-job-capture job))
                           (fourth row) (fnn-snapshot-job-maintenance job))))
    (when (eq (first answer) :begun)
      (setf (fnn-snapshot-job-key-cursor job) (second answer)
            (fnn-snapshot-job-cold-mapping job) nil))
    answer))

(defun %fnn-snapshot-job-key-step (job)
  "Walk the offered row's Message-ID under the captured target genesis salt."
  (let* ((key (fnn-snapshot-job-key-cursor job))
         (answer (fnn-core 'fn-omk-tick key nil)))
    (case (first answer)
      (:continue
       (setf (fnn-snapshot-job-key-cursor job) (second answer))
       :yield)
      (:need-byte
       (let ((child (fnn-core 'fn-ocb-key-child key))
             (token (fourth (fnn-snapshot-job-pending-row job))))
         (unless (fnn-snapshot-job-cold-mapping job)
           (setf (fnn-snapshot-job-cold-mapping job)
                 (fnn-hsr-cold-begin
                  (fnn-core 'fn-osrc-at 5 (fnn-snapshot-job-source job))
                  token (fnn-snapshot-job-maintenance job))))
         (multiple-value-bind (word mapping)
             (fnn-hsr-cold-step (fnn-snapshot-job-service job)
                               (fnn-snapshot-job-root job)
                               (fnn-snapshot-job-maintenance job)
                               (fnn-snapshot-job-reader job)
                               (fnn-snapshot-job-cold-mapping job) token child)
           (setf (fnn-snapshot-job-cold-mapping job) mapping)
           (if (and (consp word) (eq (first word) :supply))
               (let ((next (fnn-core 'fn-omk-tick key
                                      (fnn-core 'fn-ocb-key-observation key word))))
                 (when (eq (first next) :continue)
                   (setf (fnn-snapshot-job-key-cursor job) (second next)))
                 next)
             word))))
      (otherwise answer))))

(defun %fnn-snapshot-job-emission-cold-step (job child)
  (let ((token (fourth (fnn-snapshot-job-pending-row job))))
    (unless (fnn-snapshot-job-cold-mapping job)
      (setf (fnn-snapshot-job-cold-mapping job)
            (fnn-hsr-cold-begin
             (fnn-core 'fn-osrc-at 5 (fnn-snapshot-job-source job))
             token (fnn-snapshot-job-maintenance job))))
    (multiple-value-bind (word mapping)
        (fnn-hsr-cold-step (fnn-snapshot-job-service job)
                          (fnn-snapshot-job-root job)
                          (fnn-snapshot-job-maintenance job)
                          (fnn-snapshot-job-reader job)
                          (fnn-snapshot-job-cold-mapping job) token child)
      (setf (fnn-snapshot-job-cold-mapping job) mapping)
      (when (and (consp word) (eq (first word) :supply))
        ; The writer consumes this scalar on the NEXT scheduling action.
        (setf (fnn-snapshot-job-observation job) word))
      word)))

(defun %fnn-snapshot-job-emission-step (job)
  "Fetch only on the actual funded writer's row demand; retain through ACK."
  (when (member (fnn-snapshot-job-outcome job) '(:refused :uncertain))
    (return-from %fnn-snapshot-job-emission-step
      (list (fnn-snapshot-job-outcome job) (fnn-snapshot-job-observation job))))
  (unless (fnn-snapshot-job-hpi-stage job)
    (fnn-fault "snapshot emission stage has not been installed"))
  (unless (fnn-snapshot-job-writer job)
    (fnn-fault "snapshot emission writer has not been installed"))
  (if (eq (fnn-snapshot-job-pipeline-phase job) :emission-key)
      (if (null (fnn-snapshot-job-key-cursor job))
          (%fnn-snapshot-job-key-begin job)
        (let ((key (%fnn-snapshot-job-key-step job)))
          (if (and (consp key) (eq (first key) :done))
              (let* ((row (fnn-snapshot-job-pending-row job))
                     (word (sb-thread:with-mutex (*fnn-extent-lock*)
                             (fnn-hpi-offer (fnn-snapshot-job-writer job)
                                            (second row) (third row)
                                            (fourth row) (second key)))))
                (when (eq word :started)
                  (setf (fnn-snapshot-job-pipeline-phase job) :emission-body
                        (fnn-snapshot-job-key-cursor job) nil
                        (fnn-snapshot-job-cold-mapping job) nil))
                word)
            key)))
    (let ((observation (fnn-snapshot-job-observation job)))
      (setf (fnn-snapshot-job-observation job) nil)
      (multiple-value-bind (word effect next-observation)
          (fnn-hpi-action (fnn-snapshot-job-writer job)
                          (fnn-snapshot-job-hpi-stage job) observation)
        (when (or next-observation (member word '(:write :io)))
          (setf (fnn-snapshot-job-observation job) next-observation)
          (case (fnn-core 'fn-hpi-effect-observation-disposition next-observation)
            (:ready
             (return-from %fnn-snapshot-job-emission-step :yield))
            (:refused
             (setf (fnn-snapshot-job-outcome job) :refused)
             (return-from %fnn-snapshot-job-emission-step
               (list :refused effect next-observation)))
            (otherwise
             (setf (fnn-snapshot-job-outcome job) :uncertain)
             (return-from %fnn-snapshot-job-emission-step
               (list :uncertain effect next-observation)))))
        (case word
          (:need-row
           (when (fnn-snapshot-job-pending-row job)
             (fnn-fault "snapshot writer requests next row before emitted-row ACK"))
           (let ((row (%fnn-snapshot-job-row-step job)))
             (when (and (consp row) (eq (first row) :row))
               (unless (and (eq (first effect) :source-row)
                            (fnn-core 'fn-omk-token-matchp (second effect) (fourth row)))
                 (fnn-fault "snapshot source row does not match writer demand"))
               (multiple-value-bind (word mapped)
                   (%fnn-snapshot-job-remap-row job row)
                 (unless (eq word :mapped)
                   (return-from %fnn-snapshot-job-emission-step word))
                 (setf (fnn-snapshot-job-pending-row job) mapped
                       (fnn-snapshot-job-key-cursor job) nil
                       (fnn-snapshot-job-cold-mapping job) nil
                       (fnn-snapshot-job-pipeline-phase job) :emission-key)))
             :yield))
          (:need-byte (%fnn-snapshot-job-emission-cold-step job effect))
          (:row-done
           (let ((row (fnn-snapshot-job-pending-row job)))
             (unless (and (eq (first effect) :row-emitted)
                          (fnn-core 'fn-omk-token-matchp
                                    (second effect) (fourth row)))
               (fnn-fault "snapshot emitted-row ACK does not bind pending row"))
             (destructuring-bind (ack remapper)
                 (fnn-call 'fn-osm-emission-ack (fnn-snapshot-job-remapper job) effect)
               (setf (fnn-snapshot-job-remapper job) remapper)
               (unless (eq ack :acknowledged)
                 (return-from %fnn-snapshot-job-emission-step ack)))
             (setf (fnn-snapshot-job-pending-row job) nil
                   (fnn-snapshot-job-key-cursor job) nil
                   (fnn-snapshot-job-cold-mapping job) nil
                   (fnn-snapshot-job-pipeline-phase job) :emission)
             row))
          (:continue :yield)
          (otherwise (list word effect)))))))
(defun %fnn-snapshot-job-source-step (job)
  "Hold each first-pass row until its actual canonical census completes."
  (if (member (fnn-snapshot-job-pipeline-phase job)
              '(:emission :emission-key :emission-body))
      (%fnn-snapshot-job-emission-step job)
    (progn
      (%fnn-snapshot-job-census-begin job)
      (if (fnn-snapshot-job-pending-row job)
          (destructuring-bind (word summary next)
              (fnn-call 'fn-hct-tick (fnn-snapshot-job-census job))
            (declare (ignore summary))
            (setf (fnn-snapshot-job-census job) next)
            (case word
              (:row-done
               (destructuring-bind (ack remapper)
                   (fnn-call 'fn-osm-census-ack (fnn-snapshot-job-remapper job) next)
                 (setf (fnn-snapshot-job-remapper job) remapper)
                 (if (eq ack :acknowledged)
                     (prog1 (fnn-snapshot-job-pending-row job)
                       (setf (fnn-snapshot-job-pending-row job) nil
                             (fnn-snapshot-job-cold-mapping job) nil))
                   ack)))
              (:continue :yield)
              (otherwise
               (if (and (consp word) (eq (first word) :need-byte))
                   (%fnn-snapshot-job-census-cold-step job word)
                 word))))
        (let ((answer (%fnn-snapshot-job-row-step job)))
          (cond
            ((and (consp answer) (eq (first answer) :row))
             (multiple-value-bind (remapped mapped)
                 (%fnn-snapshot-job-remap-row job answer)
               (unless (eq remapped :mapped)
                 (return-from %fnn-snapshot-job-source-step remapped))
               (setf (fnn-snapshot-job-pending-row job) mapped)
               (destructuring-bind (word census)
                   (fnn-call 'fn-hct-offer (fnn-snapshot-job-census job)
                             (second mapped) (third mapped))
                 (setf (fnn-snapshot-job-census job) census)
                 (if (eq word :started) :yield word))))
            ((and (consp answer) (eq (first answer) :done))
             (destructuring-bind (word summary census)
                 (fnn-call 'fn-hct-tick (fnn-snapshot-job-census job))
               (setf (fnn-snapshot-job-census job) census)
               (if (eq word :prepared) (list :census-complete summary) word)))
            (t answer)))))))

(defun %fnn-snapshot-job-restart-source (job)
  "Restart the actual drained source after the completed canonical census.
The caller holds the job action mutex; the retained reader/root are reused."
  (when (fnn-snapshot-job-pending-row job)
    (return-from %fnn-snapshot-job-restart-source '(:retained :census-row)))
  (destructuring-bind (word summary census)
      (fnn-call 'fn-hct-tick (fnn-snapshot-job-census job))
    (declare (ignore summary))
    (setf (fnn-snapshot-job-census job) census)
    (unless (eq word :prepared)
      (return-from %fnn-snapshot-job-restart-source word)))
  (let ((answer (fnn-core 'fn-osrc-restart (fnn-snapshot-job-source job))))
    (when (eq (first answer) :restarted)
      (setf (fnn-snapshot-job-source job) (second answer)
            (fnn-snapshot-job-remapper job)
            (fnn-core 'fn-osm-begin (fnn-core 'fn-osrc-token (second answer)))
            (fnn-snapshot-job-phase job) :source
            (fnn-snapshot-job-provider job) nil
            (fnn-snapshot-job-observation job) nil
            (fnn-snapshot-job-completion job) nil
            (fnn-snapshot-job-cold-mapping job) nil
            (fnn-snapshot-job-pipeline-phase job) :emission))
    answer))

(defun fnn-snapshot-job-restart-source (job)
  (sb-thread:with-mutex ((fnn-snapshot-job-action-lock job))
    (setf (fnn-snapshot-job-returned job) :running)
    (unwind-protect (%fnn-snapshot-job-restart-source job)
      (setf (fnn-snapshot-job-returned job) :returned))))

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
  ; The executing action has returned under ACTION-LOCK. Remove every
  ; census/codec/pending span authority before releasing its root file.
  ; A later cleanup failure cannot resume the cancelled pipeline.
  (setf (fnn-snapshot-job-phase job) :cancelling
        (fnn-snapshot-job-pipeline-phase job) :cancelling
        (fnn-snapshot-job-canonical job) nil
        (fnn-snapshot-job-account-publication job) nil
        (fnn-snapshot-job-remapper job) nil
          (fnn-snapshot-job-key-cursor job) nil
          (fnn-snapshot-job-census job) nil
        (fnn-snapshot-job-pending-row job) nil
        (fnn-snapshot-job-cold-mapping job) nil
        (fnn-snapshot-job-writer job) nil
        (fnn-snapshot-job-provider job) nil
        (fnn-snapshot-job-source job) nil
        (fnn-snapshot-job-observation job) nil
        (fnn-snapshot-job-completion job) nil)
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
    (let ((word (fnn-core 'fn-osj-cleanup-log-word
                          (fnn-snapshot-job-returned job)
                          (fnn-snapshot-job-stage job)
                          (fnn-snapshot-job-log-phase job))))
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

(define-condition fnn-snapshot-capture-uncertain (fnn-store-indeterminate)
  ((job :initarg :job :reader fnn-snapshot-capture-uncertain-job)))

(defun fnn-snapshot-job-freeze-log (job)
  "Caller holds the same owner control fence as capture. Retain the actual
rotation position, never infer its physical chain from an event count. The
job exists before rename/head I/O, so any thrown failure carries its held
source and resource authority to recovery."
  (let* ((store (fnn-owner-service-store (fnn-snapshot-job-service job)))
         (log (fnn-store-log store)))
    (handler-case
        (setf (fnn-snapshot-job-log-position job)
              (fnn-log-with-kernel (log) (fnn-log-rotate store))
              (fnn-snapshot-job-log-phase job)
              (fnn-core 'fn-osj-log-observation :rotation-returned))
      (error (condition)
        ; Generic failures from the existing rotation API do not expose a
        ; definite no-I/O result. Keep them uncertain, including the grant.
        (setf (fnn-snapshot-job-log-phase job)
              (fnn-core 'fn-osj-log-observation :rotation-threw)
              (fnn-snapshot-job-phase job) :recovery-required
              (fnn-snapshot-job-outcome job) :uncertain)
        (error 'fnn-snapshot-capture-uncertain :job job
               :message (format nil "snapshot log capture is uncertain: ~a" condition)))))
  job)

(defun fnn-snapshot-job-log-durable (job)
  "One returned publication barrier, off the owner mutex. F may name the
frozen position only after this actual existing log barrier returns. An
ambiguous barrier retains the job; cancellation does not erase it."
  (sb-thread:with-mutex ((fnn-snapshot-job-action-lock job))
    (let ((word (fnn-core 'fn-osj-log-fence-word (fnn-snapshot-job-log-phase job))))
      (unless (eq word :fence)
        (return-from fnn-snapshot-job-log-durable word))
      (setf (fnn-snapshot-job-returned job) :running)
      (unwind-protect
           (handler-case
               (progn
                 (fnn-log-make-durable
                  (fnn-store-log (fnn-owner-service-store (fnn-snapshot-job-service job))))
                 (setf (fnn-snapshot-job-log-phase job)
                       (fnn-core 'fn-osj-log-observation :rotation-durable))
                 :durable)
             (error (condition)
               (setf (fnn-snapshot-job-log-phase job)
                     (fnn-core 'fn-osj-log-observation :rotation-threw)
                     (fnn-snapshot-job-phase job) :recovery-required
                     (fnn-snapshot-job-outcome job) :uncertain)
               (error 'fnn-snapshot-capture-uncertain :job job
                      :message (format nil "snapshot log barrier is uncertain: ~a" condition))))
        (setf (fnn-snapshot-job-returned job) :returned)))))

(defun fnn-owner-snapshot-capture (service maintenance)
  "MAINTENANCE is an already admitted, operation-derived demand. Recheck
its exact live ledger binding before acquiring a root or capture. This
operational fence does not claim the complete rescue reserve is installed."
  (let ((captured nil) (canonical nil) (publication nil) (root nil) (view nil) (job nil))
    (unwind-protect
         (fnn-owner-gated (service :control)
           ; The retirement observation is read at the same serialized
           ; owner fence as capture, not at an earlier accept-loop poll.
           (unless (eq (fnn-core 'fn-ort-maintenance-action
                                 (fnn-owner-service-retire service)) :admit)
             (fnn-refuse-io "snapshot admission skipped during retirement"))
           (let* ((store (fnn-owner-service-store service))
                  (log (fnn-store-log store))
                  (context (fnn-snapshot-source-context))
                  (plan (fnn-core 'fn-osj-resource-word context maintenance)))
             ; The off-mutex publisher prepares its rotation spare first.
             ; This fence never performs preallocation or waits for it.
             (unless (fnn-log-with-kernel (log)
                       (and (fnn-core 'fn-lgc-rotate-admitsp (fnn-log-kernel log))
                            (fnn-log-rotation-ready-p store)))
               (fnn-refuse-io "snapshot log rotation is not ready"))
             (unless (eq (first plan) :capture)
               (fnn-refuse-io "snapshot capture refused: ~a" (second plan)))
             (unless (eq (first (fnn-core-page-read-pool
                                'fn-owner-maintenance-grow maintenance '(0 0 0 0 0))) :grown)
               (fnn-refuse-io "snapshot maintenance lease is not live"))
             (setq canonical (fnn-core-state 'fn-owner-osn-canonical-capture context))
             (unless (eq (first canonical) :ready)
               (fnn-refuse-io "snapshot canonical context is unavailable"))
             (setq publication
                   (fnn-core-state 'fn-owner-osn-consumer-publication-capture context))
             (unless (eq (first publication) :ok)
               (fnn-refuse-io "snapshot consumer publication is unavailable: ~a"
                             (second publication)))
             ; Private account preparation is not fully represented by CP/root.
             ; Keep its begin replay source held; do not capture a checkpoint.
             (let ((checkpoint-word
                     (fnn-core-state 'fn-owner-checkpoint-account-word)))
               (unless (eq checkpoint-word :checkpoint)
                 (fnn-refuse-io "snapshot deferred: account preparation pending")))
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
             (setf (fnn-snapshot-job-canonical job) canonical)
             (setf (fnn-snapshot-job-account-publication job) publication)
             (fnn-snapshot-job-freeze-log job)))
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
