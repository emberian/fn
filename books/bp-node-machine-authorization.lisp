; Exact durable-effect authorization for the host-called BP lifecycle.
(in-package "ACL2")
(include-book "bp-node-machine-invariants")

; A proposal records every externally observable result before the host is
; asked to persist it.  This predicate binds those results to the exact
; lifecycle record and, where needed, to the retained job that authorizes a
; send.  Merely well-typed effects are deliberately insufficient.
(defun fn-bpn-proposal-effectsp (st record success refusal uncertain)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((kind (fn-cbor-ag-car record))
         (key (fn-bpn-record-key record))
         (work (nth 0 key))
         (attempt (nth 1 key))
         (generation (nth 2 key))
         (job (fn-bpn-find-job key (fn-bpn-machine-state-jobs st))))
    (cond
     ((equal kind :queued)
      (let ((queued (nth 2 record)))
        (and
         (equal success
                (list (list :bundle-queue-accepted
                            (fn-bpn-job-work-id queued)
                            (fn-bpn-job-attempt-id queued)
                            (fn-bpn-job-generation queued)
                            (fn-bpn-job-sequence queued)
                            :durable)))
         (equal refusal
                (list :bundle-queue-refused
                      (fn-bpn-job-work-id queued)
                      (fn-bpn-job-attempt-id queued)
                      (fn-bpn-job-generation queued)
                      :persistence-refused))
         (equal uncertain
                (list :bundle-queue-uncertain
                      (fn-bpn-job-work-id queued)
                      (fn-bpn-job-attempt-id queued)
                      (fn-bpn-job-generation queued)
                      :persistence)))))
     ((equal kind :attempting)
      (and job
           (equal (fn-bpn-job-status job) :queued)
           (equal success
                  (list (list :cl-send (fn-bpn-job-route job)
                              (fn-bpn-job-peer job) key
                              (fn-bpn-job-wire job))))
           (equal refusal
                  (list :bundle-queue-refused work attempt generation
                        :attempt-persistence-refused))
           (equal uncertain
                  (list :bundle-queue-uncertain work attempt generation
                        :attempt-persistence))))
     ((equal kind :requeued)
      (and job
           (equal (fn-bpn-job-status job) :attempting)
           (equal success
                  (list (list :transport work attempt generation :attempted)
                        (list :forward-refused work attempt generation
                              (nth 5 record))))
           (equal refusal
                  (list :bundle-queue-refused work attempt generation
                        :result-persistence-refused))
           (equal uncertain
                  (list :bundle-queue-uncertain work attempt generation
                        :result-persistence))))
     ((equal kind :finished)
      (and job
           (equal (fn-bpn-job-status job) :attempting)
           (equal success
                  (list (list :transport work attempt generation :forwarded)))
           (equal refusal
                  (list :bundle-queue-refused work attempt generation
                        :result-persistence-refused))
           (equal uncertain
                  (list :bundle-queue-uncertain work attempt generation
                        :result-persistence))))
     ((equal kind :expired)
      (and job
           (fn-bpn-member (fn-bpn-job-status job) '(:queued :attempting))
           (equal success
                  (list (list :transport work attempt generation :expired)))
           (equal refusal
                  (list :bundle-queue-refused work attempt generation
                        :expiry-persistence-refused))
           (equal uncertain
                  (list :bundle-queue-uncertain work attempt generation
                        :expiry-persistence))))
     (t nil))))

(defun fn-bpn-pending-authorizedp (st)
  (declare (xargs :guard t :verify-guards nil))
  (let ((pending (fn-bpn-machine-state-pending st)))
    (or
     (null pending)
     (and
      (equal (fn-bpn-pending-token pending)
             (fn-bpn-record-token (fn-bpn-pending-record pending)))
      (fn-bpn-record-applicablep st (fn-bpn-pending-record pending))
      (fn-bpn-proposal-effectsp
       st
       (fn-bpn-pending-record pending)
       (fn-bpn-pending-success-effects pending)
       (fn-bpn-pending-refusal-effect pending)
       (fn-bpn-pending-uncertainty-effect pending))))))

(defun fn-bpn-lifecycle-invariantp (st)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-bpn-machine-invariantp st)
       (fn-bpn-pending-authorizedp st)))

(defthm fn-bpn-lifecycle-invariant-implies-machine-invariant
  (implies (fn-bpn-lifecycle-invariantp st)
           (fn-bpn-machine-invariantp st))
  :hints (("Goal" :in-theory
           (union-theories '(fn-bpn-lifecycle-invariantp)
                           (theory 'minimal-theory)))))

(defthm fn-bpn-lifecycle-invariant-without-pending
  (implies (and (fn-bpn-machine-invariantp st)
                (not (fn-bpn-machine-state-pending st)))
           (fn-bpn-lifecycle-invariantp st))
  :hints (("Goal" :in-theory
           (union-theories
            '(fn-bpn-lifecycle-invariantp fn-bpn-pending-authorizedp)
            (theory 'minimal-theory)))))

(defthm fn-bpn-initial-machine-state-has-lifecycle-invariant
  (implies
   (and (fn-bpn-configp config)
        (fn-bpn-machine-limitp max-jobs)
        (fn-bpn-machine-limitp max-octets))
   (fn-bpn-lifecycle-invariantp
    (fn-bpn-initial-machine-state config max-jobs max-octets)))
  :hints
  (("Goal"
    :use ((:instance fn-bpn-initial-machine-state-has-invariant))
    :in-theory
    (union-theories
     '(fn-bpn-lifecycle-invariantp fn-bpn-pending-authorizedp
       fn-bpn-initial-machine-state fn-bpn-machine-constructor-accessors)
     (theory 'minimal-theory)))))

(defthm fn-bpn-proposal-effectsp-of-metadata-state-with
  (equal
   (fn-bpn-proposal-effectsp
    (fn-bpn-state-with
     st (fn-bpn-machine-state-jobs st) contacts pending fenced next-token)
    record success refusal uncertain)
   (fn-bpn-proposal-effectsp st record success refusal uncertain))
  :hints
  (("Goal"
    :in-theory
    (union-theories
     '(fn-bpn-proposal-effectsp fn-bpn-state-with-accessors)
     (theory 'minimal-theory)))))

(defthm fn-bpn-record-applicable-implies-token
  (implies (fn-bpn-record-applicablep st record)
           (equal (fn-bpn-record-token record)
                  (fn-bpn-machine-state-next-token st)))
  :hints
  (("Goal" :in-theory
    (union-theories '(fn-bpn-record-applicablep)
                    (theory 'minimal-theory)))))

(defthm fn-bpn-propose-preserves-lifecycle-invariant
  (implies
   (and (fn-bpn-lifecycle-invariantp st)
        (fn-bpn-lifecycle-recordp record)
        (fn-bpn-record-applicablep st record)
        (fn-bpn-proposal-effectsp st record success refusal uncertain)
        (fn-bpn-effect-listp success)
        (fn-bpn-effectp refusal)
        (fn-bpn-effectp uncertain))
   (fn-bpn-lifecycle-invariantp
    (fn-bpn-answer-state
     (fn-bpn-propose st record success refusal uncertain))))
  :hints
  (("Goal"
    :use
    ((:instance fn-bpn-lifecycle-invariant-implies-machine-invariant)
     (:instance fn-bpn-propose-preserves-machine-invariant))
    :in-theory
    (union-theories
     '(fn-bpn-lifecycle-invariantp fn-bpn-pending-authorizedp
       fn-bpn-propose fn-bpn-answer-constructor-accessors
       fn-bpn-state-with-accessors fn-bpn-pending-constructor-accessors
       fn-bpn-record-applicablep-of-metadata-state-with
       fn-bpn-proposal-effectsp-of-metadata-state-with
       fn-bpn-record-applicable-implies-token)
     (theory 'minimal-theory)))))

(defthm fn-bpn-enqueue-proposal-is-authorized
  (implies
   (and (fn-bpn-machine-invariantp st)
        (not (fn-bpn-machine-state-fenced st))
        (not (fn-bpn-machine-state-pending st))
        (fn-bpn-keyp (list work attempt generation))
        (fn-bpp-timep sequence)
        (fn-bpn-routep route)
        (fn-bpp-eidp peer)
        (fn-bpb-datap adu)
        (fn-clock-observationp obs)
        (not (fn-bpn-find-job (list work attempt generation)
                              (fn-bpn-machine-state-jobs st)))
        (< (len (fn-bpn-machine-state-jobs st))
           (fn-bpn-machine-state-max-jobs st))
        (<= (len (fn-bpn-send (fn-bpn-machine-state-config st)
                              peer adu sequence obs))
            *fn-bpn-machine-max-job-octets*)
        (<= (+ (fn-bpn-jobs-octets (fn-bpn-machine-state-jobs st))
               (len (fn-bpn-send (fn-bpn-machine-state-config st)
                                 peer adu sequence obs)))
            (fn-bpn-machine-state-max-octets st)))
   (let* ((token (fn-bpn-machine-state-next-token st))
          (bundle (fn-bpn-send-bundle (fn-bpn-machine-state-config st)
                                      peer adu sequence obs))
          (wire (fn-bpn-send (fn-bpn-machine-state-config st)
                             peer adu sequence obs))
          (job (fn-bpn-make-job work attempt generation sequence
                                (fn-bpn-anchor-of bundle obs) peer route
                                bundle wire :queued token))
          (record (list :queued token job))
          (success
           (list (list :bundle-queue-accepted work attempt generation
                       sequence :durable)))
          (refusal
           (list :bundle-queue-refused work attempt generation
                 :persistence-refused))
          (uncertain
           (list :bundle-queue-uncertain work attempt generation
                 :persistence)))
     (and (fn-bpn-lifecycle-recordp record)
          (fn-bpn-record-applicablep st record)
          (fn-bpn-proposal-effectsp st record success refusal uncertain)
          (fn-bpn-effect-listp success)
          (fn-bpn-effectp refusal)
          (fn-bpn-effectp uncertain))))
  :hints
  (("Goal"
    :use
    ((:instance fn-bpn-lifecycle-invariant-implies-machine-invariant)
     (:instance fn-bpn-machine-invariant-components)
     (:instance fn-bpn-machine-statep-components)
     (:instance fn-bpn-enqueue-record-is-typed
                (config (fn-bpn-machine-state-config st))
                (token (fn-bpn-machine-state-next-token st))))
    :in-theory
    (union-theories
     '(fn-bpn-record-applicablep fn-bpn-proposal-effectsp
       fn-bpn-record-key fn-bpn-record-token fn-bpn-nth fn-bpn-job-key
       fn-bpn-job-work-id-of-fn-bpn-make-job
       fn-bpn-job-attempt-id-of-fn-bpn-make-job
       fn-bpn-job-generation-of-fn-bpn-make-job
       fn-bpn-job-sequence-of-fn-bpn-make-job
       fn-bpn-job-wire-of-fn-bpn-make-job
       fn-bpn-effect-listp fn-bpn-effectp fn-bpn-member
       fn-cbor-ag-car car-cons cdr-cons true-listp len nth zp natp)
     (theory 'minimal-theory)))))

(defthm fn-bpn-enqueue-step-preserves-lifecycle-invariant
  (implies
   (fn-bpn-lifecycle-invariantp st)
   (fn-bpn-lifecycle-invariantp
    (fn-bpn-answer-state
     (fn-bpn-enqueue-step st work attempt generation sequence
                          route peer adu obs))))
  :hints
  (("Goal"
    :use
    ((:instance fn-bpn-lifecycle-invariant-implies-machine-invariant)
     (:instance fn-bpn-machine-invariant-components)
     (:instance fn-bpn-machine-statep-components)
     (:instance fn-bpn-enqueue-proposal-is-authorized))
    :in-theory
    (union-theories
     '(fn-bpn-enqueue-step fn-bpn-propose-preserves-lifecycle-invariant
       fn-bpn-enqueue-record-is-typed fn-bpn-answer-constructor-accessors
       fn-bpn-record-applicablep fn-bpn-proposal-effectsp
       fn-bpn-record-key fn-bpn-record-token fn-bpn-nth fn-bpn-job-key
       fn-bpn-job-key-accessors fn-bpn-job-exactp
       fn-bpn-job-work-id-of-fn-bpn-make-job
       fn-bpn-job-attempt-id-of-fn-bpn-make-job
       fn-bpn-job-generation-of-fn-bpn-make-job
       fn-bpn-job-sequence-of-fn-bpn-make-job
       fn-bpn-effect-listp-of-singleton fn-bpn-effectp fn-bpn-member
       car-cons cdr-cons true-listp len nth zp)
     (theory 'minimal-theory)))))

(defthm fn-bpn-peer-of-find-queued-for-peer
  (implies (fn-bpn-find-queued-for-peer peer jobs)
           (equal (fn-bpn-job-peer
                   (fn-bpn-find-queued-for-peer peer jobs))
                  peer))
  :hints
  (("Goal" :induct (fn-bpn-find-queued-for-peer peer jobs)
    :in-theory (enable fn-bpn-find-queued-for-peer))))

(defthm fn-bpn-find-job-of-find-queued-for-peer
  (implies (and (fn-bpn-job-listp jobs)
                (fn-bpn-find-queued-for-peer peer jobs))
           (equal
            (fn-bpn-find-job
             (fn-bpn-job-key (fn-bpn-find-queued-for-peer peer jobs))
             jobs)
            (fn-bpn-find-queued-for-peer peer jobs)))
  :hints
  ;; The job recognizer and its field predicates opened in every case
  ;; (354,000 steps); the argument needs only key uniqueness.
  (("Goal" :induct (fn-bpn-find-queued-for-peer peer jobs)
    :in-theory
    (union-theories '(fn-bpn-find-queued-for-peer fn-bpn-find-job
                      fn-bpn-job-listp fn-bpn-job-key-memberp)
                    (theory 'minimal-theory)))))

(defthm fn-bpn-attempt-proposal-is-authorized
  (implies
   (and (fn-bpn-machine-invariantp st)
        (not (fn-bpn-machine-state-pending st))
        (fn-bpn-jobp job)
        (equal (fn-bpn-job-status job) :queued)
        (equal (fn-bpn-job-peer job) peer)
        (equal (fn-bpn-find-job (fn-bpn-job-key job)
                                (fn-bpn-machine-state-jobs st))
               job))
   (let* ((token (fn-bpn-machine-state-next-token st))
          (key (fn-bpn-job-key job))
          (record (list :attempting token
                        (nth 0 key) (nth 1 key) (nth 2 key)))
          (success
           (list (list :cl-send (fn-bpn-job-route job) peer key
                       (fn-bpn-job-wire job))))
          (refusal
           (list :bundle-queue-refused (nth 0 key) (nth 1 key) (nth 2 key)
                 :attempt-persistence-refused))
          (uncertain
           (list :bundle-queue-uncertain (nth 0 key) (nth 1 key) (nth 2 key)
                 :attempt-persistence)))
     (and (fn-bpn-lifecycle-recordp record)
          (fn-bpn-record-applicablep st record)
          (fn-bpn-proposal-effectsp st record success refusal uncertain)
          (fn-bpn-effect-listp success)
          (fn-bpn-effectp refusal)
          (fn-bpn-effectp uncertain))))
  :hints
  (("Goal"
    :use
    ((:instance fn-bpn-machine-invariant-components)
     (:instance fn-bpn-machine-statep-components)
     (:instance fn-bpn-attempting-record-is-typed
                (token (fn-bpn-machine-state-next-token st))))
    :in-theory
    (union-theories
     '(fn-bpn-record-applicablep fn-bpn-proposal-effectsp
       fn-bpn-record-key fn-bpn-record-token fn-bpn-nth
       fn-bpn-job-key fn-bpn-job-key-accessors
       fn-bpn-job-accessors-forward-consp
       fn-bpn-effect-listp fn-bpn-effectp
       fn-bpn-member fn-cbor-ag-car car-cons cdr-cons true-listp
       len nth zp natp)
     (theory 'minimal-theory)))))

(defthm fn-bpn-start-one-preserves-lifecycle-invariant
  (implies
   (fn-bpn-lifecycle-invariantp st)
   (fn-bpn-lifecycle-invariantp
    (fn-bpn-answer-state (fn-bpn-start-one st peer))))
  :hints
  (("Goal"
    :use
    ((:instance fn-bpn-lifecycle-invariant-implies-machine-invariant)
     (:instance fn-bpn-machine-invariant-components)
     (:instance fn-bpn-machine-statep-components)
     (:instance fn-bpn-find-queued-for-peer-is-a-job
                (jobs (fn-bpn-machine-state-jobs st)))
     (:instance fn-bpn-peer-of-find-queued-for-peer
                (jobs (fn-bpn-machine-state-jobs st)))
     (:instance fn-bpn-find-job-of-find-queued-for-peer
                (jobs (fn-bpn-machine-state-jobs st)))
     (:instance fn-bpn-attempt-proposal-is-authorized
                (job (fn-bpn-find-queued-for-peer
                      peer (fn-bpn-machine-state-jobs st)))))
    :in-theory
    (union-theories
     '(fn-bpn-start-one fn-bpn-propose-preserves-lifecycle-invariant
       fn-bpn-attempting-record-is-typed fn-bpn-answer-constructor-accessors
       fn-bpn-record-applicablep fn-bpn-proposal-effectsp
       fn-bpn-record-key fn-bpn-record-token fn-bpn-nth
       fn-bpn-job-key-accessors fn-bpn-key-of-found-job
       fn-bpn-effect-listp-of-singleton fn-bpn-effectp fn-bpn-member
       fn-cbor-ag-car car-cons cdr-cons true-listp len nth zp natp)
     (theory 'minimal-theory)))))

(defthm fn-bpn-contact-state-with-preserves-lifecycle-invariant
  (implies
   (and (fn-bpn-lifecycle-invariantp st)
        (not (fn-bpn-machine-state-pending st))
        (fn-bpn-contact-listp contacts))
   (fn-bpn-lifecycle-invariantp
    (fn-bpn-state-with
     st (fn-bpn-machine-state-jobs st) contacts nil
     (fn-bpn-machine-state-fenced st)
     (fn-bpn-machine-state-next-token st))))
  :hints
  (("Goal"
    :use
    ((:instance fn-bpn-lifecycle-invariant-implies-machine-invariant)
     (:instance fn-bpn-contact-state-with-preserves-machine-invariant))
    :in-theory
    (union-theories
     '(fn-bpn-lifecycle-invariant-without-pending
       fn-bpn-state-with-accessors)
     (theory 'minimal-theory)))))

(defthm fn-bpn-contact-step-preserves-lifecycle-invariant
  (implies
   (fn-bpn-lifecycle-invariantp st)
   (fn-bpn-lifecycle-invariantp
    (fn-bpn-answer-state (fn-bpn-contact-step st peer openp))))
  :hints
  (("Goal"
    :use
    ((:instance fn-bpn-lifecycle-invariant-implies-machine-invariant)
     (:instance fn-bpn-machine-invariant-components)
     (:instance fn-bpn-machine-statep-components)
     (:instance fn-bpn-contact-state-with-preserves-lifecycle-invariant
                (contacts
                 (fn-bpn-open-contact
                  peer (fn-bpn-machine-state-contacts st))))
     (:instance fn-bpn-contact-state-with-preserves-lifecycle-invariant
                (contacts
                 (fn-bpn-close-contact
                  peer (fn-bpn-machine-state-contacts st)))))
    :in-theory
    (union-theories
     '(fn-bpn-contact-step fn-bpn-start-one-preserves-lifecycle-invariant
       fn-bpn-open-contact-preserves-contact-listp
       fn-bpn-close-contact-preserves-contact-listp
       fn-bpn-answer-constructor-accessors)
     (theory 'minimal-theory)))))

(defthm fn-bpn-persist-result-step-preserves-lifecycle-invariant
  (implies
   (fn-bpn-lifecycle-invariantp st)
   (fn-bpn-lifecycle-invariantp
    (fn-bpn-answer-state
     (fn-bpn-persist-result-step st token outcome))))
  :hints
  (("Goal"
    :use
    ((:instance fn-bpn-lifecycle-invariant-implies-machine-invariant)
     (:instance fn-bpn-persist-result-step-preserves-machine-invariant))
    :in-theory
    (union-theories
     '(fn-bpn-persist-result-step
       fn-bpn-lifecycle-invariant-without-pending
       fn-bpn-apply-record fn-bpn-state-with-accessors
       fn-bpn-answer-constructor-accessors)
     (theory 'minimal-theory)))))

(defthm fn-bpn-restart-step-preserves-lifecycle-invariant
  (implies
   (and (fn-bpn-lifecycle-invariantp st)
        (true-listp records)
        (<= (len records) *fn-bpn-machine-max-records*))
   (fn-bpn-lifecycle-invariantp
    (fn-bpn-answer-state
     (fn-bpn-restart-step st records sequence-ready))))
  :hints
  (("Goal"
    :use
    ((:instance fn-bpn-lifecycle-invariant-implies-machine-invariant)
     (:instance fn-bpn-restart-step-preserves-machine-invariant))
    :in-theory
    (union-theories
     '(fn-bpn-restart-step fn-bpn-replay-records
       fn-bpn-lifecycle-invariant-without-pending
       fn-bpn-state-with-accessors fn-bpn-answer-constructor-accessors)
     (theory 'minimal-theory)))))

(defthm fn-bpn-true-list-of-length-three-reconstruction
  (implies (and (true-listp values)
                (equal (len values) 3))
           (equal (list (nth 0 values) (nth 1 values) (nth 2 values))
                  values))
  :hints
  (("Goal"
    :do-not-induct t
    :cases ((consp values)
            (consp (cdr values))
            (consp (cddr values))
            (consp (cdddr values)))
    :expand ((len values) (len (cdr values))
             (len (cddr values)) (len (cdddr values))
             (true-listp values) (true-listp (cdr values))
             (true-listp (cddr values)) (true-listp (cdddr values)))
    :in-theory (enable true-listp len nth zp))))

(defthm fn-bpn-key-reconstruction
  (implies (fn-bpn-keyp key)
           (equal (list (nth 0 key) (nth 1 key) (nth 2 key)) key))
  :hints
  (("Goal"
    :use ((:instance fn-bpn-true-list-of-length-three-reconstruction
                     (values key)))
    :in-theory
    (union-theories '(fn-bpn-keyp)
                    (theory 'minimal-theory)))))

(defthm fn-bpn-finished-proposal-is-authorized
  (implies
   (and (fn-bpn-machine-invariantp st)
        (not (fn-bpn-machine-state-pending st))
        (fn-bpn-keyp key)
        (fn-bpn-find-job key (fn-bpn-machine-state-jobs st))
        (equal (fn-bpn-job-status
                (fn-bpn-find-job key (fn-bpn-machine-state-jobs st)))
               :attempting))
   (let* ((token (fn-bpn-machine-state-next-token st))
          (record (list :finished token (nth 0 key) (nth 1 key) (nth 2 key)
                        :none :finished))
          (success (list (list :transport (nth 0 key) (nth 1 key)
                               (nth 2 key) :forwarded)))
          (refusal (list :bundle-queue-refused (nth 0 key) (nth 1 key)
                         (nth 2 key) :result-persistence-refused))
          (uncertain (list :bundle-queue-uncertain (nth 0 key) (nth 1 key)
                           (nth 2 key) :result-persistence)))
     (and (fn-bpn-lifecycle-recordp record)
          (fn-bpn-record-applicablep st record)
          (fn-bpn-proposal-effectsp st record success refusal uncertain)
          (fn-bpn-effect-listp success)
          (fn-bpn-effectp refusal)
          (fn-bpn-effectp uncertain))))
  :hints
  (("Goal"
    :use
    ((:instance fn-bpn-machine-invariant-components)
     (:instance fn-bpn-machine-statep-components)
     (:instance fn-bpn-key-reconstruction)
     (:instance fn-bpn-terminal-record-is-typed
                (token (fn-bpn-machine-state-next-token st))
                (kind :finished) (reason :none)))
    :in-theory
    (union-theories
     '(fn-bpn-record-applicablep fn-bpn-proposal-effectsp
       fn-bpn-record-key fn-bpn-record-token fn-bpn-nth
       fn-bpn-key-reconstruction
       fn-bpn-effect-listp fn-bpn-effectp fn-bpn-member
       fn-cbor-ag-car car-cons cdr-cons true-listp len nth zp natp)
     (theory 'minimal-theory)))))

(defthm fn-bpn-requeued-proposal-is-authorized
  (implies
   (and (fn-bpn-machine-invariantp st)
        (not (fn-bpn-machine-state-pending st))
        (fn-bpn-keyp key)
        (fn-bpn-find-job key (fn-bpn-machine-state-jobs st))
        (equal (fn-bpn-job-status
                (fn-bpn-find-job key (fn-bpn-machine-state-jobs st)))
               :attempting)
        (fn-bpn-member reason '(:refused :failed :uncertain)))
   (let* ((token (fn-bpn-machine-state-next-token st))
          (record (list :requeued token (nth 0 key) (nth 1 key) (nth 2 key)
                        reason :requeued))
          (success (list (list :transport (nth 0 key) (nth 1 key)
                               (nth 2 key) :attempted)
                         (list :forward-refused (nth 0 key) (nth 1 key)
                               (nth 2 key) reason)))
          (refusal (list :bundle-queue-refused (nth 0 key) (nth 1 key)
                         (nth 2 key) :result-persistence-refused))
          (uncertain (list :bundle-queue-uncertain (nth 0 key) (nth 1 key)
                           (nth 2 key) :result-persistence)))
     (and (fn-bpn-lifecycle-recordp record)
          (fn-bpn-record-applicablep st record)
          (fn-bpn-proposal-effectsp st record success refusal uncertain)
          (fn-bpn-effect-listp success)
          (fn-bpn-effectp refusal)
          (fn-bpn-effectp uncertain))))
  :hints
  (("Goal"
    :use
    ((:instance fn-bpn-machine-invariant-components)
     (:instance fn-bpn-machine-statep-components)
     (:instance fn-bpn-key-reconstruction)
     (:instance fn-bpn-terminal-record-is-typed
                (token (fn-bpn-machine-state-next-token st))
                (kind :requeued)))
    :in-theory
    (union-theories
     '(fn-bpn-record-applicablep fn-bpn-proposal-effectsp
       fn-bpn-record-key fn-bpn-record-token fn-bpn-nth
       fn-bpn-key-reconstruction
       fn-bpn-effect-listp fn-bpn-effect-listp-of-pair
       fn-bpn-effectp fn-bpn-member fn-cbor-ag-car
       car-cons cdr-cons true-listp len nth zp natp)
     (theory 'minimal-theory)))))

(defthm fn-bpn-forward-result-step-preserves-lifecycle-invariant
  (implies
   (fn-bpn-lifecycle-invariantp st)
   (fn-bpn-lifecycle-invariantp
    (fn-bpn-answer-state (fn-bpn-forward-result-step st key outcome))))
  :hints
  (("Goal"
    :use
    ((:instance fn-bpn-lifecycle-invariant-implies-machine-invariant)
     (:instance fn-bpn-machine-invariant-components)
     (:instance fn-bpn-machine-statep-components)
     (:instance fn-bpn-find-job-is-a-job
                (jobs (fn-bpn-machine-state-jobs st)))
     (:instance fn-bpn-key-of-found-job
                (jobs (fn-bpn-machine-state-jobs st)))
     (:instance fn-bpn-job-key-is-typed
                (job (fn-bpn-find-job
                      key (fn-bpn-machine-state-jobs st))))
     (:instance fn-bpn-finished-proposal-is-authorized)
     (:instance fn-bpn-requeued-proposal-is-authorized
                (reason (if (equal outcome :refused) :refused
                          (if (equal outcome :uncertain) :uncertain
                            :failed)))))
    :in-theory
    (union-theories
     '(fn-bpn-forward-result-step
       fn-bpn-propose-preserves-lifecycle-invariant
       fn-bpn-terminal-record-is-typed fn-bpn-job-key-is-typed
       fn-bpn-record-applicablep fn-bpn-proposal-effectsp
       fn-bpn-record-key fn-bpn-record-token fn-bpn-nth
       fn-bpn-answer-constructor-accessors
       fn-bpn-effect-listp-of-singleton fn-bpn-effect-listp-of-pair
       fn-bpn-effectp fn-bpn-member fn-cbor-ag-car
       car-cons cdr-cons true-listp len nth zp natp)
     (theory 'minimal-theory)))))

(defthm fn-bpn-status-of-find-expired
  (implies (fn-bpn-find-expired jobs obs)
           (fn-bpn-member
            (fn-bpn-job-status (fn-bpn-find-expired jobs obs))
            '(:queued :attempting)))
  :hints
  (("Goal" :induct (fn-bpn-find-expired jobs obs)
    :in-theory
    (union-theories '(fn-bpn-find-expired fn-bpn-member)
                    (theory 'minimal-theory)))))

(defthm fn-bpn-find-job-of-find-expired
  (implies (and (fn-bpn-job-listp jobs)
                (fn-bpn-find-expired jobs obs))
           (equal
            (fn-bpn-find-job
             (fn-bpn-job-key (fn-bpn-find-expired jobs obs)) jobs)
            (fn-bpn-find-expired jobs obs)))
  :hints
  (("Goal" :induct (fn-bpn-find-expired jobs obs)
    :in-theory
    (union-theories
     '(fn-bpn-find-expired fn-bpn-find-job
       fn-bpn-job-listp fn-bpn-job-key-memberp)
     (theory 'minimal-theory)))))

(defthm fn-bpn-expired-proposal-is-authorized
  (implies
   (and (fn-bpn-machine-invariantp st)
        (not (fn-bpn-machine-state-pending st))
        (fn-bpn-jobp job)
        (fn-bpn-member (fn-bpn-job-status job) '(:queued :attempting))
        (equal (fn-bpn-find-job (fn-bpn-job-key job)
                                (fn-bpn-machine-state-jobs st))
               job))
   (let* ((token (fn-bpn-machine-state-next-token st))
          (key (fn-bpn-job-key job))
          (record (list :expired token (nth 0 key) (nth 1 key) (nth 2 key)
                        :none :expired))
          (success (list (list :transport (nth 0 key) (nth 1 key)
                               (nth 2 key) :expired)))
          (refusal (list :bundle-queue-refused (nth 0 key) (nth 1 key)
                         (nth 2 key) :expiry-persistence-refused))
          (uncertain (list :bundle-queue-uncertain (nth 0 key) (nth 1 key)
                           (nth 2 key) :expiry-persistence)))
     (and (fn-bpn-lifecycle-recordp record)
          (fn-bpn-record-applicablep st record)
          (fn-bpn-proposal-effectsp st record success refusal uncertain)
          (fn-bpn-effect-listp success)
          (fn-bpn-effectp refusal)
          (fn-bpn-effectp uncertain))))
  :hints
  (("Goal"
    :use
    ((:instance fn-bpn-machine-invariant-components)
     (:instance fn-bpn-machine-statep-components)
     (:instance fn-bpn-job-key-is-typed)
     (:instance fn-bpn-terminal-record-is-typed
                (token (fn-bpn-machine-state-next-token st))
                (key (fn-bpn-job-key job))
                (kind :expired) (reason :none)))
    :in-theory
    (union-theories
     '(fn-bpn-record-applicablep fn-bpn-proposal-effectsp
       fn-bpn-record-key fn-bpn-record-token fn-bpn-nth fn-bpn-job-key
       fn-bpn-job-key-accessors fn-bpn-job-accessors-forward-consp
       fn-bpn-effect-listp fn-bpn-effectp fn-bpn-member
       fn-cbor-ag-car car-cons cdr-cons true-listp len nth zp natp)
     (theory 'minimal-theory)))))

(defthm fn-bpn-clock-step-preserves-lifecycle-invariant
  (implies
   (fn-bpn-lifecycle-invariantp st)
   (fn-bpn-lifecycle-invariantp
    (fn-bpn-answer-state (fn-bpn-clock-step st obs))))
  :hints
  (("Goal"
    :use
    ((:instance fn-bpn-lifecycle-invariant-implies-machine-invariant)
     (:instance fn-bpn-machine-invariant-components)
     (:instance fn-bpn-machine-statep-components)
     (:instance fn-bpn-find-expired-is-a-job
                (jobs (fn-bpn-machine-state-jobs st)))
     (:instance fn-bpn-status-of-find-expired
                (jobs (fn-bpn-machine-state-jobs st)))
     (:instance fn-bpn-find-job-of-find-expired
                (jobs (fn-bpn-machine-state-jobs st)))
     (:instance fn-bpn-job-key-is-typed
                (job (fn-bpn-find-expired
                      (fn-bpn-machine-state-jobs st) obs)))
     (:instance fn-bpn-expired-proposal-is-authorized
                (job (fn-bpn-find-expired
                      (fn-bpn-machine-state-jobs st) obs))))
    :in-theory
    (union-theories
     '(fn-bpn-clock-step fn-bpn-propose-preserves-lifecycle-invariant
       fn-bpn-terminal-record-is-typed fn-bpn-job-key-is-typed
       fn-bpn-record-applicablep fn-bpn-proposal-effectsp
       fn-bpn-record-key fn-bpn-record-token fn-bpn-nth
       fn-bpn-answer-constructor-accessors
       fn-bpn-effect-listp-of-singleton fn-bpn-effectp fn-bpn-member
       fn-cbor-ag-car car-cons cdr-cons true-listp len nth zp natp)
     (theory 'minimal-theory)))))

; Keystone: this is the dispatcher called by fnn-bps-step in the native
; service, with the bounded restart event contract carried at its boundary.
(defthm fn-bpn-step-preserves-lifecycle-invariant
  (implies
   (and (fn-bpn-lifecycle-invariantp st)
        (fn-bpn-machine-eventp event))
   (fn-bpn-lifecycle-invariantp
    (fn-bpn-answer-state (fn-bpn-step st event))))
  :hints
  (("Goal"
    :in-theory
    (union-theories
     '(fn-bpn-machine-eventp fn-bpn-eventp fn-bpn-step fn-bpn-dispatch
       fn-bpn-enqueue-step-preserves-lifecycle-invariant
       fn-bpn-contact-step-preserves-lifecycle-invariant
       fn-bpn-start-one-preserves-lifecycle-invariant
       fn-bpn-persist-result-step-preserves-lifecycle-invariant
       fn-bpn-forward-result-step-preserves-lifecycle-invariant
       fn-bpn-clock-step-preserves-lifecycle-invariant
       fn-bpn-restart-step-preserves-lifecycle-invariant
       fn-bpn-answer-constructor-accessors fn-bpn-member)
     (theory 'minimal-theory)))))

(defun fn-bpn-machine-event-listp (events)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom events)
      (null events)
    (and (fn-bpn-machine-eventp (car events))
         (fn-bpn-machine-event-listp (cdr events)))))

(defthm fn-bpn-trace-preserves-lifecycle-invariant
  (implies
   (and (fn-bpn-lifecycle-invariantp st)
        (fn-bpn-machine-event-listp events))
   (fn-bpn-lifecycle-invariantp (fn-bpn-trace st events)))
  :hints
  (("Goal"
    :induct (fn-bpn-trace st events)
    :in-theory
    (union-theories
     '(fn-bpn-trace fn-bpn-machine-event-listp
       fn-bpn-step-preserves-lifecycle-invariant)
     (theory 'minimal-theory)))))

(defthm fn-bpn-lifecycle-invariant-authorizes-pending
  (implies
   (and (fn-bpn-lifecycle-invariantp st)
        (fn-bpn-machine-state-pending st))
   (let ((pending (fn-bpn-machine-state-pending st)))
     (and
      (equal (fn-bpn-pending-token pending)
             (fn-bpn-record-token (fn-bpn-pending-record pending)))
      (fn-bpn-record-applicablep st (fn-bpn-pending-record pending))
      (fn-bpn-proposal-effectsp
       st (fn-bpn-pending-record pending)
       (fn-bpn-pending-success-effects pending)
       (fn-bpn-pending-refusal-effect pending)
       (fn-bpn-pending-uncertainty-effect pending)))))
  :hints
  (("Goal" :in-theory
    (union-theories
     '(fn-bpn-lifecycle-invariantp fn-bpn-pending-authorizedp)
     (theory 'minimal-theory)))))

; The two effect theorems below keep nth and zp closed: the event's fields
; are named by nth in the statement and the step alike, and opening nth
; doubled the case split (1.8 s to 0.8 s each).
;
; A convergence-layer send can leave the actual dispatcher only after the
; matching :attempting record has been reported durable.  The proposal
; relation binds the output to the exact retained route, peer, key and wire.
(defthm fn-bpn-step-cl-send-is-authorized-by-durable-attempt-record
  (implies
   (and (fn-bpn-lifecycle-invariantp st)
        (fn-bpn-effect-kind-memberp
         :cl-send (fn-bpn-answer-effects (fn-bpn-step st event))))
   (let* ((pending (fn-bpn-machine-state-pending st))
          (record (fn-bpn-pending-record pending)))
     (and pending
          (equal (car event) :persist-result)
          (equal (nth 1 event) (fn-bpn-pending-token pending))
          (equal (nth 2 event) :durable)
          (equal (fn-cbor-ag-car record) :attempting)
          (fn-bpn-record-applicablep st record)
          (equal (fn-bpn-answer-effects (fn-bpn-step st event))
                 (fn-bpn-pending-success-effects pending))
          (fn-bpn-proposal-effectsp
           st record
           (fn-bpn-pending-success-effects pending)
           (fn-bpn-pending-refusal-effect pending)
           (fn-bpn-pending-uncertainty-effect pending)))))
  :hints
  (("Goal"
    :use ((:instance fn-bpn-lifecycle-invariant-authorizes-pending))
    :in-theory
    (union-theories
     '(fn-bpn-step fn-bpn-dispatch fn-bpn-enqueue-step fn-bpn-contact-step
       fn-bpn-start-one fn-bpn-persist-result-step
       fn-bpn-forward-result-step fn-bpn-clock-step fn-bpn-restart-step
       fn-bpn-propose fn-bpn-apply-record fn-bpn-proposal-effectsp
       fn-bpn-effect-kind-memberp fn-bpn-answer-constructor-accessors
       fn-bpn-pending-authorizedp fn-bpn-lifecycle-invariantp
       fn-bpn-member fn-cbor-ag-car car-cons cdr-cons true-listp)
     (theory 'minimal-theory)))))

; Queue acceptance has two intentionally distinct authorities.  :durable is
; released only by a durable queued record.  :duplicate is an idempotent
; acknowledgement grounded in the exact already-retained job binding.
(defthm fn-bpn-step-queue-acceptance-is-durable-or-exact-duplicate
  (implies
   (and (fn-bpn-lifecycle-invariantp st)
        (fn-bpn-effect-kind-memberp
         :bundle-queue-accepted
         (fn-bpn-answer-effects (fn-bpn-step st event))))
   (or
    (let* ((work (nth 1 event))
           (attempt (nth 2 event))
           (generation (nth 3 event))
           (sequence (nth 4 event))
           (route (nth 5 event))
           (peer (nth 6 event))
           (adu (nth 7 event))
           (obs (nth 8 event))
           (old (fn-bpn-find-job
                 (list work attempt generation)
                 (fn-bpn-machine-state-jobs st)))
           (bundle (fn-bpn-send-bundle
                    (fn-bpn-machine-state-config st)
                    peer adu sequence obs))
           (wire (fn-bpn-send (fn-bpn-machine-state-config st)
                              peer adu sequence obs)))
      (and (equal (car event) :enqueue)
           old
           (fn-bpn-job-exactp old sequence route peer bundle wire)
           (equal
            (fn-bpn-answer-effects (fn-bpn-step st event))
            (list (list :bundle-queue-accepted work attempt generation
                        sequence :duplicate)))))
    (let* ((pending (fn-bpn-machine-state-pending st))
           (record (fn-bpn-pending-record pending)))
      (and pending
           (equal (car event) :persist-result)
           (equal (nth 1 event) (fn-bpn-pending-token pending))
           (equal (nth 2 event) :durable)
           (equal (fn-cbor-ag-car record) :queued)
           (fn-bpn-record-applicablep st record)
           (equal (fn-bpn-answer-effects (fn-bpn-step st event))
                  (fn-bpn-pending-success-effects pending))
           (fn-bpn-proposal-effectsp
            st record
            (fn-bpn-pending-success-effects pending)
            (fn-bpn-pending-refusal-effect pending)
            (fn-bpn-pending-uncertainty-effect pending))))))
  :hints
  (("Goal"
    :use ((:instance fn-bpn-lifecycle-invariant-authorizes-pending))
    :in-theory
    (union-theories
     '(fn-bpn-step fn-bpn-dispatch fn-bpn-enqueue-step fn-bpn-contact-step
       fn-bpn-start-one fn-bpn-persist-result-step
       fn-bpn-forward-result-step fn-bpn-clock-step fn-bpn-restart-step
       fn-bpn-propose fn-bpn-apply-record fn-bpn-proposal-effectsp
       fn-bpn-effect-kind-memberp fn-bpn-answer-constructor-accessors
       fn-bpn-pending-authorizedp fn-bpn-lifecycle-invariantp
       fn-bpn-member fn-cbor-ag-car car-cons cdr-cons true-listp)
     (theory 'minimal-theory)))))
