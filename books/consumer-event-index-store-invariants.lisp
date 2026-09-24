; The derived sequence index tracks the *actual* Store event list.  No served
; command checks this full correspondence: it is carried by Store transitions
; and rebuilt during observed recovery.
(in-package "ACL2")
(include-book "store-node")
(include-book "store-files-traces")

(defun fn-ceis-relatedp (s)
  (declare (xargs :guard t :verify-guards nil))
  (if (member-eq (fn-sf-phase (fn-sn-files s))
                 '(:replaying :fault))
      t
    (fn-cei-correspondencep
     (fn-sn-event-index s) (fn-sf-records (fn-sn-files s)))))

(defthm fn-ceis-initial-related
  (fn-ceis-relatedp (fn-sn-initial groups capacity))
  :hints (("Goal" :in-theory (enable fn-ceis-relatedp fn-sn-initial
                                    fn-sn-make-v2 fn-sn-files
                                    fn-sf-phase fn-sf-records
                                    fn-sn-event-index fn-store-event-nth
                                    fn-cei-correspondencep fn-cei-build))))

; The file kernel appends only at the durable directory observation.  The
; Store candidate predicate supplies the dense sequence == old list length,
; which makes the radix extension exact rather than merely sequence-shaped.
(defthm fn-ceis-record-directory-extension
  (implies (and (fn-sf-statep files)
                (equal (fn-sf-phase files) :record-attempted)
                (fn-cei-correspondencep index (fn-sf-records files)))
           (fn-cei-correspondencep
            (fn-cei-put
             (fn-store-event-sequence (fn-sf-record-candidate files))
             (fn-sf-record-candidate files) index)
            (fn-sf-records (fn-sf-record-dir-result files :ok))))
  :hints (("Goal" :use ((:instance fn-cei-extend-preserves-correspondence
                                 (events (fn-sf-records files))
                                 (event (fn-sf-record-candidate files))))
           :in-theory
           (e/d (fn-sf-record-dir-result fn-sf-statep
                  fn-sf-phase-shapep fn-sf-candidatep)
                (fn-store-event-p fn-cei-correspondencep fn-cei-build
                 fn-cei-put fn-cei-put-digits fn-cei-branch-put)))))

(defthm fn-ceis-recovery-rebuilds-index-by-definition
  (implies (and (fn-sn-statep s)
                (equal (fn-sf-phase (fn-sn-files s)) :replaying)
                (equal (fn-sf-phase
                        (fn-sn-files (fn-sn-recover s)))
                       :recovering))
           (fn-cei-correspondencep
            (fn-sn-event-index (fn-sn-recover s))
            (fn-sf-records (fn-sn-files (fn-sn-recover s)))))
  :hints (("Goal" :in-theory
           (e/d (fn-sn-recover fn-cei-correspondencep
                  fn-sn-with-topic fn-sn-with-event-index
                  fn-sn-with-consumer fn-sn-update-replayed)
                (fn-sn-statep fn-sn-make-v6 fn-sn-event-index fn-sn-files
                 fn-sf-recover
                 fn-sf-replay-node fn-replay-identity
                 fn-cpe-projection-replay fn-th-prefix-project
                 fn-cei-build fn-cei-build-aux)))))

(defthm fn-ceis-state-has-file-state
  (implies (fn-sn-statep s)
           (fn-sf-statep (fn-sn-files s)))
  :hints (("Goal" :in-theory (enable fn-sn-statep))))

(defthm fn-ceis-io-preserves-related
  (implies (and (fn-sn-statep s) (fn-ceis-relatedp s)
                (not (member-eq (fn-sf-phase (fn-sn-files s))
                                '(:replaying :fault))))
           (fn-ceis-relatedp (fn-sn-io s operation result)))
  :hints (("Goal" :cases ((and (eq operation :record-directory)
                                (eq result :ok)
                                (eq (fn-sf-phase (fn-sn-files s))
                                    :record-attempted)))
           :use ((:instance fn-ceis-record-directory-extension
                            (files (fn-sn-files s))
                            (index (fn-sn-event-index s))))
           :in-theory (e/d (fn-ceis-relatedp fn-sn-io fn-sn-file-step
                            fn-sf-record-dir-result
                            fn-store-files-traces-vocabulary)
                           (fn-sn-update fn-sn-with-event-index fn-sn-make-v6
                            fn-sf-statep fn-store-event-p
                            fn-cei-correspondencep fn-cei-build
                            fn-cei-build-aux fn-cei-put fn-cei-put-digits
                            fn-cei-branch-put fn-sn-statep)))))

(defthm fn-ceis-prepare-consumer-preserves-related
  (implies (and (fn-sn-statep s) (fn-ceis-relatedp s)
                (not (member-eq (fn-sf-phase (fn-sn-files s))
                                '(:replaying :fault))))
           (fn-ceis-relatedp (fn-sn-prepare-consumer s event)))
  :hints (("Goal" :in-theory
           (e/d (fn-ceis-relatedp fn-sn-prepare-consumer
                  fn-store-files-traces-vocabulary)
                (fn-sn-update fn-sn-make-v6
                 fn-sn-statep fn-sf-statep fn-store-event-p
                 fn-cei-correspondencep fn-cei-build
                 fn-cei-build-aux)))))

(defthm fn-ceis-finish-keeps-index
  (equal (fn-sn-event-index (fn-sn-finish s))
         (fn-sn-event-index s))
  :hints (("Goal" :in-theory
           (e/d (fn-sn-finish fn-sn-finish-identity
                  fn-sn-advance-identity-next
                  fn-sn-with-topic fn-sn-with-consumer
                  fn-sn-update-indexed fn-sn-update-accepted
                  fn-sn-make-v6 fn-sn-event-index)
                (fn-sn-completion-enabledp fn-sn-completion-record
                 fn-store-retention-event-p fn-stxe-p fn-stxk-p
                 fn-stxa-p fn-cpe-eventp fn-th-topic-eventp
                 fn-replay-apply-record fn-replay-apply-retention-event
                 fn-replay-identity-step fn-sn-composite-delta
                 fn-sn-accepted-delta
                 fn-sf-core-completion fn-sf-emit-success)))))

(defthm fn-ceis-finish-keeps-records
  (equal (fn-sf-records (fn-sn-files (fn-sn-finish s)))
         (fn-sf-records (fn-sn-files s)))
  :hints (("Goal" :in-theory
           (e/d (fn-sn-finish fn-sn-finish-identity
                  fn-sn-advance-identity-next
                  fn-sn-with-topic fn-sn-with-consumer
                  fn-sn-update-indexed fn-sn-update-accepted
                  fn-sn-make-v6 fn-sn-files
                  fn-sf-core-completion fn-sf-emit-success)
                (fn-sn-completion-enabledp fn-sn-completion-record
                 fn-store-retention-event-p fn-stxe-p fn-stxk-p
                 fn-stxa-p fn-cpe-eventp fn-th-topic-eventp
                 fn-replay-apply-record fn-replay-apply-retention-event
                 fn-replay-identity-step fn-sn-composite-delta
                 fn-sn-accepted-delta fn-store-event-p)))))

(defthm fn-ceis-finish-preserves-related
  (implies (and (fn-ceis-relatedp s)
                (not (member-eq (fn-sf-phase (fn-sn-files s))
                                '(:replaying :fault))))
           (fn-ceis-relatedp (fn-sn-finish s)))
  :hints (("Goal" :use (fn-ceis-finish-keeps-index
                         fn-ceis-finish-keeps-records)
           :in-theory (e/d (fn-ceis-relatedp)
                           (fn-sn-finish fn-cei-correspondencep
                            fn-ceis-finish-keeps-index
                            fn-ceis-finish-keeps-records)))))

(defthm fn-ceis-crash-preserves-related
  (implies (fn-ceis-relatedp s)
           (fn-ceis-relatedp
            (fn-sn-crash s frontier-choice record-choice)))
  :hints (("Goal" :in-theory
           (e/d (fn-ceis-relatedp fn-sn-crash fn-sf-crash)
                (fn-sn-statep fn-sf-statep
                 fn-sn-make-v6 fn-cei-correspondencep fn-cei-build)))))

(defthm fn-ceis-recover-preserves-related
  (implies (and (fn-sn-statep s) (fn-ceis-relatedp s))
           (fn-ceis-relatedp (fn-sn-recover s)))
  :hints (("Goal" :use (fn-ceis-recovery-rebuilds-index-by-definition)
           :in-theory
           (e/d (fn-ceis-relatedp fn-sn-recover)
                (fn-sn-statep fn-sf-statep fn-sf-recover
                 fn-sn-make-v6 fn-cei-correspondencep fn-cei-build
                 fn-cei-build-aux)))))
