; Proof-side maintained topic interpretation of the actual Store directory.
; The served machine carries fn-sn-topic; it never scans this prefix per call.
(in-package "ACL2")
(include-book "consumer-store-invariants")
(include-book "topic-history-prefix-invariants")

(defun fn-sti-completed-prefixp (s)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((n (fn-sn-identity-next s))
         (records (fn-sf-records (fn-sn-files s))))
    (and (natp n)
         (<= n (len records))
         (equal (fn-th-at 1 (fn-sn-topic s)) n)
         (equal (fn-th-prefix-project (take n records))
                (fn-sn-topic s))
         (eq (fn-th-at 0 (fn-sn-topic s)) :ok))))

; Before finish, the physical directory may already include the last event.
; Before a record link is observed, a staged candidate may also become
; visible in a process-death image. Both must extend the *carried* prefix.
(defun fn-sti-livep (s)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((files (fn-sn-files s))
         (phase (fn-sf-phase files))
         (candidate (fn-sf-record-candidate files)))
    (and (fn-csi-livep s)
         (fn-sti-completed-prefixp s)
         (or (not (fn-sf-completion-phasep phase))
             (eq (fn-th-at 0
                           (fn-th-prefix-step
                            (fn-sn-topic s) (fn-sn-completion-record s)))
                 :ok))
         ; In :completed the physical last record can remain visible after
         ; the completion selector changes.  Validate that actual last
         ; record against the carried prefix, not only the selector above.
         (or (not (equal phase :completed))
             (eq (fn-th-at 0
                           (fn-th-prefix-step
                            (fn-sn-topic s)
                            (nth (fn-sn-identity-next s)
                                 (fn-sf-records files))))
                 :ok))
         (or (not (fn-sf-record-phasep phase))
             (not (fn-th-topic-eventp candidate))
             (eq (fn-th-at 0
                           (fn-th-prefix-step (fn-sn-topic s) candidate))
                 :ok)))))

(defthm fn-sti-initial-completed-prefix
  (fn-sti-completed-prefixp (fn-sn-initial groups capacity))
  :hints (("Goal" :in-theory
           (enable fn-sti-completed-prefixp fn-sn-initial fn-sn-topic
                   fn-sn-identity-next fn-sn-files
                   fn-sn-make-v2 fn-store-event-nth
                   fn-sf-initial-state fn-th-prefix-project
                   fn-th-prefix-loop fn-th-prefix-state))))

(defthm fn-sti-initial-live
  (implies (and (fn-string-listp groups)
                (fn-no-duplicatesp groups)
                (natp capacity))
           (fn-sti-livep (fn-sn-initial groups capacity)))
  :hints (("Goal" :use (fn-csi-initial-live fn-sti-initial-completed-prefix)
           :in-theory (e/d (fn-sti-livep fn-sf-record-phasep
                            fn-sf-completion-phasep)
                           (fn-csi-livep fn-sti-completed-prefixp)))))

(defthm fn-sti-finish-advances-topic-by-definition
  (implies (fn-sn-completion-enabledp s)
           (equal (fn-sn-topic (fn-sn-finish s))
                  (fn-th-prefix-step
                   (fn-sn-topic s) (fn-sn-completion-record s))))
  :hints (("Goal" :in-theory
           (e/d (fn-sn-finish)
                (fn-sn-with-topic fn-sn-with-consumer fn-sn-make-v6
                 fn-sn-completion-enabledp fn-sn-completion-record
                 fn-store-retention-event-p fn-cpe-eventp fn-th-topic-eventp
                 fn-stxe-p fn-stxk-p fn-stxa-p
                 fn-replay-apply-record fn-replay-apply-retention-event
                 fn-cpe-projection-step fn-th-prefix-step
                 fn-sn-identity-context fn-replay-identity-step
                 fn-record-record-vocabulary fn-record-shape-vocabulary)))))

(defthm fn-sti-enabled-topic-step-ok-by-definition
  (implies (fn-sn-completion-enabledp s)
           (eq (fn-th-at 0
                         (fn-th-prefix-step
                          (fn-sn-topic s) (fn-sn-completion-record s)))
               :ok))
  :hints (("Goal" :in-theory (enable fn-sn-completion-enabledp))))

(defthm fn-sti-finish-preserves-completed-prefix
  (let* ((n (fn-sn-identity-next s))
         (records (fn-sf-records (fn-sn-files s))))
    (implies (and (fn-sti-completed-prefixp s)
                  (fn-sn-completion-enabledp s)
                  (true-listp records)
                  (equal (len records) (1+ n))
                  (equal (nth n records) (fn-sn-completion-record s)))
             (fn-sti-completed-prefixp (fn-sn-finish s))))
  :hints (("Goal" :do-not '(preprocess)
           :use (fn-sti-finish-advances-topic-by-definition
                 fn-sti-enabled-topic-step-ok-by-definition
                 (:instance fn-sti-prefix-step-success-advances-next
                   (projection (fn-sn-topic s))
                   (event (fn-sn-completion-record s)))
                 fn-snt-finish-image
                 fn-sn-finish-enabled-advances-identity-next
                 (:instance fn-csi-len-of-take
                   (n (fn-sn-identity-next s))
                   (records (fn-sf-records (fn-sn-files s))))
                 (:instance fn-csi-take-next
                   (n (fn-sn-identity-next s))
                   (records (fn-sf-records (fn-sn-files s))))
                 (:instance fn-sti-prefix-project-append-one
                   (records (take (fn-sn-identity-next s)
                                  (fn-sf-records (fn-sn-files s))))
                   (event (fn-sn-completion-record s))))
           :in-theory (e/d (fn-sti-completed-prefixp)
                           (fn-sn-finish fn-sn-completion-enabledp
                            fn-th-prefix-project fn-th-prefix-step)))))

(defthm fn-sti-topic-of-update
  (equal (fn-sn-topic (fn-sn-update s files node))
         (fn-sn-topic s))
  :hints (("Goal" :in-theory
           (enable fn-sn-update fn-sn-make-v6 fn-sn-topic))))

(defthm fn-sti-staged-nontopic-candidate-step-ok
  (implies (and (fn-sn-statep s)
                (fn-sn-identity-sequencep s)
                (fn-sti-completed-prefixp s)
                (fn-sf-record-phasep (fn-sf-phase (fn-sn-files s)))
                (not (fn-th-topic-eventp
                      (fn-sf-record-candidate (fn-sn-files s)))))
           (eq (fn-th-at 0
                         (fn-th-prefix-step
                          (fn-sn-topic s)
                          (fn-sf-record-candidate (fn-sn-files s))))
               :ok))
  :hints (("Goal" :use
           (fn-sis-staged-candidate-matches-identity-next-by-definition
            (:instance fn-sti-nontopic-step-succeeds-at-next-sequence
              (projection (fn-sn-topic s))
              (event (fn-sf-record-candidate (fn-sn-files s)))))
           :in-theory (disable fn-sn-statep fn-sn-identity-sequencep
                               fn-th-prefix-step fn-th-topic-eventp))))

(defthm fn-sti-prepare-topic-preserves-completed-prefix
  (implies (fn-sti-completed-prefixp s)
           (fn-sti-completed-prefixp (fn-sn-prepare-topic s event)))
  :hints (("Goal" :in-theory
           (e/d (fn-sti-completed-prefixp fn-sn-prepare-topic
                   fn-sn-update fn-sf-prepare-record)
                (fn-th-prefix-project fn-th-prefix-step
                 fn-replay-apply-record fn-th-topic-eventp
                 fn-sn-statep fn-sf-statep)))))

(defthm fn-sti-prepare-consumer-preserves-completed-prefix
  (implies (fn-sti-completed-prefixp s)
           (fn-sti-completed-prefixp (fn-sn-prepare-consumer s event)))
  :hints (("Goal" :in-theory
           (e/d (fn-sti-completed-prefixp fn-sn-prepare-consumer
                   fn-sn-update fn-sf-prepare-record)
                (fn-th-prefix-project fn-cpe-projection-step
                 fn-replay-apply-record fn-cpe-eventp
                 fn-sn-statep fn-sf-statep)))))

(defthm fn-sti-prepare-article-preserves-completed-prefix
  (implies (fn-sti-completed-prefixp s)
           (fn-sti-completed-prefixp (fn-sn-prepare s record)))
  :hints (("Goal" :in-theory
           (e/d (fn-sti-completed-prefixp fn-sn-prepare
                   fn-sn-update fn-sf-prepare-record)
                (fn-th-prefix-project fn-sn-statep fn-sf-statep
                 fn-sn-prepare-node fn-sn-record-bindsp)))))

(defthm fn-sti-prepare-retention-preserves-completed-prefix
  (implies (fn-sti-completed-prefixp s)
           (fn-sti-completed-prefixp (fn-sn-prepare-retention s event)))
  :hints (("Goal" :in-theory
           (e/d (fn-sti-completed-prefixp fn-sn-prepare-retention
                   fn-sn-update fn-sf-prepare-record)
                (fn-th-prefix-project fn-replay-apply-retention-event
                 fn-store-retention-event-p fn-sn-statep fn-sf-statep)))))

(defthm fn-sti-prepare-identity-preserves-completed-prefix
  (implies (fn-sti-completed-prefixp s)
           (fn-sti-completed-prefixp (fn-sn-prepare-identity s event)))
  :hints (("Goal" :in-theory
           (e/d (fn-sti-completed-prefixp fn-sn-prepare-identity
                   fn-sn-update fn-sf-prepare-record)
                (fn-th-prefix-project fn-replay-apply-record
                 fn-replay-identity-step fn-sn-identity-context
                 fn-stxe-p fn-stxk-p fn-stxa-p
                 fn-sn-statep fn-sf-statep)))))

(defthm fn-sti-refuse-reservation-preserves-completed-prefix
  (implies (fn-sti-completed-prefixp s)
           (fn-sti-completed-prefixp (fn-sn-refuse-reservation s txid)))
  :hints (("Goal" :in-theory
           (e/d (fn-sti-completed-prefixp fn-sn-refuse-reservation
                   fn-sn-update fn-sf-refuse-reservation)
                (fn-th-prefix-project fn-sn-statep fn-sf-statep
                 fn-replay-advance-txid)))))

(defthm fn-sti-known-abort-preserves-completed-prefix
  (implies (fn-sti-completed-prefixp s)
           (fn-sti-completed-prefixp (fn-sn-known-abort s)))
  :hints (("Goal" :in-theory
           (e/d (fn-sti-completed-prefixp fn-sn-known-abort
                   fn-sn-known-abort-files fn-sn-known-abort-file-start
                   fn-sn-update fn-sf-prepublish-abort
                   fn-sf-abort-completion fn-sf-record-file-result)
                (fn-th-prefix-project fn-sn-statep fn-sf-statep
                 fn-replay-advance-txid)))))

(defthm fn-sti-io-preserves-completed-prefix
  (implies (and (fn-sn-statep s)
                (fn-sti-completed-prefixp s))
           (fn-sti-completed-prefixp (fn-sn-io s operation result)))
  :hints (("Goal"
           :use ((:instance fn-csi-take-append-after-prefix
                    (n (fn-sn-identity-next s))
                    (records (fn-sf-records (fn-sn-files s)))
                    (suffix (list (fn-sf-record-candidate
                                   (fn-sn-files s))))))
           :in-theory (e/d (fn-sti-completed-prefixp fn-sn-io
                            fn-sn-file-step fn-sf-start-frontier
                            fn-sf-frontier-file-result
                            fn-sf-frontier-replace-result
                            fn-sf-frontier-dir-result
                            fn-sf-record-file-result
                            fn-sf-record-link-result
                            fn-sf-record-dir-result
                            fn-sf-recovery-barrier)
                           (fn-sn-update fn-sn-with-event-index
                            fn-sn-make-v6 fn-cei-put
                            fn-th-prefix-project fn-sn-statep fn-sf-statep
                            fn-csi-take-append-after-prefix)))))

(defthm fn-sti-prepare-topic-preserves-live
  (implies (fn-sti-livep s)
           (fn-sti-livep (fn-sn-prepare-topic s event)))
  :hints (("Goal"
           :use (fn-csi-prepare-topic-preserves-live
                 fn-sti-prepare-topic-preserves-completed-prefix)
           :in-theory (e/d (fn-sti-livep fn-sn-prepare-topic
                            fn-sf-prepare-record fn-sf-record-phasep
                            fn-sf-completion-phasep)
                           (fn-csi-livep fn-sti-completed-prefixp
                            fn-th-topic-eventp fn-th-prefix-step
                            fn-replay-apply-record fn-sn-statep
                            fn-sf-statep)))))

(defthm fn-sti-prepare-article-from-reserved-stages-nontopic
  (implies (and (fn-sn-statep s)
                (equal (fn-sf-phase (fn-sn-files s)) :reserved)
                (fn-sf-record-phasep
                 (fn-sf-phase (fn-sn-files (fn-sn-prepare s record)))))
           (not (fn-th-topic-eventp
                 (fn-sf-record-candidate
                  (fn-sn-files (fn-sn-prepare s record))))))
  :hints (("Goal"
           :use ((:instance fn-snt-an-article-record-is-no-other-store-event
                    (record record)))
           :in-theory (e/d (fn-sn-prepare fn-sf-prepare-record)
                           (fn-sn-statep fn-sf-statep fn-record-p
                            fn-th-topic-eventp fn-sn-prepare-node
                            fn-sn-record-bindsp fn-sf-history-recoverablep
                            fn-stxe-p fn-stxk-p fn-stxa-p)))))

(defthm fn-sti-prepare-article-unreserved-no-op-by-definition
  (implies (not (equal (fn-sf-phase (fn-sn-files s)) :reserved))
           (equal (fn-sn-prepare s record) s))
  :hints (("Goal" :in-theory (enable fn-sn-prepare))))

(defthm fn-sti-prepare-article-keeps-topic-by-definition
  (equal (fn-sn-topic (fn-sn-prepare s record)) (fn-sn-topic s))
  :hints (("Goal" :in-theory (e/d (fn-sn-prepare)
                                   (fn-sn-statep fn-sn-prepare-node
                                    fn-sn-record-bindsp fn-sf-prepare-record
                                    fn-cpe-projection-step fn-record-p)))))

(defthm fn-sti-prepare-article-preserves-consumer-live
  (implies (fn-csi-livep s)
           (fn-csi-livep (fn-sn-prepare s record)))
  :hints (("Goal"
           :use ((:instance fn-csi-live-store-step-preserves-projection
                    (event (list :prepare record))))
           :in-theory (e/d (fn-snrt-step fn-snt-step)
                           (fn-sn-prepare fn-csi-livep)))))

(defthm fn-sti-prepare-article-from-reserved-is-not-completing
  (implies (equal (fn-sf-phase (fn-sn-files s)) :reserved)
           (not (fn-sf-completion-phasep
                 (fn-sf-phase (fn-sn-files (fn-sn-prepare s record))))))
  :hints (("Goal" :in-theory (e/d (fn-sn-prepare fn-sf-prepare-record
                                   fn-sf-completion-phasep)
                                  (fn-sn-statep fn-sf-statep fn-record-p
                                   fn-sn-prepare-node fn-sn-record-bindsp
                                   fn-sf-history-recoverablep)))))

(defthm fn-sti-prepare-article-preserves-live
  (implies (fn-sti-livep s)
           (fn-sti-livep (fn-sn-prepare s record)))
  :hints (("Goal"
           :cases ((equal (fn-sf-phase (fn-sn-files s)) :reserved))
           :use (fn-sti-prepare-article-preserves-consumer-live
                 fn-sti-prepare-article-preserves-completed-prefix
                 fn-sti-prepare-article-from-reserved-stages-nontopic
                 fn-sti-prepare-article-keeps-topic-by-definition
                 fn-sti-prepare-article-from-reserved-is-not-completing)
           :in-theory (e/d (fn-sti-livep fn-sf-record-phasep
                            fn-sf-completion-phasep)
                           (fn-sn-prepare fn-csi-livep
                            fn-sti-completed-prefixp fn-th-topic-eventp
                            fn-th-prefix-step fn-sn-statep fn-sf-statep)))))

(defthm fn-sti-current-records-topic-ok
  (implies (and (fn-sti-livep s)
                (not (equal (fn-sf-phase (fn-sn-files s)) :completed)))
           (fn-sn-observed-topic-okp
            (fn-sf-records (fn-sn-files s))))
  :hints (("Goal"
           :use ((:instance fn-sf-state-records-are-true-list
                    (s (fn-sn-files s)))
                 (:instance fn-cbor-take-whole-list
                    (xs (fn-sf-records (fn-sn-files s))))
                 (:instance fn-csi-take-next
                    (n (fn-sn-identity-next s))
                    (records (fn-sf-records (fn-sn-files s))))
                 (:instance fn-sti-prefix-project-append-one
                    (records (take (fn-sn-identity-next s)
                                   (fn-sf-records (fn-sn-files s))))
                    (event (fn-sn-completion-record s))))
           :in-theory (e/d (fn-sti-livep fn-sti-completed-prefixp
                            fn-csi-livep fn-csi-completion-lastp
                            fn-sn-identity-sequencep
                            fn-sf-completion-phasep
                            fn-sn-observed-topic-okp)
                           (fn-th-prefix-project fn-th-prefix-step
                            fn-sn-statep fn-sf-statep)))))

(defthm fn-sti-record-candidate-append-topic-ok
  (implies (and (fn-sti-livep s)
                (fn-sf-record-present-visiblep (fn-sn-files s)))
           (fn-sn-observed-topic-okp
            (append (fn-sf-records (fn-sn-files s))
                    (list (fn-sf-record-candidate (fn-sn-files s))))))
  :hints (("Goal"
           :use ((:instance fn-sti-prefix-project-append-one
                    (records (fn-sf-records (fn-sn-files s)))
                    (event (fn-sf-record-candidate (fn-sn-files s))))
                 (:instance fn-cbor-take-whole-list
                    (xs (fn-sf-records (fn-sn-files s))))
                 (:instance fn-sf-state-records-are-true-list
                    (s (fn-sn-files s)))
                 fn-sti-staged-nontopic-candidate-step-ok)
           :in-theory (e/d (fn-sti-livep fn-sti-completed-prefixp
                            fn-csi-livep fn-sn-identity-sequencep
                            fn-sf-completion-phasep
                            fn-sf-record-present-visiblep
                            fn-sf-record-phasep
                            fn-sn-observed-topic-okp)
                           (fn-th-prefix-project fn-th-prefix-step
                            fn-sn-statep fn-sf-statep)))))

; The recovery window may drop exactly the last unacknowledged directory
; entry. A successful topic interpretation remains successful on that prefix.
(defthm fn-sti-prefix-loop-but-last-ok
  (implies (and (true-listp records)
                (eq (fn-th-at 0 (fn-th-prefix-loop projection records)) :ok))
           (eq (fn-th-at 0
                         (fn-th-prefix-loop projection
                                            (fn-sf-but-last records)))
               :ok))
  :hints (("Goal" :induct (fn-th-prefix-loop projection records)
           :in-theory (e/d (fn-sf-but-last fn-th-prefix-loop)
                           (fn-th-prefix-step)))))

(defthm fn-sti-prefix-project-but-last-ok
  (implies (and (true-listp records)
                (fn-sn-observed-topic-okp records))
           (fn-sn-observed-topic-okp (fn-sf-but-last records)))
  :hints (("Goal"
           :use ((:instance fn-sti-prefix-loop-but-last-ok
                    (projection (fn-th-prefix-state :ok 0 nil nil nil nil nil))))
           :in-theory (e/d (fn-sn-observed-topic-okp fn-th-prefix-project)
                           (fn-th-prefix-loop fn-sf-but-last)))))

(defthm fn-sti-live-recovery-crash-image-topic-ok
  (implies (and (fn-sti-livep s)
                (not (equal (fn-sf-phase (fn-sn-files s)) :completed))
                (fn-sf-recovery-crash-imagep
                 (fn-sn-files s) frontier records))
           (fn-sn-observed-topic-okp records))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-sti-current-records-topic-ok
                 fn-sti-record-candidate-append-topic-ok
                 (:instance fn-sti-prefix-project-but-last-ok
                   (records (fn-sf-records (fn-sn-files s))))
                 (:instance fn-sf-state-records-are-true-list
                   (s (fn-sn-files s))))
           :in-theory (e/d (fn-sf-recovery-crash-imagep)
                           (fn-sti-livep fn-sf-statep
                            fn-sn-observed-topic-okp)))))

; The :completed phase also holds one physical record beyond the carried
; topic cursor.  fn-sti-livep checks that exact record, so every admissible
; recovery image remains a valid topic prefix even across the recovery-only
; rollback arm.
(defthm fn-sti-current-records-topic-ok-including-completed
  (implies (fn-sti-livep s)
           (fn-sn-observed-topic-okp
            (fn-sf-records (fn-sn-files s))))
  :hints (("Goal"
           :use ((:instance fn-sf-state-records-are-true-list
                    (s (fn-sn-files s)))
                 (:instance fn-cbor-take-whole-list
                    (xs (fn-sf-records (fn-sn-files s))))
                 (:instance fn-csi-take-next
                    (n (fn-sn-identity-next s))
                    (records (fn-sf-records (fn-sn-files s))))
                 (:instance fn-sti-prefix-project-append-one
                    (records (take (fn-sn-identity-next s)
                                   (fn-sf-records (fn-sn-files s))))
                    (event (nth (fn-sn-identity-next s)
                                (fn-sf-records (fn-sn-files s))))))
           :in-theory (e/d (fn-sti-livep fn-sti-completed-prefixp
                            fn-csi-livep fn-csi-completion-lastp
                            fn-sn-identity-sequencep
                            fn-sf-completion-phasep
                            fn-sn-observed-topic-okp)
                           (fn-th-prefix-project fn-th-prefix-step
                            fn-sn-statep fn-sf-statep)))))

(defthm fn-sti-live-recovery-crash-image-topic-ok-all-phases
  (implies (and (fn-sti-livep s)
                (fn-sf-recovery-crash-imagep
                 (fn-sn-files s) frontier records))
           (fn-sn-observed-topic-okp records))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-sti-current-records-topic-ok-including-completed
                 fn-sti-record-candidate-append-topic-ok
                 (:instance fn-sti-prefix-project-but-last-ok
                   (records (fn-sf-records (fn-sn-files s))))
                 (:instance fn-sf-state-records-are-true-list
                   (s (fn-sn-files s))))
           :in-theory (e/d (fn-sf-recovery-crash-imagep)
                           (fn-sti-livep fn-sf-statep
                            fn-sn-observed-topic-okp)))))

; The host I/O dispatcher cannot leave either completion phase.  The only
; transition into :completing is a successful record-directory result for
; the previously staged event; the topic proof can use that finite case
; split without opening every file operation in its main theorem.
(defthm fn-sti-completion-phase-io-files-no-op-by-definition
  (implies (and (fn-sf-statep files)
                (fn-sf-completion-phasep (fn-sf-phase files)))
           (equal (fn-sn-file-step files operation result) files))
  :hints (("Goal"
           :in-theory (e/d (fn-sn-file-step fn-sf-start-frontier
                            fn-sf-frontier-file-result
                            fn-sf-frontier-replace-result
                            fn-sf-frontier-dir-result
                            fn-sf-record-file-result fn-sf-record-link-result
                            fn-sf-record-dir-result fn-sf-recovery-barrier
                            fn-sf-completion-phasep)
                           (fn-sf-statep fn-sf-phase-shapep)))))

(defthm fn-sti-completion-phase-io-no-op
  (implies (and (fn-sn-statep s)
                (fn-sf-completion-phasep
                 (fn-sf-phase (fn-sn-files s))))
           (equal (fn-sn-io s operation result) s))
  :hints (("Goal"
           :use ((:instance
                  fn-sti-completion-phase-io-files-no-op-by-definition
                  (files (fn-sn-files s)))
                 fn-snt-state-reconstruction)
           :in-theory (e/d (fn-sn-io fn-sn-update
                            fn-sf-completion-phasep)
                           (fn-sn-statep fn-sf-statep fn-sn-file-step
                            fn-sn-with-event-index fn-sn-make-v6)))))

(defthm fn-sti-io-enters-completion-only-from-record-attempted
  (implies (and (fn-sf-statep files)
                (not (fn-sf-completion-phasep (fn-sf-phase files)))
                (fn-sf-completion-phasep
                 (fn-sf-phase (fn-sn-file-step files operation result))))
           (and (equal (fn-sf-phase files) :record-attempted)
                (equal operation :record-directory)
                (equal result :ok)))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (fn-sn-file-step fn-sf-start-frontier
                            fn-sf-frontier-file-result
                            fn-sf-frontier-replace-result
                            fn-sf-frontier-dir-result
                            fn-sf-record-file-result fn-sf-record-link-result
                            fn-sf-record-dir-result fn-sf-recovery-barrier
                            fn-sf-completion-phasep)
                           (fn-sf-statep fn-sf-phase-shapep)))))

(defthm fn-sti-record-directory-completion-is-staged-candidate
  (let ((after (fn-sn-io s :record-directory :ok)))
    (implies (and (fn-sn-statep s)
                  (fn-sn-identity-sequencep s)
                  (equal (fn-sf-phase (fn-sn-files s)) :record-attempted))
             (equal (fn-sn-completion-record after)
                    (fn-sf-record-candidate (fn-sn-files s)))))
  :hints (("Goal"
           :use ((:instance fn-snt-find-published-candidate
                    (files (fn-sn-files s))
                    (record (fn-sf-record-candidate (fn-sn-files s))))
                 (:instance fn-snt-typed-record-phase
                    (files (fn-sn-files s))))
           :in-theory (e/d (fn-sn-io fn-sn-file-step fn-sn-update
                            fn-sf-record-dir-result fn-sn-completion-record
                            fn-sn-identity-sequencep
                            fn-sf-completion-phasep)
                           (fn-sn-statep fn-sf-statep
                            fn-sn-with-event-index fn-sn-make-v6
                            fn-cei-put fn-th-prefix-step)))))

(defthm fn-sti-io-keeps-topic-by-definition
  (equal (fn-sn-topic (fn-sn-io s operation result)) (fn-sn-topic s))
  :hints (("Goal" :in-theory
           (e/d (fn-sn-io)
                (fn-sn-update fn-sn-with-event-index fn-sn-make-v6
                 fn-cei-put fn-sn-statep)))))

(defthm fn-sti-record-directory-installs-topic-valid-completion
  (let ((after (fn-sn-io s :record-directory :ok)))
    (implies (and (fn-sti-livep s)
                  (equal (fn-sf-phase (fn-sn-files s)) :record-attempted))
             (eq (fn-th-at 0
                           (fn-th-prefix-step
                            (fn-sn-topic after)
                            (fn-sn-completion-record after)))
                 :ok)))
  :hints (("Goal"
           :use (fn-sti-record-directory-completion-is-staged-candidate
                 fn-sti-io-keeps-topic-by-definition)
           :in-theory (e/d (fn-sti-livep fn-sf-record-phasep)
                           (fn-sn-io fn-sn-statep fn-sf-statep
                            fn-th-prefix-step fn-th-topic-eventp)))))

(defthm fn-sti-files-of-io-by-definition
  (implies (fn-sn-statep s)
           (equal (fn-sn-files (fn-sn-io s operation result))
                  (fn-sn-file-step (fn-sn-files s) operation result)))
  :hints (("Goal" :in-theory
           (e/d (fn-sn-io)
                (fn-sn-statep fn-sn-update fn-sn-with-event-index
                 fn-sn-make-v6 fn-cei-put)))))

(defthm fn-sti-io-record-phase-keeps-candidate
  (implies (and (fn-sf-statep files)
                (fn-sf-record-phasep
                 (fn-sf-phase (fn-sn-file-step files operation result))))
           (and (fn-sf-record-phasep (fn-sf-phase files))
                (equal (fn-sf-record-candidate
                        (fn-sn-file-step files operation result))
                       (fn-sf-record-candidate files))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (fn-sn-file-step fn-sf-start-frontier
                            fn-sf-frontier-file-result
                            fn-sf-frontier-replace-result
                            fn-sf-frontier-dir-result
                            fn-sf-record-file-result fn-sf-record-link-result
                            fn-sf-record-dir-result fn-sf-recovery-barrier
                            fn-sf-record-phasep)
                           (fn-sf-statep fn-sf-phase-shapep)))))

(defthm fn-sti-io-new-completion-topic-valid
  (implies (and (fn-sti-livep s)
                (not (fn-sf-completion-phasep
                      (fn-sf-phase (fn-sn-files s))))
                (fn-sf-completion-phasep
                 (fn-sf-phase (fn-sn-files (fn-sn-io s operation result)))))
           (eq (fn-th-at 0
                         (fn-th-prefix-step
                          (fn-sn-topic (fn-sn-io s operation result))
                          (fn-sn-completion-record
                           (fn-sn-io s operation result))))
               :ok))
  :hints (("Goal"
           :use ((:instance
                  fn-sti-io-enters-completion-only-from-record-attempted
                  (files (fn-sn-files s)))
                 fn-sti-record-directory-installs-topic-valid-completion
                 fn-sti-files-of-io-by-definition)
           :in-theory (e/d (fn-sti-livep fn-csi-livep)
                           (fn-sn-io fn-sn-file-step
                            fn-sti-completed-prefixp fn-th-prefix-step
                            fn-th-topic-eventp fn-sf-completion-phasep
                            fn-sn-statep fn-sf-statep)))))

(defthm fn-sti-io-record-phase-topic-valid
  (implies (and (fn-sti-livep s)
                (fn-sf-record-phasep
                 (fn-sf-phase (fn-sn-files (fn-sn-io s operation result)))))
           (or (not (fn-th-topic-eventp
                     (fn-sf-record-candidate
                      (fn-sn-files (fn-sn-io s operation result)))))
               (eq (fn-th-at 0
                             (fn-th-prefix-step
                              (fn-sn-topic (fn-sn-io s operation result))
                              (fn-sf-record-candidate
                               (fn-sn-files
                                (fn-sn-io s operation result)))))
                   :ok)))
  :hints (("Goal"
           :use ((:instance fn-sti-io-record-phase-keeps-candidate
                    (files (fn-sn-files s)))
                 fn-sti-files-of-io-by-definition
                 fn-sti-io-keeps-topic-by-definition)
           :in-theory (e/d (fn-sti-livep fn-csi-livep)
                           (fn-sn-io fn-sn-file-step
                            fn-sti-completed-prefixp fn-th-prefix-step
                            fn-th-topic-eventp fn-sn-statep fn-sf-statep)))))

(defthm fn-sti-io-cannot-enter-completed
  (implies (and (fn-sn-statep s)
                (not (fn-sf-completion-phasep
                      (fn-sf-phase (fn-sn-files s))))
                (fn-sf-completion-phasep
                 (fn-sf-phase (fn-sn-files (fn-sn-io s operation result)))))
           (equal (fn-sf-phase
                   (fn-sn-files (fn-sn-io s operation result)))
                  :completing))
  :hints (("Goal"
           :use ((:instance
                  fn-sti-io-enters-completion-only-from-record-attempted
                  (files (fn-sn-files s)))
                 fn-sti-files-of-io-by-definition)
           :in-theory (e/d (fn-sn-file-step fn-sf-record-dir-result)
                           (fn-sn-io fn-sn-statep fn-sf-statep
                            fn-sf-completion-phasep)))))

(defthm fn-sti-io-preserves-live
  (implies (fn-sti-livep s)
           (fn-sti-livep (fn-sn-io s operation result)))
  :hints (("Goal"
           :cases ((fn-sf-completion-phasep
                    (fn-sf-phase (fn-sn-files s)))
                   (fn-sf-completion-phasep
                    (fn-sf-phase
                     (fn-sn-files (fn-sn-io s operation result)))))
           :use (fn-csi-io-preserves-live
                 fn-sti-io-preserves-completed-prefix
                 fn-sti-completion-phase-io-no-op
                 fn-sti-io-cannot-enter-completed
                 fn-sti-io-new-completion-topic-valid
                 fn-sti-io-record-phase-topic-valid
                 fn-sti-files-of-io-by-definition)
           :in-theory (e/d (fn-sti-livep fn-csi-livep
                            fn-sf-completion-phasep)
                           (fn-sti-completed-prefixp fn-sn-statep
                            fn-sf-statep fn-th-prefix-step
                            fn-th-topic-eventp fn-sn-io fn-sn-file-step
                            fn-sn-update fn-sn-with-event-index
                            fn-sn-make-v6 fn-cei-put)))))

(defthm fn-sti-finish-preserves-live
  (implies (fn-sti-livep s)
           (fn-sti-livep (fn-sn-finish s)))
  :hints (("Goal"
           :cases ((fn-sn-completion-enabledp s))
           :use (fn-csi-finish-preserves-live
                 fn-sti-finish-preserves-completed-prefix
                 fn-sn-finish-disabled-is-no-op
                 fn-snt-finish-image
                 (:instance fn-sf-state-records-are-true-list
                   (s (fn-sn-files s))))
           :in-theory (e/d (fn-sti-livep fn-csi-livep
                            fn-sn-identity-sequencep
                            fn-csi-completion-lastp
                            fn-sf-completion-phasep)
                           (fn-sn-finish fn-sn-statep fn-sf-statep
                            fn-sti-completed-prefixp fn-th-prefix-step
                            fn-th-topic-eventp fn-sn-completion-enabledp)))))

; The retention candidate is a different tagged Store event.  Its prepare
; transition can stage it, but it cannot create a topic obligation before
; the common directory barrier.
(defthm fn-sti-retention-event-is-not-topic
  (implies (fn-store-retention-event-p event)
           (not (fn-th-topic-eventp event)))
  :hints (("Goal"
           :in-theory (e/d (fn-store-retention-event-p fn-th-topic-eventp
                            fn-th-local-admin-eventp fn-th-at
                            fn-store-event-nth)
                           (fn-th-source-id-p fn-th-auth-ref-p
                            fn-th-exact-octets-p)))))

(defthm fn-sti-prepare-retention-stages-nontopic
  (implies (and (fn-sn-statep s)
                (equal (fn-sf-phase (fn-sn-files s)) :reserved)
                (fn-sf-record-phasep
                 (fn-sf-phase (fn-sn-files
                               (fn-sn-prepare-retention s event)))))
           (not (fn-th-topic-eventp
                 (fn-sf-record-candidate
                  (fn-sn-files (fn-sn-prepare-retention s event))))))
  :hints (("Goal"
           :in-theory (e/d (fn-sn-prepare-retention fn-sf-prepare-record)
                           (fn-sn-statep fn-sf-statep
                            fn-store-retention-event-p
                            fn-th-topic-eventp fn-cpe-projection-step
                            fn-replay-apply-retention-event)))))

(defthm fn-sti-prepare-retention-preserves-consumer-live
  (implies (fn-csi-livep s)
           (fn-csi-livep (fn-sn-prepare-retention s event)))
  :hints (("Goal"
           :use ((:instance fn-csi-live-store-step-preserves-projection
                    (event (list :prepare-retention event))))
           :in-theory (e/d (fn-snrt-step) (fn-sn-prepare-retention
                                           fn-csi-livep)))))

(defthm fn-sti-prepare-retention-preserves-live
  (implies (fn-sti-livep s)
           (fn-sti-livep (fn-sn-prepare-retention s event)))
  :hints (("Goal"
           :cases ((equal (fn-sf-phase (fn-sn-files s)) :reserved))
           :use (fn-sti-prepare-retention-preserves-completed-prefix
                 fn-sti-prepare-retention-stages-nontopic
                 fn-sti-prepare-retention-preserves-consumer-live)
           :in-theory (e/d (fn-sti-livep fn-sn-prepare-retention
                            fn-sf-completion-phasep fn-sf-record-phasep)
                           (fn-csi-livep fn-sti-completed-prefixp
                            fn-th-topic-eventp fn-th-prefix-step
                            fn-sn-statep fn-sf-statep)))))

(defthm fn-sti-consumer-event-is-not-topic
  (implies (fn-cpe-eventp event)
           (not (fn-th-topic-eventp event)))
  :hints (("Goal"
           :in-theory (e/d (fn-cpe-eventp fn-th-topic-eventp
                            fn-th-local-admin-eventp fn-th-at fn-cp-nth)
                           (fn-th-source-id-p fn-th-auth-ref-p
                            fn-th-exact-octets-p)))))

(defthm fn-sti-prepare-consumer-stages-nontopic
  (implies (and (fn-sn-statep s)
                (equal (fn-sf-phase (fn-sn-files s)) :reserved)
                (fn-sf-record-phasep
                 (fn-sf-phase (fn-sn-files
                               (fn-sn-prepare-consumer s event)))))
           (not (fn-th-topic-eventp
                 (fn-sf-record-candidate
                  (fn-sn-files (fn-sn-prepare-consumer s event))))))
  :hints (("Goal"
           :in-theory (e/d (fn-sn-prepare-consumer fn-sf-prepare-record)
                           (fn-sn-statep fn-sf-statep
                            fn-cpe-eventp fn-th-topic-eventp
                            fn-cpe-projection-step
                            fn-replay-apply-record)))))

(defthm fn-sti-prepare-consumer-preserves-consumer-live
  (implies (fn-csi-livep s)
           (fn-csi-livep (fn-sn-prepare-consumer s event)))
  :hints (("Goal"
           :use ((:instance fn-csi-live-store-step-preserves-projection
                    (event (list :prepare-consumer event))))
           :in-theory (e/d (fn-snrt-step) (fn-sn-prepare-consumer
                                           fn-csi-livep)))))

(defthm fn-sti-prepare-consumer-preserves-live
  (implies (fn-sti-livep s)
           (fn-sti-livep (fn-sn-prepare-consumer s event)))
  :hints (("Goal"
           :cases ((equal (fn-sf-phase (fn-sn-files s)) :reserved))
           :use (fn-sti-prepare-consumer-preserves-completed-prefix
                 fn-sti-prepare-consumer-stages-nontopic
                 fn-sti-prepare-consumer-preserves-consumer-live)
           :in-theory (e/d (fn-sti-livep fn-sn-prepare-consumer
                            fn-sf-completion-phasep fn-sf-record-phasep)
                           (fn-csi-livep fn-sti-completed-prefixp
                            fn-th-topic-eventp fn-th-prefix-step
                            fn-sn-statep fn-sf-statep)))))

(defthm fn-sti-prepare-identity-stages-nontopic
  (implies (and (fn-sn-statep s)
                (equal (fn-sf-phase (fn-sn-files s)) :reserved)
                (fn-sf-record-phasep
                 (fn-sf-phase (fn-sn-files
                               (fn-sn-prepare-identity s event)))))
           (not (fn-th-topic-eventp
                 (fn-sf-record-candidate
                  (fn-sn-files (fn-sn-prepare-identity s event))))))
  :hints (("Goal"
           :use ((:instance fn-th-topic-event-is-not-stxe)
                 (:instance fn-th-topic-event-is-not-stxk)
                 (:instance fn-th-topic-event-is-not-stxa))
           :in-theory (e/d (fn-sn-prepare-identity fn-sf-prepare-record)
                           (fn-sn-statep fn-sf-statep
                            fn-th-topic-eventp fn-stxe-p fn-stxk-p fn-stxa-p
                            fn-cpe-projection-step fn-replay-apply-record
                            fn-replay-identity-step)))))

(defthm fn-sti-prepare-identity-preserves-consumer-live
  (implies (fn-csi-livep s)
           (fn-csi-livep (fn-sn-prepare-identity s event)))
  :hints (("Goal"
           :use ((:instance fn-csi-live-store-step-preserves-projection
                    (event (list :prepare-identity event))))
           :in-theory (e/d (fn-snrt-step) (fn-sn-prepare-identity
                                           fn-csi-livep)))))

(defthm fn-sti-prepare-identity-preserves-live
  (implies (fn-sti-livep s)
           (fn-sti-livep (fn-sn-prepare-identity s event)))
  :hints (("Goal"
           :cases ((equal (fn-sf-phase (fn-sn-files s)) :reserved))
           :use (fn-sti-prepare-identity-preserves-completed-prefix
                 fn-sti-prepare-identity-stages-nontopic
                 fn-sti-prepare-identity-preserves-consumer-live)
           :in-theory (e/d (fn-sti-livep fn-sn-prepare-identity
                            fn-sf-completion-phasep fn-sf-record-phasep)
                           (fn-csi-livep fn-sti-completed-prefixp
                            fn-th-topic-eventp fn-th-prefix-step
                            fn-sn-statep fn-sf-statep
                            fn-replay-identity-step fn-replay-apply-record
                            fn-stxe-p fn-stxk-p fn-stxa-p)))))

(defthm fn-sti-refuse-reservation-preserves-consumer-live
  (implies (fn-csi-livep s)
           (fn-csi-livep (fn-sn-refuse-reservation s txid)))
  :hints (("Goal"
           :use ((:instance fn-csi-live-store-step-preserves-projection
                    (event (list :refuse-reservation txid))))
           :in-theory (e/d (fn-snrt-step)
                           (fn-sn-refuse-reservation fn-csi-livep)))))

(defthm fn-sti-refuse-reservation-preserves-live
  (implies (fn-sti-livep s)
           (fn-sti-livep (fn-sn-refuse-reservation s txid)))
  :hints (("Goal"
           :use (fn-sti-refuse-reservation-preserves-completed-prefix
                 fn-sti-refuse-reservation-preserves-consumer-live)
           :in-theory (e/d (fn-sti-livep fn-sn-refuse-reservation
                            fn-sf-refuse-reservation
                            fn-sn-completion-record
                            fn-sf-completion-phasep fn-sf-record-phasep)
                           (fn-csi-livep fn-sti-completed-prefixp
                            fn-sn-statep fn-sf-statep
                            fn-sn-update fn-sn-make-v6
                            fn-th-prefix-step fn-th-topic-eventp)))))

(defthm fn-sti-known-abort-preserves-consumer-live
  (implies (fn-csi-livep s)
           (fn-csi-livep (fn-sn-known-abort s)))
  :hints (("Goal"
           :use ((:instance fn-csi-live-store-step-preserves-projection
                    (event (list :known-abort))))
           :in-theory (e/d (fn-snrt-step)
                           (fn-sn-known-abort fn-csi-livep)))))
