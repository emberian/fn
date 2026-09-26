; E2 exact completed-prefix interpretation of the Store-carried consumer
; projection.  The record directory can contain one linked but unfinished
; candidate; fn-sn-identity-next selects only durable finishes.
(in-package "ACL2")
(include-book "store-identity-sequence-invariants")
(include-book "store-observed")

(defun fn-csi-completed-prefixp (s)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((n (fn-sn-identity-next s))
         (records (fn-sf-records (fn-sn-files s))))
    (and (natp n)
         (<= n (len records))
         (equal (fn-cpe-projection-replay nil (take n records) 0)
                (list :ok (fn-sn-consumer s))))))

(defthm fn-csi-initial-completed-prefix
  (implies (and (fn-string-listp groups)
                (fn-no-duplicatesp groups)
                (natp capacity))
           (fn-csi-completed-prefixp (fn-sn-initial groups capacity)))
  :hints (("Goal" :in-theory (enable fn-csi-completed-prefixp
                                      fn-sn-initial fn-sf-initial-state
                                      fn-cpe-projection-replay))))

(defthm fn-csi-take-next
  (implies (and (natp n) (< n (len records)))
           (equal (take (1+ n) records)
                  (append (take n records) (list (nth n records)))))
  :hints (("Goal" :induct (take n records))))

(defthm fn-csi-len-of-take
  (implies (and (natp n) (<= n (len records)))
           (equal (len (take n records)) n))
  :hints (("Goal" :induct (take n records))))

(defthm fn-csi-nth-appended-last
  (equal (nth (len records) (append records (list event))) event)
  :hints (("Goal" :induct (len records))))

(defthm fn-csi-take-append-after-prefix
  (implies (and (natp n) (<= n (len records)))
           (equal (take n (append records suffix))
                  (take n records)))
  :hints (("Goal" :induct (take n records))))

; Completion also updates the separate topic projection.  Keep the two
; selector facts closed so the consumer proof never opens the fourteen-field
; Store constructor, the accepted-article codec, or the topic prefix step.
(defthm fn-csi-consumer-of-with-topic
  (equal (fn-sn-consumer (fn-sn-with-topic s topic))
         (fn-sn-consumer s))
  :hints (("Goal" :in-theory (enable fn-sn-with-topic fn-sn-make-v6 fn-sn-make-v7
                                     fn-sn-consumer fn-store-event-nth))))

(defthm fn-csi-consumer-of-with-consumer
  (equal (fn-sn-consumer (fn-sn-with-consumer s consumer))
         consumer)
  :hints (("Goal" :in-theory (enable fn-sn-with-consumer fn-sn-make-v6 fn-sn-make-v7
                                     fn-sn-consumer fn-store-event-nth))))

(defthm fn-csi-consumer-of-with-event-index
  (equal (fn-sn-consumer (fn-sn-with-event-index s index))
         (fn-sn-consumer s))
  :hints (("Goal" :in-theory (enable fn-sn-with-event-index fn-sn-make-v6 fn-sn-make-v7
                                     fn-sn-consumer fn-store-event-nth))))

(defthm fn-csi-files-of-with-topic
  (equal (fn-sn-files (fn-sn-with-topic s topic))
         (fn-sn-files s))
  :hints (("Goal" :in-theory (enable fn-sn-with-topic fn-sn-make-v6 fn-sn-make-v7
                                     fn-sn-files))))

(defthm fn-csi-files-of-with-consumer
  (equal (fn-sn-files (fn-sn-with-consumer s consumer))
         (fn-sn-files s))
  :hints (("Goal" :in-theory (enable fn-sn-with-consumer fn-sn-make-v6 fn-sn-make-v7
                                     fn-sn-files))))

(defthm fn-csi-files-of-update-replayed
  (equal (fn-sn-files (fn-sn-update-replayed s files node index context))
         files)
  :hints (("Goal" :in-theory (enable fn-sn-update-replayed fn-sn-make-v6 fn-sn-make-v7
                                     fn-sn-files))))

(defthm fn-csi-identity-next-of-with-event-index
  (equal (fn-sn-identity-next (fn-sn-with-event-index s index))
         (fn-sn-identity-next s))
  :hints (("Goal" :in-theory (enable fn-sn-with-event-index fn-sn-make-v6 fn-sn-make-v7
                                     fn-sn-identity-next))))

(defthm fn-csi-identity-next-of-update
  (equal (fn-sn-identity-next (fn-sn-update s files node))
         (fn-sn-identity-next s))
  :hints (("Goal" :in-theory (enable fn-sn-update fn-sn-make-v6 fn-sn-make-v7
                                     fn-sn-identity-next))))

(defthm fn-csi-consumer-of-update
  (equal (fn-sn-consumer (fn-sn-update s files node))
         (fn-sn-consumer s))
  :hints (("Goal" :in-theory (enable fn-sn-update fn-sn-make-v6 fn-sn-make-v7
                                     fn-sn-consumer fn-store-event-nth))))

; The Store's v6 tuple is representation, not the consumer proof vocabulary.
; Subsequent transition proofs use the exported selector facts above.  A
; theorem that truly needs constructor internals can enable it in its hint.
(local (in-theory (disable fn-sn-make-v6 fn-sn-make-v7)))

(defthm fn-csi-finish-advances-projection-by-definition
  (implies (fn-sn-completion-enabledp s)
           (equal (fn-sn-consumer (fn-sn-finish s))
                  (fn-cp-nth 1
                   (fn-cpe-projection-step
                    (fn-sn-consumer s)
                    (fn-sn-completion-record s)
                    (fn-sn-identity-next s)))))
  :hints (("Goal" :in-theory
           (e/d (fn-sn-finish)
                (fn-sn-with-topic fn-sn-with-consumer fn-sn-make-v6 fn-sn-make-v7
                 fn-sn-completion-enabledp fn-sn-completion-record
                 fn-store-retention-event-p fn-cpe-eventp
                 fn-stxe-p fn-stxk-p fn-stxa-p
                 fn-replay-apply-record fn-replay-apply-retention-event
                 fn-cpe-projection-step fn-sn-identity-context
                 fn-replay-identity-step fn-record-record-vocabulary
                 fn-record-shape-vocabulary)))))

(defthm fn-csi-enabled-projection-step-ok-by-definition
  (implies (fn-sn-completion-enabledp s)
           (eq (car (fn-cpe-projection-step
                     (fn-sn-consumer s) (fn-sn-completion-record s)
                     (fn-sn-identity-next s))) :ok))
  :hints (("Goal" :in-theory (enable fn-sn-completion-enabledp))))

(defthm fn-csi-enabled-phase-by-definition
  (implies (fn-sn-completion-enabledp s)
           (equal (fn-sf-phase (fn-sn-files s)) :completing))
  :hints (("Goal" :in-theory (enable fn-sn-completion-enabledp))))

(defthm fn-csi-recover-uses-strict-full-replay-by-definition
  (implies (and (fn-sn-statep s)
                (equal (fn-sf-phase (fn-sn-files s)) :replaying)
                (equal (fn-sf-phase
                        (fn-sn-files (fn-sn-recover s))) :recovering))
           (equal (fn-sn-consumer (fn-sn-recover s))
                  (fn-cp-nth 1
                   (fn-cpe-projection-replay
                    nil (fn-sf-records (fn-sn-files (fn-sn-recover s))) 0))))
  :hints (("Goal" :in-theory
           (e/d (fn-sn-recover)
                (fn-sn-with-topic fn-sn-with-event-index
                 fn-sn-with-consumer fn-sn-update-replayed fn-sn-update
                 fn-sn-make-v6 fn-sn-make-v7 fn-sf-recover fn-sf-replay-node
                 fn-replay-identity fn-cpe-projection-replay
                 fn-th-prefix-project)))))

(defthm fn-csi-one-more-prefix
  (implies (and (natp n)
                (true-listp records)
                (< n (len records))
                (equal (fn-cpe-projection-replay nil (take n records) 0)
                       (list :ok before))
                (equal (nth n records) event)
                (eq (car (fn-cpe-projection-step before event n)) :ok))
           (equal (fn-cpe-projection-replay
                   nil (take (1+ n) records) 0)
                  (list :ok (fn-cp-nth 1
                             (fn-cpe-projection-step before event n)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-csi-take-next)
                 (:instance fn-csi-len-of-take)
                 (:instance fn-cpe-projection-replay-append-one
                   (s nil) (prefix (take n records)) (start 0)
                   (after before))
                 (:instance fn-cpe-projection-step-ok-pair-by-definition
                   (s before) (event event) (expected n)))
           :in-theory (disable fn-csi-take-next fn-csi-len-of-take
                               fn-cpe-projection-replay-append-one
                               fn-cpe-projection-replay
                               fn-cpe-projection-step))))

(defthm fn-csi-finish-preserves-completed-prefix
  (let* ((n (fn-sn-identity-next s))
         (records (fn-sf-records (fn-sn-files s))))
    (implies (and (fn-csi-completed-prefixp s)
                  (fn-sn-completion-enabledp s)
                  (true-listp records)
                  (equal (len records) (1+ n))
                  (equal (nth n records) (fn-sn-completion-record s)))
             (fn-csi-completed-prefixp (fn-sn-finish s))))
  :hints (("Goal"
           ; The instantiated append and step facts preprocess into a
           ; recursive rewrite expansion before the closed theory applies.
           :do-not '(preprocess)
           :use (fn-csi-finish-advances-projection-by-definition
                 fn-snt-finish-image
                 fn-sn-finish-enabled-advances-identity-next
                 fn-csi-enabled-projection-step-ok-by-definition
                 (:instance fn-csi-len-of-take
                   (n (fn-sn-identity-next s))
                   (records (fn-sf-records (fn-sn-files s))))
                 (:instance fn-cpe-projection-step-ok-pair-by-definition
                   (s (fn-sn-consumer s))
                   (event (fn-sn-completion-record s))
                   (expected (fn-sn-identity-next s)))
                 (:instance fn-csi-one-more-prefix
                   (n (fn-sn-identity-next s))
                   (records (fn-sf-records (fn-sn-files s)))
                   (before (fn-sn-consumer s))
                   (event (fn-sn-completion-record s))))
           :in-theory (e/d (fn-csi-completed-prefixp)
                           (fn-sn-finish fn-sn-completion-enabledp
                            fn-cpe-projection-replay-append-one
                            fn-cpe-projection-replay
                            fn-cpe-projection-step)))))

(defthm fn-csi-finish-preserves-sequenced-last-completion
  (let ((n (fn-sn-identity-next s))
        (records (fn-sf-records (fn-sn-files s))))
    (implies (and (fn-sn-statep s)
                  (fn-sn-identity-sequencep s)
                  (fn-csi-completed-prefixp s)
                  (fn-sn-completion-enabledp s)
                  (equal (nth n records) (fn-sn-completion-record s)))
             (fn-csi-completed-prefixp (fn-sn-finish s))))
  :hints (("Goal"
           :use (fn-csi-finish-preserves-completed-prefix
                 fn-csi-enabled-phase-by-definition
                 (:instance fn-sf-state-records-are-true-list
                   (s (fn-sn-files s))))
           :in-theory (e/d (fn-sn-identity-sequencep
                            fn-sf-completion-phasep)
                           (fn-csi-completed-prefixp fn-sn-finish
                            fn-csi-finish-preserves-completed-prefix
                            fn-sn-completion-enabledp
                            fn-sf-statep fn-sn-statep)))))

(defthm fn-csi-record-directory-installs-next-completion
  (let ((after (fn-sn-io s :record-directory :ok)))
    (implies (and (fn-sn-statep s)
                  (fn-sn-identity-sequencep s)
                  (equal (fn-sf-phase (fn-sn-files s)) :record-attempted))
             (and (equal (fn-sf-phase (fn-sn-files after)) :completing)
                  (equal (nth (fn-sn-identity-next after)
                              (fn-sf-records (fn-sn-files after)))
                         (fn-sn-completion-record after)))))
  :hints (("Goal"
           :use ((:instance fn-snt-find-published-candidate
                   (files (fn-sn-files s))
                   (record (fn-sf-record-candidate (fn-sn-files s))))
                 (:instance fn-snt-typed-record-phase
                   (files (fn-sn-files s)))
                 (:instance fn-csi-nth-appended-last
                   (records (fn-sf-records (fn-sn-files s)))
                   (event (fn-sf-record-candidate (fn-sn-files s)))))
           :in-theory (e/d (fn-sn-io fn-sn-file-step fn-sn-update
                            fn-sf-record-dir-result fn-sn-completion-record
                            fn-sn-identity-sequencep fn-sf-completion-phasep)
                           (fn-sn-make-v6 fn-sn-make-v7 fn-sn-with-event-index fn-cei-put
                            fn-sn-statep fn-sf-statep
                            fn-sf-candidatep fn-sf-record-listp
                            fn-snt-find-published-candidate
                            fn-snt-typed-record-phase)))))

; The directory observation may append a candidate, but it has not consumed
; the carried journal cursor.  Every earlier completed record is unchanged.
(defthm fn-csi-io-preserves-completed-prefix
  (implies (and (fn-sn-statep s)
                (fn-csi-completed-prefixp s))
           (fn-csi-completed-prefixp (fn-sn-io s operation result)))
  :hints (("Goal"
           :use ((:instance fn-csi-take-append-after-prefix
                    (n (fn-sn-identity-next s))
                    (records (fn-sf-records (fn-sn-files s)))
                    (suffix (list (fn-sf-record-candidate (fn-sn-files s))))))
           :in-theory (e/d (fn-csi-completed-prefixp fn-sn-io fn-sn-file-step
                            fn-sf-start-frontier
                            fn-sf-frontier-file-result
                            fn-sf-frontier-replace-result
                            fn-sf-frontier-dir-result
                            fn-sf-record-file-result
                            fn-sf-record-link-result
                            fn-sf-record-dir-result
                            fn-sf-recovery-barrier)
                           (fn-sn-update fn-sn-with-event-index fn-sn-make-v6 fn-sn-make-v7
                            fn-cei-put fn-cpe-projection-replay fn-sn-statep
                            fn-sf-statep fn-csi-take-append-after-prefix)))))

(defthm fn-csi-prepare-consumer-preserves-completed-prefix
  (implies (fn-csi-completed-prefixp s)
           (fn-csi-completed-prefixp (fn-sn-prepare-consumer s event)))
  :hints (("Goal"
           :in-theory (e/d (fn-csi-completed-prefixp
                            fn-sn-prepare-consumer fn-sn-update
                            fn-sf-prepare-record)
                           (fn-cpe-projection-replay
                            fn-cpe-projection-step fn-replay-apply-record
                            fn-cpe-eventp fn-sn-statep fn-sf-statep)))))

(defthm fn-csi-prepare-article-preserves-completed-prefix
  (implies (fn-csi-completed-prefixp s)
           (fn-csi-completed-prefixp (fn-sn-prepare s record)))
  :hints (("Goal"
           :in-theory (e/d (fn-csi-completed-prefixp fn-sn-prepare
                            fn-sn-update fn-sf-prepare-record)
                           (fn-cpe-projection-replay fn-sn-statep
                            fn-sf-statep fn-sn-prepare-node
                            fn-sn-record-bindsp)))))

(defthm fn-csi-prepare-retention-preserves-completed-prefix
  (implies (fn-csi-completed-prefixp s)
           (fn-csi-completed-prefixp (fn-sn-prepare-retention s event)))
  :hints (("Goal"
           :in-theory (e/d (fn-csi-completed-prefixp
                            fn-sn-prepare-retention fn-sn-update
                            fn-sf-prepare-record)
                           (fn-cpe-projection-replay
                            fn-replay-apply-retention-event
                            fn-store-retention-event-p
                            fn-sn-statep fn-sf-statep)))))

(defthm fn-csi-prepare-identity-preserves-completed-prefix
  (implies (fn-csi-completed-prefixp s)
           (fn-csi-completed-prefixp (fn-sn-prepare-identity s event)))
  :hints (("Goal"
           :in-theory (e/d (fn-csi-completed-prefixp
                            fn-sn-prepare-identity fn-sn-update
                            fn-sf-prepare-record)
                           (fn-cpe-projection-replay
                            fn-replay-apply-record fn-replay-identity-step
                            fn-sn-identity-context fn-stxe-p fn-stxk-p
                            fn-stxa-p fn-sn-statep fn-sf-statep)))))

(defthm fn-csi-refuse-reservation-preserves-completed-prefix
  (implies (fn-csi-completed-prefixp s)
           (fn-csi-completed-prefixp (fn-sn-refuse-reservation s txid)))
  :hints (("Goal"
           :in-theory (e/d (fn-csi-completed-prefixp
                            fn-sn-refuse-reservation fn-sn-update
                            fn-sf-refuse-reservation)
                           (fn-cpe-projection-replay fn-sn-statep
                            fn-sf-statep fn-replay-advance-txid)))))

(defthm fn-csi-known-abort-preserves-completed-prefix
  (implies (fn-csi-completed-prefixp s)
           (fn-csi-completed-prefixp (fn-sn-known-abort s)))
  :hints (("Goal"
           :in-theory (e/d (fn-csi-completed-prefixp fn-sn-known-abort
                            fn-sn-known-abort-files
                            fn-sn-known-abort-file-start
                            fn-sn-update fn-sf-prepublish-abort
                            fn-sf-abort-completion
                            fn-sf-record-file-result)
                           (fn-cpe-projection-replay fn-sn-statep
                            fn-sf-statep fn-replay-advance-txid
                            fn-node-complete)))))

(defthm fn-csi-ready-full-replay
  (implies (and (fn-sn-statep s)
                (fn-sn-identity-sequencep s)
                (fn-csi-completed-prefixp s)
                (equal (fn-sf-phase (fn-sn-files s)) :ready))
           (equal (fn-cpe-projection-replay
                   nil (fn-sf-records (fn-sn-files s)) 0)
                  (list :ok (fn-sn-consumer s))))
  :hints (("Goal"
           :use ((:instance fn-sf-state-records-are-true-list
                    (s (fn-sn-files s)))
                 (:instance fn-cbor-take-whole-list
                    (xs (fn-sf-records (fn-sn-files s)))))
           :in-theory (e/d (fn-sn-identity-sequencep
                            fn-csi-completed-prefixp
                            fn-sf-completion-phasep)
                           (fn-cpe-projection-replay fn-sn-statep
                            fn-sf-statep)))))

(defthm fn-csi-ready-crash-retains-full-replay
  (implies (and (fn-sn-statep s)
                (fn-sn-identity-sequencep s)
                (fn-csi-completed-prefixp s)
                (equal (fn-sf-phase (fn-sn-files s)) :ready)
                (fn-sf-crash-choicep frontier-choice record-choice))
           (equal (fn-cpe-projection-replay
                   nil (fn-sf-records
                        (fn-sn-files
                         (fn-sn-crash s frontier-choice record-choice))) 0)
                  (list :ok (fn-sn-consumer s))))
  :hints (("Goal"
           :use (fn-csi-ready-full-replay)
           :in-theory (e/d (fn-sn-crash fn-sf-crash
                            fn-sf-record-present-visiblep)
                           (fn-cpe-projection-replay
                            fn-csi-ready-full-replay fn-sn-statep
                            fn-sf-statep)))))

(defthm fn-csi-recover-replay-ok-by-definition
  (let ((after (fn-sn-recover s)))
    (implies (and (fn-sn-statep s)
                  (equal (fn-sf-phase (fn-sn-files s)) :replaying)
                  (equal (fn-sf-phase (fn-sn-files after)) :recovering))
             (eq (car (fn-cpe-projection-replay
                       nil (fn-sf-records (fn-sn-files after)) 0)) :ok)))
  :hints (("Goal" :in-theory (enable fn-sn-recover))))

(defthm fn-csi-replay-ok-has-projection
  (implies (eq (car (fn-cpe-projection-replay s records expected)) :ok)
           (equal (fn-cpe-projection-replay s records expected)
                  (list :ok (fn-cp-nth 1
                             (fn-cpe-projection-replay s records expected)))))
  :rule-classes nil
  :hints (("Goal"
           :induct (fn-cpe-projection-replay s records expected)
           :in-theory (enable fn-cpe-projection-replay))))

(defthm fn-csi-successful-recover-reconstructs-completed-prefix
  (let ((after (fn-sn-recover s)))
    (implies (and (fn-sn-statep s)
                  (equal (fn-sf-phase (fn-sn-files s)) :replaying)
                  (equal (fn-sf-phase (fn-sn-files after)) :recovering)
                  (fn-sn-identity-sequencep after))
             (fn-csi-completed-prefixp after)))
  :hints (("Goal"
           :use (fn-csi-recover-uses-strict-full-replay-by-definition
                 fn-csi-recover-replay-ok-by-definition
                 (:instance fn-csi-replay-ok-has-projection
                   (s nil)
                   (records (fn-sf-records (fn-sn-files (fn-sn-recover s))))
                   (expected 0))
                 (:instance fn-sf-state-records-are-true-list
                   (s (fn-sn-files (fn-sn-recover s))))
                 (:instance fn-cbor-take-whole-list
                   (xs (fn-sf-records (fn-sn-files (fn-sn-recover s))))))
           :in-theory (e/d (fn-csi-completed-prefixp
                            fn-sn-identity-sequencep
                            fn-sf-completion-phasep)
                           (fn-sn-recover fn-cpe-projection-replay
                            fn-sn-statep fn-sf-statep)))))

; The file-kernel's :completing phase has one already appended event beyond
; the carried cursor.  This equation is about the event selected by the
; actual Store completion lookup, not merely its sequence number.
(defun fn-csi-completion-lastp (s)
  (declare (xargs :guard t :verify-guards nil))
  (or (not (equal (fn-sf-phase (fn-sn-files s)) :completing))
      (equal (nth (fn-sn-identity-next s)
                  (fn-sf-records (fn-sn-files s)))
             (fn-sn-completion-record s))))

(defthm fn-csi-initial-completion-last
  (fn-csi-completion-lastp (fn-sn-initial groups capacity))
  :hints (("Goal" :in-theory (enable fn-csi-completion-lastp
                                      fn-sn-initial fn-sf-initial-state))))

(defthm fn-csi-io-preserves-completion-last
  (implies (and (fn-sn-statep s)
                (fn-sn-identity-sequencep s)
                (fn-csi-completion-lastp s))
           (fn-csi-completion-lastp (fn-sn-io s operation result)))
  :hints (("Goal"
           :use (fn-csi-record-directory-installs-next-completion)
           :in-theory (e/d (fn-csi-completion-lastp fn-sn-io
                            fn-sn-completion-record
                            fn-sn-file-step fn-sn-update
                            fn-sf-start-frontier
                            fn-sf-frontier-file-result
                            fn-sf-frontier-replace-result
                            fn-sf-frontier-dir-result
                            fn-sf-record-file-result
                            fn-sf-record-link-result
                            fn-sf-record-dir-result
                            fn-sf-recovery-barrier)
                           (fn-sn-statep fn-sf-statep
                            fn-csi-record-directory-installs-next-completion)))))

(defun fn-csi-livep (s)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-sn-statep s)
       (fn-sn-identity-sequencep s)
       (fn-csi-completed-prefixp s)
       (fn-csi-completion-lastp s)))

(defthm fn-csi-initial-live
  (implies (and (fn-string-listp groups)
                (fn-no-duplicatesp groups)
                (natp capacity))
           (fn-csi-livep (fn-sn-initial groups capacity)))
  :hints (("Goal" :in-theory (enable fn-csi-livep))))

(defthm fn-csi-io-preserves-live
  (implies (fn-csi-livep s)
           (fn-csi-livep (fn-sn-io s operation result)))
  :hints (("Goal"
           :use (fn-sn-io-preserves-state
                 fn-sn-io-preserves-identity-sequence
                 fn-csi-io-preserves-completed-prefix
                 fn-csi-io-preserves-completion-last)
           :in-theory (e/d (fn-csi-livep)
                           (fn-sn-io fn-sn-statep
                            fn-sn-identity-sequencep
                            fn-csi-completed-prefixp
                            fn-csi-completion-lastp)))))

(defthm fn-csi-finish-preserves-live
  (implies (fn-csi-livep s)
           (fn-csi-livep (fn-sn-finish s)))
  :hints (("Goal"
           :cases ((fn-sn-completion-enabledp s))
           :use (fn-sn-finish-preserves-state
                 fn-sn-finish-preserves-identity-sequence
                 fn-sn-finish-disabled-is-no-op
                 fn-snt-finish-image
                 fn-csi-finish-preserves-sequenced-last-completion)
           :in-theory (e/d (fn-csi-livep fn-csi-completion-lastp)
                           (fn-sn-finish fn-sn-statep
                            fn-sn-identity-sequencep
                            fn-csi-completed-prefixp
                            fn-csi-finish-preserves-sequenced-last-completion)))))

(defthm fn-csi-prepare-consumer-preserves-completion-last
  (implies (fn-csi-completion-lastp s)
           (fn-csi-completion-lastp (fn-sn-prepare-consumer s event)))
  :hints (("Goal"
           :in-theory (e/d (fn-csi-completion-lastp
                            fn-sn-prepare-consumer fn-sn-update
                            fn-sf-prepare-record)
                           (fn-sn-statep fn-sf-statep
                            fn-cpe-projection-step fn-replay-apply-record
                            fn-cpe-eventp)))))

(defthm fn-csi-prepare-article-preserves-completion-last
  (implies (fn-csi-completion-lastp s)
           (fn-csi-completion-lastp (fn-sn-prepare s record)))
  :hints (("Goal"
           :in-theory (e/d (fn-csi-completion-lastp fn-sn-prepare
                            fn-sn-update fn-sf-prepare-record)
                           (fn-sn-statep fn-sf-statep fn-sn-prepare-node
                            fn-sn-record-bindsp)))))

(defthm fn-csi-prepare-retention-preserves-completion-last
  (implies (fn-csi-completion-lastp s)
           (fn-csi-completion-lastp (fn-sn-prepare-retention s event)))
  :hints (("Goal"
           :in-theory (e/d (fn-csi-completion-lastp
                            fn-sn-prepare-retention fn-sn-update
                            fn-sf-prepare-record)
                           (fn-sn-statep fn-sf-statep
                            fn-replay-apply-retention-event
                            fn-store-retention-event-p)))))

(defthm fn-csi-prepare-identity-preserves-completion-last
  (implies (fn-csi-completion-lastp s)
           (fn-csi-completion-lastp (fn-sn-prepare-identity s event)))
  :hints (("Goal"
           :in-theory (e/d (fn-csi-completion-lastp
                            fn-sn-prepare-identity fn-sn-update
                            fn-sf-prepare-record)
                           (fn-sn-statep fn-sf-statep
                            fn-replay-apply-record fn-replay-identity-step
                            fn-sn-identity-context fn-stxe-p fn-stxk-p
                            fn-stxa-p)))))

(defthm fn-csi-refuse-reservation-preserves-completion-last
  (implies (fn-csi-completion-lastp s)
           (fn-csi-completion-lastp (fn-sn-refuse-reservation s txid)))
  :hints (("Goal"
           :in-theory (e/d (fn-csi-completion-lastp
                            fn-sn-completion-record
                            fn-sn-refuse-reservation fn-sn-update
                            fn-sf-refuse-reservation)
                           (fn-sn-statep fn-sf-statep
                            fn-replay-advance-txid)))))

(defthm fn-csi-known-abort-preserves-completion-last
  (implies (fn-csi-completion-lastp s)
           (fn-csi-completion-lastp (fn-sn-known-abort s)))
  :hints (("Goal"
           :in-theory (e/d (fn-csi-completion-lastp fn-sn-known-abort
                            fn-sn-completion-record
                            fn-sn-known-abort-files
                            fn-sn-known-abort-file-start
                            fn-sn-update fn-sf-prepublish-abort
                            fn-sf-abort-completion
                            fn-sf-record-file-result)
                           (fn-sn-statep fn-sf-statep
                            fn-replay-advance-txid fn-node-complete)))))

; The topic record stages through the same file publication path, but does
; not consume the consumer replay prefix or the next Store journal sequence.
; These facts close the actual :prepare-topic dispatcher arm rather than
; excluding it from the mixed Store trace.
(defthm fn-csi-prepare-topic-preserves-completed-prefix
  (implies (fn-csi-completed-prefixp s)
           (fn-csi-completed-prefixp (fn-sn-prepare-topic s event)))
  :hints (("Goal"
           :in-theory (e/d (fn-csi-completed-prefixp
                            fn-sn-prepare-topic fn-sf-prepare-record)
                           (fn-cpe-projection-replay fn-sn-statep
                            fn-sf-statep fn-th-topic-eventp
                            fn-th-prefix-step fn-replay-apply-record)))))

(defthm fn-csi-prepare-topic-preserves-completion-last
  (implies (fn-csi-completion-lastp s)
           (fn-csi-completion-lastp (fn-sn-prepare-topic s event)))
  :hints (("Goal"
           :in-theory (e/d (fn-csi-completion-lastp
                            fn-sn-prepare-topic fn-sn-update
                            fn-sf-prepare-record)
                           (fn-sn-statep fn-sf-statep
                            fn-th-topic-eventp fn-th-prefix-step
                            fn-replay-apply-record)))))

(defthm fn-csi-prepare-topic-preserves-identity-sequence
  (implies (fn-sn-identity-sequencep s)
           (fn-sn-identity-sequencep (fn-sn-prepare-topic s event)))
  :hints (("Goal"
           :in-theory (e/d (fn-sn-identity-sequencep
                            fn-sn-prepare-topic fn-sn-update
                            fn-sf-prepare-record fn-sf-completion-phasep)
                           (fn-replay-apply-record fn-th-prefix-step
                            fn-th-topic-eventp fn-record-shape-vocabulary
                            fn-record-record-vocabulary)))))

(defthm fn-csi-prepare-topic-preserves-live
  (implies (fn-csi-livep s)
           (fn-csi-livep (fn-sn-prepare-topic s event)))
  :hints (("Goal"
           :use (fn-sn-prepare-topic-preserves-state
                 fn-csi-prepare-topic-preserves-identity-sequence
                 fn-csi-prepare-topic-preserves-completed-prefix
                 fn-csi-prepare-topic-preserves-completion-last)
           :in-theory (e/d (fn-csi-livep)
                           (fn-sn-prepare-topic fn-sn-statep
                            fn-sn-identity-sequencep
                            fn-csi-completed-prefixp
                            fn-csi-completion-lastp)))))

; This is the actual decoded Store dispatcher used by the owner.  Process
; death and recovery deliberately have a separate image/replay relation;
; every live publication event is covered here.
(defthm fn-csi-live-store-step-preserves-projection
  (implies (and (fn-csi-livep s)
                (not (member-equal (car event) '(:crash :recover))))
           (fn-csi-livep (fn-snrt-step s event)))
  :hints (("Goal"
           :in-theory (e/d (fn-csi-livep fn-snrt-step fn-snt-step)
                           (fn-sn-prepare fn-sn-prepare-retention
                            fn-sn-prepare-identity fn-sn-prepare-consumer
                            fn-sn-prepare-topic fn-th-topic-eventp
                            fn-th-prefix-step
                            fn-sn-io fn-sn-finish
                            fn-sn-refuse-reservation fn-sn-known-abort
                            fn-sn-statep fn-sn-identity-sequencep
                            fn-csi-completed-prefixp
                            fn-csi-completion-lastp)))))

(defun fn-csi-no-crash-eventsp (events)
  (declare (xargs :guard t :verify-guards nil :measure (len events)))
  (if (consp events)
      (and (not (member-equal (car (car events)) '(:crash :recover)))
           (fn-csi-no-crash-eventsp (cdr events)))
    (null events)))

(defthm fn-csi-live-store-trace-preserves-projection
  (implies (and (fn-csi-livep s)
                (fn-csi-no-crash-eventsp events))
           (fn-csi-livep (fn-snrt-run s events)))
  :hints (("Goal"
           :induct (fn-snrt-run s events)
           :in-theory (e/d (fn-csi-no-crash-eventsp fn-snrt-run)
                           (fn-csi-livep fn-snrt-step)))))

(defthm fn-csi-initial-no-crash-trace-live
  (implies (and (fn-string-listp groups)
                (fn-no-duplicatesp groups)
                (natp capacity)
                (fn-csi-no-crash-eventsp events))
           (fn-csi-livep
            (fn-snrt-run (fn-sn-initial groups capacity) events)))
  :hints (("Goal"
           :use (fn-csi-initial-live
                 (:instance fn-csi-live-store-trace-preserves-projection
                   (s (fn-sn-initial groups capacity))))
           :in-theory (disable fn-csi-livep fn-snrt-run))))

(defthm fn-csi-live-ready-exact-replay
  (implies (and (fn-csi-livep s)
                (equal (fn-sf-phase (fn-sn-files s)) :ready))
           (equal (fn-cpe-projection-replay
                   nil (fn-sf-records (fn-sn-files s)) 0)
                  (list :ok (fn-sn-consumer s))))
  :hints (("Goal"
           :use (fn-csi-ready-full-replay)
           :in-theory (e/d (fn-csi-livep)
                           (fn-csi-ready-full-replay)))))

(defthm fn-csi-initial-live-trace-ready-exact-replay
  (let ((after (fn-snrt-run (fn-sn-initial groups capacity) events)))
    (implies (and (fn-string-listp groups)
                  (fn-no-duplicatesp groups)
                  (natp capacity)
                  (fn-csi-no-crash-eventsp events)
                  (equal (fn-sf-phase (fn-sn-files after)) :ready))
             (equal (fn-cpe-projection-replay
                     nil (fn-sf-records (fn-sn-files after)) 0)
                    (list :ok (fn-sn-consumer after)))))
  :hints (("Goal"
           :use (fn-csi-initial-no-crash-trace-live
                 (:instance fn-csi-live-ready-exact-replay
                   (s (fn-snrt-run (fn-sn-initial groups capacity) events))))
           :in-theory (disable fn-csi-livep fn-snrt-run
                               fn-csi-live-ready-exact-replay))))

; Conjoin the original node/file history relation with the separately
; maintained exact consumer prefix.  This is a proof-side reachability
; relation: no served command evaluates it over historical records.
(defun fn-csi-full-relationp (s)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((files (fn-sn-files s))
         (phase (fn-sf-phase files)))
    (and (fn-snt-relation s)
         (if (member-equal phase '(:replaying :fault))
             (and (null (fn-sn-consumer s))
                  (eq (car (fn-cpe-projection-replay
                            nil (fn-sf-records files) 0)) :ok))
           (and (fn-sn-identity-sequencep s)
                (fn-snt-consumerp s))))))

(defthm fn-csi-initial-consumer-prefix-by-definition
  (fn-snt-consumerp (fn-sn-initial groups capacity))
  :hints (("Goal"
           :in-theory (enable fn-snt-consumerp fn-sn-initial
                              fn-sf-initial-state
                              fn-cpe-projection-replay))))

(defthm fn-csi-initial-is-ready-by-definition
  (equal (fn-sf-phase (fn-sn-files (fn-sn-initial groups capacity)))
         :ready)
  :hints (("Goal" :in-theory (enable fn-sn-initial
                                      fn-sf-initial-state))))

(defthm fn-csi-initial-full-relation
  (implies (and (fn-string-listp groups)
                (fn-no-duplicatesp groups)
                (natp capacity))
           (fn-csi-full-relationp (fn-sn-initial groups capacity)))
  :hints (("Goal"
           :use (fn-snt-initial-relation
                 fn-sn-initial-has-identity-sequence
                 fn-csi-initial-is-ready-by-definition
                 fn-csi-initial-consumer-prefix-by-definition)
           :in-theory (e/d (fn-csi-full-relationp)
                           (fn-sn-initial fn-snt-consumerp
                            fn-snt-relation fn-sn-identity-sequencep)))))

; A completed record is already in the physical directory but not yet in
; the carried projection.  Its checked next step makes that full directory
; strictly replayable, including a process death before fn-sn-finish.
(defthm fn-csi-related-current-history-strict-replay
  (let* ((files (fn-sn-files s))
         (phase (fn-sf-phase files))
         (records (fn-sf-records files)))
    (implies (and (fn-sn-statep s)
                  (fn-snt-consumerp s)
                  (not (member-equal phase '(:replaying :fault))))
             (eq (car (fn-cpe-projection-replay nil records 0)) :ok)))
  :hints (("Goal"
           :do-not '(preprocess)
           :use ((:instance fn-sf-state-records-are-true-list
                   (s (fn-sn-files s)))
                 (:instance fn-csi-one-more-prefix
                   (n (fn-sn-identity-next s))
                   (records (fn-sf-records (fn-sn-files s)))
                   (before (fn-sn-consumer s))
                   (event (fn-sn-completion-record s)))
                 (:instance fn-cbor-take-whole-list
                   (xs (fn-sf-records (fn-sn-files s)))))
           :in-theory (e/d (fn-snt-consumerp fn-sn-statep)
                           (fn-sf-statep fn-node-statep
                            take fn-csi-take-next
                            fn-cpe-projection-replay
                            fn-cpe-projection-step)))))

(defthm fn-csi-related-candidate-append-strict-replay
  (let* ((files (fn-sn-files s))
         (records (fn-sf-records files))
         (candidate (fn-sf-record-candidate files)))
    (implies (and (fn-sn-statep s)
                  (fn-snt-consumerp s)
                  (fn-sf-record-present-visiblep files))
             (eq (car (fn-cpe-projection-replay
                       nil (append records (list candidate)) 0)) :ok)))
  :hints (("Goal"
           :do-not '(preprocess)
           :use ((:instance fn-sf-state-records-are-true-list
                   (s (fn-sn-files s)))
                 (:instance fn-cpe-projection-replay-append-one
                   (s nil)
                   (prefix (fn-sf-records (fn-sn-files s)))
                   (start 0) (after (fn-sn-consumer s))
                   (event (fn-sf-record-candidate (fn-sn-files s)))))
           :in-theory (e/d (fn-snt-consumerp
                            fn-sf-record-present-visiblep
                            fn-sf-record-phasep)
                           (fn-sn-statep fn-sf-statep
                            fn-cpe-projection-replay
                            fn-cpe-projection-step
                            fn-cpe-projection-replay-append-one)))))

(defthm fn-csi-admissible-crash-image-strict-replay
  (let* ((files (fn-sn-files s))
         (phase (fn-sf-phase files)))
    (implies (and (fn-csi-full-relationp s)
                  (not (member-equal phase '(:replaying :fault)))
                  (fn-sf-crash-imagep files frontier records))
             (eq (car (fn-cpe-projection-replay nil records 0)) :ok)))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-snt-relation-implies-structural-state
                 fn-csi-related-current-history-strict-replay
                 fn-csi-related-candidate-append-strict-replay)
           :in-theory (e/d (fn-csi-full-relationp
                            fn-sf-crash-imagep)
                           (fn-snt-relation fn-snt-consumerp
                            fn-sn-statep fn-sf-statep
                            fn-cpe-projection-replay)))))

(defthm fn-csi-crash-erases-live-consumer-by-definition
  (implies (and (fn-sn-statep s)
                (fn-sf-crash-choicep frontier-choice record-choice))
           (and (equal (fn-sf-phase
                        (fn-sn-files
                         (fn-sn-crash s frontier-choice record-choice)))
                       :replaying)
                (null (fn-sn-consumer
                       (fn-sn-crash s frontier-choice record-choice)))))
  :hints (("Goal"
           :in-theory (e/d (fn-sn-crash fn-sf-crash)
                           (fn-sn-statep fn-sf-statep
                            fn-sf-crash-choicep)))))

(defthm fn-csi-live-crash-preserves-full-relation
  (let ((phase (fn-sf-phase (fn-sn-files s))))
    (implies (and (fn-csi-full-relationp s)
                  (not (member-equal phase '(:replaying :fault)))
                  (fn-sf-crash-choicep frontier-choice record-choice))
             (fn-csi-full-relationp
              (fn-sn-crash s frontier-choice record-choice))))
  :hints (("Goal"
           :use (fn-snt-relation-implies-structural-state
                 fn-snt-crash-preserves-relation
                 fn-sn-crash-files-are-kernel-crash
                 fn-csi-crash-erases-live-consumer-by-definition
                 (:instance fn-sf-crash-image-is-admissible
                   (s (fn-sn-files s)))
                 (:instance fn-csi-admissible-crash-image-strict-replay
                   (frontier
                    (fn-sf-frontier
                     (fn-sf-crash (fn-sn-files s)
                                  frontier-choice record-choice)))
                   (records
                    (fn-sf-records
                     (fn-sf-crash (fn-sn-files s)
                                  frontier-choice record-choice)))))
           :in-theory (e/d (fn-csi-full-relationp)
                           (fn-snt-relation fn-snt-consumerp
                            fn-sn-statep fn-sf-statep
                            fn-sn-crash fn-sf-crash
                            fn-cpe-projection-replay)))))

(defthm fn-csi-successful-recover-reconstructs-identity-sequence
  (let ((after (fn-sn-recover s)))
    (implies (and (fn-sn-statep s)
                  (equal (fn-sf-phase (fn-sn-files s)) :replaying)
                  (equal (fn-sf-phase (fn-sn-files after)) :recovering))
             (fn-sn-identity-sequencep after)))
  :hints (("Goal"
           :use ((:instance fn-replay-identity-ok-next-is-record-count
                   (records (fn-sf-records
                             (fn-sf-recover
                              (fn-sn-files s)
                              (fn-sn-groups s) (fn-sn-capacity s)))))
                 (:instance fn-sf-state-records-are-true-list
                   (s (fn-sn-files s))))
           :in-theory (e/d (fn-sn-identity-sequencep fn-sn-recover
                            fn-sn-update-replayed fn-sf-recover
                            fn-sf-completion-phasep)
                           (fn-sn-statep fn-sf-statep
                            fn-replay-identity fn-cpe-projection-replay)))))

(defthm fn-csi-recovering-completed-prefix-is-consumer-relation
  (implies (and (fn-sn-statep s)
                (equal (fn-sf-phase (fn-sn-files s)) :recovering)
                (fn-sn-identity-sequencep s)
                (fn-csi-completed-prefixp s))
           (fn-snt-consumerp s))
  :hints (("Goal"
           :use ((:instance fn-sf-state-records-are-true-list
                   (s (fn-sn-files s)))
                 (:instance fn-cbor-take-whole-list
                   (xs (fn-sf-records (fn-sn-files s)))))
           :in-theory (e/d (fn-snt-consumerp
                            fn-sn-identity-sequencep
                            fn-csi-completed-prefixp)
                           (fn-sn-statep fn-sf-statep
                            take fn-cpe-projection-replay)))))

(defthm fn-csi-recover-from-replaying-phase-by-definition
  (implies (and (fn-sn-statep s)
                (equal (fn-sf-phase (fn-sn-files s)) :replaying))
           (member-equal
            (fn-sf-phase (fn-sn-files (fn-sn-recover s)))
            '(:recovering :fault)))
  :hints (("Goal"
           :in-theory (e/d (fn-sn-recover fn-sf-recover)
                           (fn-sn-statep fn-sf-statep
                            fn-replay-identity
                            fn-cpe-projection-replay)))))

(defthm fn-csi-recover-fault-keeps-erased-consumer-by-definition
  (implies (and (fn-sn-statep s)
                (equal (fn-sf-phase (fn-sn-files s)) :replaying)
                (null (fn-sn-consumer s))
                (equal (fn-sf-phase (fn-sn-files (fn-sn-recover s))) :fault))
           (null (fn-sn-consumer (fn-sn-recover s))))
  :hints (("Goal"
           :in-theory (e/d (fn-sn-recover)
                           (fn-sn-statep fn-sf-statep
                            fn-replay-identity
                            fn-cpe-projection-replay)))))

(defthm fn-csi-recover-preserves-full-relation
  (let* ((after (fn-sn-recover s))
         (before-files (fn-sn-files s)))
    (implies (and (fn-csi-full-relationp s)
                  (equal (fn-sf-phase before-files) :replaying))
             (fn-csi-full-relationp after)))
  :hints (("Goal"
           :cases ((equal (fn-sf-phase
                           (fn-sn-files (fn-sn-recover s))) :recovering))
           :use (fn-snt-relation-implies-structural-state
                 fn-snt-recover-preserves-relation
                 fn-snt-recover-keeps-records
                 fn-csi-recover-from-replaying-phase-by-definition
                 fn-csi-recover-fault-keeps-erased-consumer-by-definition
                 fn-csi-successful-recover-reconstructs-identity-sequence
                 fn-csi-successful-recover-reconstructs-completed-prefix
                 (:instance fn-csi-recovering-completed-prefix-is-consumer-relation
                   (s (fn-sn-recover s))))
           :in-theory (e/d (fn-csi-full-relationp)
                           (fn-sn-recover fn-snt-relation
                            fn-sn-statep fn-sf-statep
                            fn-csi-completed-prefixp
                            fn-sn-identity-sequencep
                            fn-snt-consumerp fn-cpe-projection-replay)))))

(defthm fn-csi-related-next-is-natural
  (implies (fn-snt-relation s)
           (natp (fn-sn-identity-next s)))
  :hints (("Goal"
           :in-theory (e/d (fn-snt-relation fn-sn-statep)
                           (fn-sn-shapep fn-snt-pending-linkp
                            fn-snt-deferred-linkp
                            fn-snt-completion-linkp)))))

(defthm fn-csi-normal-full-relation-implies-live
  (implies (and (fn-csi-full-relationp s)
                (not (member-equal
                      (fn-sf-phase (fn-sn-files s))
                      '(:replaying :fault))))
           (fn-csi-livep s))
  :hints (("Goal"
           :use (fn-snt-relation-implies-structural-state
                 fn-csi-related-next-is-natural
                 (:instance fn-sf-state-records-are-true-list
                   (s (fn-sn-files s)))
                 (:instance fn-cbor-take-whole-list
                   (xs (fn-sf-records (fn-sn-files s)))))
           :in-theory (e/d (fn-csi-full-relationp fn-csi-livep
                            fn-snt-consumerp
                            fn-csi-completed-prefixp
                            fn-csi-completion-lastp)
                           (fn-snt-relation fn-sn-statep
                            fn-sn-identity-sequencep take
                            fn-cpe-projection-replay
                            fn-cpe-projection-step)))))

(defthm fn-csi-prepare-consumer-preserves-consumer-relation
  (implies (and (fn-sn-statep s)
                (fn-snt-consumerp s))
           (fn-snt-consumerp (fn-sn-prepare-consumer s event)))
  :hints (("Goal"
           :in-theory (e/d (fn-snt-consumerp
                            fn-sn-prepare-consumer
                            fn-sf-prepare-record)
                           (fn-sn-statep fn-sf-statep
                            fn-cpe-eventp fn-cpe-projection-step
                            fn-cpe-projection-replay
                            fn-store-event-p
                            fn-sn-completion-record)))))

(defthm fn-csi-prepare-article-preserves-consumer-relation
  (implies (and (fn-sn-statep s)
                (fn-snt-consumerp s))
           (fn-snt-consumerp (fn-sn-prepare s record)))
  :hints (("Goal"
           :in-theory (e/d (fn-snt-consumerp fn-sn-prepare
                            fn-sf-prepare-record)
                           (fn-sn-statep fn-sf-statep
                            fn-cpe-projection-step fn-cpe-projection-replay
                            fn-record-p fn-sn-completion-record)))))

(defthm fn-csi-prepare-retention-preserves-consumer-relation
  (implies (and (fn-sn-statep s)
                (fn-snt-consumerp s))
           (fn-snt-consumerp (fn-sn-prepare-retention s event)))
  :hints (("Goal"
           :in-theory (e/d (fn-snt-consumerp fn-sn-prepare-retention
                            fn-sf-prepare-record)
                           (fn-sn-statep fn-sf-statep
                            fn-cpe-projection-step fn-cpe-projection-replay
                            fn-store-retention-event-p
                            fn-sn-completion-record)))))

(defthm fn-csi-prepare-identity-preserves-consumer-relation
  (implies (and (fn-sn-statep s)
                (fn-snt-consumerp s))
           (fn-snt-consumerp (fn-sn-prepare-identity s event)))
  :hints (("Goal"
           :in-theory (e/d (fn-snt-consumerp fn-sn-prepare-identity
                            fn-sf-prepare-record)
                           (fn-sn-statep fn-sf-statep
                            fn-cpe-projection-step fn-cpe-projection-replay
                            fn-stxe-p fn-stxk-p fn-stxa-p
                            fn-sn-completion-record
                            fn-csi-live-ready-exact-replay
                            fn-csi-ready-full-replay)))))

(defthm fn-csi-io-preserves-consumer-relation
  (implies (and (fn-sn-statep s)
                (natp (fn-sn-identity-next s))
                (fn-sn-identity-sequencep s)
                (fn-snt-consumerp s))
           (fn-snt-consumerp (fn-sn-io s operation result)))
  :hints (("Goal"
           :use ((:instance fn-sf-state-records-are-true-list
                    (s (fn-sn-files s)))
                 (:instance fn-cbor-take-whole-list
                    (xs (fn-sf-records (fn-sn-files s))))
                 fn-csi-record-directory-installs-next-completion)
           :in-theory (e/d (fn-snt-consumerp fn-sn-identity-sequencep
                            fn-sn-io fn-sn-file-step
                            fn-sf-start-frontier
                            fn-sf-frontier-file-result
                            fn-sf-frontier-replace-result
                            fn-sf-frontier-dir-result
                            fn-sf-record-file-result
                            fn-sf-record-link-result
                            fn-sf-record-dir-result
                            fn-sf-recovery-barrier
                            fn-sn-completion-record)
                           (fn-sn-statep fn-sf-statep
                            fn-cpe-projection-replay
                            fn-cpe-projection-step)))))

(defthm fn-csi-finish-preserves-consumer-relation
  (implies (and (fn-sn-statep s)
                (natp (fn-sn-identity-next s))
                (fn-sn-identity-sequencep s)
                (fn-snt-consumerp s))
           (fn-snt-consumerp (fn-sn-finish s)))
  :hints (("Goal"
           :do-not '(preprocess)
           :cases ((fn-sn-completion-enabledp s))
           :use (fn-csi-finish-preserves-sequenced-last-completion
                 fn-snt-finish-image
                 fn-sn-finish-preserves-state
                 fn-sn-finish-preserves-identity-sequence
                 fn-sn-finish-disabled-is-no-op)
           :in-theory (e/d (fn-snt-consumerp
                            fn-csi-completed-prefixp
                            fn-sn-identity-sequencep
                            fn-sf-completion-phasep)
                           (fn-sn-finish fn-sn-statep fn-sf-statep
                            fn-sn-completion-enabledp
                            take fn-csi-take-next
                            fn-cpe-projection-replay
                            fn-cpe-projection-step
                            fn-sn-completion-record)))))

(defthm fn-csi-refuse-reservation-preserves-consumer-relation
  (implies (and (fn-sn-statep s)
                (fn-snt-consumerp s))
           (fn-snt-consumerp (fn-sn-refuse-reservation s txid)))
  :hints (("Goal"
           :in-theory (e/d (fn-snt-consumerp fn-sn-refuse-reservation
                            fn-sf-refuse-reservation fn-sn-completion-record)
                           (fn-sn-statep fn-sf-statep
                            fn-cpe-projection-replay
                            fn-cpe-projection-step)))))

(defthm fn-csi-known-abort-preserves-consumer-relation
  (implies (and (fn-sn-statep s)
                (fn-snt-consumerp s))
           (fn-snt-consumerp (fn-sn-known-abort s)))
  :hints (("Goal"
           :in-theory (e/d (fn-snt-consumerp fn-sn-known-abort
                            fn-sn-known-abort-files
                            fn-sn-known-abort-file-start
                            fn-sf-prepublish-abort
                            fn-sf-abort-completion
                            fn-sf-record-file-result
                            fn-sn-completion-record)
                           (fn-sn-statep fn-sf-statep
                            fn-cpe-projection-replay
                            fn-cpe-projection-step)))))

; A topic event is a neutral consumer event, but its dense sequence still
; advances the consumer frontier.  The Store candidate and reserved txid
; provide the finite bound needed by fn-cpe-projection-step.
(defthm fn-csi-topic-event-is-not-consumer-event
  (implies (fn-th-topic-eventp event)
           (not (fn-cpe-eventp event)))
  :hints (("Goal" :in-theory (e/d (fn-th-topic-eventp fn-cpe-eventp
                                   fn-th-local-admin-eventp fn-th-at)
                                  (fn-th-source-id-p fn-th-auth-ref-p
                                   fn-th-exact-octets-p)))))

(defthm fn-csi-step-frontier-after-nonnull-success
  (implies (and (natp expected)
                (or (null s) (equal (fn-cp-nth 3 s) expected))
                (eq (car (fn-cpe-projection-step s event expected)) :ok)
                (not (null (fn-cp-nth 1
                            (fn-cpe-projection-step s event expected)))))
           (equal (fn-cp-nth 3 (fn-cp-nth 1
                                 (fn-cpe-projection-step s event expected)))
                  (1+ expected)))
  :hints (("Goal" :in-theory (enable fn-cpe-projection-step
                                      fn-cpe-projection-advance))))

(defthm fn-csi-second-of-ok-by-definition
  (equal (fn-cp-nth 1 (list :ok x)) x)
  :hints (("Goal" :in-theory (enable fn-cp-nth))))

(defthm fn-csi-replay-keeps-frontier-aligned
  (implies (and (natp expected)
                (or (null s) (equal (fn-cp-nth 3 s) expected))
                (eq (car (fn-cpe-projection-replay s records expected)) :ok))
           (or (null (fn-cp-nth 1
                       (fn-cpe-projection-replay s records expected)))
               (equal (fn-cp-nth 3
                        (fn-cp-nth 1
                         (fn-cpe-projection-replay s records expected)))
                      (+ expected (len records)))))
  :hints (("Goal" :induct (fn-cpe-projection-replay s records expected)
           :in-theory (e/d (fn-cpe-projection-replay)
                           (fn-cpe-projection-step fn-cp-nth null)))))

(defthm fn-csi-record-count-below-next-lower
  (implies (and (fn-sf-record-listp records sequence lower frontier)
                (natp sequence)
                (<= sequence lower))
           (<= (+ sequence (len records))
               (fn-sf-next-lower records lower)))
  :rule-classes nil
  :hints (("Goal" :induct (fn-sf-record-listp records sequence lower frontier)
           :in-theory (enable fn-sf-record-listp fn-sf-next-lower))))

(defthm fn-csi-candidate-sequence-below-max
  (implies (and (fn-sf-record-listp records 0 0 frontier)
                (fn-record-uint32p frontier)
                (fn-sf-candidatep event records frontier))
           (< (len records) *fn-cbor-max-uint*))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-csi-record-count-below-next-lower
                                      (sequence 0) (lower 0)))
           :in-theory (e/d (fn-sf-candidatep fn-record-uint32p)
                           (fn-sf-record-listp fn-sf-next-lower)))))

(defthm fn-csi-topic-candidate-preserves-consumer-frontier
  (implies (and (fn-sf-record-listp records 0 0 frontier)
                (fn-record-uint32p frontier)
                (fn-sf-candidatep event records frontier)
                (fn-th-topic-eventp event)
                (or (null consumer)
                    (equal (fn-cp-nth 3 consumer) (len records))))
           (eq (car (fn-cpe-projection-step consumer event (len records))) :ok))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-csi-candidate-sequence-below-max))
           :in-theory (e/d (fn-cpe-projection-step fn-sf-candidatep)
                           (fn-sf-record-listp fn-sf-next-lower
                            fn-th-topic-eventp fn-cpe-eventp)))))

(defthm fn-csi-prepare-topic-preserves-consumer-relation
  (implies (and (fn-sn-statep s)
                (natp (fn-sn-identity-next s))
                (fn-sn-identity-sequencep s)
                (fn-snt-consumerp s))
           (fn-snt-consumerp (fn-sn-prepare-topic s event)))
  :hints (("Goal"
           :use ((:instance fn-csi-replay-keeps-frontier-aligned
                    (s nil) (records (fn-sf-records (fn-sn-files s)))
                    (expected 0))
                 (:instance fn-csi-topic-candidate-preserves-consumer-frontier
                    (records (fn-sf-records (fn-sn-files s)))
                    (frontier (fn-sf-frontier (fn-sn-files s)))
                    (consumer (fn-sn-consumer s))))
           :in-theory (e/d (fn-snt-consumerp fn-sn-prepare-topic
                            fn-sn-identity-sequencep fn-sf-prepare-record
                            fn-sn-update fn-sf-statep fn-sf-phase-shapep)
                           (fn-sn-statep fn-cpe-projection-replay
                            fn-cpe-projection-step fn-sn-make-v6 fn-sn-make-v7
                            fn-th-topic-eventp fn-sf-record-listp
                            fn-csi-live-ready-exact-replay
                            fn-csi-ready-full-replay)))))

(defthm fn-csi-normal-step-preserves-consumer-relation
  (implies (and (fn-sn-statep s)
                (natp (fn-sn-identity-next s))
                (fn-sn-identity-sequencep s)
                (fn-snt-consumerp s)
                (not (member-equal (car event) '(:crash :recover))))
           (fn-snt-consumerp (fn-snrt-step s event)))
  :hints (("Goal"
           :in-theory (e/d (fn-snrt-step fn-snt-step)
                           (fn-sn-statep fn-snt-consumerp
                            fn-sn-prepare fn-sn-prepare-retention
                            fn-sn-prepare-identity fn-sn-prepare-consumer
                            fn-sn-prepare-topic
                            fn-sn-io fn-sn-finish
                            fn-sn-refuse-reservation fn-sn-known-abort)))))

(defthm fn-csi-normal-step-stays-normal
  (implies (and (fn-sn-statep s)
                (natp (fn-sn-identity-next s))
                (not (member-equal
                      (fn-sf-phase (fn-sn-files s)) '(:replaying :fault)))
                (not (member-equal (car event) '(:crash :recover))))
           (not (member-equal
                 (fn-sf-phase (fn-sn-files (fn-snrt-step s event)))
                 '(:replaying :fault))))
  :hints (("Goal"
           :cases ((fn-sn-completion-enabledp s))
           :use (fn-snt-finish-image fn-sn-finish-disabled-is-no-op
                 (:instance fn-sn-refuse-reservation-is-exact-advance
                   (txid (cadr event)))
                 (:instance fn-sn-refuse-reservation-disabled-is-no-op
                   (txid (cadr event)))
                 (:instance fn-sn-known-abort-files-reaches-ready
                   (files (fn-sn-files s)))
                 fn-sn-known-abort-disabled-is-no-op)
           :in-theory (e/d (fn-snrt-step fn-snt-step
                            fn-sn-known-abort-enabledp
                            fn-sn-prepare fn-sn-prepare-retention
                            fn-sn-prepare-identity fn-sn-prepare-consumer
                            fn-sn-io fn-sn-file-step
                            fn-sn-refuse-reservation fn-sn-known-abort
                            fn-sf-start-frontier
                            fn-sf-frontier-file-result
                            fn-sf-frontier-replace-result
                            fn-sf-frontier-dir-result
                            fn-sf-record-file-result
                            fn-sf-record-link-result
                            fn-sf-record-dir-result
                            fn-sf-recovery-barrier
                            fn-sf-refuse-reservation)
                           (fn-sn-statep fn-sf-statep
                            fn-cpe-projection-replay
                            fn-cpe-projection-step
                            fn-replay-apply-record
                            fn-replay-apply-retention-event
                            fn-sn-completion-enabledp fn-sn-finish
                            fn-sn-known-abort-files
                            fn-record-p fn-store-event-p
                            fn-stxe-p fn-stxk-p fn-stxa-p)))))

(defthm fn-csi-normal-step-preserves-identity-sequence
  (implies (and (fn-sn-identity-sequencep s)
                (not (member-equal (car event) '(:crash :recover))))
           (fn-sn-identity-sequencep (fn-snrt-step s event)))
  :hints (("Goal"
           :in-theory (e/d (fn-snrt-step fn-snt-step)
                           (fn-sn-identity-sequencep
                            fn-sn-prepare fn-sn-prepare-retention
                            fn-sn-prepare-identity fn-sn-prepare-consumer
                            fn-sn-prepare-topic
                            fn-sn-io fn-sn-finish
                            fn-sn-refuse-reservation fn-sn-known-abort)))))

(defthm fn-csi-normal-step-preserves-full-relation
  (implies (and (fn-csi-full-relationp s)
                (not (member-equal
                      (fn-sf-phase (fn-sn-files s)) '(:replaying :fault)))
                (not (member-equal (car event) '(:crash :recover))))
           (fn-csi-full-relationp (fn-snrt-step s event)))
  :hints (("Goal"
           :use (fn-snrt-step-preserves-relation
                 fn-csi-normal-full-relation-implies-live
                 fn-csi-live-store-step-preserves-projection
                 fn-csi-normal-step-preserves-consumer-relation
                 fn-csi-normal-step-stays-normal
                 fn-csi-normal-step-preserves-identity-sequence)
           :in-theory (e/d (fn-csi-full-relationp fn-csi-livep)
                           (fn-snrt-step fn-snt-relation
                            fn-snt-consumerp fn-sn-statep
                            fn-sn-identity-sequencep)))))

(defthm fn-csi-replaying-crash-preserves-full-relation
  (implies (and (fn-csi-full-relationp s)
                (equal (fn-sf-phase (fn-sn-files s)) :replaying)
                (fn-sf-crash-choicep frontier-choice record-choice))
           (fn-csi-full-relationp
            (fn-sn-crash s frontier-choice record-choice)))
  :hints (("Goal"
           :use (fn-snt-relation-implies-structural-state
                 fn-snt-crash-preserves-relation
                 fn-csi-crash-erases-live-consumer-by-definition)
           :in-theory (e/d (fn-csi-full-relationp fn-sn-crash fn-sf-crash)
                           (fn-snt-relation fn-sn-statep fn-sf-statep
                            fn-cpe-projection-replay)))))

(defthm fn-csi-fault-crash-preserves-full-relation
  (implies (and (fn-csi-full-relationp s)
                (equal (fn-sf-phase (fn-sn-files s)) :fault)
                (fn-sf-crash-choicep frontier-choice record-choice))
           (fn-csi-full-relationp
            (fn-sn-crash s frontier-choice record-choice)))
  :hints (("Goal"
           :use (fn-snt-relation-implies-structural-state
                 fn-snt-crash-preserves-relation
                 fn-csi-crash-erases-live-consumer-by-definition)
           :in-theory (e/d (fn-csi-full-relationp fn-sn-crash fn-sf-crash)
                           (fn-snt-relation fn-sn-statep fn-sf-statep
                            fn-cpe-projection-replay)))))

(defthm fn-csi-recover-outside-replaying-is-no-op-by-definition
  (implies (not (equal (fn-sf-phase (fn-sn-files s)) :replaying))
           (equal (fn-sn-recover s) s))
  :hints (("Goal" :in-theory (enable fn-sn-recover))))

(defthm fn-csi-replay-or-fault-normal-step-is-no-op
  (implies (and (fn-sn-statep s)
                (member-equal (fn-sf-phase (fn-sn-files s))
                              '(:replaying :fault))
                (not (member-equal (car event) '(:crash :recover))))
           (equal (fn-snrt-step s event) s))
  :hints (("Goal"
           :use (fn-snt-state-reconstruction)
           :in-theory (e/d (fn-snrt-step fn-snt-step
                            fn-sn-refuse-reservation-enabledp
                            fn-sn-known-abort-enabledp
                            fn-sn-prepare fn-sn-prepare-retention
                            fn-sn-prepare-identity fn-sn-prepare-consumer
                            fn-sn-io fn-sn-file-step fn-sn-finish
                            fn-sn-refuse-reservation fn-sn-known-abort
                            fn-sn-completion-enabledp
                            fn-sf-start-frontier
                            fn-sf-frontier-file-result
                            fn-sf-frontier-replace-result
                            fn-sf-frontier-dir-result
                            fn-sf-record-file-result
                            fn-sf-record-link-result
                            fn-sf-record-dir-result
                            fn-sf-recovery-barrier)
                           (fn-sn-statep fn-sf-statep
                            fn-cpe-projection-replay fn-cpe-projection-step
                            fn-replay-apply-record
                            fn-replay-apply-retention-event)))))

(defthm fn-csi-replay-or-fault-normal-step-preserves-full-relation
  (implies (and (fn-csi-full-relationp s)
                (member-equal (fn-sf-phase (fn-sn-files s))
                              '(:replaying :fault))
                (not (member-equal (car event) '(:crash :recover))))
           (fn-csi-full-relationp (fn-snrt-step s event)))
  :hints (("Goal"
           :use (fn-snt-relation-implies-structural-state
                 fn-csi-replay-or-fault-normal-step-is-no-op)
           :in-theory (e/d (fn-csi-full-relationp)
                           (fn-snt-relation fn-sn-statep
                            fn-snrt-step)))))

; The actual owner-decoded Store dispatcher: valid crash choices preserve
; the completed prefix; invalid choices are no-ops.  Recovery reconstructs
; the projection from physical records before service resumes.
(defthm fn-csi-invalid-crash-choice-is-no-op-by-definition
  (implies (not (fn-sf-crash-choicep frontier-choice record-choice))
           (equal (fn-sn-crash s frontier-choice record-choice) s))
  :hints (("Goal" :in-theory (enable fn-sn-crash))))

(defthm fn-csi-store-step-preserves-full-relation
  (implies (fn-csi-full-relationp s)
           (fn-csi-full-relationp (fn-snrt-step s event)))
  :hints (("Goal"
           :cases ((member-equal (fn-sf-phase (fn-sn-files s))
                                 '(:replaying :fault))
                   (equal (car event) :crash)
                   (equal (car event) :recover)
                   (fn-sf-crash-choicep (cadr event) (caddr event)))
           :use (fn-csi-normal-step-preserves-full-relation
                 (:instance fn-csi-live-crash-preserves-full-relation
                   (frontier-choice (cadr event))
                   (record-choice (caddr event)))
                 (:instance fn-csi-replaying-crash-preserves-full-relation
                   (frontier-choice (cadr event))
                   (record-choice (caddr event)))
                 (:instance fn-csi-fault-crash-preserves-full-relation
                   (frontier-choice (cadr event))
                   (record-choice (caddr event)))
                 fn-csi-recover-preserves-full-relation
                 fn-csi-recover-outside-replaying-is-no-op-by-definition
                 (:instance fn-csi-invalid-crash-choice-is-no-op-by-definition
                   (frontier-choice (cadr event))
                   (record-choice (caddr event)))
                 fn-csi-replay-or-fault-normal-step-preserves-full-relation)
           :in-theory (e/d (fn-snrt-step fn-snt-step)
                           (fn-csi-full-relationp fn-sn-crash
                            fn-sn-recover)))))

(defthm fn-csi-store-trace-preserves-full-relation
  (implies (fn-csi-full-relationp s)
           (fn-csi-full-relationp (fn-snrt-run s events)))
  :hints (("Goal"
           :induct (fn-snrt-run s events)
           :in-theory (e/d (fn-snrt-run)
                           (fn-csi-full-relationp fn-snrt-step)))))

(defthm fn-csi-initialized-mixed-trace-has-full-relation
  (implies (and (fn-string-listp groups)
                (fn-no-duplicatesp groups)
                (natp capacity))
           (fn-csi-full-relationp
            (fn-snrt-run (fn-sn-initial groups capacity) events)))
  :hints (("Goal"
           :use (fn-csi-initial-full-relation
                 (:instance fn-csi-store-trace-preserves-full-relation
                   (s (fn-sn-initial groups capacity))))
           :in-theory (disable fn-snrt-run fn-sn-initial
                               fn-csi-full-relationp))))

; Recovery may lose the last, unacknowledged record that the new process
; scanned from a dead writer's page cache.  Strict consumer replay is prefix
; closed, so this physical rollback never turns a valid prefix into an
; invalid consumer history.  Keep the step interpreter closed in this proof.
(defthm fn-csi-strict-replay-but-last
  (implies (and (true-listp records)
                (eq (car (fn-cpe-projection-replay projection records first))
                    :ok))
           (eq (car (fn-cpe-projection-replay
                     projection (fn-sf-but-last records) first)) :ok))
  :hints (("Goal" :induct (fn-cpe-projection-replay projection records first)
           :in-theory (e/d (fn-sf-but-last fn-cpe-projection-replay)
                           (fn-cpe-projection-step)))))

(defthm fn-csi-full-relation-current-history-strict-replay
  (implies (fn-csi-full-relationp s)
           (fn-sn-observed-consumer-okp
            (fn-sf-records (fn-sn-files s))))
  :hints (("Goal"
           :cases ((member-equal (fn-sf-phase (fn-sn-files s))
                                 '(:replaying :fault)))
           :use (fn-csi-related-current-history-strict-replay)
           :in-theory (e/d (fn-csi-full-relationp
                            fn-sn-observed-consumer-okp)
                           (fn-snt-relation fn-snt-consumerp
                            fn-cpe-projection-replay)))))

(defthm fn-csi-recovery-crash-image-strict-replay
  (implies (and (fn-csi-full-relationp s)
                (fn-sf-recovery-crash-imagep
                 (fn-sn-files s) frontier records))
           (fn-sn-observed-consumer-okp records))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-csi-full-relation-current-history-strict-replay
                 fn-csi-related-candidate-append-strict-replay
                 (:instance fn-csi-strict-replay-but-last
                   (projection nil)
                   (records (fn-sf-records (fn-sn-files s)))
                   (first 0)))
           :in-theory (e/d (fn-sf-recovery-crash-imagep
                            fn-sn-observed-consumer-okp
                            fn-csi-full-relationp
                            fn-sf-record-present-visiblep)
                           (fn-snt-relation fn-snt-consumerp
                            fn-cpe-projection-replay)))))
