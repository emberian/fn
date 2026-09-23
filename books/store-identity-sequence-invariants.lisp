; Maintained journal-sequence relation for the actual Store node.
(in-package "ACL2")
(include-book "store-node-resolution")

; A successful record-directory observation has appended the record before the
; single fn-sn-finish call advances the carried journal cursor.  Therefore the
; completing phase is exactly one record ahead; every other observable phase
; has equal committed-record count and next journal sequence.  :completed is
; included because it is the internal file-kernel phase between core completion
; and success emission, although no host call can observe it.
(defun fn-sn-identity-sequencep (s)
  (declare (xargs :guard (fn-sn-statep s) :verify-guards nil))
  (let* ((files (fn-sn-files s))
         (count (len (fn-sf-records files)))
         (next (fn-sn-identity-next s)))
    (if (fn-sf-completion-phasep (fn-sf-phase files))
        (equal count (1+ next))
      (equal count next))))

(verify-guards fn-sn-identity-sequencep
  :hints (("Goal" :in-theory (enable fn-sn-statep))))

(local
 (defthm fn-sis-len-of-append-singleton
   (equal (len (append xs (list x))) (1+ (len xs)))
   :hints (("Goal" :induct (len xs)))))

(defthm fn-sn-initial-has-identity-sequence
  (fn-sn-identity-sequencep (fn-sn-initial groups capacity))
  :hints (("Goal" :in-theory (enable fn-sn-identity-sequencep
                                      fn-sn-initial fn-sf-initial-state
                                      fn-sf-completion-phasep))))

; Reservation refusal may burn an allocator txid, but it cannot consume a
; Store journal sequence or append a committed record.
(defthm fn-sn-refuse-reservation-preserves-identity-next
  (equal (fn-sn-identity-next (fn-sn-refuse-reservation s txid))
         (fn-sn-identity-next s))
  :hints (("Goal" :in-theory (enable fn-sn-refuse-reservation
                                      fn-sn-update))))

(defthm fn-sn-refuse-reservation-preserves-identity-sequence
  (implies (fn-sn-identity-sequencep s)
           (fn-sn-identity-sequencep
            (fn-sn-refuse-reservation s txid)))
  :hints (("Goal"
           :in-theory (enable fn-sn-identity-sequencep
                              fn-sn-refuse-reservation fn-sn-update
                              fn-sf-refuse-reservation))))

; Known abort removes only an unpublished candidate.  It preserves the exact
; committed record list and the maintained journal cursor.
(defthm fn-sn-known-abort-preserves-identity-next
  (equal (fn-sn-identity-next (fn-sn-known-abort s))
         (fn-sn-identity-next s))
  :hints (("Goal" :in-theory (enable fn-sn-known-abort fn-sn-update))))

(defthm fn-sn-known-abort-preserves-identity-sequence
  (implies (fn-sn-identity-sequencep s)
           (fn-sn-identity-sequencep (fn-sn-known-abort s)))
  :hints (("Goal"
           :in-theory (enable fn-sn-identity-sequencep fn-sn-known-abort
                              fn-sn-known-abort-files
                              fn-sn-known-abort-file-start fn-sn-update
                              fn-sf-prepublish-abort
                              fn-sf-abort-completion
                              fn-sf-record-file-result))))

; Preparation stages only a candidate.  It neither appends the durable record
; list nor consumes the journal cursor, for all three actual preparation
; entrypoints used by the host.
(defthm fn-sn-prepare-preserves-identity-sequence
  (implies (fn-sn-identity-sequencep s)
           (fn-sn-identity-sequencep (fn-sn-prepare s record)))
  :hints (("Goal"
           :in-theory (enable fn-sn-identity-sequencep fn-sn-prepare
                              fn-sn-update fn-sf-prepare-record
                              fn-sf-completion-phasep))))

(defthm fn-sn-prepare-retention-preserves-identity-sequence
  (implies (fn-sn-identity-sequencep s)
           (fn-sn-identity-sequencep (fn-sn-prepare-retention s event)))
  :hints (("Goal"
           :in-theory (enable fn-sn-identity-sequencep
                              fn-sn-prepare-retention fn-sn-update
                              fn-sf-prepare-record
                              fn-sf-completion-phasep))))

(defthm fn-sn-prepare-identity-preserves-identity-sequence
  (implies (fn-sn-identity-sequencep s)
           (fn-sn-identity-sequencep (fn-sn-prepare-identity s event)))
  :hints (("Goal"
           :in-theory (e/d (fn-sn-identity-sequencep
                            fn-sn-prepare-identity fn-sn-update
                            fn-sf-prepare-record fn-sf-completion-phasep)
                           (fn-replay-apply-record fn-replay-identity-step
                            fn-sn-identity-context fn-stxa-p fn-stxe-p
                            fn-stxk-p fn-record-shape-vocabulary
                            fn-record-record-vocabulary)))))

(defthm fn-sn-prepare-consumer-preserves-identity-sequence
  (implies (fn-sn-identity-sequencep s)
           (fn-sn-identity-sequencep (fn-sn-prepare-consumer s event)))
  :hints (("Goal"
           :in-theory (e/d (fn-sn-identity-sequencep
                            fn-sn-prepare-consumer fn-sn-update
                            fn-sf-prepare-record fn-sf-completion-phasep)
                           (fn-replay-apply-record
                            fn-cpe-projection-step fn-cpe-eventp
                            fn-record-shape-vocabulary
                            fn-record-record-vocabulary)))))

; The actual host-called observation transition accounts for the only
; off-by-one window: :record-directory/:ok appends the record and enters
; :completing while the cursor still names that record.
(defthm fn-sn-io-preserves-identity-sequence
  (implies (fn-sn-identity-sequencep s)
           (fn-sn-identity-sequencep (fn-sn-io s operation result)))
  :hints (("Goal"
           :in-theory (enable fn-sn-identity-sequencep fn-sn-io
                              fn-sn-file-step fn-sn-update
                              fn-sf-start-frontier
                              fn-sf-frontier-file-result
                              fn-sf-frontier-replace-result
                              fn-sf-frontier-dir-result
                              fn-sf-record-file-result
                              fn-sf-record-link-result
                              fn-sf-record-dir-result
                              fn-sf-recovery-barrier
                              fn-sf-completion-phasep))))

(local
 (defthm fn-sis-snapshot-ok-next
   (implies (and (natp (fn-stxk-context-next ctx))
                 (equal (fn-stxk-context-kind ctx) :ok)
                 (equal (fn-stxk-context-kind
                         (fn-stxk-apply-snapshot ctx e)) :ok))
            (equal (fn-stxk-context-next (fn-stxk-apply-snapshot ctx e))
                   (1+ (fn-stxk-context-next ctx))))
   :hints (("Goal" :in-theory
            (e/d (fn-stxk-apply-snapshot fn-stxk-fault fn-stxk-context)
                 (fn-stxk-p fn-stxk-find fn-stxk-same-snapshotp))))))

(local
 (defthm fn-sis-verdict-ok-next
   (implies (and (natp (fn-stxk-context-next ctx))
                 (equal (fn-stxk-context-kind ctx) :ok)
                 (equal (fn-stxk-context-kind
                         (fn-stxk-apply-verdict ctx e)) :ok))
            (equal (fn-stxk-context-next (fn-stxk-apply-verdict ctx e))
                   (1+ (fn-stxk-context-next ctx))))
   :hints (("Goal" :in-theory
            (e/d (fn-stxk-apply-verdict fn-stxk-fault fn-stxk-context)
                 (fn-stxe-p fn-stxk-find))))))

(local
 (defthm fn-sis-step-ok-next
   (implies (and (natp (fn-stxk-context-next ctx))
                 (equal (fn-stxk-context-kind ctx) :ok)
                 (equal (fn-stxk-context-kind
                         (fn-replay-identity-step ctx event)) :ok))
            (equal (fn-stxk-context-next
                    (fn-replay-identity-step ctx event))
                   (1+ (fn-stxk-context-next ctx))))
   :hints (("Goal"
            :use ((:instance fn-sis-snapshot-ok-next (e event))
                  (:instance fn-sis-verdict-ok-next (e event))
                  (:instance fn-sis-verdict-ok-next
                   (e (fn-stmt-value
                       (fn-stxe-decode-exact (fn-stxa-verdict-event event))))))
            :in-theory
            (e/d (fn-replay-identity-step fn-replay-identity-advance
                  fn-stxk-fault fn-stxk-context)
                 (fn-stxk-p fn-stxe-p fn-stxa-p fn-stxa-bindsp
                  fn-hsig-article-event-snapshot-bindsp
                  fn-stxk-apply-snapshot fn-stxk-apply-verdict
                  fn-stxe-decode-exact fn-stxk-find
                  fn-record-shape-vocabulary
                  fn-record-record-vocabulary))))))

(local
 (defthm fn-sis-loop-ok-implies-input-ok
   (implies (equal (fn-stxk-context-kind
                    (fn-replay-identity-loop records ctx)) :ok)
            (equal (fn-stxk-context-kind ctx) :ok))
   :hints (("Goal"
            :induct (fn-replay-identity-loop records ctx)
            :in-theory
            (e/d (fn-replay-identity-loop fn-replay-identity-step
                  fn-stxk-fault fn-stxk-context)
                 (fn-store-event-p fn-stxk-p fn-stxe-p fn-stxa-p
                  fn-stxa-bindsp fn-hsig-article-event-snapshot-bindsp
                  fn-stxk-apply-snapshot fn-stxk-apply-verdict
                  fn-stxe-decode-exact fn-stxk-find
                  fn-record-shape-vocabulary
                  fn-record-record-vocabulary))))))

(local
 (defthm fn-replay-identity-loop-ok-next
  (implies (and (true-listp records)
                (natp (fn-stxk-context-next ctx))
                (equal (fn-stxk-context-kind ctx) :ok)
                (equal (fn-stxk-context-kind
                        (fn-replay-identity-loop records ctx)) :ok))
           (equal (fn-stxk-context-next
                   (fn-replay-identity-loop records ctx))
                  (+ (fn-stxk-context-next ctx) (len records))))
  :hints (("Goal"
           :in-theory (e/d (fn-replay-identity-loop fn-stxk-fault
                            fn-stxk-context)
                           (fn-replay-identity-step fn-store-event-p
                            fn-record-shape-vocabulary
                            fn-record-record-vocabulary))
           :induct (fn-replay-identity-loop records ctx))
          ("Subgoal *1/2.4"
           :use ((:instance fn-sis-loop-ok-implies-input-ok
                            (records (cdr records))
                            (ctx (fn-replay-identity-step ctx (car records))))
                 (:instance fn-sis-step-ok-next (event (car records)))))
          ("Subgoal *1/2.3"
           :use ((:instance fn-sis-loop-ok-implies-input-ok
                            (records (cdr records))
                            (ctx (fn-replay-identity-step ctx (car records))))
                 (:instance fn-sis-step-ok-next (event (car records)))))
          ("Subgoal *1/2.2"
           :use ((:instance fn-sis-loop-ok-implies-input-ok
                            (records (cdr records))
                            (ctx (fn-replay-identity-step ctx (car records))))
                 (:instance fn-sis-step-ok-next (event (car records)))))
          ("Subgoal *1/2.1"
           :use ((:instance fn-sis-loop-ok-implies-input-ok
                            (records (cdr records))
                            (ctx (fn-replay-identity-step ctx (car records))))
                 (:instance fn-sis-step-ok-next (event (car records))))))))

(defthm fn-replay-identity-ok-next-is-record-count
  (implies (and (true-listp records)
                (equal (fn-stxk-context-kind (fn-replay-identity records)) :ok))
           (equal (fn-stxk-context-next (fn-replay-identity records))
                  (len records)))
  :hints (("Goal"
           :use ((:instance fn-replay-identity-loop-ok-next
                            (ctx (fn-stxk-initial-context 0))))
           :in-theory (e/d (fn-replay-identity fn-stxk-initial-context
                            fn-stxk-context)
                           (fn-replay-identity-loop
                            fn-replay-identity-loop-ok-next)))))

; Recovery folds the same ordered event stream.  A successful fold installs
; its exact next cursor; a failed fold retains the prior state.  The allocator
; frontier is intentionally absent from this theorem.
(defthm fn-sn-recover-preserves-identity-sequence
  (implies (fn-sn-identity-sequencep s)
           (fn-sn-identity-sequencep (fn-sn-recover s)))
  :hints (("Goal"
           :use ((:instance fn-replay-identity-ok-next-is-record-count
                            (records
                             (fn-sf-records
                              (fn-sf-recover (fn-sn-files s)
                                             (fn-sn-groups s)
                                             (fn-sn-capacity s))))))
           :in-theory (enable fn-sn-identity-sequencep fn-sn-recover
                              fn-sn-update fn-sn-update-replayed
                              fn-sf-recover fn-sf-completion-phasep))))

; A matching kernel completion moves :completing to :ready and keeps the
; committed record list.  These facts do not depend on the record's kind.
(local
 (defthm fn-sis-file-completion-ready
   (implies (and (fn-sf-statep files)
                 (equal (fn-sf-phase files) :completing)
                 (equal (cons sequence txid) (fn-sf-completion files)))
            (equal (fn-sf-phase
                    (fn-sf-emit-success
                     (fn-sf-core-completion files sequence txid)
                     sequence txid))
                   :ready))
   :hints (("Goal"
            :use ((:instance fn-sf-core-completion-preserves-state
                             (s files)))
            :in-theory (e/d (fn-sf-core-completion fn-sf-emit-success)
                            (fn-sf-statep
                             fn-sf-core-completion-preserves-state))))))

(local
 (defthm fn-sis-file-completion-keeps-records
   (equal (fn-sf-records
           (fn-sf-emit-success
            (fn-sf-core-completion files sequence txid)
            sequence txid))
          (fn-sf-records files))
   :hints (("Goal" :in-theory
            (enable fn-sf-core-completion fn-sf-emit-success)))))

; The actual finish gate checks the file state and exact completion pair.
(local
 (defthm fn-sis-enabled-files-and-pair
   (implies (fn-sn-completion-enabledp s)
            (and (fn-sf-statep (fn-sn-files s))
                 (equal (fn-sf-phase (fn-sn-files s)) :completing)
                 (equal (cons (fn-store-event-sequence
                               (fn-sn-completion-record s))
                              (fn-store-event-txid
                               (fn-sn-completion-record s)))
                        (fn-sf-completion (fn-sn-files s)))
                 (natp (fn-sn-identity-next s))))
   :hints (("Goal" :in-theory
            (e/d (fn-sn-completion-enabledp fn-sn-statep)
                 (fn-sf-statep fn-node-statep
                  fn-store-retention-event-p fn-stxe-p fn-stxk-p fn-stxa-p
                  fn-replay-apply-record fn-replay-apply-retention-event
                  fn-replay-identity-step fn-sn-identity-context
                  fn-sn-record-bindsp fn-record-shape-vocabulary
                  fn-record-record-vocabulary))))))

; On the identity arm the :ok context has consumed exactly this event.
(local
 (defthm fn-sis-enabled-identity-next
   (implies (and (fn-sn-completion-enabledp s)
                 (not (fn-store-retention-event-p
                       (fn-sn-completion-record s)))
                 (or (fn-stxe-p (fn-sn-completion-record s))
                     (fn-stxk-p (fn-sn-completion-record s))
                     (fn-stxa-p (fn-sn-completion-record s))))
            (equal (fn-stxk-context-next
                    (fn-replay-identity-step
                     (fn-sn-identity-context s)
                     (fn-sn-completion-record s)))
                   (1+ (fn-sn-identity-next s))))
   :hints (("Goal"
            :use ((:instance fn-sis-step-ok-next
                             (ctx (fn-sn-identity-context s))
                             (event (fn-sn-completion-record s)))
                  (:instance fn-sis-enabled-files-and-pair))
            :in-theory
            (e/d (fn-sn-completion-enabledp fn-sn-identity-context
                  fn-stxk-context fn-sn-statep)
                 (fn-sis-step-ok-next fn-sis-enabled-files-and-pair
                  fn-replay-identity-step fn-replay-apply-record
                  fn-replay-apply-retention-event fn-store-retention-event-p
                  fn-stxe-p fn-stxk-p fn-stxa-p fn-sf-statep fn-node-statep
                  fn-record-shape-vocabulary fn-record-record-vocabulary))))))

(local
 (defthm fn-sis-finish-enabled-next
   (implies (fn-sn-completion-enabledp s)
            (equal (fn-sn-identity-next (fn-sn-finish s))
                   (1+ (fn-sn-identity-next s))))
   :hints (("Goal"
            :use ((:instance fn-sis-enabled-identity-next)
                  (:instance fn-sis-enabled-files-and-pair))
            :in-theory
            (e/d (fn-sn-finish fn-sn-finish-identity
                  fn-sn-advance-identity-next fn-sn-update-indexed
                  fn-sn-update-accepted)
                 (fn-sis-enabled-identity-next fn-sis-enabled-files-and-pair
                  fn-sn-completion-enabledp fn-replay-identity-step
                  fn-replay-apply-record fn-replay-apply-retention-event
                  fn-sn-composite-delta fn-store-retention-event-p
                  fn-stxe-p fn-stxk-p fn-stxa-p fn-sf-core-completion
                  fn-sf-emit-success fn-record-shape-vocabulary
                  fn-record-record-vocabulary))))))

(defthm fn-sn-finish-enabled-advances-identity-next
  (implies (fn-sn-completion-enabledp s)
           (equal (fn-sn-identity-next (fn-sn-finish s))
                  (1+ (fn-sn-identity-next s))))
  :hints (("Goal" :use fn-sis-finish-enabled-next
           :in-theory (disable fn-sn-finish fn-sn-completion-enabledp))))

(local
 (defthm fn-sis-finish-enabled-files
   (implies (fn-sn-completion-enabledp s)
            (equal (fn-sn-files (fn-sn-finish s))
                   (fn-sf-emit-success
                    (fn-sf-core-completion
                     (fn-sn-files s)
                     (fn-store-event-sequence (fn-sn-completion-record s))
                     (fn-store-event-txid (fn-sn-completion-record s)))
                    (fn-store-event-sequence (fn-sn-completion-record s))
                    (fn-store-event-txid (fn-sn-completion-record s)))))
   :hints (("Goal"
            :in-theory
            (e/d (fn-sn-finish fn-sn-finish-identity
                  fn-sn-advance-identity-next fn-sn-update-indexed
                  fn-sn-update-accepted)
                 (fn-sn-completion-enabledp fn-replay-identity-step
                  fn-replay-apply-record fn-replay-apply-retention-event
                  fn-sn-composite-delta fn-store-retention-event-p
                  fn-stxe-p fn-stxk-p fn-stxa-p fn-sf-core-completion
                  fn-sf-emit-success fn-record-shape-vocabulary
                  fn-record-record-vocabulary))))))

; Every enabled arm consumes one committed record and advances the carried
; journal cursor once.  A disabled completion leaves the state untouched.
(defthm fn-sn-finish-preserves-identity-sequence
  (implies (fn-sn-identity-sequencep s)
           (fn-sn-identity-sequencep (fn-sn-finish s)))
  :hints (("Goal"
           :cases ((fn-sn-completion-enabledp s))
           :use ((:instance fn-sn-finish-disabled-is-no-op)
                 (:instance fn-sis-enabled-files-and-pair)
                 (:instance fn-sis-finish-enabled-next)
                 (:instance fn-sis-finish-enabled-files)
                 (:instance fn-sis-file-completion-ready
                            (files (fn-sn-files s))
                            (sequence (fn-store-event-sequence
                                       (fn-sn-completion-record s)))
                            (txid (fn-store-event-txid
                                   (fn-sn-completion-record s))))
                 (:instance fn-sis-file-completion-keeps-records
                            (files (fn-sn-files s))
                            (sequence (fn-store-event-sequence
                                       (fn-sn-completion-record s)))
                            (txid (fn-store-event-txid
                                   (fn-sn-completion-record s)))))
           :in-theory
           (e/d (fn-sn-identity-sequencep fn-sf-completion-phasep)
                (fn-sn-finish fn-sn-completion-enabledp
                 fn-sis-enabled-files-and-pair fn-sis-finish-enabled-next
                 fn-sis-finish-enabled-files fn-sis-file-completion-ready
                 fn-sis-file-completion-keeps-records
                 fn-sf-core-completion fn-sf-emit-success
                 fn-replay-identity-step fn-replay-apply-record
                 fn-replay-apply-retention-event fn-stxa-p fn-stxe-p fn-stxk-p
                 fn-record-shape-vocabulary
                 fn-record-record-vocabulary)))))

(in-theory (disable fn-sn-identity-sequencep))
