; fn: synchronous refusal and known prepublication abort for the live store.
(in-package "ACL2")
(include-book "store-node-traces")
(include-book "records-seam")
; The codecs cluster withdraws the record and codec definitions at export
; (2026-09-19); the proofs here open fn-record-p and the record accessors.
(local (in-theory (enable fn-record-record-vocabulary fn-record-shape-vocabulary)))

; A semantic refusal consumes the durable file reservation and advances the
; actual idle node over the same txid.  The host supplies only the reservation
; identity; it cannot supply either component's resolution result.
(defun fn-sn-refuse-reservation-enabledp (s txid)
  (declare (xargs :guard (fn-sn-statep s) :verify-guards nil))
  (and (mbe :logic (fn-sn-statep s) :exec t)
       (equal (fn-sf-phase (fn-sn-files s)) :reserved)
       (natp txid)
       (equal (1+ txid) (fn-sf-frontier (fn-sn-files s)))
       (fn-replay-advance-okp
        (fn-sn-node s) (fn-sf-frontier (fn-sn-files s)))))

(verify-guards fn-sn-refuse-reservation-enabledp
  :hints (("Goal" :in-theory (e/d (fn-sn-statep) (fn-sf-statep fn-node-statep)))))

(defun fn-sn-refuse-reservation (s txid)
  (declare (xargs :guard (fn-sn-statep s) :verify-guards nil))
  (if (fn-sn-refuse-reservation-enabledp s txid)
      (fn-sn-update
       s
       (fn-sf-refuse-reservation (fn-sn-files s) txid)
       (fn-replay-advance-txid
        (fn-sn-node s) (fn-sf-frontier (fn-sn-files s))))
    s))

(verify-guards fn-sn-refuse-reservation
  :hints (("Goal" :in-theory (e/d (fn-sn-statep fn-sn-refuse-reservation-enabledp)
                                  (fn-sf-statep fn-node-statep)))))

; Only a proposal whose immutable publication has not been attempted has a
; known-absent resolution.  Exact sequence, txid, generation, and record data
; come from the bound candidate rather than from a host completion claim.
(defun fn-sn-known-abort-enabledp (s)
  (declare (xargs :guard (fn-sn-statep s) :verify-guards nil))
  (let ((files (fn-sn-files s)))
    (and (mbe :logic (fn-sn-statep s) :exec t)
         (or (equal (fn-sf-phase files) :record-staged)
             (equal (fn-sf-phase files) :record-data-durable))
         (let ((record (fn-sf-record-candidate files)))
           (if (fn-store-retention-event-p record)
               (consp (fn-replay-apply-retention-event (fn-sn-node s) record))
             (fn-sn-record-bindsp (fn-sn-node s) record))))))

(verify-guards fn-sn-known-abort-enabledp
  :hints (("Goal" :in-theory (e/d (fn-sn-statep) (fn-sf-statep fn-node-statep)))))

(defun fn-sn-known-abort-file-start (files)
  (declare (xargs :guard (fn-sf-statep files) :verify-guards nil))
  (if (equal (fn-sf-phase files) :record-staged)
      (fn-sf-record-file-result files :known-fail)
    (fn-sf-prepublish-abort files)))

(verify-guards fn-sn-known-abort-file-start)

; The guard proof of fn-sn-known-abort-files: the abort start is a kernel state.
(defthm fn-sn-known-abort-file-start-preserves-state
  (implies (fn-sf-statep files)
           (fn-sf-statep (fn-sn-known-abort-file-start files)))
  :hints (("Goal"
           :in-theory (enable fn-sn-known-abort-file-start))))

; The public known-abort gate establishes a valid record candidate before
; calling this helper.
(defun fn-sn-known-abort-files (files)
  (declare (xargs :guard (and (fn-sf-statep files)
                              (true-listp (fn-sf-record-candidate files)))
                  :verify-guards nil))
  (let* ((record (fn-sf-record-candidate files))
         (aborting (fn-sn-known-abort-file-start files)))
    (fn-sf-abort-completion
     aborting (fn-store-event-sequence record) (fn-store-event-txid record))))

(verify-guards fn-sn-known-abort-files
  :hints (("Goal" :in-theory (disable fn-sn-known-abort-file-start))))

(local
 (defthm fn-snr-record-is-a-true-list
   (implies (fn-record-p record) (true-listp record))
   :hints (("Goal" :in-theory (enable fn-record-p)))))

; The retention arm advances the live node over the transaction id the
; abort consumes, exactly as `fn-sn-refuse-reservation' above advances it
; over a refused reservation.  `6ab2c783' added this arm and left the node
; alone, which is a `fn-sn-node' one transaction id behind the durable
; frontier in a `:ready' state: the store's own invariant says an idle node
; IS the replay of its durable history at that frontier
; (`fn-snt-relation', books/store-node-traces) and
; `fn-own-idle-node-is-replay' (books/owner-invariants) is what lets the
; reader path serve from the live node instead of replaying.  The article arm
; consumes the id through the aborted completion; a retention candidate
; staged no proposal to complete, so the advance is the whole of it.  Nothing
; else changes: `fn-replay-advance-txid' touches no article, pin, binding,
; watermark or capacity (books/replay).
(defun fn-sn-known-abort (s)
  (declare (xargs :guard (fn-sn-statep s) :verify-guards nil))
  (if (fn-sn-known-abort-enabledp s)
      (let* ((files (fn-sn-files s))
             (record (fn-sf-record-candidate files))
             (node (if (fn-store-retention-event-p record)
                       (fn-replay-advance-txid (fn-sn-node s)
                                               (fn-sf-frontier files))
                     (fn-node-complete
                      (fn-sn-node s) (fn-record-txid record)
                      (fn-record-generation record) :aborted))))
        (fn-sn-update s (fn-sn-known-abort-files files) node))
    s))

(verify-guards fn-sn-known-abort
  :hints (("Goal" :in-theory
           (e/d (fn-sn-statep fn-sn-known-abort-enabledp fn-sn-record-bindsp)
                (fn-sf-statep fn-node-statep fn-record-p
                 fn-node-pending-matchesp fn-sn-pending-record
                 fn-sn-known-abort-files fn-sn-known-abort-file-start)))))

(local (in-theory
        (e/d (fn-sn-update fn-sn-completion-core-enabledp
              fn-sn-completion-record
              fn-sn-io fn-sn-file-step fn-sn-prepare fn-sn-finish fn-sn-crash
              fn-sn-recover fn-sn-committed-recordp
              fn-replay-apply-record fn-replay-okp fn-replay-faultp
                        fn-replay-advance-okp fn-node-pending-matchesp
                        fn-store-files-invariants-vocabulary
              fn-store-files-traces-vocabulary
              fn-store-node-invariants-vocabulary
              fn-store-node-traces-vocabulary)
             (fn-sn-statep fn-sf-statep fn-node-statep fn-record-p
              fn-sn-record-bindsp fn-snt-relation fn-snt-pending-linkp
              fn-snt-deferred-linkp fn-snt-completion-linkp
              fn-sf-history-recoverablep fn-sf-replay-node
              fn-sn-completion-enabledp
              fn-sn-refuse-reservation-enabledp fn-sn-refuse-reservation
              fn-sn-known-abort-enabledp fn-sn-known-abort-file-start
              fn-sn-known-abort-files fn-sn-known-abort
              fn-sf-refuse-reservation
              fn-sf-record-file-result fn-sf-prepublish-abort
              fn-sf-abort-completion fn-replay-advance-txid
              fn-node-complete fn-node-prepare fn-replay fn-replay-loop))))

; -by-definition: the else branches with their tests negated.
(defthm fn-sn-refuse-reservation-disabled-is-no-op
  (implies (not (fn-sn-refuse-reservation-enabledp s txid))
           (equal (fn-sn-refuse-reservation s txid) s))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-sn-refuse-reservation))))

(defthm fn-sn-known-abort-disabled-is-no-op
  (implies (not (fn-sn-known-abort-enabledp s))
           (equal (fn-sn-known-abort s) s))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-sn-known-abort))))

(defthm fn-sn-refuse-reservation-preserves-state
  (implies (fn-sn-statep s)
           (fn-sn-statep (fn-sn-refuse-reservation s txid)))
  :hints (("Goal"
           :cases ((fn-sn-refuse-reservation-enabledp s txid))
           :use ((:instance fn-sf-refuse-reservation-preserves-state
                            (s (fn-sn-files s)))
                 (:instance fn-replay-advance-preserves-node-statep
                            (node (fn-sn-node s))
                            (recorded-txid
                             (fn-sf-frontier (fn-sn-files s)))))
           :in-theory (e/d (fn-sn-refuse-reservation fn-sn-update fn-sn-statep)
                           (fn-sf-refuse-reservation
                            fn-replay-advance-txid)))))

(defthm fn-sn-known-abort-files-preserves-state
  (implies (fn-sf-statep files)
           (fn-sf-statep (fn-sn-known-abort-files files)))
  :hints (("Goal"
           :use ((:instance fn-sn-known-abort-file-start-preserves-state)
                 ; `6ab2c783' changed the pair `fn-sn-known-abort-files'
                 ; hands `fn-sf-abort-completion' to the composed
                 ; `fn-store-event-sequence' and `fn-store-event-txid'
                 ; (the staged candidate is no longer always an article
                 ; record), and this book has not certified since; the
                 ; instance has to name the same pair.
                 (:instance fn-sf-abort-completion-preserves-state
                            (s (fn-sn-known-abort-file-start files))
                            (sequence (fn-store-event-sequence
                                       (fn-sf-record-candidate files)))
                            (txid (fn-store-event-txid
                                   (fn-sf-record-candidate files)))))
           :in-theory (enable fn-sn-known-abort-files))))

(defthm fn-sn-known-abort-preserves-state
  (implies (fn-sn-statep s)
           (fn-sn-statep (fn-sn-known-abort s)))
  :hints (("Goal"
           :cases ((fn-sn-known-abort-enabledp s))
           :use ((:instance fn-sn-known-abort-files-preserves-state
                            (files (fn-sn-files s)))
                 ; The retention arm's node since `6ab2c783'.
                 (:instance fn-replay-advance-preserves-node-statep
                            (node (fn-sn-node s))
                            (recorded-txid (fn-sf-frontier (fn-sn-files s))))
                 (:instance fn-node-complete-preserves-state
                            (s (fn-sn-node s))
                            (txid (fn-record-txid
                                   (fn-sf-record-candidate (fn-sn-files s))))
                            (generation (fn-record-generation
                                         (fn-sf-record-candidate
                                          (fn-sn-files s))))
                            (completion-status :aborted)))
           :in-theory (e/d (fn-sn-known-abort fn-sn-update fn-sn-statep)
                           (fn-sn-record-bindsp
                            fn-sn-known-abort-files fn-node-complete
                            fn-replay-advance-txid
                            fn-record-shape-vocabulary
                            fn-store-event-p fn-store-retention-event-p
                            fn-stxe-p fn-stxk-p fn-stxa-p)))))

; -----------------------------------------------------------------------------
; The carried statement index (D21): the two resolution transitions
;
; Neither publishes an article, so neither changes the store and both carry
; the index unchanged through fn-sn-update.  Without these two the claim
; "fn-sn-indexedp holds of every state the host installs" would be false at
; host/store-node-host.lisp lines 377 and 392.

(local (defthm fn-snr-refusal-keeps-the-store-unfolds
         (equal (fn-stx-store (fn-replay-advance-txid node recorded-txid))
                (fn-stx-store node))
         :hints (("Goal" :in-theory (enable fn-stx-store)))))

(local (defthm fn-snr-aborted-completion-keeps-the-store-unfolds
         (equal (fn-stx-store (fn-node-complete node txid generation :aborted))
                (fn-stx-store node))
         :hints (("Goal" :in-theory (enable fn-stx-store fn-node-complete
                                            fn-accept-complete fn-clear-pending)))))

(defthm fn-sn-refuse-reservation-preserves-indexedp
  (implies (fn-sn-indexedp s)
           (fn-sn-indexedp (fn-sn-refuse-reservation s txid)))
  :hints (("Goal"
           :use ((:instance fn-sn-refuse-reservation-preserves-state))
           :in-theory (e/d (fn-sn-indexedp fn-sn-refuse-reservation
                            fn-sn-update fn-stx-index-invariantp)
                           (fn-sn-statep fn-node-statep fn-sf-statep
                            fn-sf-refuse-reservation fn-replay-advance-txid
                            fn-stx-index-of-store fn-stx-store)))))

(defthm fn-sn-known-abort-preserves-indexedp
  (implies (fn-sn-indexedp s)
           (fn-sn-indexedp (fn-sn-known-abort s)))
  :hints (("Goal"
           :use ((:instance fn-sn-known-abort-preserves-state))
           :in-theory (e/d (fn-sn-indexedp fn-sn-known-abort fn-sn-update
                            fn-stx-index-invariantp)
                           (fn-sn-statep fn-node-statep fn-sf-statep
                            fn-sn-known-abort-files fn-node-complete
                            fn-sn-record-bindsp
                            fn-stx-index-of-store fn-stx-store)))))

(defthm fn-sn-refuse-reservation-preserves-configuration
  (and (equal (fn-sn-groups (fn-sn-refuse-reservation s txid))
              (fn-sn-groups s))
       (equal (fn-sn-capacity (fn-sn-refuse-reservation s txid))
              (fn-sn-capacity s)))
  :hints (("Goal" :in-theory (enable fn-sn-refuse-reservation
                                      fn-sn-update))))

(defthm fn-sn-known-abort-preserves-configuration
  (and (equal (fn-sn-groups (fn-sn-known-abort s)) (fn-sn-groups s))
       (equal (fn-sn-capacity (fn-sn-known-abort s)) (fn-sn-capacity s)))
  :hints (("Goal" :in-theory (enable fn-sn-known-abort fn-sn-update))))

(defthm fn-sn-refuse-reservation-cannot-acknowledge
  (equal (fn-sf-successes
          (fn-sn-files (fn-sn-refuse-reservation s txid)))
         (fn-sf-successes (fn-sn-files s)))
  :hints (("Goal"
           :use ((:instance fn-sf-successes-of-refuse-reservation
                            (s (fn-sn-files s))))
           :in-theory (e/d (fn-sn-refuse-reservation fn-sn-update)
                           (fn-sf-refuse-reservation )))))

(defthm fn-sn-known-abort-file-start-cannot-acknowledge
  (equal (fn-sf-successes (fn-sn-known-abort-file-start files))
         (fn-sf-successes files))
  :hints (("Goal"
           :in-theory (e/d (fn-sn-known-abort-file-start)
                           (fn-sf-record-file-result fn-sf-prepublish-abort
                            )))))

(defthm fn-sn-known-abort-cannot-acknowledge
  (equal (fn-sf-successes (fn-sn-files (fn-sn-known-abort s)))
         (fn-sf-successes (fn-sn-files s)))
  :hints (("Goal"
           ; The composed pair, as in `fn-sn-known-abort-files-preserves-state'
           ; above (`6ab2c783').
           :use ((:instance fn-sf-successes-of-abort-completion
                            (s (fn-sn-known-abort-file-start (fn-sn-files s)))
                            (sequence (fn-store-event-sequence
                                       (fn-sf-record-candidate (fn-sn-files s))))
                            (txid (fn-store-event-txid
                                   (fn-sf-record-candidate (fn-sn-files s))))))
           :in-theory (e/d (fn-sn-known-abort fn-sn-known-abort-files
                             fn-sn-update)
                           (fn-sn-known-abort-file-start
                            fn-sf-abort-completion
                            fn-record-shape-vocabulary
                            fn-store-event-p fn-store-retention-event-p
                            fn-stxe-p fn-stxk-p fn-stxa-p
                            fn-replay-apply-record
                            fn-replay-apply-retention-event
                            fn-node-complete)))))

; The two deferred preparations acknowledge nothing either: they stage a
; candidate through `fn-sf-prepare-record', which publishes no success.
; `6ab2c783' and `4bb7bb3d' put both on `fn-snrt-step' and the monotonicity
; theorems below walk every arm of it.
(defthm fn-sn-prepare-retention-cannot-acknowledge
  (equal (fn-sf-successes (fn-sn-files (fn-sn-prepare-retention s event)))
         (fn-sf-successes (fn-sn-files s)))
  :hints (("Goal"
           :use ((:instance fn-sf-successes-of-prepare-record
                            (s (fn-sn-files s)) (record event)
                            (groups (fn-sn-groups s))
                            (capacity (fn-sn-capacity s))))
           :in-theory (e/d (fn-sn-prepare-retention fn-sn-update)
                           (fn-sn-statep fn-sf-prepare-record
                            fn-replay-apply-retention-event
                            fn-record-shape-vocabulary
                            fn-store-event-p fn-store-retention-event-p
                            fn-stxe-p fn-stxk-p fn-stxa-p)))))

(defthm fn-sn-prepare-identity-cannot-acknowledge
  (equal (fn-sf-successes (fn-sn-files (fn-sn-prepare-identity s event)))
         (fn-sf-successes (fn-sn-files s)))
  :hints (("Goal"
           :use ((:instance fn-sf-successes-of-prepare-record
                            (s (fn-sn-files s)) (record event)
                            (groups (fn-sn-groups s))
                            (capacity (fn-sn-capacity s))))
           :in-theory (e/d (fn-sn-prepare-identity fn-sn-update)
                           (fn-sn-statep fn-sf-prepare-record
                            fn-replay-apply-record
                            fn-replay-identity-step fn-sn-identity-context
                            fn-record-shape-vocabulary
                            fn-store-event-p fn-store-retention-event-p
                            fn-stxe-p fn-stxk-p fn-stxa-p)))))

(defthm fn-sn-prepare-consumer-cannot-acknowledge
  (equal (fn-sf-successes (fn-sn-files (fn-sn-prepare-consumer s event)))
         (fn-sf-successes (fn-sn-files s)))
  :hints (("Goal"
           :use ((:instance fn-sf-successes-of-prepare-record
                            (s (fn-sn-files s)) (record event)
                            (groups (fn-sn-groups s))
                            (capacity (fn-sn-capacity s))))
           :in-theory (e/d (fn-sn-prepare-consumer fn-sn-update)
                           (fn-sn-statep fn-sf-prepare-record
                            fn-replay-apply-record fn-cpe-projection-step
                            fn-record-shape-vocabulary
                            fn-store-event-p fn-cpe-eventp)))))

(defthm fn-sn-known-abort-files-reaches-ready
  (implies (and (fn-sf-statep files)
                (or (equal (fn-sf-phase files) :record-staged)
                    (equal (fn-sf-phase files) :record-data-durable)))
           (equal (fn-sf-phase (fn-sn-known-abort-files files)) :ready))
  :hints (("Goal"
           :use ((:instance fn-sn-known-abort-file-start-preserves-state))
           :in-theory (enable fn-sn-known-abort-files
                              fn-sn-known-abort-file-start
                              fn-sf-record-file-result
                              fn-sf-prepublish-abort
                              fn-sf-abort-completion))))

(defthm fn-sn-refuse-reservation-is-exact-advance
  (implies (fn-sn-refuse-reservation-enabledp s txid)
           (and (equal (fn-sf-phase
                        (fn-sn-files (fn-sn-refuse-reservation s txid)))
                       :ready)
                (equal (fn-sn-node (fn-sn-refuse-reservation s txid))
                       (fn-replay-advance-txid
                        (fn-sn-node s) (fn-sf-frontier (fn-sn-files s))))
                (equal (fn-state-next-txid
                        (fn-node-acceptance
                         (fn-sn-node (fn-sn-refuse-reservation s txid))))
                       (fn-sf-frontier (fn-sn-files s)))))
  :hints (("Goal" :in-theory
           (enable fn-sn-refuse-reservation
                   fn-sn-refuse-reservation-enabledp fn-sn-update
                   fn-sf-refuse-reservation fn-replay-advance-txid))))

; `6ab2c783' gave `fn-sn-known-abort' a second arm, and on it the node is not
; an aborted completion: a retention candidate never staged a proposal on the
; live node (`fn-sn-prepare-retention' defers the whole node effect to
; `fn-sn-finish'), so the abort leaves the node where the reservation left
; it.  Stated for both arms rather than hypothesised on one, so the theorem
; still says what the transition does everywhere it is enabled.  This book has
; not certified since 2026-09-21 01:20 and the one-armed statement was never
; proved in the shape the machine has.
(defthm fn-sn-known-abort-is-exact-node-abort
  (implies (fn-sn-known-abort-enabledp s)
           (let ((record (fn-sf-record-candidate (fn-sn-files s))))
             (and (equal (fn-sf-phase
                          (fn-sn-files (fn-sn-known-abort s)))
                         :ready)
                  (equal (fn-sn-node (fn-sn-known-abort s))
                         (if (fn-store-retention-event-p record)
                             (fn-replay-advance-txid
                              (fn-sn-node s) (fn-sf-frontier (fn-sn-files s)))
                           (fn-node-complete
                            (fn-sn-node s) (fn-record-txid record)
                            (fn-record-generation record) :aborted))))))
  :hints (("Goal"
           :in-theory (e/d (fn-sn-known-abort
                             fn-sn-known-abort-enabledp fn-sn-update)
                           (fn-sn-known-abort-files
                            fn-node-complete
                            fn-record-shape-vocabulary
                            fn-store-event-p fn-store-retention-event-p
                            fn-stxe-p fn-stxk-p fn-stxa-p
                            fn-replay-apply-record
                            fn-replay-apply-retention-event)))))

(defthm fn-sn-refuse-reservation-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-sn-refuse-reservation s txid)))
  :hints (("Goal"
           :cases ((fn-sn-refuse-reservation-enabledp s txid))
           :use (fn-sn-refuse-reservation-preserves-state
                 (:instance fn-snt-advance-replayed-node
                            (groups (fn-sn-groups s))
                            (capacity (fn-sn-capacity s))
                            (records (fn-sf-records (fn-sn-files s)))
                            (first (1- (fn-sf-frontier (fn-sn-files s))))
                            (second (fn-sf-frontier (fn-sn-files s)))))
           :in-theory (e/d (fn-snt-relation fn-snt-idle-phasep
                             fn-sn-refuse-reservation
                             fn-sn-refuse-reservation-enabledp fn-sn-update
                             fn-sf-refuse-reservation)
                           (fn-sn-statep fn-sf-statep
                            fn-sf-history-recoverablep fn-sf-replay-node
                            fn-snt-pending-linkp fn-sn-completion-enabledp
                            fn-sn-completion-core-enabledp
                            fn-replay-advance-txid)))))

; Both arms land `:ready', and on both the node is the replay of the durable
; history at the frontier, which is what the `:ready' arm of the relation
; asks for.  On the article arm that is the aborted completion, as before.
; On the retention arm the relation carries the deferred link
; (`fn-snt-deferred-linkp', books/store-node-traces), whose node is the
; replay at the frontier's predecessor, and the advance `6ab2c783' left out
; is exactly `fn-snt-advance-replayed-node' -- the same step
; `fn-sn-refuse-reservation-preserves-relation' above takes.
(defthm fn-sn-known-abort-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-sn-known-abort s)))
  :hints (("Goal"
           :cases ((fn-sn-known-abort-enabledp s))
           :use (fn-sn-known-abort-preserves-state
                 fn-sn-known-abort-is-exact-node-abort
                 (:instance fn-snt-an-article-record-is-no-other-store-event
                   (record (fn-sf-record-candidate (fn-sn-files s))))
                 (:instance fn-snt-advance-replayed-node
                   (groups (fn-sn-groups s))
                   (capacity (fn-sn-capacity s))
                   (records (fn-sf-records (fn-sn-files s)))
                   (first (+ -1 (fn-sf-frontier (fn-sn-files s))))
                   (second (fn-sf-frontier (fn-sn-files s)))))
           :in-theory (e/d (fn-snt-relation fn-snt-idle-phasep
                             fn-snt-pending-linkp fn-snt-deferred-linkp
                             fn-snt-completion-linkp
                             fn-sn-known-abort fn-sn-known-abort-enabledp
                             fn-sn-known-abort-files
                             fn-sn-known-abort-file-start fn-sn-update
                             fn-sf-record-file-result
                             fn-sf-prepublish-abort
                             fn-sf-abort-completion)
                            (fn-sn-statep fn-sf-statep
                             fn-sn-record-bindsp
                             fn-sf-history-recoverablep
                             fn-sf-replay-node fn-node-complete
                             fn-sn-completion-enabledp
                             fn-sn-completion-core-enabledp
                             fn-record-shape-vocabulary
                             fn-store-event-p fn-store-retention-event-p
                             fn-stxe-p fn-stxk-p fn-stxa-p
                             fn-replay-apply-record
                             fn-replay-apply-retention-event)))))

; =============================================================================
; Mixed live-store traces including refusal and known prepublication abort
; (folded from store-node-resolution-traces.lisp, 2026-09-19 realignment).
; The two deferred preparations stay closed in this section, as
; `fn-sn-prepare' is on export from books/store-node (that book's export
; disable predates them and leaves them enabled).  Open, each unfolds through
; `fn-replay-apply-retention-event', `fn-replay-apply-record',
; `fn-replay-identity-step' and the record and stx recognizers, and a goal
; over `fn-snrt-step' that only dispatches on the event kind split into 21394
; cases (466 s; planning/evidence/store-node-resolution-cost-2026-09-23.md).
; What those goals need of an arm is its footprint: it acknowledges nothing
; (`fn-sn-prepare-retention-cannot-acknowledge' above) and publishes no
; record (`fn-snt-prepare-retention-keeps-records', books/store-node-traces).
(local (in-theory (disable fn-snt-step   fn-sf-prefixp
                           fn-node-recover fn-node-initial-state
                            fn-state-next-txid
                           fn-sn-prepare-retention fn-sn-prepare-identity
                             )))

; Like the base dispatcher, these are decoded logical events.  The two added
; branches call actual resolution operations without any invariant filter.
(defun fn-snrt-step (s event)
  (case (car event)
    (:refuse-reservation (fn-sn-refuse-reservation s (cadr event)))
    (:known-abort (fn-sn-known-abort s))
    (:prepare-retention (fn-sn-prepare-retention s (cadr event)))
    (:prepare-identity (fn-sn-prepare-identity s (cadr event)))
    (:prepare-consumer (fn-sn-prepare-consumer s (cadr event)))
    (otherwise (fn-snt-step s event))))

(defun fn-snrt-run (s events)
  (if (consp events)
      (fn-snrt-run (fn-snrt-step s (car events)) (cdr events))
    s))

; The two arms `6ab2c783' and `4bb7bb3d' added are closed here like the
; others, so the step is decided by the preservation theorems of the
; transitions themselves -- `fn-snt-prepare-retention-preserves-relation' and
; `fn-snt-prepare-identity-preserves-relation' (books/store-node-traces) are
; the two that did not exist when those arms landed.
(defthm fn-snrt-step-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-snrt-step s event)))
  :hints (("Goal" :in-theory (disable fn-snt-relation fn-sn-prepare fn-sn-io
                      fn-sn-finish fn-sn-crash fn-sn-recover
                      fn-sn-prepare-retention fn-sn-prepare-identity
                      fn-sn-prepare-consumer))))

(defthm fn-snrt-mixed-trace-preserves-live-history-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-snrt-run s events)))
  :hints (("Goal" :induct (fn-snrt-run s events)
           :in-theory (disable fn-snt-relation fn-snrt-step))))

(defthm fn-snrt-initialized-mixed-trace-has-live-history-relation
  (implies (and (fn-string-listp groups) (fn-no-duplicatesp groups) (natp capacity))
           (fn-snt-relation (fn-snrt-run (fn-sn-initial groups capacity) events)))
  :hints (("Goal" :in-theory (disable fn-snt-relation fn-snrt-run fn-sn-initial))))

(defthm fn-snrt-mixed-trace-ready-node-is-exact-replay
  (let ((final (fn-snrt-run s events)))
    (implies (and (fn-snt-relation s)
                  (member-equal (fn-sf-phase (fn-sn-files final))
                                '(:ready :recovering :fenced-recovery)))
             (equal (fn-sn-node final)
                    (fn-sf-replay-node (fn-sn-groups final) (fn-sn-capacity final)
                      (fn-sf-records (fn-sn-files final))
                      (fn-sf-frontier (fn-sn-files final))))))
  :hints (("Goal" :use ((:instance fn-snt-ready-or-recovered-node-is-exact-replay
                                   (s (fn-snrt-run s events))))
           :in-theory (disable fn-snt-relation fn-snrt-run))))

(defthm fn-snrt-step-success-history-monotone
  (implies (fn-snt-relation s)
           (fn-sf-prefixp (fn-sf-successes (fn-sn-files s))
                          (fn-sf-successes (fn-sn-files (fn-snrt-step s event)))))
  :hints (("Goal" :in-theory (enable fn-snrt-step))))

(defthm fn-snrt-mixed-trace-success-history-monotone
  (implies (fn-snt-relation s)
           (fn-sf-prefixp (fn-sf-successes (fn-sn-files s))
                          (fn-sf-successes (fn-sn-files (fn-snrt-run s events)))))
  :hints (("Goal" :induct (fn-snrt-run s events)
           :in-theory (disable fn-snt-relation fn-snrt-step 
                                fn-sf-prefixp))
          ("Subgoal *1/1" :use ((:instance fn-sf-prefixp-transitive
                                 (xs (fn-sf-successes (fn-sn-files s)))
                                 (ys (fn-sf-successes (fn-sn-files (fn-snrt-step s (car events)))))
                                 (zs (fn-sf-successes (fn-sn-files (fn-snrt-run
                                       (fn-snrt-step s (car events)) (cdr events))))))))))

; Prior acknowledged pairs survive arbitrary mixed wrapper traces.  Whenever
; the final live node is ready/recovered it equals replay of precisely this
; surviving history, rather than an independently trusted completion cache.
(defthm fn-snrt-acknowledged-history-retained-through-mixed-trace
  (let ((final (fn-snrt-run s events)))
    (implies (and (fn-snt-relation s)
                  (member-equal pair (fn-sf-successes (fn-sn-files s))))
             (and (member-equal pair (fn-sf-successes (fn-sn-files final)))
                  (fn-sf-record-has-pairp pair (fn-sf-records (fn-sn-files final))))))
  :hints (("Goal"
    :use (fn-snrt-mixed-trace-success-history-monotone
          fn-snrt-mixed-trace-preserves-live-history-relation
          (:instance fn-snt-relation-implies-structural-state (s (fn-snrt-run s events)))
          (:instance fn-snt-typed-store-components (s (fn-snrt-run s events)))
          (:instance fn-sf-state-success-member-has-record
            (s (fn-sn-files (fn-snrt-run s events))))
          (:instance fn-sf-member-preserved-by-prefix
            (x pair) (xs (fn-sf-successes (fn-sn-files s)))
            (ys (fn-sf-successes (fn-sn-files (fn-snrt-run s events))))))
    :in-theory (disable fn-snrt-run fn-snt-relation 
                          fn-sf-record-has-pairp))))

; Refusal and abort add no acknowledgement-producing paths.  Any step that
; changes acknowledgement history executes the actual matching live durable
; completion, including its exact article and retention obligation.
; The safety conjuncts -- a new acknowledgement only from `:finish', and only
; under an enabled completion -- stand for all three arms of `fn-sn-finish'.
; The article-specific conclusions are conditional on the acceptance arm, as
; they are in the keystone this uses
; (`fn-sn-new-success-requires-actual-matching-durable-node-completion',
; books/store-node-invariants): since `6ab2c783' and `4bb7bb3d' the completion
; record can be a retention or identity event, whose node transition is not a
; `fn-node-complete' and whose article accessors name nothing.
(defthm fn-snrt-new-success-is-actual-matching-durable-completion
  (let ((next (fn-snrt-step s event)))
    (implies
     (not (equal (fn-sf-successes (fn-sn-files next))
                  (fn-sf-successes (fn-sn-files s))))
     (and (equal (car event) :finish)
          (fn-sn-completion-enabledp s)
          (implies
           (and (not (fn-store-retention-event-p (fn-sn-completion-record s)))
                (not (fn-stxe-p (fn-sn-completion-record s)))
                (not (fn-stxk-p (fn-sn-completion-record s)))
                (not (fn-stxa-p (fn-sn-completion-record s)))
                (not (fn-cpe-eventp (fn-sn-completion-record s))))
           (and (fn-sn-record-bindsp (fn-sn-node s) (fn-sn-completion-record s))
                (equal (fn-sn-node next)
                       (fn-node-complete (fn-sn-node s)
                         (fn-record-txid (fn-sn-completion-record s))
                         (fn-record-generation (fn-sn-completion-record s))
                         :durable))
                (fn-sn-committed-recordp (fn-sn-node next)
                                         (fn-sn-completion-record s)))))))
  :hints (("Goal"
           :use fn-sn-new-success-requires-actual-matching-durable-node-completion
           :in-theory (e/d (fn-snrt-step fn-snt-step)
                            (fn-sn-prepare fn-sn-io fn-sn-crash fn-sn-recover
                             fn-sn-finish fn-sn-completion-enabledp
                             fn-sn-record-bindsp fn-sn-completion-record
                             fn-sn-committed-recordp fn-node-complete
                             fn-record-shape-vocabulary
                             fn-store-event-p fn-store-retention-event-p
                             fn-stxe-p fn-stxk-p fn-stxa-p
                             fn-replay-apply-record
                             fn-replay-apply-retention-event
                             fn-sn-prepare-retention fn-sn-prepare-identity
                              fn-record-txid fn-record-generation)))))

; -----------------------------------------------------------------------------
; Stable records only grow along resolution traces as well.

(defthm fn-snrt-refuse-keeps-records
  (equal (fn-sf-records (fn-sn-files (fn-sn-refuse-reservation s txid)))
         (fn-sf-records (fn-sn-files s)))
  :hints (("Goal" :in-theory (e/d (fn-sn-refuse-reservation fn-sn-update 
                                   )
                                  (fn-sn-refuse-reservation-enabledp
                                   fn-sf-refuse-reservation )))))

(defthm fn-snrt-known-abort-files-keep-records
  (equal (fn-sf-records (fn-sn-known-abort-files files))
         (fn-sf-records files))
  :hints (("Goal" :in-theory (e/d (fn-sn-known-abort-files
                                   fn-sn-known-abort-file-start)
                                  (fn-sf-abort-completion fn-sf-record-file-result
                                   fn-sf-prepublish-abort )))))

(defthm fn-snrt-known-abort-keeps-records
  (equal (fn-sf-records (fn-sn-files (fn-sn-known-abort s)))
         (fn-sf-records (fn-sn-files s)))
  :hints (("Goal" :in-theory (e/d (fn-sn-known-abort fn-sn-update 
                                   )
                                  (fn-sn-known-abort-enabledp
                                   fn-sn-known-abort-files 
                                   fn-node-complete)))))

(defthm fn-snrt-step-records-prefix
  (implies (fn-snt-relation s)
           (fn-sf-prefixp (fn-sf-records (fn-sn-files s))
                          (fn-sf-records (fn-sn-files (fn-snrt-step s event)))))
  :hints (("Goal"
           :use (fn-snt-related-records-true-list
                 (:instance fn-snt-step-records-prefix))
           :in-theory (e/d (fn-snrt-step
                            fn-snt-prepare-retention-keeps-records
                            fn-snt-prepare-identity-keeps-records
                            fn-snt-prepare-consumer-keeps-records)
                           (fn-snt-relation fn-snt-step fn-sn-refuse-reservation
                            fn-sn-known-abort  
                            fn-sf-prefixp fn-snt-step-records-prefix)))))

(defthm fn-snrt-mixed-trace-records-prefix
  (implies (fn-snt-relation s)
           (fn-sf-prefixp (fn-sf-records (fn-sn-files s))
                          (fn-sf-records (fn-sn-files (fn-snrt-run s events)))))
  :hints (("Goal" :induct (fn-snrt-run s events)
           :in-theory (disable fn-snt-relation fn-snrt-step 
                                fn-sf-prefixp))
          ("Subgoal *1/1" :use ((:instance fn-sf-prefixp-transitive
                                 (xs (fn-sf-records (fn-sn-files s)))
                                 (ys (fn-sf-records (fn-sn-files (fn-snrt-step s (car events)))))
                                 (zs (fn-sf-records (fn-sn-files (fn-snrt-run
                                       (fn-snrt-step s (car events)) (cdr events))))))))))

; -----------------------------------------------------------------------------
; Export theory.  Withdrawn: the two resolution operations and their gates,
; the file helpers, the dispatcher, and under a name the file-helper and
; footprint lemmas.  Enabled on include: preservation of state, relation and
; configuration, the cannot-acknowledge family, the exact-advance and
; exact-abort keystones, fn-snrt-run and the snrt trace keystones.
(deftheory fn-store-node-resolution-vocabulary
  '(fn-sn-known-abort-file-start-preserves-state
    fn-sn-known-abort-files-preserves-state
    fn-sn-known-abort-file-start-cannot-acknowledge
    fn-sn-known-abort-files-reaches-ready
    fn-snrt-refuse-keeps-records fn-snrt-known-abort-files-keep-records
    fn-snrt-known-abort-keeps-records))
(in-theory (disable fn-store-node-resolution-vocabulary
                    fn-sn-refuse-reservation-enabledp fn-sn-refuse-reservation
                    fn-sn-known-abort-enabledp fn-sn-known-abort-file-start
                    fn-sn-known-abort-files fn-sn-known-abort fn-snrt-step))
