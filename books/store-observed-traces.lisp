; Trace theorems rooted at the observed physical-image entry.
;
; host/store-node-host.lisp:27 calls fn-sn-open-observed on each process start
; (tools/run_store.py:568, acl2.recover(records, self.frontier)).  This book
; (1) establishes fn-snt-relation at that root, so every trace theorem in
; store-node-traces.lisp and store-node-resolution-traces.lisp applies to the
; state the host actually resumes from (D6), and (2) carries acknowledged-record
; retention across the reopen boundary with A-DURABILITY as the hypothesis
; fn-sf-crash-imagep rather than as the crash constructor (D5).
; Acknowledgement history is not reconstructed from the image: the adapter
; persists no acknowledgement anchor, so a reconstruction would have to guess.
; The retention claim is stated over records, which the adapter does persist.
;
; This is a separate book from store-observed because the opening theorems
; there certify in the theory of store-node-invariants and stall under the
; rewrite rules the trace books export.  The host keeps including
; store-observed; nothing here is executed by the host.

(in-package "ACL2")
(include-book "store-observed")
(include-book "store-node-resolution-traces")

; -----------------------------------------------------------------------------
; The process root establishes the live-history relation (D6).

(defthm fn-sn-open-observed-success-configuration
  (implies (fn-sn-open-okp (fn-sn-open-observed groups capacity frontier records))
           (and (equal (fn-sn-groups
                        (fn-sn-open-state
                         (fn-sn-open-observed groups capacity frontier records)))
                       groups)
                (equal (fn-sn-capacity
                        (fn-sn-open-state
                         (fn-sn-open-observed groups capacity frontier records)))
                       capacity)))
  :hints (("Goal"
           :in-theory (e/d (fn-sn-open-observed fn-sn-open-okp fn-sn-open-state
                                                 fn-sn-open-ok fn-sn-observed-seed
                                                 fn-sn-recover fn-sn-update
                                                 fn-sn-make fn-sn-groups
                                                 fn-sn-capacity)
                            (fn-sn-statep fn-sf-statep fn-sf-history-recoverablep
                             fn-sf-replay-node fn-sf-recover)))))

; The opened kernel state reached :recovering, which fn-sf-recover grants only
; to a replayable history at its own frontier.
(defthm fn-sn-open-observed-success-implies-recoverable-history
  (implies (fn-sn-open-okp (fn-sn-open-observed groups capacity frontier records))
           (fn-sf-history-recoverablep groups capacity records frontier))
  :hints (("Goal"
           :in-theory (e/d (fn-sn-open-observed fn-sn-open-okp fn-sn-open-state
                                                 fn-sn-open-ok fn-sn-observed-seed
                                                 fn-sn-recover fn-sf-recover
                                                 fn-sn-update fn-sn-make
                                                 fn-sn-files fn-sf-make fn-sf-phase)
                            (fn-sn-statep fn-sf-statep fn-sf-history-recoverablep
                             fn-sf-replay-node)))))

; Every process starts here.  A successful open satisfies the same relation
; that fn-sn-initial satisfies, so fn-snrt-mixed-trace-preserves-live-history-relation
; and its consequences hold for the host's actual starting state.
(defthm fn-sn-open-observed-success-has-live-history-relation
  (implies (fn-sn-open-okp (fn-sn-open-observed groups capacity frontier records))
           (fn-snt-relation
            (fn-sn-open-state
             (fn-sn-open-observed groups capacity frontier records))))
  :hints (("Goal"
           :use (fn-sn-open-observed-success-is-state
                 fn-sn-open-observed-success-remains-recovering
                 fn-sn-open-observed-success-exact-history
                 fn-sn-open-observed-success-configuration
                 fn-sn-open-observed-success-implies-recoverable-history)
           :in-theory (e/d (fn-snt-relation fn-snt-idle-phasep)
                            (fn-sn-open-observed fn-sn-open-okp fn-sn-open-state
                             fn-sn-statep fn-sf-statep fn-sf-history-recoverablep
                             fn-sf-replay-node fn-snt-pending-linkp
                             fn-sn-completion-enabledp fn-sn-files fn-sn-node
                             fn-sn-groups fn-sn-capacity fn-sf-records
                             fn-sf-frontier fn-sf-phase fn-sf-barriers
                             fn-sf-record-phasep
                             fn-sn-open-observed-success-is-state
                             fn-sn-open-observed-success-remains-recovering
                             fn-sn-open-observed-success-exact-history
                             fn-sn-open-observed-success-configuration
                             fn-sn-open-observed-success-implies-recoverable-history)))))

; -----------------------------------------------------------------------------
; Reopen succeeds on every structurally valid replayable image, and retains
; every acknowledged record under A-DURABILITY as a hypothesis (D5).

(defthm fn-sn-recover-of-recoverable-replaying-is-recovering
  (implies (and (fn-sn-statep st)
                (equal (fn-sf-phase (fn-sn-files st)) :replaying)
                (fn-sf-history-recoverablep (fn-sn-groups st) (fn-sn-capacity st)
                                            (fn-sf-records (fn-sn-files st))
                                            (fn-sf-frontier (fn-sn-files st))))
           (equal (fn-sf-phase (fn-sn-files (fn-sn-recover st))) :recovering))
  :hints (("Goal"
           :use ((:instance fn-sn-statep-implies-files-statep (st st)))
           :in-theory (e/d (fn-sn-recover fn-sf-recover fn-sn-update fn-sn-make
                                           fn-sf-make)
                            (fn-sn-statep fn-sf-statep fn-sf-history-recoverablep
                             fn-sf-replay-node)))))

(defthm fn-sn-open-observed-succeeds-on-recoverable-image
  (implies (and (fn-sn-observed-configurationp groups capacity)
                (fn-sn-observed-historyp frontier records)
                (fn-sf-history-recoverablep groups capacity records frontier))
           (fn-sn-open-okp (fn-sn-open-observed groups capacity frontier records)))
  :hints (("Goal"
           :use (fn-sn-observed-seed-is-state
                 (:instance fn-sn-recover-preserves-state
                            (s (fn-sn-observed-seed groups capacity frontier records)))
                 (:instance fn-sn-recover-of-recoverable-replaying-is-recovering
                            (st (fn-sn-observed-seed groups capacity frontier records))))
           :in-theory (e/d (fn-sn-open-observed fn-sn-open-okp fn-sn-open-state
                                                 fn-sn-open-ok
                                                 fn-sn-observed-configurationp
                                                 fn-sn-observed-historyp
                                                 fn-sn-observed-seed fn-sn-make
                                                 fn-sn-files fn-sn-groups
                                                 fn-sn-capacity fn-sf-make
                                                 fn-sf-phase fn-sf-records
                                                 fn-sf-frontier)
                            (fn-sn-statep fn-sf-statep fn-sf-history-recoverablep
                             fn-sf-replay-node fn-sn-recover
                             fn-sn-observed-seed-is-state
                             fn-sn-recover-preserves-state
                             fn-sn-recover-of-recoverable-replaying-is-recovering)))))

; A-DURABILITY as hypothesis.  For every image the platform may leave behind
; from a related live state (fn-sf-crash-imagep, store-files.lisp), the host's
; reopen entry succeeds and every pair acknowledged before the crash names a
; record of the reopened state.  The acknowledgement list itself is nil after
; reopen (fn-sn-open-observed-success-exact-history); the guarantee is carried
; by the records the adapter persists, not by a reconstructed ghost.
; The live-history relation carries the observed configuration predicate
; through fn-sn-statep (fn-snt-relation-implies-structural-state).
(defthm fn-snt-relation-implies-observed-configuration
  (implies (fn-snt-relation s)
           (fn-sn-observed-configurationp (fn-sn-groups s) (fn-sn-capacity s)))
  :hints (("Goal"
           :use fn-snt-relation-implies-structural-state
           :in-theory (e/d (fn-sn-statep fn-sn-observed-configurationp)
                            (fn-snt-relation fn-sf-statep fn-node-statep
                             fn-snt-relation-implies-structural-state
                             fn-snt-typed-store-components)))))

(defthm fn-sn-acknowledged-record-survives-observed-reopen
  (implies (and (fn-snt-relation s)
                (fn-sf-crash-imagep (fn-sn-files s) frontier records)
                (member-equal pair (fn-sf-successes (fn-sn-files s))))
           (and (fn-sn-open-okp
                 (fn-sn-open-observed (fn-sn-groups s) (fn-sn-capacity s)
                                      frontier records))
                (fn-sf-record-has-pairp
                 pair
                 (fn-sf-records
                  (fn-sn-files
                   (fn-sn-open-state
                    (fn-sn-open-observed (fn-sn-groups s) (fn-sn-capacity s)
                                         frontier records)))))))
  :hints (("Goal"
           :use (fn-snt-relation-implies-observed-configuration
                 fn-snt-admissible-crash-image-is-recoverable
                 (:instance fn-sf-admissible-image-facts (s (fn-sn-files s)))
                 (:instance fn-sn-open-observed-succeeds-on-recoverable-image
                            (groups (fn-sn-groups s)) (capacity (fn-sn-capacity s)))
                 (:instance fn-sn-open-observed-success-exact-history
                            (groups (fn-sn-groups s)) (capacity (fn-sn-capacity s))))
           :in-theory (e/d (fn-sn-observed-historyp)
                            (fn-snt-relation fn-sn-statep fn-sf-statep fn-node-statep
                             fn-sn-observed-configurationp
                             fn-snt-relation-implies-observed-configuration
                             fn-snt-relation-implies-structural-state
                             fn-sf-crash-imagep fn-sn-open-observed fn-sn-open-okp
                             fn-sn-open-state fn-sf-history-recoverablep
                             fn-sf-replay-node fn-sf-record-has-pairp
                             fn-sf-record-listp fn-sn-files fn-sn-groups
                             fn-sn-capacity fn-sf-records fn-sf-successes
                             fn-snt-admissible-crash-image-is-recoverable
                             fn-sf-admissible-image-facts
                             fn-sn-open-observed-succeeds-on-recoverable-image
                             fn-sn-open-observed-success-exact-history)))))

; -----------------------------------------------------------------------------
; The trace theorems re-rooted at the process entry.

(defthm fn-snrt-observed-open-mixed-trace-preserves-live-history-relation
  (implies (fn-sn-open-okp (fn-sn-open-observed groups capacity frontier records))
           (fn-snt-relation
            (fn-snrt-run
             (fn-sn-open-state
              (fn-sn-open-observed groups capacity frontier records))
             events)))
  :hints (("Goal"
           :use (fn-sn-open-observed-success-has-live-history-relation
                 (:instance fn-snrt-mixed-trace-preserves-live-history-relation
                            (s (fn-sn-open-state
                                (fn-sn-open-observed groups capacity frontier records)))))
           :in-theory (disable fn-snt-relation fn-snrt-run fn-sn-open-observed
                               fn-sn-open-okp fn-sn-open-state))))

; The ready or recovered node of any process that started from an observed
; image and ran any finite mixed trace is exact replay of its own surviving
; history and frontier.
(defthm fn-snrt-observed-open-ready-node-is-exact-replay
  (let ((final (fn-snrt-run
                (fn-sn-open-state
                 (fn-sn-open-observed groups capacity frontier records))
                events)))
    (implies (and (fn-sn-open-okp
                   (fn-sn-open-observed groups capacity frontier records))
                  (member-equal (fn-sf-phase (fn-sn-files final))
                                '(:ready :recovering :fenced-recovery)))
             (equal (fn-sn-node final)
                    (fn-sf-replay-node (fn-sn-groups final) (fn-sn-capacity final)
                                       (fn-sf-records (fn-sn-files final))
                                       (fn-sf-frontier (fn-sn-files final))))))
  :hints (("Goal"
           :use (fn-sn-open-observed-success-has-live-history-relation
                 (:instance fn-snrt-mixed-trace-ready-node-is-exact-replay
                            (s (fn-sn-open-state
                                (fn-sn-open-observed groups capacity frontier records)))))
           :in-theory (disable fn-snt-relation fn-snrt-run fn-sn-open-observed
                               fn-sn-open-okp fn-sn-open-state fn-sf-replay-node))))

; Acknowledged before the crash, present after reopen, present after any
; further mixed trace of the reopened process.
(defthm fn-snrt-acknowledged-record-retained-across-observed-reopen
  (let ((final (fn-snrt-run
                (fn-sn-open-state
                 (fn-sn-open-observed (fn-sn-groups s) (fn-sn-capacity s)
                                      frontier records))
                events)))
    (implies (and (fn-snt-relation s)
                  (fn-sf-crash-imagep (fn-sn-files s) frontier records)
                  (member-equal pair (fn-sf-successes (fn-sn-files s))))
             (fn-sf-record-has-pairp pair (fn-sf-records (fn-sn-files final)))))
  :hints (("Goal"
           :use (fn-sn-acknowledged-record-survives-observed-reopen
                 (:instance fn-sn-open-observed-success-has-live-history-relation
                            (groups (fn-sn-groups s)) (capacity (fn-sn-capacity s)))
                 (:instance fn-snrt-mixed-trace-records-prefix
                            (s (fn-sn-open-state
                                (fn-sn-open-observed (fn-sn-groups s) (fn-sn-capacity s)
                                                     frontier records))))
                 (:instance fn-sf-record-pair-preserved-by-prefix
                            (records
                             (fn-sf-records
                              (fn-sn-files
                               (fn-sn-open-state
                                (fn-sn-open-observed (fn-sn-groups s) (fn-sn-capacity s)
                                                     frontier records)))))
                            (more-records
                             (fn-sf-records
                              (fn-sn-files
                               (fn-snrt-run
                                (fn-sn-open-state
                                 (fn-sn-open-observed (fn-sn-groups s) (fn-sn-capacity s)
                                                      frontier records))
                                events))))))
           :in-theory (disable fn-snt-relation fn-snrt-run fn-sn-open-observed
                               fn-sn-open-okp fn-sn-open-state fn-sf-crash-imagep
                               fn-sf-record-has-pairp fn-sf-prefixp fn-sn-files
                               fn-sf-records fn-sf-successes fn-sn-groups
                               fn-sn-capacity
                               fn-sn-acknowledged-record-survives-observed-reopen
                               fn-sn-open-observed-success-has-live-history-relation
                               fn-snrt-mixed-trace-records-prefix
                               fn-sf-record-pair-preserved-by-prefix))))
