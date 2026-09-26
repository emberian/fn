; The host's reopen and the store-only reopen the K4 family is stated over.
;
; host/store-node-host.lisp:159 (fn-store-sn-recover) and
; host/owner-host.lisp:193 open every process through fn-cpo-open-observed
; (books/config-observed.lisp).  The crash keystones K4 (books/store-observed,
; books/byte-store-keystones, books/bp-receiver-evolving-store-invariants) are
; stated over fn-sn-open-observed, which no host line calls.  This book states
; the exact relation between the two and carries each cited K4 statement to
; the host's call as a corollary named <keystone>-of-host-open.
;
; THE RELATION.  Both opens refuse unless the same four image conditions hold
; (fn-sn-observed-historyp and the identity, consumer and topic replays of
; the Store journal); they differ in exactly one conjunct, the replay that
; builds the node:
;   fn-sn-open-observed G C   needs fn-sn-observed-configurationp G C and
;                             fn-sf-history-recoverablep G C events frontier
;                             (one fixed group table, fn-replay);
;   fn-cpo-open-observed cfgs needs fn-sob-configured-openp cfgs frontier
;                             events (the configuration journal interleaved
;                             with the Store journal, fn-cpr-replay).
; On success both carry the same kernel, fn-bs-recovered-kernel frontier
; events 0: the journal as observed, the frontier, no successes, :recovering
; at zero barriers.  They do not carry the same node, groups, capacity or
; configuration history: the host's node is the configured replay's.
;
; WHAT TRANSFERS.  Every K4 conclusion about the kernel (records, frontier,
; successes, the five barriers) and every conclusion that the reopen
; succeeds transfers, the latter under fn-sob-configured-openp as the one
; added hypothesis.  Conclusions about the node against a fixed group table
; do not: the exact-history node conjunct of
; fn-sn-open-observed-success-exact-history, fn-snt-relation
; (fn-sn-open-observed-success-has-live-history-relation) and the two BP
; theorems whose invariant contains fn-snt-relation.  The host-side relation
; for the node is fn-cpo-history-relation (config-observed.lisp).
(in-package "ACL2")
(include-book "byte-store-k0-recovery")
(include-book "bp-receiver-evolving-store-invariants")

; The configuration-journal conjuncts of fn-cpo-open-observed's success.
(defun fn-sob-configured-openp (configs frontier events)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((replayed (fn-cpr-replay configs events))
         (cn (fn-replay-result-node replayed)))
    (and (not (null configs))
         (equal (fn-replay-result-kind replayed) :ok)
         (fn-cnode-statep cn)
         (fn-replay-advance-okp (fn-cnode-node cn) frontier))))
(defthm fn-sob-sn-open-ok-facts
  (implies (fn-sn-open-okp (fn-sn-open-observed groups capacity frontier events))
           (and (fn-sn-observed-historyp frontier events)
                (fn-sn-observed-identity-okp events)
                (fn-sn-observed-consumer-okp events)
                (fn-sn-observed-topic-okp events)
                (equal (fn-sn-files (fn-sn-open-state
                                     (fn-sn-open-observed groups capacity frontier events)))
                       (fn-bs-recovered-kernel frontier events 0))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-sn-observed-seed-is-state)
           :in-theory
           (e/d (fn-sn-open-observed fn-sn-open-okp fn-sn-observed-seed
                 fn-sn-recover fn-sf-recover fn-sn-update fn-sn-update-replayed
                 fn-bs-recovered-kernel fn-sn-observed-historyp
                 fn-sn-observed-identity-okp fn-sn-observed-consumer-okp
                 fn-sn-observed-topic-okp)
                (fn-sn-statep fn-sf-statep fn-sf-history-recoverablep
                 fn-sf-replay-node fn-replay-identity fn-cpe-projection-replay
                 fn-th-prefix-project fn-stx-index-of-store fn-cei-build
                 fn-sn-observed-seed-is-state)))))
(defthm fn-sob-cpo-open-ok-facts
  (implies (fn-sn-open-okp (fn-cpo-open-observed configs frontier events))
           (and (fn-sob-configured-openp configs frontier events)
                (fn-sn-observed-historyp frontier events)
                (fn-sn-observed-identity-okp events)
                (fn-sn-observed-consumer-okp events)
                (fn-sn-observed-topic-okp events)
                (fn-sn-statep (fn-sn-open-state
                               (fn-cpo-open-observed configs frontier events)))
                (equal (fn-sn-files (fn-sn-open-state
                                     (fn-cpo-open-observed configs frontier events)))
                       (fn-bs-recovered-kernel frontier events 0))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-host-reopened-kernel-is-the-recovered-kernel)
           :in-theory
           (e/d (fn-cpo-open-observed fn-sn-open-okp fn-sob-configured-openp
                 fn-sn-observed-identity-okp fn-sn-observed-consumer-okp
                 fn-sn-observed-topic-okp)
                (fn-cpr-replay fn-cpr-loop fn-replay-identity fn-replay-identity-loop
                 fn-stx-index-of-store fn-sn-statep fn-cnode-statep
                 fn-sn-observed-seed fn-replay-advance-txid fn-sn-with-configuration
                 fn-sn-observed-historyp fn-cpe-projection-replay
                 fn-th-prefix-project fn-cei-build fn-cpo-install
                 fn-sn-update-replayed fn-bs-recovered-kernel)))))
(local (defthm fn-sob-group-listp-names-are-strings
  (implies (fn-cfg-group-listp es)
           (fn-string-listp (fn-cfg-group-all-names es)))
  :hints (("Goal" :in-theory (enable fn-cfg-group-listp fn-cfg-group-all-names
                                     fn-cfg-group-entryp fn-record-group-namep)))))
(local (defthm fn-sob-member-namep-is-member
  (iff (fn-cfg-member-namep name names) (member-equal name names))
  :hints (("Goal" :in-theory (enable fn-cfg-member-namep)))))
(local (defthm fn-sob-no-duplicate-namesp-is-no-duplicatesp
  (implies (fn-cfg-no-duplicate-namesp names) (fn-no-duplicatesp names))
  :hints (("Goal" :in-theory (enable fn-cfg-no-duplicate-namesp)))))
(local (defthm fn-sob-cnode-statep-configuration-facts
  (implies (fn-cnode-statep cn)
           (and (fn-string-listp (fn-cnode-domain-of (fn-cnode-config cn)))
                (fn-no-duplicatesp (fn-cnode-domain-of (fn-cnode-config cn)))
                (natp (fn-cfg-capacity (fn-cfg-value (fn-cnode-config cn))))
                (fn-node-statep (fn-cnode-node cn))))
  :hints (("Goal" :in-theory (enable fn-cnode-statep fn-cfgp fn-cfg-valuep
                                     fn-cnode-domain-of)))))

(local (defthm fn-sob-recovering-kernel-is-state
  (implies (and (fn-record-uint32p f) (fn-sf-record-listp r 0 0 f))
           (fn-sf-statep (fn-sf-make :recovering f nil r nil nil nil 0)))
  :hints (("Goal" :in-theory (enable fn-sf-statep fn-sf-phase-shapep)))))

(local (defthm fn-sob-with-configuration-of-make-v6
  (equal (fn-sn-with-configuration
          (fn-sn-make-v6 g c files node keyring index kgen verdicts snapshots
                         next history consumer topic event-index)
          g2 c2 node2 history2)
         (fn-sn-make-v6 g2 c2 files node2 keyring index kgen verdicts snapshots
                        next history2 consumer topic event-index))
  :hints (("Goal" :in-theory (enable fn-sn-with-configuration fn-sn-make-v6 fn-sn-make-v7)))))

(local (defthm fn-sob-statep-of-v6-fields
   (implies (and (fn-string-listp groups)
                 (fn-no-duplicatesp groups)
                 (natp capacity)
                 (fn-sf-statep files)
                 (fn-node-statep node)
                 (fn-prin-keyringp keyring)
                 (natp keyring-generation)
                 (fn-sn-verdict-listp verdicts)
                 (fn-sn-keyring-snapshot-listp snapshots)
                 (natp identity-next))
            (fn-sn-statep
             (fn-sn-make-v6 groups capacity files node keyring index
                            keyring-generation verdicts snapshots identity-next
                            config-history consumer topic event-index)))
   :hints (("Goal" :in-theory
            (enable fn-sn-statep fn-sn-shapep fn-sn-make-v6 fn-sn-make-v7
                    fn-sn-groups fn-sn-capacity fn-sn-files fn-sn-node
                    fn-sn-keyring fn-sn-keyring-generation fn-sn-verdicts
                    fn-sn-keyring-snapshots fn-sn-identity-next)))))

(defun fn-sob-identity-typedp (events)
  (declare (xargs :guard t :verify-guards nil))
  (let ((ctx (fn-replay-identity events)))
    (and (fn-sn-verdict-listp
          (fn-replay-verdict-pairs (fn-stxk-context-verdicts ctx)))
         (fn-sn-keyring-snapshot-listp (fn-stxk-context-snapshots ctx))
         (natp (fn-stxk-context-next ctx)))))

(local (defthm fn-sob-sn-open-ok-identity-typed
  (implies (fn-sn-open-okp (fn-sn-open-observed groups capacity frontier events))
           (fn-sob-identity-typedp events))
  :hints (("Goal"
           :use (fn-sn-open-observed-success-is-state)
           :in-theory
           (e/d (fn-sn-open-observed fn-sn-open-okp fn-sn-observed-seed
                 fn-sn-recover fn-sf-recover fn-sn-update fn-sn-update-replayed
                 fn-sob-identity-typedp fn-sn-statep
                 fn-sn-with-event-index fn-sn-with-topic fn-sn-with-consumer)
                (fn-sf-statep fn-sf-history-recoverablep fn-node-statep
                 fn-sf-replay-node fn-replay-identity fn-cpe-projection-replay
                 fn-th-prefix-project fn-stx-index-of-store fn-cei-build
                 fn-sn-verdict-listp fn-sn-keyring-snapshot-listp
                 fn-replay-verdict-pairs
                 fn-sn-open-observed-success-is-state))))))

(defthm fn-sob-cpo-opens-on-configured-image
  (implies (and (fn-sob-configured-openp configs frontier events)
                (fn-sn-observed-historyp frontier events)
                (fn-sn-observed-identity-okp events)
                (fn-sn-observed-consumer-okp events)
                (fn-sn-observed-topic-okp events)
                (fn-sob-identity-typedp events))
           (fn-sn-open-okp (fn-cpo-open-observed configs frontier events)))
  :hints (("Goal"
           :use (fn-cpr-replay-ok-is-configured)
           :in-theory
           (e/d (fn-cpo-open-observed fn-sn-open-okp fn-sob-configured-openp
                 fn-sn-observed-identity-okp fn-sn-observed-consumer-okp
                 fn-sn-observed-topic-okp fn-cpo-install fn-sob-identity-typedp
                 fn-sn-with-event-index fn-sn-with-topic fn-sn-with-consumer
                 fn-sn-update-replayed fn-sn-observed-seed fn-sn-observed-historyp
                 )
                (fn-cpr-replay fn-cpr-loop fn-replay-identity fn-replay-identity-loop
                 fn-stx-index-of-store fn-cnode-statep fn-sn-statep
                 fn-sn-with-configuration fn-sn-make-v6 fn-sn-make-v7 fn-sn-make fn-sn-make-v2
                 fn-replay-advance-txid 
                 fn-cpe-projection-replay fn-cpr-replay-ok-is-configured
                 fn-th-prefix-project fn-cei-build)))))

(local (defthm fn-sob-cpo-open-ok-identity-typed
  (implies (fn-sn-open-okp (fn-cpo-open-observed configs frontier events))
           (fn-sob-identity-typedp events))
  :hints (("Goal"
           :in-theory
           (e/d (fn-cpo-open-observed fn-sn-open-okp fn-cpo-install
                 fn-sn-update-replayed fn-sob-identity-typedp fn-sn-statep
                 fn-sn-with-event-index fn-sn-with-topic fn-sn-with-consumer)
                (fn-cpr-replay fn-cpr-loop fn-replay-identity fn-replay-identity-loop
                 fn-stx-index-of-store fn-cnode-statep fn-sn-observed-seed
                 fn-replay-advance-txid fn-sn-with-configuration fn-sf-statep
                 fn-node-statep fn-cpe-projection-replay fn-th-prefix-project
                 fn-cei-build fn-sn-verdict-listp fn-sn-keyring-snapshot-listp
                 fn-replay-verdict-pairs fn-sn-observed-historyp))))))

; THE BRIDGE, part 1: the exact success condition of the host's open.  It
; shares four conjuncts with fn-sn-open-observed's (the history shape and the
; identity, consumer and topic replays; the fifth, the identity context's
; field types, is what fn-sn-statep asks of the opened state) and replaces
; the fixed-table replay by the configured one.
(defthm fn-cpo-open-observed-succeeds-exactly
  (iff (fn-sn-open-okp (fn-cpo-open-observed configs frontier events))
       (and (fn-sob-configured-openp configs frontier events)
            (fn-sn-observed-historyp frontier events)
            (fn-sn-observed-identity-okp events)
            (fn-sn-observed-consumer-okp events)
            (fn-sn-observed-topic-okp events)
            (fn-sob-identity-typedp events)))
  :rule-classes nil
  :hints (("Goal" :use (fn-sob-cpo-open-ok-facts fn-sob-cpo-open-ok-identity-typed
                        fn-sob-cpo-opens-on-configured-image)
           :in-theory nil)))

; THE BRIDGE, part 2: whenever the store-only reopen succeeds on an image
; whose configuration journal replays to a configured node accepting the
; frontier, the host's reopen succeeds on the same image and carries the
; same file kernel.
(defthm fn-cpo-open-observed-is-sn-open-observed-on-the-kernel
  (implies (and (fn-sn-open-okp (fn-sn-open-observed groups capacity frontier events))
                (fn-sob-configured-openp configs frontier events))
           (and (fn-sn-open-okp (fn-cpo-open-observed configs frontier events))
                (equal (fn-sn-files (fn-sn-open-state
                                     (fn-cpo-open-observed configs frontier events)))
                       (fn-sn-files (fn-sn-open-state
                                     (fn-sn-open-observed groups capacity frontier events))))))
  :rule-classes nil
  :hints (("Goal" :use (fn-sob-sn-open-ok-facts fn-sob-sn-open-ok-identity-typed
                        fn-sob-cpo-opens-on-configured-image
                        fn-sob-cpo-open-ok-facts)
           :in-theory nil)))

; =============================================================================
; The K4 statements at the host's call.  Each corollary names its keystone.
;
; Kernel conclusions: over the host's success alone.  The host's success does
; not imply fn-sn-open-observed's for any group table (the configured replay
; may accept an event a fixed final table refuses), so these three are proved
; from the bridge's kernel fact and the generic barrier lemmas their keystones
; also stand on, not by instantiating the keystone.

(defthm fn-sn-open-observed-success-exact-history-of-host-open
  (implies (fn-sn-open-okp (fn-cpo-open-observed configs frontier events))
           (let ((files (fn-sn-files (fn-sn-open-state
                                      (fn-cpo-open-observed configs frontier events)))))
             (and (equal (fn-sf-records files) events)
                  (equal (fn-sf-frontier files) frontier)
                  (equal (fn-sf-successes files) nil))))
  :hints (("Goal" :use (fn-sob-cpo-open-ok-facts)
           :in-theory (e/d (fn-bs-recovered-kernel) (fn-cpo-open-observed)))))

(local (defthm fn-sob-host-open-recovering-state
  (implies (fn-sn-open-okp (fn-cpo-open-observed configs frontier events))
           (let ((st (fn-sn-open-state (fn-cpo-open-observed configs frontier events))))
             (and (fn-sn-statep st)
                  (equal (fn-sf-phase (fn-sn-files st)) :recovering)
                  (equal (fn-sf-barriers (fn-sn-files st)) 0))))
  :hints (("Goal" :use (fn-sob-cpo-open-ok-facts)
           :in-theory (e/d (fn-bs-recovered-kernel)
                           (fn-cpo-open-observed fn-sn-statep))))))

(defthm fn-sn-open-observed-not-ready-before-five-barriers-of-host-open
  (implies (fn-sn-open-okp (fn-cpo-open-observed configs frontier events))
           (let ((st (fn-sn-open-state (fn-cpo-open-observed configs frontier events))))
             (and (equal (fn-sf-phase (fn-sn-files (fn-sn-observed-rebarrier st 0))) :recovering)
                  (equal (fn-sf-phase (fn-sn-files (fn-sn-observed-rebarrier st 1))) :recovering)
                  (equal (fn-sf-phase (fn-sn-files (fn-sn-observed-rebarrier st 2))) :recovering)
                  (equal (fn-sf-phase (fn-sn-files (fn-sn-observed-rebarrier st 3))) :recovering)
                  (equal (fn-sf-phase (fn-sn-files (fn-sn-observed-rebarrier st 4))) :recovering))))
  :hints (("Goal"
           :use (fn-sob-host-open-recovering-state
                 (:instance fn-sn-observed-four-ok-barriers-remain-recovering
                            (st (fn-sn-open-state
                                 (fn-cpo-open-observed configs frontier events)))))
           :in-theory (disable fn-sob-host-open-recovering-state
                               fn-sn-observed-four-ok-barriers-remain-recovering
                               fn-cpo-open-observed fn-sn-open-okp
                               fn-sn-observed-rebarrier fn-sn-statep))))

(defthm fn-sn-open-observed-five-barriers-open-ready-of-host-open
  (implies (fn-sn-open-okp (fn-cpo-open-observed configs frontier events))
           (equal (fn-sf-phase
                   (fn-sn-files
                    (fn-sn-observed-rebarrier
                     (fn-sn-open-state (fn-cpo-open-observed configs frontier events)) 5)))
                  :ready))
  :hints (("Goal"
           :use (fn-sob-host-open-recovering-state
                 (:instance fn-sn-observed-five-ok-barriers-is-ready
                            (st (fn-sn-open-state
                                 (fn-cpo-open-observed configs frontier events)))))
           :in-theory (disable fn-sob-host-open-recovering-state
                               fn-sn-observed-five-ok-barriers-is-ready
                               fn-cpo-open-observed fn-sn-open-okp
                               fn-sn-observed-rebarrier fn-sn-statep))))

; fn-sn-open-observed-success-has-live-history-relation does not transfer:
; fn-snt-relation compares the node with fn-sf-replay-node over the state's
; own groups, and the host's node is the configured replay's.  Its host-side
; counterpart is the configuration-aware relation, which holds of every
; successful host open.
(defthm fn-cpo-open-observed-success-has-history-relation
  (implies (fn-sn-open-okp (fn-cpo-open-observed configs frontier events))
           (fn-cpo-history-relation
            (fn-sn-open-state (fn-cpo-open-observed configs frontier events))))
  :hints (("Goal"
           :use (fn-sob-cpo-open-ok-facts)
           :in-theory
           (e/d (fn-cpo-open-observed fn-sn-open-okp fn-cpo-history-relation
                 fn-cpo-install fn-sob-configured-openp fn-bs-recovered-kernel
                 fn-sn-update-replayed fn-sn-with-event-index fn-sn-with-topic
                 fn-sn-with-consumer)
                (fn-cpr-replay fn-cpr-loop fn-replay-identity fn-replay-identity-loop
                 fn-stx-index-of-store fn-cnode-statep fn-sn-observed-seed
                 fn-replay-advance-txid fn-sn-with-configuration fn-sn-statep
                 fn-sn-make-v6 fn-sn-make-v7 fn-sn-make fn-sn-make-v2
                 fn-cpe-projection-replay fn-th-prefix-project fn-cei-build
                 fn-sn-observed-historyp)))))

; Reopen conclusions: the keystone's hypotheses and fn-sob-configured-openp
; over the configuration journal the host reads.  Each is the keystone
; instance composed with fn-cpo-open-observed-is-sn-open-observed-on-the-kernel.

(defthm fn-sn-acknowledged-record-survives-observed-reopen-of-host-open
  (implies (and (fn-snt-relation s)
                (fn-sf-crash-imagep (fn-sn-files s) frontier records)
                (fn-sn-observed-identity-okp records)
                (fn-sn-observed-consumer-okp records)
                (fn-sn-observed-topic-okp records)
                (member-equal pair (fn-sf-successes (fn-sn-files s)))
                (fn-sob-configured-openp configs frontier records))
           (and (fn-sn-open-okp (fn-cpo-open-observed configs frontier records))
                (fn-sf-record-has-pairp
                 pair
                 (fn-sf-records
                  (fn-sn-files
                   (fn-sn-open-state (fn-cpo-open-observed configs frontier records)))))))
  :hints (("Goal"
           :use (fn-sn-acknowledged-record-survives-observed-reopen
                 (:instance fn-cpo-open-observed-is-sn-open-observed-on-the-kernel
                            (groups (fn-sn-groups s)) (capacity (fn-sn-capacity s))
                            (events records)))
           :in-theory nil)))

(defthm fn-sn-recovery-admissible-image-reopens-of-host-open
  (implies (and (fn-snt-relation s)
                (fn-sf-recovery-crash-imagep (fn-sn-files s) frontier records)
                (fn-sn-observed-identity-okp records)
                (fn-sn-observed-consumer-okp records)
                (fn-sn-observed-topic-okp records)
                (fn-sob-configured-openp configs frontier records))
           (fn-sn-open-okp (fn-cpo-open-observed configs frontier records)))
  :hints (("Goal"
           :use (fn-sn-recovery-admissible-image-reopens
                 (:instance fn-cpo-open-observed-is-sn-open-observed-on-the-kernel
                            (groups (fn-sn-groups s)) (capacity (fn-sn-capacity s))
                            (events records)))
           :in-theory nil)))

; fn-bprv-system-invariantp is fn-snt-relation and fn-bprv-evolving-invariantp;
; the second reads the Store only through its journal, so it transfers, and
; the first does not (see above).
(local (defthm fn-sob-evolving-invariant-reads-the-journal
  (implies (equal (fn-sn-files a) (fn-sn-files b))
           (equal (fn-bprv-evolving-invariantp a st journal)
                  (fn-bprv-evolving-invariantp b st journal)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-bprv-evolving-invariantp fn-bprv-history)))))

(defthm fn-bprv-evolving-invariant-survives-observed-reopen-of-host-open
  (implies (and (fn-bprv-system-invariantp store st journal)
                (fn-csi-full-relationp store)
                (fn-sf-crash-imagep (fn-sn-files store) frontier records)
                (fn-sn-observed-identity-okp records)
                (fn-sn-observed-topic-okp records)
                (fn-sob-configured-openp configs frontier records))
           (let ((opened (fn-cpo-open-observed configs frontier records)))
             (and (fn-sn-open-okp opened)
                  (fn-bprv-evolving-invariantp (fn-sn-open-state opened) st journal))))
  :hints (("Goal"
           :use (fn-bprv-evolving-invariant-survives-observed-reopen
                 (:instance fn-cpo-open-observed-is-sn-open-observed-on-the-kernel
                            (groups (fn-sn-groups store)) (capacity (fn-sn-capacity store))
                            (events records))
                 (:instance fn-sob-evolving-invariant-reads-the-journal
                            (a (fn-sn-open-state (fn-cpo-open-observed configs frontier records)))
                            (b (fn-sn-open-state (fn-sn-open-observed
                                                  (fn-sn-groups store) (fn-sn-capacity store)
                                                  frontier records)))))
           :in-theory '(fn-bprv-system-invariantp))))


(defthm fn-bs-crash-image-reopens-of-host-open
  (implies (and (fn-csi-full-relationp s)
                (fn-bs-store-relation bs (fn-sn-files s))
                (fn-bs-crash-imagep bs image)
                (fn-sn-observed-identity-okp
                 (fn-bs-scan-records (fn-bs-scan-store image)))
                (fn-sn-observed-topic-okp
                 (fn-bs-scan-records (fn-bs-scan-store image)))
                (fn-sob-configured-openp configs
                                         (fn-bs-scan-frontier (fn-bs-scan-store image))
                                         (fn-bs-scan-records (fn-bs-scan-store image))))
           (fn-sn-open-okp
            (fn-cpo-open-observed configs
                                  (fn-bs-scan-frontier (fn-bs-scan-store image))
                                  (fn-bs-scan-records (fn-bs-scan-store image)))))
  :hints (("Goal"
           :use (fn-bs-crash-image-reopens
                 (:instance fn-cpo-open-observed-is-sn-open-observed-on-the-kernel
                            (groups (fn-sn-groups s)) (capacity (fn-sn-capacity s))
                            (frontier (fn-bs-scan-frontier (fn-bs-scan-store image)))
                            (events (fn-bs-scan-records (fn-bs-scan-store image)))))
           :in-theory nil)))

(defthm fn-bs-acknowledged-record-survives-byte-crash-of-host-open
  (implies (and (fn-csi-full-relationp s)
                (fn-bs-store-relation bs (fn-sn-files s))
                (fn-bs-crash-imagep bs image)
                (fn-sn-observed-identity-okp
                 (fn-bs-scan-records (fn-bs-scan-store image)))
                (fn-sn-observed-topic-okp
                 (fn-bs-scan-records (fn-bs-scan-store image)))
                (member-equal pair (fn-sf-successes (fn-sn-files s)))
                (fn-sob-configured-openp configs
                                         (fn-bs-scan-frontier (fn-bs-scan-store image))
                                         (fn-bs-scan-records (fn-bs-scan-store image))))
           (let ((opened (fn-cpo-open-observed
                          configs
                          (fn-bs-scan-frontier (fn-bs-scan-store image))
                          (fn-bs-scan-records (fn-bs-scan-store image)))))
             (and (fn-sn-open-okp opened)
                  (fn-sf-record-has-pairp
                   pair (fn-sf-records (fn-sn-files (fn-sn-open-state opened)))))))
  :hints (("Goal"
           :use (fn-bs-acknowledged-record-survives-byte-crash
                 (:instance fn-cpo-open-observed-is-sn-open-observed-on-the-kernel
                            (groups (fn-sn-groups s)) (capacity (fn-sn-capacity s))
                            (frontier (fn-bs-scan-frontier (fn-bs-scan-store image)))
                            (events (fn-bs-scan-records (fn-bs-scan-store image)))))
           :in-theory nil)))

(defthm fn-bs-sweep-round-keeps-every-cut-reopenable-of-host-open
  (implies (and (fn-csi-full-relationp s)
                (fn-bs-store-relation bs (fn-sn-files s))
                (member-equal pair
                              (fn-bs-run bs (fn-sn-files s)
                                         (fn-bs-recover-sweep-program
                                          (cadr (fn-sn-sweep-round s observed overp held)))
                                         outcomes groups capacity))
                (fn-bs-crash-imagep (car pair) image)
                (fn-sn-observed-identity-okp
                 (fn-bs-scan-records (fn-bs-scan-store image)))
                (fn-sn-observed-topic-okp
                 (fn-bs-scan-records (fn-bs-scan-store image)))
                (fn-sob-configured-openp configs
                                         (fn-bs-scan-frontier (fn-bs-scan-store image))
                                         (fn-bs-scan-records (fn-bs-scan-store image))))
           (and (equal (cdr pair) (fn-sn-files s))
                (equal (fn-bs-scan-store (car pair)) (fn-bs-scan-store bs))
                (fn-sn-open-okp
                 (fn-cpo-open-observed configs
                                       (fn-bs-scan-frontier (fn-bs-scan-store image))
                                       (fn-bs-scan-records (fn-bs-scan-store image))))))
  :hints (("Goal"
           :use (fn-bs-sweep-round-keeps-every-cut-reopenable
                 (:instance fn-cpo-open-observed-is-sn-open-observed-on-the-kernel
                            (groups (fn-sn-groups s)) (capacity (fn-sn-capacity s))
                            (frontier (fn-bs-scan-frontier (fn-bs-scan-store image)))
                            (events (fn-bs-scan-records (fn-bs-scan-store image)))))
           :in-theory nil)))
