; fn: the live configuration completion from the owner's carried state
; (lane control-quanta, 2026-09-27; PRF-265, PKT-827).
;
; This book shares the prefix `fn-oclc-' (docs/prefixes.md).
(in-package "ACL2")
(include-book "config-owner-publish")
(include-book "config-carried-candidate")

; What this replaces.  host/owner-host.lisp `fn-owner-reconfigure-complete'
; (called by host/native/admin.lisp `fnn-owner-live-reconfigure-locked', the
; one completion of every live `group create', `control grant' and the other
; live configuration verbs) called `fn-ocl-publish', whose `fn-ocl-complete'
; runs `fn-cpo-configure-durable': a full `fn-cpr-replay' of the
; configuration and Store histories and `fn-sn-statep' of the store (inside
; `fn-cpo-history-relation'), a second full replay of the extended
; configuration history, `fn-sn-statep' of the candidate, then
; `fn-ocl-store-config', a third full replay.  Each walks every Store record
; (re-validating it through `fn-record-p'); the hold of one control quantum
; grew with the store: 2.9 s at 1,000 articles on an idle hbox owner, 85 per
; cent of its samples in those replays (planning/evidence/
; control-quanta-2026-09-27.md section 1).  The owner carries what the
; replays recompute: its store's node IS the replayed node advanced to the
; frontier, and its configuration IS the replayed configuration, both by
; `fn-ocl-relation' (books/config-owner-live.lisp), the invariant
; `fn-owner-recover' establishes (books/owner-recover-ocl.lisp
; `fn-orec-started-owner-ocl-relation') and the owner's transitions preserve.
; So the one configuration record is applied to the carried node: one step of
; the fold, no record revisited, and the keystone below equates the result
; with `fn-ocl-publish' under that invariant.

; -----------------------------------------------------------------------------
; The carried steps: the fold's one configuration step without its
; whole-node recognizer, which the carried invariant supplies.

; `fn-replay-advance-okp' without `fn-node-statep': its scalar tests (as
; books/config-carried-open.lisp `fn-oclc-advance-okp', which this book does
; not include: its closure holds the BP receiver books).
(defun fn-oclc-advance-okp (node txid)
  (declare (xargs :guard t))
  (let ((acceptance (fn-node-acceptance node)))
    (and (natp txid)
         (null (fn-node-stage node))
         (null (fn-state-pending acceptance))
         (equal (fn-state-fenced acceptance) nil)
         (natp (fn-state-next-txid acceptance))
         (<= (fn-state-next-txid acceptance) txid))))

; `fn-replay-advance-txid' without `fn-node-statep'.
(defun fn-oclc-advance (node txid)
  (declare (xargs :guard t))
  (let ((acceptance (fn-node-acceptance node)))
    (if (fn-oclc-advance-okp node txid)
        (fn-node-make-state
         (fn-make-state (fn-state-groups acceptance)
                        (fn-state-nexts acceptance)
                        (fn-state-articles acceptance)
                        txid nil nil)
         (fn-node-retention node)
         nil
         (fn-node-bindings node))
      node)))

; `fn-cnode-apply-config' with the carried acceptance check and without the
; configured-node recognizer.
(defun fn-oclc-apply (cn record)
  (declare (xargs :guard t))
  (if (not (fn-cnode-carried-acceptablep cn record (fn-cnode-line-ceiling)))
      cn
    (let* ((node (fn-cnode-node cn))
           (acc (fn-node-acceptance node))
           (ret (fn-node-retention node))
           (config (fn-cfg-apply-record (fn-cnode-config cn) record))
           (domain (fn-cnode-domain-of config)))
      (fn-cnode-make
       (fn-node-make-state
        (fn-make-state domain
                       (fn-cnode-extend-nexts domain (fn-state-nexts acc))
                       (fn-state-articles acc)
                       (fn-state-next-txid acc)
                       nil nil)
        (fn-retain-make-state (fn-cfg-capacity (fn-cfg-value config))
                              (fn-retain-reserved ret)
                              (fn-retain-pins ret)
                              (fn-retain-releases ret))
        nil
        (fn-node-bindings node))
       config))))

; The conjuncts of `fn-sn-statep' a configuration install can change, other
; than the node (which the fold's success makes a node state).
(defun fn-oclc-install-okp (groups capacity)
  (declare (xargs :guard t))
  (and (fn-string-listp groups)
       (fn-no-duplicatesp groups)
       (natp capacity)))

; `fn-cpo-configure-durable' from the carried node and configuration: (mv
; STORE CONFIG), the installed store and its configuration, or ST and CONFIG
; unchanged when the record does not apply.
(defun fn-oclc-configure (st config record)
  (declare (xargs :guard t))
  (let* ((configs (fn-sn-config-history st))
         (files (fn-sn-files st))
         (frontier (fn-sf-frontier files))
         (node (fn-sn-node st)))
    (if (and (true-listp st)
             (true-listp configs)
             (equal (fn-sf-phase files) :ready)
             (fn-cfg-recordp record)
             (equal (fn-cfg-record-txid record) frontier)
             (equal (fn-cfg-record-sequence record) (len configs))
             (fn-oclc-advance-okp node frontier))
        (let ((at (fn-cnode-make (fn-oclc-advance node frontier) config)))
          (if (fn-cnode-carried-acceptablep at record (fn-cnode-line-ceiling))
              (let* ((cn (fn-oclc-apply at record))
                     (n1 (fn-cnode-node cn))
                     (config1 (fn-cnode-config cn)))
                (if (and (fn-oclc-advance-okp n1 frontier)
                         (fn-oclc-install-okp
                          (fn-cnode-domain-of config1)
                          (fn-cfg-capacity (fn-cfg-value config1))))
                    (mv (fn-cpo-install
                         st (fn-cnode-make (fn-oclc-advance n1 frontier) config1)
                         (append configs (list record)))
                        config1)
                  (mv st config)))
            (mv st config)))
      (mv st config))))

; -----------------------------------------------------------------------------
; The completion and the publication the host calls.

; `fn-ocl-complete''s staged arm from the carried state.  The publication
; below calls it only with a staged record.
(defun fn-oclc-complete (oc)
  (declare (xargs :guard t))
  (let* ((record (fn-ocfg-staged oc))
         (o (fn-ocfg-owner oc))
         (old-store (fn-own-store o)))
    (mv-let (new-store config1)
      (fn-oclc-configure old-store (fn-ocfg-config oc) record)
      (if (equal (fn-sn-config-history new-store)
                 (fn-sn-config-history old-store))
          oc
        (fn-ocfg-make (fn-ocl-owner-with-store o new-store)
                      config1 (fn-ocfg-pins oc) nil)))))

; THE HOST-CALLED COMPLETION: host/owner-host.lisp
; `fn-owner-reconfigure-complete'.  `fn-ocl-publish' with `fn-oclc-complete'
; for `fn-ocl-complete'.
(defun fn-oclc-publish (oc generation max-octets)
  (declare (xargs :guard t))
  (let ((record (fn-ocfg-staged oc)))
    (if (or (not record)
            (not (equal (fn-cfg-record-generation record) generation)))
        (mv :refused oc)
      (let ((next (fn-oclc-complete oc)))
        (if (fn-ocfg-staged next)
            (mv :recovery-required oc)
          (mv :durable
              (fn-ocfg-with-owner
               next
               (fn-own-configure
                (fn-ocfg-owner next)
                (fn-oag-post-config (fn-ocfg-config next) max-octets)))))))))

; -----------------------------------------------------------------------------
; The carried steps are the fold's steps on a node state.
(defthm fn-oclc-advance-is-replay-advance
  (implies (fn-node-statep node)
           (equal (fn-oclc-advance node txid)
                  (fn-replay-advance-txid node txid)))
  :hints (("Goal" :in-theory (enable fn-replay-advance-txid fn-oclc-advance-okp
                                     fn-node-statep fn-statep))))

(defthm fn-oclc-advance-okp-of-advance
  (implies (fn-replay-advance-okp node txid)
           (fn-oclc-advance-okp (fn-replay-advance-txid node txid) txid))
  :hints (("Goal" :in-theory (enable fn-replay-advance-txid fn-replay-advance-okp
                                     fn-oclc-advance-okp))))

(defthm fn-oclc-advance-of-advance
  (implies (fn-replay-advance-okp node txid)
           (equal (fn-replay-advance-txid (fn-replay-advance-txid node txid) txid)
                  (fn-replay-advance-txid node txid)))
  :hints (("Goal" :in-theory (enable fn-replay-advance-txid fn-replay-advance-okp))))

(defthm fn-oclc-apply-is-apply-config
  (implies (fn-cnode-statep cn)
           (equal (fn-oclc-apply cn record)
                  (fn-cnode-apply-config cn record (fn-cnode-line-ceiling))))
  :hints (("Goal" :use ((:instance fn-cnode-record-acceptablep-is-the-carried-check
                                   (ceiling (fn-cnode-line-ceiling))))
           :in-theory (e/d (fn-cnode-apply-config)
                           (fn-cnode-statep fn-cnode-carried-acceptablep
                            fn-cnode-record-acceptablep fn-cnode-line-ceiling)))))

(defthm fn-oclc-sn-statep-of-with-configuration
  (implies (fn-sn-statep st)
           (equal (fn-sn-statep (fn-sn-with-configuration st groups capacity node configs))
                  (and (fn-oclc-install-okp groups capacity)
                       (fn-node-statep node))))
  :hints (("Goal" :in-theory (e/d (fn-sn-statep fn-sn-shapep fn-sn-with-configuration
                                   fn-sn-groups fn-sn-capacity fn-sn-files fn-sn-node
                                   fn-sn-keyring fn-sn-keyring-generation fn-sn-verdicts
                                   fn-sn-keyring-snapshots fn-sn-identity-next)
                                  (fn-node-statep fn-sf-statep fn-prin-keyringp
                                   fn-sn-verdict-listp fn-sn-keyring-snapshot-listp)))))

(defthm fn-oclc-advance-keeps-groups
  (equal (fn-state-groups (fn-node-acceptance (fn-replay-advance-txid node txid)))
         (fn-state-groups (fn-node-acceptance node)))
  :hints (("Goal" :in-theory (enable fn-replay-advance-txid))))

(defthm fn-oclc-cnode-statep-of-advanced
  (implies (fn-cnode-statep cn)
           (fn-cnode-statep (fn-cnode-make (fn-replay-advance-txid (fn-cnode-node cn) txid)
                                           (fn-cnode-config cn))))
  :hints (("Goal" :in-theory (e/d (fn-cnode-statep fn-cnode-domain)
                                  (fn-node-statep fn-cfgp fn-replay-advance-txid
                                   fn-cnode-domain-of)))))

(defthm fn-oclc-cpr-loop-one-config
  (implies (fn-cnode-statep cn)
           (equal (fn-cpr-loop cn (list record) nil cs es)
                  (let* ((node (fn-cnode-node cn))
                         (txid (fn-cfg-record-txid record))
                         (position (+ (nfix cs) (nfix es))))
                    (cond ((not (fn-cfg-recordp record))
                           (fn-replay-fault cn position :invalid-config-record))
                          ((not (equal (fn-cfg-record-sequence record) cs))
                           (fn-replay-fault cn position :config-sequence))
                          ((not (fn-replay-advance-okp node txid))
                           (fn-replay-fault cn position :config-txid))
                          (t (let ((at (fn-cnode-make (fn-replay-advance-txid node txid)
                                                      (fn-cnode-config cn))))
                               (if (not (fn-cnode-record-acceptablep
                                         at record (fn-cnode-line-ceiling)))
                                   (fn-replay-fault cn position :config-refusal)
                                 (fn-replay-ok (fn-cnode-apply-config
                                                at record (fn-cnode-line-ceiling))
                                               (+ (nfix (+ 1 (nfix cs))) (nfix es))))))))))
  :hints (("Goal" :expand ((fn-cpr-loop cn (list record) nil cs es)
                           (:free (x a b) (fn-cpr-loop x nil nil a b)))
           :in-theory (e/d (fn-cpr-config-firstp)
                           (fn-cnode-statep fn-cnode-apply-config fn-cnode-record-acceptablep
                            fn-cfg-recordp fn-replay-advance-okp fn-replay-advance-txid
                            fn-cnode-line-ceiling)))))

(defthm fn-oclc-advance-okp-is-replay-advance-okp
  (implies (fn-node-statep node)
           (equal (fn-oclc-advance-okp node txid)
                  (fn-replay-advance-okp node txid)))
  :hints (("Goal" :in-theory (enable fn-replay-advance-okp fn-node-statep fn-statep))))

(defthm fn-oclc-replay-advance-okp-of-advance
  (implies (fn-replay-advance-okp node txid)
           (fn-replay-advance-okp (fn-replay-advance-txid node txid) txid))
  :hints (("Goal" :in-theory (disable fn-replay-advance-okp fn-replay-advance-txid)
           :use (fn-replay-advance-preserves-node-statep
                 (:instance fn-replay-advance-preserves-node-statep (recorded-txid txid))
                 fn-oclc-advance-okp-of-advance
                 (:instance fn-oclc-advance-okp-is-replay-advance-okp
                            (node (fn-replay-advance-txid node txid))))
           :expand ((fn-replay-advance-okp node txid)))))

; -----------------------------------------------------------------------------
; What the store's history relation carries: the replayed node, advanced to
; the frontier, is the store's node, and the store's node is a node state.
(defun fn-oclc-replayed (st)
  ; Proof vocabulary: the configured node the full fold computes.
  (declare (xargs :guard t :verify-guards nil))
  (fn-replay-result-node (fn-cpr-replay (fn-sn-config-history st)
                                        (fn-sf-records (fn-sn-files st)))))

(defthm fn-oclc-relation-facts
  (implies (fn-cpo-history-relation st)
           (let ((frontier (fn-sf-frontier (fn-sn-files st)))
                 (cn (fn-oclc-replayed st)))
             (and (fn-sn-statep st)
                  (fn-cnode-statep cn)
                  (equal (fn-replay-result-kind
                          (fn-cpr-replay (fn-sn-config-history st)
                                         (fn-sf-records (fn-sn-files st))))
                         :ok)
                  (fn-sn-observed-historyp frontier (fn-sf-records (fn-sn-files st)))
                  (fn-replay-advance-okp (fn-cnode-node cn) frontier)
                  (equal (fn-replay-advance-txid (fn-cnode-node cn) frontier)
                         (fn-sn-node st))
                  (fn-replay-advance-okp (fn-sn-node st) frontier)
                  (equal (fn-replay-advance-txid (fn-sn-node st) frontier)
                         (fn-sn-node st))
                  (fn-node-statep (fn-sn-node st))
                  (fn-cnode-statep (fn-cnode-make (fn-sn-node st) (fn-cnode-config cn))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-cpr-replay-ok-is-configured
                            (configs (fn-sn-config-history st))
                            (events (fn-sf-records (fn-sn-files st))))
                 (:instance fn-oclc-replay-advance-okp-of-advance
                            (node (fn-cnode-node (fn-oclc-replayed st)))
                            (txid (fn-sf-frontier (fn-sn-files st))))
                 (:instance fn-oclc-advance-of-advance
                            (node (fn-cnode-node (fn-oclc-replayed st)))
                            (txid (fn-sf-frontier (fn-sn-files st))))
                 (:instance fn-oclc-cnode-statep-of-advanced
                            (cn (fn-oclc-replayed st))
                            (txid (fn-sf-frontier (fn-sn-files st)))))
           :in-theory (e/d (fn-cpo-history-relation fn-oclc-replayed)
                           (fn-cpr-replay fn-cnode-statep fn-sn-statep
                            fn-replay-advance-okp fn-replay-advance-txid
                            fn-cpr-replay-ok-is-configured
                            fn-oclc-replay-advance-okp-of-advance
                            fn-oclc-advance-of-advance
                            fn-oclc-cnode-statep-of-advanced
                            fn-sn-observed-historyp))
           :expand ((fn-sn-statep st)))))

(defthm fn-oclc-cnode-statep-forward-node
  (implies (fn-cnode-statep cn) (fn-node-statep (fn-cnode-node cn)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-cnode-statep))))

(defthm fn-oclc-replayed-node-advances-to-the-store-node
  (implies (and (fn-cpo-history-relation st)
                (equal txid (fn-sf-frontier (fn-sn-files st))))
           (and (equal (fn-replay-advance-txid
                        (fn-cnode-node
                         (fn-replay-result-node
                          (fn-cpr-replay (fn-sn-config-history st)
                                         (fn-sf-records (fn-sn-files st)))))
                        txid)
                       (fn-sn-node st))
                (fn-replay-advance-okp
                 (fn-cnode-node
                  (fn-replay-result-node
                   (fn-cpr-replay (fn-sn-config-history st)
                                  (fn-sf-records (fn-sn-files st)))))
                 txid)))
  :hints (("Goal" :use fn-oclc-relation-facts
           :in-theory (e/d (fn-oclc-replayed)
                           (fn-cpo-history-relation fn-cpr-replay
                            fn-replay-advance-txid fn-replay-advance-okp)))))

; -----------------------------------------------------------------------------
; The configuration install from the carried state is fn-cpo-configure-durable
; (the fold over CONFIGS ++ (RECORD) is one step from the fold over CONFIGS,
; books/config-carried-candidate.lisp fn-cfgc-cpr-replay-of-one-more, and that
; fold's node advanced to the frontier is the store's node), and on success
; the configuration it answers is fn-ocl-store-config of the new store.
(defthm fn-oclc-configure-is-configure-durable
  (implies (and (fn-cpo-history-relation st)
                (equal config (fn-cnode-config (fn-oclc-replayed st))))
           (equal (mv-nth 0 (fn-oclc-configure st config record))
                  (fn-cpo-configure-durable st record)))
  :hints (("Goal"
           :use (fn-oclc-relation-facts
                 (:instance fn-cfgc-observed-is-below
                            (frontier (fn-sf-frontier (fn-sn-files st)))
                            (events (fn-sf-records (fn-sn-files st)))
                            (bound (fn-cfg-record-txid record)))
                 (:instance fn-cnode-apply-config-preserves-state
                            (cn (fn-cnode-make (fn-sn-node st)
                                               (fn-cnode-config (fn-oclc-replayed st))))
                            (ceiling (fn-cnode-line-ceiling)))
                 (:instance fn-cnode-record-acceptablep-is-the-carried-check
                            (cn (fn-cnode-make (fn-sn-node st)
                                               (fn-cnode-config (fn-oclc-replayed st))))
                            (ceiling (fn-cnode-line-ceiling))))
           :in-theory (e/d (fn-cpo-configure-durable fn-cfgc-cpr-extend fn-cpo-install
                            fn-oclc-replayed)
                           (fn-cpo-history-relation
                            fn-cpr-replay fn-cpr-loop fn-cnode-statep fn-sn-statep
                            fn-cnode-apply-config fn-cnode-record-acceptablep
                            fn-cnode-carried-acceptablep fn-cfg-recordp
                            fn-replay-advance-okp fn-replay-advance-txid
                            fn-oclc-advance fn-oclc-advance-okp fn-oclc-apply
                            fn-sn-observed-historyp fn-cfgc-observed-is-below
                            fn-cnode-line-ceiling fn-cnode-apply-config-preserves-state
                            fn-oclc-install-okp fn-node-statep)))))

(defthm fn-oclc-configure-config-is-store-config
  (implies (and (fn-cpo-history-relation st)
                (equal config (fn-cnode-config (fn-oclc-replayed st)))
                (not (equal (fn-sn-config-history
                             (mv-nth 0 (fn-oclc-configure st config record)))
                            (fn-sn-config-history st))))
           (equal (mv-nth 1 (fn-oclc-configure st config record))
                  (fn-ocl-store-config (mv-nth 0 (fn-oclc-configure st config record)))))
  :hints (("Goal"
           :use (fn-oclc-relation-facts
                 (:instance fn-cfgc-observed-is-below
                            (frontier (fn-sf-frontier (fn-sn-files st)))
                            (events (fn-sf-records (fn-sn-files st)))
                            (bound (fn-cfg-record-txid record)))
                 (:instance fn-cnode-apply-config-preserves-state
                            (cn (fn-cnode-make (fn-sn-node st)
                                               (fn-cnode-config (fn-oclc-replayed st))))
                            (ceiling (fn-cnode-line-ceiling)))
                 (:instance fn-cnode-record-acceptablep-is-the-carried-check
                            (cn (fn-cnode-make (fn-sn-node st)
                                               (fn-cnode-config (fn-oclc-replayed st))))
                            (ceiling (fn-cnode-line-ceiling))))
           :in-theory (e/d (fn-ocl-store-config fn-cfgc-cpr-extend fn-cpo-install
                            fn-oclc-replayed)
                           (fn-cpo-history-relation
                            fn-cpr-replay fn-cpr-loop fn-cnode-statep fn-sn-statep
                            fn-cnode-apply-config fn-cnode-record-acceptablep
                            fn-cnode-carried-acceptablep fn-cfg-recordp
                            fn-replay-advance-okp fn-replay-advance-txid
                            fn-oclc-advance fn-oclc-advance-okp fn-oclc-apply
                            fn-sn-observed-historyp fn-cfgc-observed-is-below
                            fn-cnode-line-ceiling fn-cnode-apply-config-preserves-state
                            fn-oclc-install-okp fn-node-statep)))))

; -----------------------------------------------------------------------------
; The owner invariant's Store conjunct at the ready phase is the history
; relation fn-cpo-configure-durable tests.
(defthm fn-oclc-ready-cst-relation-is-history-relation
  (implies (and (fn-cst-relation st)
                (equal (fn-sf-phase (fn-sn-files st)) :ready))
           (fn-cpo-history-relation st))
  :hints (("Goal" :in-theory
           '(fn-cst-relation fn-cpo-history-relation
             fn-cst-final-configurationp fn-cst-recoverablep
             fn-cst-replay-node fn-snt-idle-phasep member-equal
             (:executable-counterpart equal) (:executable-counterpart member-equal)))))

(defthm fn-oclc-configure-unready
  (implies (not (equal (fn-sf-phase (fn-sn-files st)) :ready))
           (and (equal (mv-nth 0 (fn-oclc-configure st config record)) st)
                (equal (fn-cpo-configure-durable st record) st)))
  :hints (("Goal" :in-theory (enable fn-cpo-configure-durable))))

(defthm fn-oclc-complete-is-complete
  (implies (and (fn-ocfg-staged oc)
                (fn-cst-relation (fn-own-store (fn-ocfg-owner oc)))
                (fn-ocl-config-historyp oc))
           (equal (fn-oclc-complete oc) (fn-ocl-complete oc)))
  :hints (("Goal"
           :cases ((equal (fn-sf-phase (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))) :ready))
           :use ((:instance fn-oclc-configure-is-configure-durable
                            (st (fn-own-store (fn-ocfg-owner oc)))
                            (config (fn-ocfg-config oc))
                            (record (fn-ocfg-staged oc)))
                 (:instance fn-oclc-configure-config-is-store-config
                            (st (fn-own-store (fn-ocfg-owner oc)))
                            (config (fn-ocfg-config oc))
                            (record (fn-ocfg-staged oc))))
           :in-theory (e/d (fn-oclc-complete fn-ocl-complete fn-ocl-config-historyp
                            fn-oclc-replayed)
                           (fn-oclc-configure fn-cpo-configure-durable
                            fn-oclc-configure-is-configure-durable
                            fn-oclc-configure-config-is-store-config
                            fn-cpo-history-relation fn-cst-relation
                            fn-cpr-replay fn-ocl-store-config fn-ocl-owner-with-store)))))

; KEYSTONE (PRF-265).  Under the owner's carried invariant fn-ocl-relation the
; host-called completion fn-oclc-publish is fn-ocl-publish: the same verdict
; and the same owner, so every theorem about fn-ocl-publish
; (books/config-owner-publish.lisp) holds of what the host installs.  No
; hypothesis on the record, the generation or the phase: a record that does
; not apply, a wrong generation and an unready store answer as fn-ocl-publish
; does.
(defthm fn-oclc-publish-is-publish
  (implies (fn-ocl-relation oc)
           (equal (fn-oclc-publish oc generation max-octets)
                  (fn-ocl-publish oc generation max-octets)))
  :hints (("Goal"
           :use (fn-oclc-complete-is-complete)
           :in-theory (e/d (fn-oclc-publish fn-ocl-publish fn-ocl-relation)
                           (fn-oclc-complete fn-ocl-complete fn-oclc-complete-is-complete
                            fn-cst-relation fn-ocl-config-historyp
                            fn-ocl-view-configp fn-ocl-view-historyp fn-ocl-conns-historyp)))))

; -----------------------------------------------------------------------------
; The invariant is carried: a :durable publication leaves an owner that
; satisfies it again, so the next completion's hypothesis holds.
(defthm fn-oclc-ocl-relation-of-configure
  (implies (fn-ocl-relation oc)
           (fn-ocl-relation (fn-ocfg-with-owner
                             oc (fn-own-configure (fn-ocfg-owner oc) post))))
  :hints (("Goal" :in-theory (e/d (fn-ocl-relation fn-ocfg-with-owner fn-own-configure
                                   fn-ocl-config-historyp fn-ocl-view-configp
                                   fn-ocl-view-historyp fn-ocl-conns-historyp)
                                  (fn-cst-relation fn-cpr-replay fn-cst-replay-node
                                   fn-own-take)))))

(defthm fn-oclc-complete-unready-keeps-stage
  (implies (and (fn-ocfg-staged oc)
                (not (equal (fn-sf-phase (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))
                            :ready)))
           (equal (fn-ocl-complete oc) oc))
  :hints (("Goal" :use ((:instance fn-oclc-configure-unready
                                   (st (fn-own-store (fn-ocfg-owner oc)))
                                   (record (fn-ocfg-staged oc))))
           :in-theory (e/d (fn-ocl-complete)
                           (fn-oclc-configure-unready fn-cpo-configure-durable)))))

(defthm fn-oclc-ocl-relation-forward-cst
  (implies (fn-ocl-relation oc)
           (fn-cst-relation (fn-own-store (fn-ocfg-owner oc))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (e/d (fn-ocl-relation) (fn-cst-relation)))))

(local
 (defthm fn-oclc-publish-preserves-ocl-relation
   (implies (and (fn-ocl-relation oc)
                 (equal (mv-nth 0 (fn-oclc-publish oc generation max-octets)) :durable))
            (fn-ocl-relation (mv-nth 1 (fn-oclc-publish oc generation max-octets))))
   :hints (("Goal"
            :cases ((equal (fn-sf-phase (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))
                           :ready))
            :use (fn-ocl-complete-preserves-full-historical-relation
                  fn-oclc-complete-unready-keeps-stage
                  (:instance fn-oclc-ready-cst-relation-is-history-relation
                             (st (fn-own-store (fn-ocfg-owner oc))))
                  (:instance fn-oclc-ocl-relation-of-configure
                             (oc (fn-ocl-complete oc))
                             (post (fn-oag-post-config
                                    (fn-ocfg-config (fn-ocl-complete oc)) max-octets))))
            :in-theory (e/d (fn-ocl-publish)
                            (fn-ocl-complete fn-ocl-relation fn-cst-relation
                             fn-cpo-history-relation fn-ocfg-with-owner fn-own-configure
                             fn-oag-post-config fn-oclc-publish
                             fn-oclc-ocl-relation-of-configure
                             fn-oclc-ready-cst-relation-is-history-relation
                             fn-oclc-complete-unready-keeps-stage)))
           ("Subgoal 2" :in-theory (e/d (fn-ocl-publish fn-ocl-relation)
                            (fn-ocl-complete fn-cst-relation
                             fn-cpo-history-relation fn-ocfg-with-owner fn-own-configure
                             fn-oag-post-config fn-oclc-publish
                             fn-oclc-ocl-relation-of-configure
                             fn-oclc-ready-cst-relation-is-history-relation
                             fn-oclc-complete-unready-keeps-stage))))))

; KEYSTONE (PRF-265, the invariant carried).  Whatever the verdict, the owner
; the host installs satisfies fn-ocl-relation again: :durable by
; fn-ocl-complete-preserves-full-historical-relation
; (books/config-owner-live.lisp) through the keystone above, :refused and
; :recovery-required because the owner is the one given.
(defthm fn-oclc-publish-carries-ocl-relation
  (implies (fn-ocl-relation oc)
           (fn-ocl-relation (mv-nth 1 (fn-oclc-publish oc generation max-octets))))
  :hints (("Goal"
           :cases ((equal (mv-nth 0 (fn-oclc-publish oc generation max-octets)) :durable))
           :use (fn-oclc-publish-preserves-ocl-relation)
           :in-theory (e/d (fn-oclc-publish)
                           (fn-ocl-relation fn-oclc-complete fn-ocfg-with-owner
                            fn-own-configure fn-oag-post-config
                            fn-oclc-publish-preserves-ocl-relation fn-oclc-publish-is-publish)))))
