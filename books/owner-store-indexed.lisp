;; fn: the Store's derived event index, carried from the host's open across
;; every owner transition the host installs (PRF-144; lane
;; signed-history-index-2, 2026-09-26).
;
; The maintained relation is fn-ceis-indexedp
; (books/consumer-event-index-store-invariants.lisp): the Store's derived
; event index is the index of its committed history, in every phase.  The
; BP receiver's Message-ID lookups read that index
; (books/bp-native-app-fast.lisp, fn-bpaj-indexed-records-are-the-walk) and
; so does the consumer poll (books/consumer-owner-index-invariants.lisp).
; It is never evaluated on a served path.  This book:
;
;   ESTABLISHES it at the host's open.  host/owner-host.lisp
;   fn-owner-recover-extended installs fn-ock-recover-extended of the
;   extended checkpoint (books/owner-checkpoint-open.lisp), on both paths
;   (fn-owner-recover, fn-owner-recover-from-checkpoint,
;   fn-owner-recover-from-store-open); that owner is fn-ock-install over
;   fn-cpo-open-observed (fn-owner-recover-from-checkpoint-equals-full-recover),
;   whose opened Store carries fn-cei-build of the history it read
;   (fn-osi-cpo-open-observed-is-indexed).  The store-only model reopen
;   fn-sn-open-observed (fn-own-reopen) and fn-sn-initial establish it too.
;
;   PRESERVES it across every owner the host installs: fn-osi-host-step
;   names each of them with the ACL2 function host/owner-host.lisp calls
;   (fn-owner-step's fn-ocfg-step, fn-owner-io's fn-rcon-ocfg-io, the carried
;   prepares, completion, finish and outcome, the publication, the profile
;   and posting configuration, the feed table, the connection events, the
;   carried read, the exposure open and the clock).  Only the kernel's
;   (:store (:crash ...)) event breaks it (the crash image's index is empty
;   while its history is not), and the host never issues it: a crash is the
;   death of the process, whose next owner is the open above.  The model's
;   own restart (:reopen) re-establishes it (fn-osi-own-reopen-is-indexed).
;
; KEYSTONE fn-osi-live-owner-store-is-indexed: the Store of every owner the
; host reaches from its open by the installed transitions is indexed.  That
; is the Store host/native/bp-app.lisp fnn-bpapp-accept-locked binds
; (fnn-bpapp-bind-owner-store -> host/bp-native-app-host.lisp
; fn-owner-app-bind-receipt-store: (fn-own-store (fn-ocfg-owner oc)) of the
; installed owner) before every fn-bprj-request-action ->
; fn-bpaj-dispatch-fast, so PRF-132's keystones (restated below over that
; owner) carry no index premise.

(in-package "ACL2")
(include-book "owner-offer-indexed")
(include-book "owner-checkpoint-open")
(include-book "records-concrete-owner")
(include-book "owner-served-bound")
(include-book "public-exposure")
(include-book "store-node-resolution")
(include-book "consumer-event-index-store-invariants")
(include-book "bp-signed-binding")

; The owner field laws this book reads (withdrawn at owner-invariants'
; export with its vocabulary).
(local (in-theory (enable fn-own-refresh-keeps-fields
                          fn-own-connection-events-keep-store-bound-and-ledger)))

; -----------------------------------------------------------------------------
; The Store transitions the owner reaches that the invariants book does not
; include: the resolution events and the carried identity prepare.  Each
; keeps the history and the index.

(defthm fn-osi-refuse-reservation-keeps-indexed
  (implies (fn-ceis-indexedp s)
           (fn-ceis-indexedp (fn-sn-refuse-reservation s txid)))
  :hints (("Goal" :in-theory
           (e/d (fn-ceis-indexedp fn-sn-refuse-reservation
                 fn-sf-refuse-reservation)
                (fn-sn-refuse-reservation-enabledp fn-sn-update
                 fn-sn-make-v6 fn-cei-correspondencep fn-cei-build
                 fn-replay-advance-txid)))))

(defthm fn-osi-known-abort-keeps-indexed
  (implies (fn-ceis-indexedp s)
           (fn-ceis-indexedp (fn-sn-known-abort s)))
  :hints (("Goal" :in-theory
           (e/d (fn-ceis-indexedp fn-sn-known-abort fn-sn-known-abort-files
                 fn-sn-known-abort-file-start fn-sf-abort-completion
                 fn-sf-prepublish-abort fn-store-files-traces-vocabulary)
                (fn-sn-known-abort-enabledp fn-sn-update
                 fn-sn-make-v6 fn-cei-correspondencep fn-cei-build
                 fn-replay-advance-txid fn-node-complete)))))

(defthm fn-osi-ccar-prepare-identity-keeps-indexed
  (implies (fn-ceis-indexedp s)
           (fn-ceis-indexedp (fn-ccar-sn-prepare-identity s event)))
  :hints (("Goal" :in-theory
           (e/d (fn-ceis-indexedp fn-ccar-sn-prepare-identity
                 fn-spc-stage-record)
                (fn-sn-update fn-sn-make-v6 fn-cei-correspondencep
                 fn-cei-build fn-sn-statep fn-store-event-p
                 fn-stxe-p fn-stxk-p fn-stxa-p
                 fn-replay-apply-record fn-replay-identity-step)))))

; The store-only kernel crash is the one Store transition that breaks the
; relation; the host never issues it (see the head of this book).
(defun fn-osi-host-store-eventp (event)
  (declare (xargs :guard t))
  (not (and (consp event) (equal (car event) :crash))))

(defthm fn-osi-snrt-step-keeps-indexed
  (implies (and (fn-ceis-indexedp s)
                (fn-osi-host-store-eventp event))
           (fn-ceis-indexedp (fn-snrt-step s event)))
  :hints (("Goal" :in-theory
           (e/d (fn-snrt-step fn-snt-step fn-osi-host-store-eventp)
                (fn-ceis-indexedp fn-sn-prepare fn-sn-io fn-sn-finish
                 fn-sn-crash fn-sn-recover fn-sn-prepare-retention
                 fn-sn-prepare-identity fn-sn-prepare-consumer
                 fn-sn-prepare-topic fn-sn-refuse-reservation
                 fn-sn-known-abort)))))

; -----------------------------------------------------------------------------
; Establishment

(defthm fn-osi-cpo-open-observed-is-indexed
  (implies (equal (fn-sn-open-kind (fn-cpo-open-observed configs frontier events))
                  :ok)
           (fn-ceis-indexedp
            (fn-sn-open-state (fn-cpo-open-observed configs frontier events))))
  :hints (("Goal" :in-theory
           (e/d (fn-cpo-open-observed fn-ceis-indexedp fn-sn-open-ok
                 fn-sn-open-error fn-sn-open-kind fn-sn-open-state
                 fn-cpo-install)
                (fn-cpr-replay fn-sn-statep fn-cnode-statep
                 fn-sn-update-replayed fn-sn-observed-seed
                 fn-replay-identity fn-cpe-projection-replay
                 fn-th-prefix-project fn-replay-advance-txid
                 fn-replay-advance-okp fn-sn-observed-historyp
                 fn-stx-index-of-store fn-cei-build
                 fn-cei-correspondencep)))))

(defthm fn-osi-observed-seed-is-replaying
  (equal (fn-sf-phase (fn-sn-files (fn-sn-observed-seed groups capacity
                                                        frontier records)))
         :replaying)
  :hints (("Goal" :in-theory (e/d (fn-sn-observed-seed)
                                  (fn-node-initial-state)))))

(defthm fn-osi-sn-open-observed-is-indexed
  (implies (fn-sn-open-okp (fn-sn-open-observed groups capacity frontier records))
           (fn-ceis-indexedp
            (fn-sn-open-state
             (fn-sn-open-observed groups capacity frontier records))))
  :hints (("Goal" :in-theory
           (e/d (fn-sn-open-observed fn-sn-open-okp fn-sn-open-ok
                 fn-sn-open-error fn-sn-open-state fn-ceis-indexedp)
                (fn-sn-statep fn-sn-observed-seed fn-sn-recover
                 fn-sn-observed-configurationp fn-cei-correspondencep))
           :use ((:instance fn-ceis-recovery-rebuilds-index-by-definition
                            (s (fn-sn-observed-seed groups capacity
                                                    frontier records)))))))

(defthm fn-osi-own-start-store
  (equal (fn-own-store (fn-own-start store max-conns)) store)
  :hints (("Goal" :in-theory (e/d (fn-own-start fn-own-refresh-keeps-fields
                                   fn-own-store-of-fn-own-make)
                                  (fn-own-refresh fn-own-store fn-own-make
                                   fn-own-view-make-visible fn-midx-build
                                   fn-gidx-build fn-own-prefix-archive
                                   fn-ctl-visible-state)))))

; The owner the host installs at open, on either path, or :fault.
(defthm fn-osi-ock-install-is-indexed
  (implies (and (not (equal (fn-ock-install replayed opened max-conns) :fault))
                (fn-ceis-indexedp (fn-sn-open-state opened)))
           (fn-ceis-indexedp
            (fn-own-store (fn-ocfg-owner
                           (fn-ock-install replayed opened max-conns)))))
  :hints (("Goal" :in-theory (e/d (fn-ock-install)
                                  (fn-ceis-indexedp fn-own-start
                                   fn-own-configure fn-oag-post-config)))))

(defthm fn-osi-ock-install-requires-an-ok-open
  (implies (not (equal (fn-ock-install replayed opened max-conns) :fault))
           (equal (fn-sn-open-kind opened) :ok))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-ock-install)
                                  (fn-own-start fn-own-configure
                                   fn-oag-post-config)))))

; The open the host runs (host/owner-host.lisp fn-owner-recover-extended,
; on both paths: the extended checkpoint of a prefix of the history, over
; the records after it), and the owner the host holds after the installed
; transitions EVS.  Abbreviations for the statements below.
(defun fn-osi-open (configs prefix suffix frontier max-conns)
  (declare (xargs :guard t :verify-guards nil))
  (fn-ock-recover-extended
   (fn-sco-extend (fn-sco-capture configs prefix) configs suffix)
   configs frontier max-conns))

; A refused open is :fault, whose owner has the empty Store, whose empty
; index is the index of its empty history.
(defthm fn-osi-refused-open-is-indexed
  (fn-ceis-indexedp (fn-own-store (fn-ocfg-owner :fault)))
  :hints (("Goal" :in-theory (enable fn-ceis-indexedp))))

; KEYSTONE (establishment): the owner host/owner-host.lisp
; fn-owner-recover-extended installs, on either path, has an indexed Store.
; No hypothesis.
(defthm fn-osi-open-installs-indexed-store
  (fn-ceis-indexedp
   (fn-own-store (fn-ocfg-owner (fn-osi-open configs prefix suffix
                                            frontier max-conns))))
  :hints (("Goal"
           :cases ((equal (fn-osi-open configs prefix suffix frontier max-conns)
                          :fault))
           :use (fn-owner-recover-from-checkpoint-equals-full-recover
                 fn-osi-refused-open-is-indexed
                 (:instance fn-osi-ock-install-is-indexed
                            (replayed (fn-cpr-replay configs (append prefix suffix)))
                            (opened (fn-cpo-open-observed
                                     configs frontier (append prefix suffix))))
                 (:instance fn-osi-cpo-open-observed-is-indexed
                            (events (append prefix suffix)))
                 (:instance fn-osi-ock-install-requires-an-ok-open
                            (replayed (fn-cpr-replay configs (append prefix suffix)))
                            (opened (fn-cpo-open-observed
                                     configs frontier (append prefix suffix)))))
           :in-theory (e/d (fn-ock-recover-full fn-osi-open)
                           (fn-ock-recover-extended fn-ock-install
                            fn-cpo-open-observed fn-ceis-indexedp
                            fn-sco-extend fn-sco-capture
                            fn-osi-refused-open-is-indexed
                            fn-osi-ock-install-is-indexed
                            fn-osi-cpo-open-observed-is-indexed)))))

; -----------------------------------------------------------------------------
; The carried article prepare's Store step keeps the history and the index.

(defthm fn-osi-spc-prepare-keeps-indexed
  (implies (fn-ceis-indexedp s)
           (fn-ceis-indexedp (fn-spc-prepare s record)))
  :hints (("Goal" :in-theory
           (e/d (fn-ceis-indexedp fn-spc-prepare fn-spc-stage-record)
                (fn-sn-update fn-sn-make-v6 fn-cei-correspondencep
                 fn-cei-build fn-sn-statep fn-record-p
                 fn-sn-prepare-node fn-sn-record-bindsp
                 fn-cpe-projection-step)))))

; -----------------------------------------------------------------------------
; The raw owner.  Only the :store, :complete and :reopen events of
; fn-own-step move the Store (as books/owner-invariants.lisp's local
; fn-own-step-store-of-other-events says); every other event keeps it.

; Owner transitions the configured owner reaches outside fn-own-step.
(defthm fn-osi-own-keeps-store-outside-step
  (and (equal (fn-own-store (cdr (fn-own-advance-result o id))) (fn-own-store o))
       (equal (fn-own-store (fn-own-reader-context o id cfg)) (fn-own-store o))
       (equal (fn-own-store (cdr (fn-own-open-peer o peer cfg acfg)))
              (fn-own-store o))
       (equal (fn-own-store (cdr (fn-own-fault o id))) (fn-own-store o))
       (equal (fn-own-store (fn-own-with-feeds o feeds)) (fn-own-store o))
       (equal (fn-own-store (fn-own-configure o config)) (fn-own-store o))
       (equal (fn-own-store (cdr (fn-own-transit-outcome o id kind reason word)))
              (fn-own-store o))
       (equal (fn-own-store (cdr (fn-acar-own-outcome o id word)))
              (fn-own-store o)))
  :hints (("Goal" :in-theory (e/d (fn-own-advance-result fn-own-reader-context
                                   fn-own-open-peer fn-own-fault
                                   fn-own-with-feeds fn-own-configure
                                   fn-own-transit-outcome fn-acar-own-outcome
                                   fn-acar-own-advance-result
                                   fn-own-invariants-vocabulary
                                   fn-own-set-conns fn-own-enqueue)
                                  (fn-served-step fn-served-dispatch
                                   fn-served-post-outcome fn-served-open
                                   fn-own-conn-boundedp fn-own-outcome-completion
                                   fn-own-find-conn-id fn-own-refresh)))))

(defthm fn-osi-own-step-store-of-other-events
  (implies (not (member-equal (car event) '(:store :complete :reopen)))
           (equal (fn-own-store (fn-own-step o event)) (fn-own-store o)))
  :hints (("Goal" :in-theory (e/d (fn-own-step fn-own-invariants-vocabulary
                                   fn-own-feed-reply fn-own-tick fn-own-tick-peer
                                   fn-own-feed-connect fn-own-feed-lost
                                   fn-own-feed-recover fn-own-feeds-reconfigure
                                   fn-own-with-feeds fn-own-control-submit
                                   fn-own-operator-submit fn-own-bp-transit-submit
                                   fn-own-control-outcome fn-own-bp-transit-outcome
                                   fn-own-enqueue fn-own-set-conns
                                   fn-own-transit-outcome)
                                  (fn-served-step fn-served-dispatch
                                   fn-served-post-outcome fn-served-open
                                   fn-own-conn-boundedp fn-own-outcome-completion
                                   fn-own-find-conn-id)))))

(defthm fn-osi-own-store-step-keeps-indexed
  (implies (and (fn-ceis-indexedp (fn-own-store o))
                (fn-osi-host-store-eventp event))
           (fn-ceis-indexedp (fn-own-store (fn-own-store-step o event))))
  :hints (("Goal" :in-theory (e/d (fn-own-store-step)
                                  (fn-ceis-indexedp fn-snrt-step
                                   fn-osi-host-store-eventp)))))

(defthm fn-osi-own-complete-keeps-indexed
  (implies (fn-ceis-indexedp (fn-own-store o))
           (fn-ceis-indexedp (fn-own-store (fn-own-complete o))))
  :hints (("Goal" :in-theory (e/d (fn-own-complete)
                                  (fn-ceis-indexedp fn-sn-finish
                                   fn-sn-completion-enabledp)))))

; The model's restart re-establishes the relation whatever the old Store.
(defthm fn-osi-own-reopen-is-indexed
  (implies (fn-ceis-indexedp (fn-own-store o))
           (fn-ceis-indexedp (fn-own-store (fn-own-reopen o frontier records))))
  :hints (("Goal" :in-theory (e/d (fn-own-reopen)
                                  (fn-ceis-indexedp fn-sn-open-observed
                                   fn-sf-crash-imagep fn-sn-open-okp
                                   fn-sn-open-state)))))

; The owner events the host issues: every one but the kernel crash.
(defun fn-osi-host-own-eventp (event)
  (declare (xargs :guard t))
  (not (and (consp event) (equal (car event) :store)
            (consp (cdr event))
            (not (fn-osi-host-store-eventp (cadr event))))))

(defthm fn-osi-own-step-of-store-changing-events
  (and (implies (equal (car event) :store)
                (equal (fn-own-step o event) (fn-own-store-step o (cadr event))))
       (implies (equal (car event) :complete)
                (equal (fn-own-step o event) (fn-own-complete o)))
       (implies (equal (car event) :reopen)
                (equal (fn-own-step o event)
                       (fn-own-reopen o (cadr event) (caddr event)))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-own-step))))

(defthm fn-osi-own-step-keeps-indexed
  (implies (and (fn-ceis-indexedp (fn-own-store o))
                (fn-osi-host-own-eventp event))
           (fn-ceis-indexedp (fn-own-store (fn-own-step o event))))
  :hints (("Goal"
           :cases ((equal (car event) :store) (equal (car event) :complete)
                   (equal (car event) :reopen))
           :use (fn-osi-own-step-of-store-changing-events
                 fn-osi-own-step-store-of-other-events
                 (:instance fn-osi-own-store-step-keeps-indexed
                            (event (cadr event)))
                 fn-osi-own-complete-keeps-indexed
                 (:instance fn-osi-own-reopen-is-indexed
                            (frontier (cadr event)) (records (caddr event))))
           :in-theory (union-theories '(fn-osi-host-own-eventp member-equal
                                        (:executable-counterpart member-equal)
                                        (:executable-counterpart fn-osi-host-store-eventp))
                                      (theory 'ground-zero)))))

(defthm fn-osi-own-finish-keeps-indexed
  (implies (fn-ceis-indexedp (fn-own-store o))
           (fn-ceis-indexedp (fn-own-store (cdr (fn-ccar-own-finish o cfg)))))
  :hints (("Goal" :in-theory (e/d (fn-ccar-own-finish-is-own-finish fn-own-finish)
                                  (fn-ceis-indexedp fn-own-complete
                                   fn-own-completion-names-submission-p)))))

; -----------------------------------------------------------------------------
; The configured owner.

(defthm fn-osi-ocfg-step-keeps-indexed
  (implies (and (fn-ceis-indexedp (fn-own-store (fn-ocfg-owner oc)))
                (fn-osi-host-own-eventp event))
           (fn-ceis-indexedp (fn-own-store (fn-ocfg-owner (fn-ocfg-step oc event)))))
  :hints (("Goal" :in-theory (e/d (fn-ocfg-step fn-ocfg-open fn-ocfg-advance
                                   fn-ocfg-close fn-ocfg-read fn-ocfg-read-step
                                   fn-ocfg-open-peer fn-ocfg-fault
                                   fn-ocfg-reconfigure fn-ocfg-complete
                                   fn-ocfg-pass fn-ocfg-with-owner
                                   fn-ocfg-with-read-owner)
                                  (fn-ceis-indexedp fn-own-step fn-own-complete
                                   fn-osi-host-own-eventp
                                   fn-own-open fn-own-reader-context
                                   fn-own-advance-result fn-own-close
                                   fn-own-read fn-own-read-step fn-own-open-peer
                                   fn-own-fault fn-ocfg-reconfig-okp))
           :use ((:instance fn-osi-own-step-keeps-indexed
                            (o (fn-ocfg-owner oc)))
                 (:instance fn-osi-own-complete-keeps-indexed
                            (o (fn-ocfg-owner oc)))))))

(defthm fn-osi-ocfg-with-owner-store
  (equal (fn-own-store (fn-ocfg-owner (fn-ocfg-with-owner oc owner)))
         (fn-own-store owner))
  :hints (("Goal" :in-theory (enable fn-ocfg-with-owner))))

(defthm fn-osi-rcon-io-keeps-indexed
  (implies (fn-ceis-indexedp (fn-own-store (fn-ocfg-owner oc)))
           (fn-ceis-indexedp
            (fn-own-store (fn-ocfg-owner (fn-rcon-ocfg-io oc operation result)))))
  :hints (("Goal" :use ((:instance fn-osi-ocfg-step-keeps-indexed
                                   (event (list :store (list :io operation result)))))
           :in-theory (e/d (fn-rcon-ocfg-io-is-ocfg-step fn-osi-host-own-eventp
                            fn-osi-host-store-eventp)
                           (fn-ceis-indexedp fn-ocfg-step fn-rcon-ocfg-io
                            fn-osi-ocfg-step-keeps-indexed)))))

(defthm fn-osi-pcar-prepare-keeps-indexed
  (implies (fn-ceis-indexedp (fn-own-store (fn-ocfg-owner oc)))
           (fn-ceis-indexedp
            (fn-own-store (fn-ocfg-owner (fn-pcar-sbud-prepare oc record budget)))))
  :hints (("Goal" :in-theory (e/d (fn-pcar-sbud-prepare-is-sbud-prepare
                                   fn-sbud-prepare fn-opc-prepare
                                   fn-opc-owner-prepare)
                                  (fn-ceis-indexedp fn-pcar-sbud-prepare
                                   fn-spc-prepare fn-own-refresh
                                   fn-sbud-admitp fn-sbud-used)))))

(defthm fn-osi-ccar-ocfg-prepare-identity-keeps-indexed
  (implies (fn-ceis-indexedp (fn-own-store (fn-ocfg-owner oc)))
           (fn-ceis-indexedp
            (fn-own-store (fn-ocfg-owner (fn-ccar-ocfg-prepare-identity oc event)))))
  :hints (("Goal" :in-theory (e/d (fn-ccar-ocfg-prepare-identity)
                                  (fn-ceis-indexedp fn-ccar-sn-prepare-identity
                                   fn-own-refresh)))))

(defthm fn-osi-ccar-ocfg-complete-keeps-indexed
  (implies (fn-ceis-indexedp (fn-own-store (fn-ocfg-owner oc)))
           (fn-ceis-indexedp
            (fn-own-store (fn-ocfg-owner (fn-ccar-ocfg-complete oc)))))
  :hints (("Goal" :use ((:instance fn-osi-ocfg-step-keeps-indexed
                                   (event '(:complete))))
           :in-theory (e/d (fn-ccar-ocfg-complete-is-ocfg-step-complete
                            fn-osi-host-own-eventp)
                           (fn-ceis-indexedp fn-ocfg-step
                            fn-osi-ocfg-step-keeps-indexed)))))

(defthm fn-osi-cpo-configure-durable-keeps-indexed
  (implies (fn-ceis-indexedp st)
           (fn-ceis-indexedp (fn-cpo-configure-durable st record)))
  :hints (("Goal" :in-theory (e/d (fn-cpo-configure-durable fn-cpo-install
                                   fn-ceis-indexedp)
                                  (fn-cpo-history-relation fn-cpr-replay
                                   fn-sn-statep fn-cnode-statep
                                   fn-replay-advance-txid fn-replay-advance-okp
                                   fn-cei-correspondencep)))))

(defthm fn-osi-ocl-publish-keeps-indexed
  (implies (fn-ceis-indexedp (fn-own-store (fn-ocfg-owner oc)))
           (fn-ceis-indexedp
            (fn-own-store (fn-ocfg-owner
                           (mv-nth 1 (fn-ocl-publish oc generation max-octets))))))
  :hints (("Goal" :in-theory (e/d (fn-ocl-publish fn-ocl-complete
                                   fn-ocl-owner-with-store)
                                  (fn-ceis-indexedp fn-own-complete
                                   fn-own-refresh fn-own-configure
                                   fn-cpo-configure-durable fn-oag-post-config
                                   fn-ocl-store-config)))))

(defthm fn-osi-ocfg-open-keeps-store
  (and (equal (fn-own-store (fn-ocfg-owner (cdr (fn-ocfg-open oc acfg))))
              (fn-own-store (fn-ocfg-owner oc)))
       (equal (fn-own-store (fn-ocfg-owner (cdr (fn-ocfg-open-peer oc peer acfg))))
              (fn-own-store (fn-ocfg-owner oc)))
       (equal (fn-own-store (fn-ocfg-owner (cdr (fn-ocfg-read-step oc id event))))
              (fn-own-store (fn-ocfg-owner oc)))
       (equal (fn-own-store (fn-ocfg-owner (cdr (fn-ocfg-fault oc id))))
              (fn-own-store (fn-ocfg-owner oc)))
       (equal (fn-own-store (fn-ocfg-owner (fn-ocfg-observe oc obs)))
              (fn-own-store (fn-ocfg-owner oc))))
  :hints (("Goal" :in-theory (e/d (fn-ocfg-open fn-ocfg-open-peer
                                   fn-ocfg-read-step fn-ocfg-fault
                                   fn-ocfg-observe fn-ocfg-with-owner
                                   fn-ocfg-with-read-owner)
                                  (fn-own-open fn-own-open-peer
                                   fn-own-reader-context fn-own-read-step
                                   fn-own-fault fn-own-observe)))))

(defthm fn-osi-exp-at-one
  (equal (fn-exp-at 1 (cons a (cons b c))) b)
  :hints (("Goal" :expand ((fn-exp-at 1 (cons a (cons b c)))
                           (fn-exp-at 0 (cons b c))))))

(defthm fn-osi-exp-open-keeps-store
  (equal (fn-own-store (fn-ocfg-owner
                        (fn-exp-open-ocfg
                         (fn-exp-open oc st limits auth peer address now))))
         (fn-own-store (fn-ocfg-owner oc)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-exp-open fn-exp-open-ocfg fn-osi-exp-at-one
                                fn-osi-ocfg-open-keeps-store)
                              (theory 'minimal-theory)))))

; -----------------------------------------------------------------------------
; The host's owner transitions, one arm per owner host/owner-host.lisp
; installs (fn-owner-install-ocfg or fn-owner-replace-core), with the ACL2
; function it installs:
;
;   :step            fn-owner-step, fn-owner-refuse-reservation, -begin, ...  fn-ocfg-step
;   :io              fn-owner-io                              fn-rcon-ocfg-io
;   :prepare         fn-owner-prepare, fn-owner-prepare-buffer fn-pcar-sbud-prepare
;   :prepare-identity fn-owner-prepare-identity               fn-ccar-ocfg-prepare-identity
;   :complete        fn-owner-finish                          fn-ccar-ocfg-complete
;   :finish          fn-owner-finish-submission               fn-ccar-own-finish
;   :publish         fn-owner-reconfigure-complete            fn-ocl-publish
;   :configure       fn-owner-posting-configure               fn-own-configure
;   :profile         fn-owner-install-profile                 fn-osb-install
;   :feeds           fn-owner-feed-install-port-result        fn-own-with-feeds
;   :transit-outcome fn-owner-transit-outcome                 fn-own-transit-outcome
;   :outcome         the served POST outcome                  fn-acar-own-outcome
;   :open-peer       fn-owner-open-peer                       fn-ocfg-open-peer
;   :read-step       fn-owner-tls-established                 fn-ocfg-read-step
;   :open            fn-owner-open                            fn-ocfg-open
;   :exposure-open   fn-owner-exposure-open                   fn-exp-open
;   :read            fn-owner-chunk                           fn-scar-ocfg-read-tls-prefix
;   :fault           fn-owner-fault                           fn-ocfg-fault
;   :observe         fn-owner-observe                         fn-ocfg-observe
;
; The :step arm admits every owner event but the kernel crash
; (fn-osi-host-own-eventp), a superset of the events the host sends.
(defun fn-osi-host-step (oc ev)
  (declare (xargs :guard t :verify-guards nil))
  (let ((a (cadr ev)) (b (caddr ev)) (c (cadddr ev)))
    (case (car ev)
      (:step (if (fn-osi-host-own-eventp a) (fn-ocfg-step oc a) oc))
      (:io (fn-rcon-ocfg-io oc a b))
      (:prepare (fn-pcar-sbud-prepare oc a b))
      (:prepare-identity (fn-ccar-ocfg-prepare-identity oc a))
      (:complete (fn-ccar-ocfg-complete oc))
      (:finish (if (fn-ocfg-staged oc) oc
                 (fn-ocfg-with-owner
                  oc (cdr (fn-ccar-own-finish (fn-ocfg-owner oc)
                                              (fn-ocfg-config oc))))))
      (:publish (mv-let (verdict next) (fn-ocl-publish oc a b)
                  (declare (ignore verdict))
                  next))
      (:configure (fn-ocfg-with-owner oc (fn-own-configure (fn-ocfg-owner oc) a)))
      (:profile (mv-let (verdict next) (fn-osb-install (fn-ocfg-owner oc) a)
                  (declare (ignore verdict))
                  (fn-ocfg-with-owner oc next)))
      (:feeds (fn-ocfg-with-owner oc (fn-own-with-feeds (fn-ocfg-owner oc) a)))
      (:transit-outcome
       (fn-ocfg-with-owner
        oc (cdr (fn-own-transit-outcome (fn-ocfg-owner oc) a b c
                                        (car (cddddr ev))))))
      (:outcome (fn-ocfg-with-owner
                 oc (cdr (fn-acar-own-outcome (fn-ocfg-owner oc) a b))))
      (:open-peer (cdr (fn-ocfg-open-peer oc a b)))
      (:read-step (cdr (fn-ocfg-read-step oc a b)))
      (:open (cdr (fn-ocfg-open oc a)))
      (:exposure-open
       (fn-exp-open-ocfg (fn-exp-open oc a b c (car (cddddr ev))
                                      (cadr (cddddr ev))
                                      (caddr (cddddr ev)))))
      (:read (fn-own-tls-result-owner (fn-scar-ocfg-read-tls-prefix oc a b)))
      (:fault (cdr (fn-ocfg-fault oc a)))
      (:observe (fn-ocfg-observe oc a))
      (otherwise oc))))

(defun fn-osi-host-run (oc evs)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp evs)
      (fn-osi-host-run (fn-osi-host-step oc (car evs)) (cdr evs))
    oc))

(defthm fn-osi-osb-install-keeps-store
  (equal (fn-own-store (mv-nth 1 (fn-osb-install o profile))) (fn-own-store o))
  :hints (("Goal" :in-theory (e/d (fn-osb-install)
                                  (fn-bs-profile-admittedp fn-osb-config
                                   fn-own-configure)))))

(defthm fn-osi-host-step-keeps-indexed
  (implies (fn-ceis-indexedp (fn-own-store (fn-ocfg-owner oc)))
           (fn-ceis-indexedp (fn-own-store (fn-ocfg-owner (fn-osi-host-step oc ev)))))
  :hints (("Goal"
           :use ((:instance fn-osi-own-finish-keeps-indexed
                            (o (fn-ocfg-owner oc)) (cfg (fn-ocfg-config oc))))
           :in-theory (union-theories
                       '(fn-osi-host-step
                         fn-osi-ocfg-step-keeps-indexed fn-osi-rcon-io-keeps-indexed
                         fn-osi-pcar-prepare-keeps-indexed
                         fn-osi-ccar-ocfg-prepare-identity-keeps-indexed
                         fn-osi-ccar-ocfg-complete-keeps-indexed
                         fn-osi-ocl-publish-keeps-indexed
                         fn-osi-ocfg-with-owner-store fn-osi-own-keeps-store-outside-step
                         fn-osi-osb-install-keeps-store fn-osi-ocfg-open-keeps-store
                         fn-osi-exp-open-keeps-store fn-scar-ocfg-read-keeps-store)
                       (theory 'minimal-theory)))))

(defthm fn-osi-host-run-keeps-indexed
  (implies (fn-ceis-indexedp (fn-own-store (fn-ocfg-owner oc)))
           (fn-ceis-indexedp (fn-own-store (fn-ocfg-owner (fn-osi-host-run oc evs)))))
  :hints (("Goal" :induct (fn-osi-host-run oc evs)
           :in-theory (e/d (fn-osi-host-run)
                           (fn-ceis-indexedp fn-osi-host-step)))))

(defun fn-osi-live-owner (configs prefix suffix frontier max-conns evs)
  (declare (xargs :guard t :verify-guards nil))
  (fn-osi-host-run (fn-osi-open configs prefix suffix frontier max-conns) evs))

(defun fn-osi-live-store (configs prefix suffix frontier max-conns evs)
  (declare (xargs :guard t :verify-guards nil))
  (fn-own-store (fn-ocfg-owner (fn-osi-live-owner configs prefix suffix
                                                  frontier max-conns evs))))

; KEYSTONE (PRF-144): the Store of every owner the host reaches from its
; open, by any sequence of the owners it installs, is indexed.  No
; hypothesis.  This is the Store fnn-bpapp-accept-locked binds before each
; dispatch.
(defthm fn-osi-live-owner-store-is-indexed
  (fn-ceis-indexedp (fn-osi-live-store configs prefix suffix frontier
                                       max-conns evs))
  :hints (("Goal" :use (fn-osi-open-installs-indexed-store
                        (:instance fn-osi-host-run-keeps-indexed
                                   (oc (fn-osi-open configs prefix suffix
                                                    frontier max-conns))))
           :in-theory (e/d (fn-osi-live-store fn-osi-live-owner)
                           (fn-ceis-indexedp fn-osi-host-run fn-osi-open
                            fn-osi-open-installs-indexed-store
                            fn-osi-host-run-keeps-indexed)))))

; -----------------------------------------------------------------------------
; PRF-132, restated over the Store the host dispatches over.  host/native/
; bp-app.lisp fnn-bpapp-accept-locked binds the installed owner's Store
; (fn-owner-app-bind-receipt-store) and asks fn-bprj-request-action ->
; fn-bpaj-dispatch-fast before every step; that Store is
; (fn-osi-live-store ...) of the open and the transitions the host has
; installed since.  The index premise of books/bp-signed-binding.lisp's
; refinement lemmas is discharged by fn-osi-live-owner-store-is-indexed; no
; conclusion changes.

; KEYSTONE: once the live Store's history holds an article record (plain or
; signed) with the Message-ID the dispatcher reads, the dispatcher never
; answers (:submit).
(defthm fn-bpaj-dispatch-never-resubmits-a-stored-article
  (let ((store (fn-osi-live-store configs prefix suffix frontier max-conns evs)))
    (implies (and (member-equal record
                                (fn-bpr-article-records
                                 (fn-sf-records (fn-sn-files store))))
                  (fn-record-p record)
                  (equal (fn-record-msgid record)
                         (fn-bpaj-dispatch-msgid joined request-octets)))
             (not (equal (fn-bpaj-dispatch-fast joined store request-octets
                                                generation)
                         (list :submit)))))
  :hints (("Goal"
           :use (fn-osi-live-owner-store-is-indexed
                 (:instance fn-bpaj-dispatch-never-resubmits-under-index
                            (store (fn-osi-live-store configs prefix suffix
                                                      frontier max-conns evs))))
           :in-theory (union-theories '() (theory 'minimal-theory)))))

; KEYSTONE: whatever the dispatcher binds over the live Store is an article
; record of an event of that Store's own history, for the request's
; Message-ID, accepted by the receiver's Store check; a signed composite
; binds its verdict to exactly that record.
(defthm fn-bpaj-dispatch-binds-the-stores-own-record
  (let ((store (fn-osi-live-store configs prefix suffix frontier max-conns evs)))
    (implies (equal (car (fn-bpaj-dispatch-fast joined store request-octets
                                                generation))
                    :bind)
             (let* ((record (cadr (fn-bpaj-dispatch-fast
                                   joined store request-octets generation)))
                    (events (fn-sf-records (fn-sn-files store)))
                    (event (fn-bpaj-article-event record events)))
               (and (fn-record-p record)
                    (equal (fn-record-msgid record)
                           (fn-bpaj-dispatch-msgid joined request-octets))
                    (fn-bpaj-store-record-accepted-fast store record)
                    (member-equal event events)
                    (equal (fn-bpr-event-article event) record)
                    (implies (fn-stxa-p event) (fn-stxa-bindsp event))))))
  :hints (("Goal"
           :use (fn-osi-live-owner-store-is-indexed
                 (:instance fn-bpaj-dispatch-binds-the-stores-own-record-under-index
                            (store (fn-osi-live-store configs prefix suffix
                                                      frontier max-conns evs))))
           :in-theory (union-theories '() (theory 'minimal-theory)))))

; The fast/checked equalities over the live Store: the Store record check,
; the two Message-ID lookups and the dispatcher they compose into are the
; checked walks over the history.
(defthm fn-osi-live-store-record-accepted-fast-is-checked
  (let ((store (fn-osi-live-store configs prefix suffix frontier max-conns evs)))
    (implies (fn-sn-statep store)
             (equal (fn-bpaj-store-record-accepted-fast store record)
                    (fn-bpr-store-record-acceptedp store record))))
  :hints (("Goal"
           :use (fn-osi-live-owner-store-is-indexed
                 (:instance fn-bpaj-store-record-accepted-fast-is-checked
                            (store (fn-osi-live-store configs prefix suffix
                                                      frontier max-conns evs))))
           :in-theory (union-theories '() (theory 'minimal-theory)))))

(defthm fn-osi-live-record-lookup-fast-is-checked
  (let ((store (fn-osi-live-store configs prefix suffix frontier max-conns evs)))
    (implies (fn-sn-statep store)
             (equal (fn-bpaj-record-lookup-fast store request)
                    (fn-bpaj-record-lookup store request))))
  :hints (("Goal"
           :use (fn-osi-live-owner-store-is-indexed
                 (:instance fn-bpaj-record-lookup-fast-is-checked
                            (store (fn-osi-live-store configs prefix suffix
                                                      frontier max-conns evs))))
           :in-theory (union-theories '() (theory 'minimal-theory)))))

(defthm fn-osi-live-transit-record-lookup-fast-is-checked
  (let ((store (fn-osi-live-store configs prefix suffix frontier max-conns evs)))
    (implies (fn-sn-statep store)
             (equal (fn-bpaj-transit-record-lookup-fast store request intent)
                    (fn-bpaj-transit-record-lookup store request intent))))
  :hints (("Goal"
           :use (fn-osi-live-owner-store-is-indexed
                 (:instance fn-bpaj-transit-record-lookup-fast-is-checked
                            (store (fn-osi-live-store configs prefix suffix
                                                      frontier max-conns evs))))
           :in-theory (union-theories '() (theory 'minimal-theory)))))

(defthm fn-osi-live-dispatch-fast-is-checked
  (let ((store (fn-osi-live-store configs prefix suffix frontier max-conns evs)))
    (implies (and (fn-bpaj-statep joined) (fn-sn-statep store))
             (equal (fn-bpaj-dispatch-fast joined store request-octets
                                           current-generation)
                    (fn-bpaj-dispatch joined store request-octets
                                      current-generation))))
  :hints (("Goal"
           :use (fn-osi-live-owner-store-is-indexed
                 (:instance fn-bpaj-dispatch-fast-is-checked
                            (store (fn-osi-live-store configs prefix suffix
                                                      frontier max-conns evs))))
           :in-theory (union-theories '() (theory 'minimal-theory)))))

(in-theory (disable fn-osi-open fn-osi-live-owner fn-osi-live-store
                    fn-osi-host-step fn-osi-host-run))
