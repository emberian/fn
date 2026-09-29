; owner-host-relation.lisp -- the relation the host carries in `fn-owner'
; (fn-ohr-, lane owner-relation, row Q3c).
;
; The host keeps ONE configured owner in the ACL2 state global `fn-owner'
; (host/owner-host.lisp fn-owner-ocfg / fn-owner-install-ocfg) and every
; entry that mutates it is `(fn-owner-install-ocfg (F (fn-owner-ocfg state)
; ...) state)' for some ACL2 function F.  The relation the host carries is
; `fn-lgoc-invariantp' (books/owner-log-ocl.lisp): `fn-ocl-relation' of the
; configured owner and `fn-cstp-carriedp' of its Store.  This book names,
; for every such F, the theorem that F preserves it (or establishes it, for
; the open), stated over F with the arguments as the host passes them.
; Where the theorem already exists it is cited by a corollary named
; `fn-ohr-<entry>-...-by-<theorem>'; where it did not, it is proved here.
;
; COVERAGE: host entry (host/owner-host.lisp) -> the ACL2 function it installs
; -> the theorem that carries fn-lgoc-invariantp (or fn-ocl-relation) across it.
;   fn-owner-recover-from-store-open  fn-ock-install         fn-ohr-store-open-installs-the-carried-relation (PRF-926)
;   fn-owner-recover-extended         fn-ock-recover-extended fn-lgoc-recover-installs-invariant (PRF-286)
;   fn-owner-fault                    fn-ocfg-fault          fn-ohr-fault-preserves-carried-relation (PRF-924)
;   fn-owner-step (:reconfigure)      fn-ocfg-reconfigure    fn-ohr-step-reconfigure-preserves-carried-relation (PRF-924)
;   fn-owner-step (:close)            fn-ocfg-close          fn-ohr-step-close-preserves-carried-relation (fn-ocl-close-preserves-historical-relation)
;   fn-owner-step (:advance)          fn-ocfg-advance        fn-ohr-step-advance-preserves-carried-relation (fn-ocl-advance-preserves-historical-relation)
;   fn-owner-step (:take :control-submit :operator-submit :feed-replay :control-outcome
;                  :bp-transit-outcome :feeds :feed-conn)    fn-ohr-step-<event>-preserves-carried-relation (PRF-925)
;   fn-owner-posting-configure        fn-own-configure       fn-ohr-configure-preserves-carried-relation (PRF-925)
;   fn-owner-install-profile          fn-osb-install         fn-ohr-osb-install-preserves-carried-relation (PRF-925)
;   fn-owner-feed-install-port-result fn-own-with-feeds      fn-ohr-with-feeds-preserves-carried-relation (PRF-925)
;   fn-owner-install-node-secret      fn-own-with-node-secret fn-ohr-with-node-secret-preserves-carried-relation (PRF-925)
;   fn-owner-reconfigure-complete     fn-oclc-publish        fn-lgoc-publish-preserves-invariant (PRF-286)
;   fn-owner-reconfigure-unstage      fn-psrv-unstage        fn-psrv-unstage-preserves-invariant (PRF-290)
;   fn-owner-io                       fn-olr-ocfg-order/-reserve, fn-rcon-ocfg-io  fn-lgoc-log-order/-log-reserve/-rcon-io-preserves-invariant (PRF-286)
;   fn-owner-prepare, -prepare-buffer fn-pout-prepare-article (= fn-psrv-prepare)  fn-psrv-prepare-preserves-invariant (PRF-290)
;   fn-owner-prepare-identity         fn-pout-prepare-identity (= fn-oiis-prepare-identity)  fn-oiis-prepare-identity-preserves-invariant
;   fn-owner-prepare-topic            fn-pout-prepare-topic  fn-psrv-prepare-topic-preserves-invariant
;   fn-owner-prepare-retention/-consumer, -refuse-reservation, -known-abort
;                                     fn-ocfg-step (:store ...)  fn-psrv-prepare-retention/-consumer-, fn-lgoc-refuse-reservation-, fn-psrv-known-abort-preserves-invariant
;   fn-owner-finish-submission-synced fn-apc-own-finish (= fn-ccar-own-finish)  fn-lgoc-finish-preserves-invariant (PRF-286)
;   fn-owner-open-at                  fn-ocar-ocfg-open (= fn-ocfg-open)  fn-ocl-open-preserves-historical-relation
;   fn-owner-observe                  fn-ocfg-observe        fn-ocl-observe-preserves-historical-relation
;   fn-owner-at-reader-view/-working-view  fn-ocfg-with-view  fn-orr-relation-of-with-view, fn-ocl-relation-of-a-view-captured-before-appends
;   fn-owner-chunk                    fn-scar-ocfg-read-tls-prefix (= fn-ocfg-read-tls-prefix = fn-ocfg-read of the consumed prefix)  fn-ocl-read-preserves-historical-relation [composite owed]
;   fn-owner-chunk-span-at            fn-oas-read-span       [owed: join-f2's fn-otm-read-span arm]
;   fn-owner-exposure-open            fn-ocar-exp-open (= fn-exp-open)  [owed: composite over fn-ocfg-open / fn-ocfg-open-peer]
;   fn-owner-finish-synced            fn-rix-ocfg-complete (= fn-ccar-ocfg-complete)  [owed]
;   fn-owner-begin, -declare-group    fn-pout-begin, fn-pout-declare-group  [owed: :begin keeps control; :declare-group appends a fact]
;   fn-owner-tls-established          fn-ocfg-read-step (:tls-established)  [owed]
;   fn-owner-open-peer, fn-exp-open's peer branch  fn-ocfg-open-peer  NOT PRESERVED: no pin (PKT-888)
;   fn-owner-outcome, -transit-outcome  fn-apc-own-outcome (= fn-own-outcome), fn-own-transit-outcome
;                                     a :durable completion advances the connection without re-pinning (PKT-889)

(in-package "ACL2")

(include-book "owner-identity-served")
(include-book "owner-prepare-outcome")
(include-book "owner-open-carried")
(include-book "owner-parse-carried")
(include-book "config-owner-advance-invariants")
(include-book "owner-served-bound")

(local (in-theory (disable fn-lgoc-invariantp fn-ocl-relation fn-cst-relation fn-cpr-replay fn-cst-replay-node
                           fn-ocl-conns-historyp fn-ocl-conn-historyp fn-ocl-view-historyp
                           fn-ocl-unique-conn-idsp fn-ocl-config-historyp fn-ocl-view-configp
                           fn-ocfg-pins-okp fn-ocfg-conns-pinnedp fn-ocfg-pins-pin-conns-only
                           fn-own-ids-below-next-p fn-own-ledger-durablep fn-own-facts-okp
                           fn-cfg-recordp fn-cfg-record-generation fn-cfgp)))

; ---------------------------------------------------------------------------
; The staged slot.  Nothing but the last conjunct of fn-ocl-relation reads it,
; so a configured owner that satisfies the relation still does with any
; staged record of the next generation, or none.  Staging (fn-ocfg-reconfigure)
; and the fault (which keeps the staged record where the close drops it) are
; both this lemma.
(defthm fn-ohr-ocl-relation-with-staged
  (implies (and (fn-ocl-relation x)
                (or (null s)
                    (and (fn-cfg-recordp s)
                         (equal (fn-cfg-record-generation s)
                                (+ 1 (nfix (fn-cfg-generation (fn-ocfg-config x))))))))
           (fn-ocl-relation (fn-ocfg-make (fn-ocfg-owner x) (fn-ocfg-config x)
                                          (fn-ocfg-pins x) s)))
  :hints (("Goal"
           :use ((:instance fn-ocl-conns-historyp-under-same-store-and-pins
                            (oc x)
                            (next (fn-ocfg-make (fn-ocfg-owner x) (fn-ocfg-config x)
                                                (fn-ocfg-pins x) s))
                            (conns (fn-own-conns (fn-ocfg-owner x)))))
           :in-theory (e/d (fn-ocl-relation fn-ocl-config-historyp fn-ocl-view-configp)
                           (fn-ocl-conns-historyp-under-same-store-and-pins)))))

(defthm fn-ohr-relation-staged-okp
  (implies (fn-ocl-relation oc)
           (or (null (fn-ocfg-staged oc))
               (and (fn-cfg-recordp (fn-ocfg-staged oc))
                    (equal (fn-cfg-record-generation (fn-ocfg-staged oc))
                           (+ 1 (nfix (fn-cfg-generation (fn-ocfg-config oc))))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-ocl-relation))))

; ---------------------------------------------------------------------------
; HOST-FAULT (host/owner-host.lisp fn-owner-fault: fn-ocfg-fault).  The fault
; is the close with the staged record kept.
(defthm fn-ohr-fault-unfolds-to-close-with-staged
  (equal (cdr (fn-ocfg-fault oc id))
         (fn-ocfg-make (fn-ocfg-owner (fn-ocfg-close oc id))
                       (fn-ocfg-config (fn-ocfg-close oc id))
                       (fn-ocfg-pins (fn-ocfg-close oc id))
                       (fn-ocfg-staged oc)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-ocfg-fault fn-own-fault fn-ocfg-close))))

(defthm fn-ohr-fault-preserves-ocl-relation
  (implies (fn-ocl-relation oc)
           (fn-ocl-relation (cdr (fn-ocfg-fault oc id))))
  :hints (("Goal"
           :use ((:instance fn-ohr-ocl-relation-with-staged
                            (x (fn-ocfg-close oc id)) (s (fn-ocfg-staged oc)))
                 fn-ohr-relation-staged-okp
                 fn-ohr-fault-unfolds-to-close-with-staged
                 fn-ocl-close-preserves-historical-relation)
           :in-theory (e/d (fn-ocfg-close) (fn-ocfg-fault fn-own-close)))))

; ---------------------------------------------------------------------------
; STAGING (host/owner-host.lisp fn-owner-reconfigure: fn-owner-step of
; (:reconfigure id deltas), fn-ocfg-step's :reconfigure arm).  An admitted
; request stages fn-ocfg-reconfig-record, whose acceptability
; (fn-cnode-record-acceptablep, inside fn-ocfg-reconfig-okp) is the record
; predicate the relation's last conjunct asks for; a refused request changes
; nothing.
(local (defthm fn-ohr-cfgp-generation-natp
  (implies (fn-cfgp c) (natp (fn-cfg-generation c)))
  :hints (("Goal" :in-theory (enable fn-cfgp fn-record-uint32p)))))

(defthm fn-ohr-reconfigure-preserves-ocl-relation
  (implies (fn-ocl-relation oc)
           (fn-ocl-relation (fn-ocfg-reconfigure oc id deltas)))
  :hints (("Goal"
           :use ((:instance fn-ohr-ocl-relation-with-staged
                            (x oc) (s (fn-ocfg-reconfig-record oc deltas))))
           :in-theory (e/d (fn-ocfg-reconfigure fn-ocfg-reconfig-okp
                            fn-cnode-record-acceptablep fn-cfg-record-acceptablep
                            fn-ocfg-reconfig-record)
                           (fn-cfg-record-fitsp fn-cfg-admissiblep
                            fn-ocfg-live-cnode fn-ocfg-config-stamp
                            fn-ocfg-group-pinned-by-readerp
                            fn-ocfg-conn-generation fn-cfg-delta-listp)))))

; ---------------------------------------------------------------------------
; Same control: an owner step that keeps the store, the view, the connections,
; the identifier bound, the ledger, the clock and the facts keeps the relation
; (the frame theorem fn-ocl-relation-under-same-control-and-valid-connections
; with the connection clauses discharged from the relation before).  Every
; queue, in-flight, feed, secret and configuration step below is an instance.
(defthm fn-ohr-ocl-relation-with-owner-of-same-control
  (implies (and (fn-ocl-relation oc)
                (fn-own-shapep o2)
                (equal (fn-own-store o2) (fn-own-store (fn-ocfg-owner oc)))
                (equal (fn-own-view o2) (fn-own-view (fn-ocfg-owner oc)))
                (equal (fn-own-conns o2) (fn-own-conns (fn-ocfg-owner oc)))
                (equal (fn-own-next-id o2) (fn-own-next-id (fn-ocfg-owner oc)))
                (equal (fn-own-max-conns o2) (fn-own-max-conns (fn-ocfg-owner oc)))
                (equal (fn-own-ledger o2) (fn-own-ledger (fn-ocfg-owner oc)))
                (equal (fn-own-clock o2) (fn-own-clock (fn-ocfg-owner oc)))
                (equal (fn-own-facts o2) (fn-own-facts (fn-ocfg-owner oc))))
           (fn-ocl-relation (fn-ocfg-with-owner oc o2)))
  :hints (("Goal"
           :use ((:instance fn-ocl-relation-under-same-control-and-valid-connections
                            (next (fn-ocfg-with-owner oc o2)))
                 (:instance fn-ocl-conns-historyp-under-same-store-and-pins
                            (next (fn-ocfg-with-owner oc o2))
                            (conns (fn-own-conns (fn-ocfg-owner oc)))))
           :in-theory (e/d (fn-ocfg-with-owner)
                           (fn-ocl-relation-under-same-control-and-valid-connections
                            fn-ocl-conns-historyp-under-same-store-and-pins)))
          ("Goal'" :in-theory (e/d (fn-ocl-relation fn-ocfg-with-owner)
                                   (fn-ocl-relation-under-same-control-and-valid-connections
                                    fn-ocl-conns-historyp-under-same-store-and-pins)))))

(defthm fn-ohr-relation-owner-shapep
  (implies (fn-ocl-relation oc) (fn-own-shapep (fn-ocfg-owner oc)))
  :hints (("Goal" :in-theory (enable fn-ocl-relation))))

; The frame facts, one per owner step the host reaches through fn-ocfg-pass
; (fn-owner-step) or fn-owner-replace-core.
(defthm fn-ohr-take-submission-keeps-control
  (implies (fn-own-shapep o)
           (let ((o2 (fn-own-take-submission o)))
             (and (fn-own-shapep o2)
                  (equal (fn-own-store o2) (fn-own-store o))
                  (equal (fn-own-view o2) (fn-own-view o))
                  (equal (fn-own-conns o2) (fn-own-conns o))
                  (equal (fn-own-next-id o2) (fn-own-next-id o))
                  (equal (fn-own-max-conns o2) (fn-own-max-conns o))
                  (equal (fn-own-ledger-field o2) (fn-own-ledger-field o))
                  (equal (fn-own-clock o2) (fn-own-clock o))
                  (equal (fn-own-facts o2) (fn-own-facts o)))))
  :hints (("Goal" :in-theory (enable fn-own-take-submission))))
(defthm fn-ohr-control-submit-keeps-control
  (implies (fn-own-shapep o)
           (let ((o2 (fn-own-control-submit o msgid groups octets)))
             (and (fn-own-shapep o2)
                  (equal (fn-own-store o2) (fn-own-store o))
                  (equal (fn-own-view o2) (fn-own-view o))
                  (equal (fn-own-conns o2) (fn-own-conns o))
                  (equal (fn-own-next-id o2) (fn-own-next-id o))
                  (equal (fn-own-max-conns o2) (fn-own-max-conns o))
                  (equal (fn-own-ledger-field o2) (fn-own-ledger-field o))
                  (equal (fn-own-clock o2) (fn-own-clock o))
                  (equal (fn-own-facts o2) (fn-own-facts o)))))
  :hints (("Goal" :in-theory (enable fn-own-control-submit fn-own-enqueue))))
(defthm fn-ohr-operator-submit-keeps-control
  (implies (fn-own-shapep o)
           (let ((o2 (fn-own-operator-submit o msgid groups octets stored)))
             (and (fn-own-shapep o2)
                  (equal (fn-own-store o2) (fn-own-store o))
                  (equal (fn-own-view o2) (fn-own-view o))
                  (equal (fn-own-conns o2) (fn-own-conns o))
                  (equal (fn-own-next-id o2) (fn-own-next-id o))
                  (equal (fn-own-max-conns o2) (fn-own-max-conns o))
                  (equal (fn-own-ledger-field o2) (fn-own-ledger-field o))
                  (equal (fn-own-clock o2) (fn-own-clock o))
                  (equal (fn-own-facts o2) (fn-own-facts o)))))
  :hints (("Goal" :in-theory (enable fn-own-operator-submit fn-own-enqueue))))
(defthm fn-ohr-control-outcome-keeps-control
  (implies (fn-own-shapep o)
           (let ((o2 (fn-own-control-outcome o word)))
             (and (fn-own-shapep o2)
                  (equal (fn-own-store o2) (fn-own-store o))
                  (equal (fn-own-view o2) (fn-own-view o))
                  (equal (fn-own-conns o2) (fn-own-conns o))
                  (equal (fn-own-next-id o2) (fn-own-next-id o))
                  (equal (fn-own-max-conns o2) (fn-own-max-conns o))
                  (equal (fn-own-ledger-field o2) (fn-own-ledger-field o))
                  (equal (fn-own-clock o2) (fn-own-clock o))
                  (equal (fn-own-facts o2) (fn-own-facts o)))))
  :hints (("Goal" :in-theory (enable fn-own-control-outcome))))
(defthm fn-ohr-with-feeds-keeps-control
  (implies (fn-own-shapep o)
           (let ((o2 (fn-own-with-feeds o feeds)))
             (and (fn-own-shapep o2)
                  (equal (fn-own-store o2) (fn-own-store o))
                  (equal (fn-own-view o2) (fn-own-view o))
                  (equal (fn-own-conns o2) (fn-own-conns o))
                  (equal (fn-own-next-id o2) (fn-own-next-id o))
                  (equal (fn-own-max-conns o2) (fn-own-max-conns o))
                  (equal (fn-own-ledger-field o2) (fn-own-ledger-field o))
                  (equal (fn-own-clock o2) (fn-own-clock o))
                  (equal (fn-own-facts o2) (fn-own-facts o)))))
  :hints (("Goal" :in-theory (enable fn-own-with-feeds))))
(defthm fn-ohr-feeds-reconfigure-keeps-control
  (implies (fn-own-shapep o)
           (let ((o2 (fn-own-feeds-reconfigure o cfg)))
             (and (fn-own-shapep o2)
                  (equal (fn-own-store o2) (fn-own-store o))
                  (equal (fn-own-view o2) (fn-own-view o))
                  (equal (fn-own-conns o2) (fn-own-conns o))
                  (equal (fn-own-next-id o2) (fn-own-next-id o))
                  (equal (fn-own-max-conns o2) (fn-own-max-conns o))
                  (equal (fn-own-ledger-field o2) (fn-own-ledger-field o))
                  (equal (fn-own-clock o2) (fn-own-clock o))
                  (equal (fn-own-facts o2) (fn-own-facts o)))))
  :hints (("Goal" :in-theory (enable fn-own-feeds-reconfigure))))
(defthm fn-ohr-feed-connect-keeps-control
  (implies (fn-own-shapep o)
           (let ((o2 (fn-own-feed-connect o peer conn form)))
             (and (fn-own-shapep o2)
                  (equal (fn-own-store o2) (fn-own-store o))
                  (equal (fn-own-view o2) (fn-own-view o))
                  (equal (fn-own-conns o2) (fn-own-conns o))
                  (equal (fn-own-next-id o2) (fn-own-next-id o))
                  (equal (fn-own-max-conns o2) (fn-own-max-conns o))
                  (equal (fn-own-ledger-field o2) (fn-own-ledger-field o))
                  (equal (fn-own-clock o2) (fn-own-clock o))
                  (equal (fn-own-facts o2) (fn-own-facts o)))))
  :hints (("Goal" :in-theory (enable fn-own-feed-connect))))
(defthm fn-ohr-feed-recover-keeps-control
  (implies (fn-own-shapep o)
           (let ((o2 (fn-own-feed-recover o peer entries)))
             (and (fn-own-shapep o2)
                  (equal (fn-own-store o2) (fn-own-store o))
                  (equal (fn-own-view o2) (fn-own-view o))
                  (equal (fn-own-conns o2) (fn-own-conns o))
                  (equal (fn-own-next-id o2) (fn-own-next-id o))
                  (equal (fn-own-max-conns o2) (fn-own-max-conns o))
                  (equal (fn-own-ledger-field o2) (fn-own-ledger-field o))
                  (equal (fn-own-clock o2) (fn-own-clock o))
                  (equal (fn-own-facts o2) (fn-own-facts o)))))
  :hints (("Goal" :in-theory (enable fn-own-feed-recover))))
(defthm fn-ohr-with-node-secret-keeps-control
  (implies (fn-own-shapep o)
           (let ((o2 (fn-own-with-node-secret o secret)))
             (and (fn-own-shapep o2)
                  (equal (fn-own-store o2) (fn-own-store o))
                  (equal (fn-own-view o2) (fn-own-view o))
                  (equal (fn-own-conns o2) (fn-own-conns o))
                  (equal (fn-own-next-id o2) (fn-own-next-id o))
                  (equal (fn-own-max-conns o2) (fn-own-max-conns o))
                  (equal (fn-own-ledger-field o2) (fn-own-ledger-field o))
                  (equal (fn-own-clock o2) (fn-own-clock o))
                  (equal (fn-own-facts o2) (fn-own-facts o)))))
  :hints (("Goal" :in-theory (enable fn-own-with-node-secret))))
(defthm fn-ohr-configure-keeps-control
  (implies (fn-own-shapep o)
           (let ((o2 (fn-own-configure o config)))
             (and (fn-own-shapep o2)
                  (equal (fn-own-store o2) (fn-own-store o))
                  (equal (fn-own-view o2) (fn-own-view o))
                  (equal (fn-own-conns o2) (fn-own-conns o))
                  (equal (fn-own-next-id o2) (fn-own-next-id o))
                  (equal (fn-own-max-conns o2) (fn-own-max-conns o))
                  (equal (fn-own-ledger-field o2) (fn-own-ledger-field o))
                  (equal (fn-own-clock o2) (fn-own-clock o))
                  (equal (fn-own-facts o2) (fn-own-facts o)))))
  :hints (("Goal" :in-theory (enable fn-own-configure))))
(defthm fn-ohr-osb-install-keeps-control
  (implies (fn-own-shapep o)
           (let ((o2 (mv-nth 1 (fn-osb-install o profile))))
             (and (fn-own-shapep o2)
                  (equal (fn-own-store o2) (fn-own-store o))
                  (equal (fn-own-view o2) (fn-own-view o))
                  (equal (fn-own-conns o2) (fn-own-conns o))
                  (equal (fn-own-next-id o2) (fn-own-next-id o))
                  (equal (fn-own-max-conns o2) (fn-own-max-conns o))
                  (equal (fn-own-ledger-field o2) (fn-own-ledger-field o))
                  (equal (fn-own-clock o2) (fn-own-clock o))
                  (equal (fn-own-facts o2) (fn-own-facts o)))))
  :hints (("Goal" :in-theory (e/d (fn-osb-install) (fn-bs-profile-admittedp)))))
(defthm fn-ohr-osb-install-keeps-control
  (implies (fn-own-shapep o)
           (let ((o2 (mv-nth 1 (fn-osb-install o profile))))
             (and (fn-own-shapep o2)
                  (equal (fn-own-store o2) (fn-own-store o))
                  (equal (fn-own-view o2) (fn-own-view o))
                  (equal (fn-own-conns o2) (fn-own-conns o))
                  (equal (fn-own-next-id o2) (fn-own-next-id o))
                  (equal (fn-own-max-conns o2) (fn-own-max-conns o))
                  (equal (fn-own-ledger-field o2) (fn-own-ledger-field o))
                  (equal (fn-own-clock o2) (fn-own-clock o))
                  (equal (fn-own-facts o2) (fn-own-facts o)))))
  :hints (("Goal" :in-theory (e/d (fn-osb-install) (fn-bs-profile-admittedp)))))
; The same-control frame with the ledger FIELD named (what the owner steps
; below keep; fn-own-ledger is the field read back, fn-sl-list-of-fn-own-ledger-field).
(defthm fn-ohr-ocl-relation-with-owner-of-same-control-field
  (implies (and (fn-ocl-relation oc)
                (fn-own-shapep o2)
                (equal (fn-own-store o2) (fn-own-store (fn-ocfg-owner oc)))
                (equal (fn-own-view o2) (fn-own-view (fn-ocfg-owner oc)))
                (equal (fn-own-conns o2) (fn-own-conns (fn-ocfg-owner oc)))
                (equal (fn-own-next-id o2) (fn-own-next-id (fn-ocfg-owner oc)))
                (equal (fn-own-max-conns o2) (fn-own-max-conns (fn-ocfg-owner oc)))
                (equal (fn-own-ledger-field o2) (fn-own-ledger-field (fn-ocfg-owner oc)))
                (equal (fn-own-clock o2) (fn-own-clock (fn-ocfg-owner oc)))
                (equal (fn-own-facts o2) (fn-own-facts (fn-ocfg-owner oc))))
           (fn-ocl-relation (fn-ocfg-with-owner oc o2)))
  :hints (("Goal" :use (fn-ohr-ocl-relation-with-owner-of-same-control
                        (:instance fn-sl-list-of-fn-own-ledger-field (o o2))
                        (:instance fn-sl-list-of-fn-own-ledger-field (o (fn-ocfg-owner oc))))
           :in-theory (disable fn-sl-list-of-fn-own-ledger-field
                               fn-ohr-ocl-relation-with-owner-of-same-control))))

(defthm fn-ohr-configure-preserves-ocl-relation
  (implies (fn-ocl-relation oc)
           (fn-ocl-relation (fn-ocfg-with-owner oc (fn-own-configure (fn-ocfg-owner oc) config))))
  :hints (("Goal" :use ((:instance fn-ohr-ocl-relation-with-owner-of-same-control-field
                                   (o2 (fn-own-configure (fn-ocfg-owner oc) config)))))))
(defthm fn-ohr-with-feeds-preserves-ocl-relation
  (implies (fn-ocl-relation oc)
           (fn-ocl-relation (fn-ocfg-with-owner oc (fn-own-with-feeds (fn-ocfg-owner oc) feeds))))
  :hints (("Goal" :use ((:instance fn-ohr-ocl-relation-with-owner-of-same-control-field
                                   (o2 (fn-own-with-feeds (fn-ocfg-owner oc) feeds)))))))
(defthm fn-ohr-with-node-secret-preserves-ocl-relation
  (implies (fn-ocl-relation oc)
           (fn-ocl-relation (fn-ocfg-with-owner oc (fn-own-with-node-secret (fn-ocfg-owner oc) secret))))
  :hints (("Goal" :use ((:instance fn-ohr-ocl-relation-with-owner-of-same-control-field
                                   (o2 (fn-own-with-node-secret (fn-ocfg-owner oc) secret)))))))
(defthm fn-ohr-osb-install-preserves-ocl-relation
  (implies (fn-ocl-relation oc)
           (fn-ocl-relation (fn-ocfg-with-owner oc (mv-nth 1 (fn-osb-install (fn-ocfg-owner oc) profile)))))
  :hints (("Goal" :use ((:instance fn-ohr-ocl-relation-with-owner-of-same-control-field
                                   (o2 (mv-nth 1 (fn-osb-install (fn-ocfg-owner oc) profile)))))
           :in-theory (disable fn-osb-install fn-bs-profile-admittedp))))
(defthm fn-ohr-pass-take-preserves-ocl-relation
  (implies (fn-ocl-relation oc)
           (fn-ocl-relation (fn-ocfg-pass oc (list :take) fn-arena)))
  :hints (("Goal" :use ((:instance fn-ohr-ocl-relation-with-owner-of-same-control-field
                                   (o2 (fn-own-take-submission (fn-ocfg-owner oc)))))
           :in-theory (enable fn-ocfg-pass fn-own-step))))
(defthm fn-ohr-pass-control-submit-preserves-ocl-relation
  (implies (fn-ocl-relation oc)
           (fn-ocl-relation (fn-ocfg-pass oc (list :control-submit msgid groups octets) fn-arena)))
  :hints (("Goal" :use ((:instance fn-ohr-ocl-relation-with-owner-of-same-control-field
                                   (o2 (fn-own-control-submit (fn-ocfg-owner oc) msgid groups octets))))
           :in-theory (enable fn-ocfg-pass fn-own-step))))
(defthm fn-ohr-pass-operator-submit-preserves-ocl-relation
  (implies (fn-ocl-relation oc)
           (fn-ocl-relation (fn-ocfg-pass oc (list :operator-submit msgid groups octets stored) fn-arena)))
  :hints (("Goal" :use ((:instance fn-ohr-ocl-relation-with-owner-of-same-control-field
                                   (o2 (fn-own-operator-submit (fn-ocfg-owner oc) msgid groups octets stored))))
           :in-theory (enable fn-ocfg-pass fn-own-step))))
(defthm fn-ohr-pass-feed-replay-preserves-ocl-relation
  (implies (fn-ocl-relation oc)
           (fn-ocl-relation (fn-ocfg-pass oc (list :feed-replay peer entries) fn-arena)))
  :hints (("Goal" :use ((:instance fn-ohr-ocl-relation-with-owner-of-same-control-field
                                   (o2 (fn-own-feed-recover (fn-ocfg-owner oc) peer entries))))
           :in-theory (enable fn-ocfg-pass fn-own-step))))
(defthm fn-ohr-pass-control-outcome-preserves-ocl-relation
  (implies (fn-ocl-relation oc)
           (fn-ocl-relation (fn-ocfg-pass oc (list :control-outcome word) fn-arena)))
  :hints (("Goal" :use ((:instance fn-ohr-ocl-relation-with-owner-of-same-control-field
                                   (o2 (fn-own-control-outcome (fn-ocfg-owner oc) word))))
           :in-theory (enable fn-ocfg-pass fn-own-step))))
(defthm fn-ohr-pass-bp-transit-outcome-preserves-ocl-relation
  (implies (fn-ocl-relation oc)
           (fn-ocl-relation (fn-ocfg-pass oc (list :bp-transit-outcome word) fn-arena)))
  :hints (("Goal" :use ((:instance fn-ohr-ocl-relation-with-owner-of-same-control-field
                                   (o2 (fn-own-bp-transit-outcome (fn-ocfg-owner oc) word))))
           :in-theory (enable fn-ocfg-pass fn-own-step))))
(defthm fn-ohr-pass-feeds-preserves-ocl-relation
  (implies (fn-ocl-relation oc)
           (fn-ocl-relation (fn-ocfg-pass oc (list :feeds cfg) fn-arena)))
  :hints (("Goal" :use ((:instance fn-ohr-ocl-relation-with-owner-of-same-control-field
                                   (o2 (fn-own-feeds-reconfigure (fn-ocfg-owner oc) cfg))))
           :in-theory (enable fn-ocfg-pass fn-own-step))))
(defthm fn-ohr-pass-feed-conn-preserves-ocl-relation
  (implies (fn-ocl-relation oc)
           (fn-ocl-relation (fn-ocfg-pass oc (list :feed-conn peer conn form) fn-arena)))
  :hints (("Goal" :use ((:instance fn-ohr-ocl-relation-with-owner-of-same-control-field
                                   (o2 (fn-own-feed-connect (fn-ocfg-owner oc) peer conn form))))
           :in-theory (enable fn-ocfg-pass fn-own-step))))
(defthm fn-ohr-step-reconfigure-preserves-ocl-relation
  (implies (fn-ocl-relation oc)
           (fn-ocl-relation (fn-ocfg-step oc (list :reconfigure id deltas) fn-arena)))
  :hints (("Goal" :in-theory (enable fn-ocfg-step))))
(defthm fn-ohr-step-close-preserves-ocl-relation
  (implies (fn-ocl-relation oc)
           (fn-ocl-relation (fn-ocfg-step oc (list :close id) fn-arena)))
  :hints (("Goal" :in-theory (enable fn-ocfg-step))))
(defthm fn-ohr-step-advance-preserves-ocl-relation
  (implies (fn-ocl-relation oc)
           (fn-ocl-relation (fn-ocfg-step oc (list :advance id) fn-arena)))
  :hints (("Goal" :use fn-ocl-advance-preserves-historical-relation
           :in-theory (enable fn-ocfg-step))))
(defthm fn-ohr-step-take-preserves-ocl-relation
  (implies (fn-ocl-relation oc)
           (fn-ocl-relation (fn-ocfg-step oc (list :take) fn-arena)))
  :hints (("Goal" :in-theory (enable fn-ocfg-step))))
(defthm fn-ohr-step-control-submit-preserves-ocl-relation
  (implies (fn-ocl-relation oc)
           (fn-ocl-relation (fn-ocfg-step oc (list :control-submit msgid groups octets) fn-arena)))
  :hints (("Goal" :in-theory (enable fn-ocfg-step))))
(defthm fn-ohr-step-operator-submit-preserves-ocl-relation
  (implies (fn-ocl-relation oc)
           (fn-ocl-relation (fn-ocfg-step oc (list :operator-submit msgid groups octets stored) fn-arena)))
  :hints (("Goal" :in-theory (enable fn-ocfg-step))))
(defthm fn-ohr-step-feed-replay-preserves-ocl-relation
  (implies (fn-ocl-relation oc)
           (fn-ocl-relation (fn-ocfg-step oc (list :feed-replay peer entries) fn-arena)))
  :hints (("Goal" :in-theory (enable fn-ocfg-step))))
(defthm fn-ohr-step-control-outcome-preserves-ocl-relation
  (implies (fn-ocl-relation oc)
           (fn-ocl-relation (fn-ocfg-step oc (list :control-outcome word) fn-arena)))
  :hints (("Goal" :in-theory (enable fn-ocfg-step))))
(defthm fn-ohr-step-bp-transit-outcome-preserves-ocl-relation
  (implies (fn-ocl-relation oc)
           (fn-ocl-relation (fn-ocfg-step oc (list :bp-transit-outcome word) fn-arena)))
  :hints (("Goal" :in-theory (enable fn-ocfg-step))))
(defthm fn-ohr-step-feeds-preserves-ocl-relation
  (implies (fn-ocl-relation oc)
           (fn-ocl-relation (fn-ocfg-step oc (list :feeds cfg) fn-arena)))
  :hints (("Goal" :in-theory (enable fn-ocfg-step))))
(defthm fn-ohr-step-feed-conn-preserves-ocl-relation
  (implies (fn-ocl-relation oc)
           (fn-ocl-relation (fn-ocfg-step oc (list :feed-conn peer conn form) fn-arena)))
  :hints (("Goal" :in-theory (enable fn-ocfg-step))))


; ---------------------------------------------------------------------------
; The relation the host CARRIES is fn-lgoc-invariantp (books/owner-log-ocl.lisp):
; fn-ocl-relation of the configured owner and fn-cstp-carriedp of its Store.
; The io steps need the Store half; every entry above keeps the Store, so its
; fn-ocl-relation theorem lifts.
(defthm fn-ohr-carried-implies-ocl-relation
  (implies (fn-lgoc-invariantp oc) (fn-ocl-relation oc))
  :hints (("Goal" :in-theory (enable fn-lgoc-invariantp))))

(defthm fn-ohr-carried-of-same-store
  (implies (and (fn-lgoc-invariantp oc)
                (fn-ocl-relation x)
                (equal (fn-own-store (fn-ocfg-owner x)) (fn-own-store (fn-ocfg-owner oc))))
           (fn-lgoc-invariantp x))
  :hints (("Goal" :in-theory (enable fn-lgoc-invariantp))))

(defthm fn-ohr-fault-keeps-store
  (equal (fn-own-store (fn-ocfg-owner (cdr (fn-ocfg-fault oc id))))
         (fn-own-store (fn-ocfg-owner oc)))
  :hints (("Goal" :in-theory (enable fn-ocfg-fault fn-own-fault fn-own-close))))

(defthm fn-ohr-reconfigure-keeps-owner
  (equal (fn-ocfg-owner (fn-ocfg-reconfigure oc id deltas)) (fn-ocfg-owner oc))
  :hints (("Goal" :in-theory (enable fn-ocfg-reconfigure))))

(defthm fn-ohr-fault-preserves-carried-relation
  (implies (fn-lgoc-invariantp oc)
           (fn-lgoc-invariantp (cdr (fn-ocfg-fault oc id))))
  :hints (("Goal" :use ((:instance fn-ohr-carried-of-same-store (x (cdr (fn-ocfg-fault oc id)))))
           :in-theory (disable fn-ocfg-fault fn-ocfg-close fn-ocfg-advance fn-ocfg-reconfigure fn-ocfg-pass fn-ocfg-with-owner fn-osb-install fn-bs-profile-admittedp))))
(defthm fn-ohr-reconfigure-preserves-carried-relation
  (implies (fn-lgoc-invariantp oc)
           (fn-lgoc-invariantp (fn-ocfg-reconfigure oc id deltas)))
  :hints (("Goal" :use ((:instance fn-ohr-carried-of-same-store (x (fn-ocfg-reconfigure oc id deltas))))
           :in-theory (disable fn-ocfg-fault fn-ocfg-close fn-ocfg-advance fn-ocfg-reconfigure fn-ocfg-pass fn-ocfg-with-owner fn-osb-install fn-bs-profile-admittedp))))
(defthm fn-ohr-configure-preserves-carried-relation
  (implies (fn-lgoc-invariantp oc)
           (fn-lgoc-invariantp (fn-ocfg-with-owner oc (fn-own-configure (fn-ocfg-owner oc) config))))
  :hints (("Goal" :use ((:instance fn-ohr-carried-of-same-store (x (fn-ocfg-with-owner oc (fn-own-configure (fn-ocfg-owner oc) config)))))
           :in-theory (disable fn-ocfg-fault fn-ocfg-close fn-ocfg-advance fn-ocfg-reconfigure fn-ocfg-pass fn-ocfg-with-owner fn-osb-install fn-bs-profile-admittedp))))
(defthm fn-ohr-with-feeds-preserves-carried-relation
  (implies (fn-lgoc-invariantp oc)
           (fn-lgoc-invariantp (fn-ocfg-with-owner oc (fn-own-with-feeds (fn-ocfg-owner oc) feeds))))
  :hints (("Goal" :use ((:instance fn-ohr-carried-of-same-store (x (fn-ocfg-with-owner oc (fn-own-with-feeds (fn-ocfg-owner oc) feeds)))))
           :in-theory (disable fn-ocfg-fault fn-ocfg-close fn-ocfg-advance fn-ocfg-reconfigure fn-ocfg-pass fn-ocfg-with-owner fn-osb-install fn-bs-profile-admittedp))))
(defthm fn-ohr-with-node-secret-preserves-carried-relation
  (implies (fn-lgoc-invariantp oc)
           (fn-lgoc-invariantp (fn-ocfg-with-owner oc (fn-own-with-node-secret (fn-ocfg-owner oc) secret))))
  :hints (("Goal" :use ((:instance fn-ohr-carried-of-same-store (x (fn-ocfg-with-owner oc (fn-own-with-node-secret (fn-ocfg-owner oc) secret)))))
           :in-theory (disable fn-ocfg-fault fn-ocfg-close fn-ocfg-advance fn-ocfg-reconfigure fn-ocfg-pass fn-ocfg-with-owner fn-osb-install fn-bs-profile-admittedp))))
(defthm fn-ohr-osb-install-preserves-carried-relation
  (implies (fn-lgoc-invariantp oc)
           (fn-lgoc-invariantp (fn-ocfg-with-owner oc (mv-nth 1 (fn-osb-install (fn-ocfg-owner oc) profile)))))
  :hints (("Goal" :use ((:instance fn-ohr-carried-of-same-store (x (fn-ocfg-with-owner oc (mv-nth 1 (fn-osb-install (fn-ocfg-owner oc) profile))))))
           :in-theory (disable fn-ocfg-fault fn-ocfg-close fn-ocfg-advance fn-ocfg-reconfigure fn-ocfg-pass fn-ocfg-with-owner fn-osb-install fn-bs-profile-admittedp))))
(defthm fn-ohr-step-reconfigure-preserves-carried-relation
  (implies (fn-lgoc-invariantp oc)
           (fn-lgoc-invariantp (fn-ocfg-step oc (list :reconfigure id deltas) fn-arena)))
  :hints (("Goal" :use ((:instance fn-ohr-carried-of-same-store
                                   (x (fn-ocfg-step oc (list :reconfigure id deltas) fn-arena))))
           :in-theory (e/d (fn-ocfg-step) (fn-ocfg-fault fn-ocfg-close fn-ocfg-advance fn-ocfg-reconfigure fn-ocfg-pass fn-ocfg-with-owner)))))
(defthm fn-ohr-step-close-preserves-carried-relation
  (implies (fn-lgoc-invariantp oc)
           (fn-lgoc-invariantp (fn-ocfg-step oc (list :close id) fn-arena)))
  :hints (("Goal" :use ((:instance fn-ohr-carried-of-same-store
                                   (x (fn-ocfg-step oc (list :close id) fn-arena))))
           :in-theory (e/d (fn-ocfg-step) (fn-ocfg-fault fn-ocfg-close fn-ocfg-advance fn-ocfg-reconfigure fn-ocfg-pass fn-ocfg-with-owner)))))
(defthm fn-ohr-step-advance-preserves-carried-relation
  (implies (fn-lgoc-invariantp oc)
           (fn-lgoc-invariantp (fn-ocfg-step oc (list :advance id) fn-arena)))
  :hints (("Goal" :use ((:instance fn-ohr-carried-of-same-store
                                   (x (fn-ocfg-step oc (list :advance id) fn-arena)))
                 fn-ocl-advance-preserves-historical-relation)
           :in-theory (e/d (fn-ocfg-step) (fn-ocfg-fault fn-ocfg-close fn-ocfg-advance fn-ocfg-reconfigure fn-ocfg-pass fn-ocfg-with-owner)))))
(defthm fn-ohr-step-take-preserves-carried-relation
  (implies (fn-lgoc-invariantp oc)
           (fn-lgoc-invariantp (fn-ocfg-step oc (list :take) fn-arena)))
  :hints (("Goal" :use ((:instance fn-ohr-carried-of-same-store
                                   (x (fn-ocfg-step oc (list :take) fn-arena))))
           :in-theory (e/d (fn-ocfg-step) (fn-ocfg-fault fn-ocfg-close fn-ocfg-advance fn-ocfg-reconfigure fn-ocfg-pass fn-ocfg-with-owner)))))
(defthm fn-ohr-step-control-submit-preserves-carried-relation
  (implies (fn-lgoc-invariantp oc)
           (fn-lgoc-invariantp (fn-ocfg-step oc (list :control-submit msgid groups octets) fn-arena)))
  :hints (("Goal" :use ((:instance fn-ohr-carried-of-same-store
                                   (x (fn-ocfg-step oc (list :control-submit msgid groups octets) fn-arena))))
           :in-theory (e/d (fn-ocfg-step) (fn-ocfg-fault fn-ocfg-close fn-ocfg-advance fn-ocfg-reconfigure fn-ocfg-pass fn-ocfg-with-owner)))))
(defthm fn-ohr-step-operator-submit-preserves-carried-relation
  (implies (fn-lgoc-invariantp oc)
           (fn-lgoc-invariantp (fn-ocfg-step oc (list :operator-submit msgid groups octets stored) fn-arena)))
  :hints (("Goal" :use ((:instance fn-ohr-carried-of-same-store
                                   (x (fn-ocfg-step oc (list :operator-submit msgid groups octets stored) fn-arena))))
           :in-theory (e/d (fn-ocfg-step) (fn-ocfg-fault fn-ocfg-close fn-ocfg-advance fn-ocfg-reconfigure fn-ocfg-pass fn-ocfg-with-owner)))))
(defthm fn-ohr-step-feed-replay-preserves-carried-relation
  (implies (fn-lgoc-invariantp oc)
           (fn-lgoc-invariantp (fn-ocfg-step oc (list :feed-replay peer entries) fn-arena)))
  :hints (("Goal" :use ((:instance fn-ohr-carried-of-same-store
                                   (x (fn-ocfg-step oc (list :feed-replay peer entries) fn-arena))))
           :in-theory (e/d (fn-ocfg-step) (fn-ocfg-fault fn-ocfg-close fn-ocfg-advance fn-ocfg-reconfigure fn-ocfg-pass fn-ocfg-with-owner)))))
(defthm fn-ohr-step-control-outcome-preserves-carried-relation
  (implies (fn-lgoc-invariantp oc)
           (fn-lgoc-invariantp (fn-ocfg-step oc (list :control-outcome word) fn-arena)))
  :hints (("Goal" :use ((:instance fn-ohr-carried-of-same-store
                                   (x (fn-ocfg-step oc (list :control-outcome word) fn-arena))))
           :in-theory (e/d (fn-ocfg-step) (fn-ocfg-fault fn-ocfg-close fn-ocfg-advance fn-ocfg-reconfigure fn-ocfg-pass fn-ocfg-with-owner)))))
(defthm fn-ohr-step-bp-transit-outcome-preserves-carried-relation
  (implies (fn-lgoc-invariantp oc)
           (fn-lgoc-invariantp (fn-ocfg-step oc (list :bp-transit-outcome word) fn-arena)))
  :hints (("Goal" :use ((:instance fn-ohr-carried-of-same-store
                                   (x (fn-ocfg-step oc (list :bp-transit-outcome word) fn-arena))))
           :in-theory (e/d (fn-ocfg-step) (fn-ocfg-fault fn-ocfg-close fn-ocfg-advance fn-ocfg-reconfigure fn-ocfg-pass fn-ocfg-with-owner)))))
(defthm fn-ohr-step-feeds-preserves-carried-relation
  (implies (fn-lgoc-invariantp oc)
           (fn-lgoc-invariantp (fn-ocfg-step oc (list :feeds cfg) fn-arena)))
  :hints (("Goal" :use ((:instance fn-ohr-carried-of-same-store
                                   (x (fn-ocfg-step oc (list :feeds cfg) fn-arena))))
           :in-theory (e/d (fn-ocfg-step) (fn-ocfg-fault fn-ocfg-close fn-ocfg-advance fn-ocfg-reconfigure fn-ocfg-pass fn-ocfg-with-owner)))))
(defthm fn-ohr-step-feed-conn-preserves-carried-relation
  (implies (fn-lgoc-invariantp oc)
           (fn-lgoc-invariantp (fn-ocfg-step oc (list :feed-conn peer conn form) fn-arena)))
  :hints (("Goal" :use ((:instance fn-ohr-carried-of-same-store
                                   (x (fn-ocfg-step oc (list :feed-conn peer conn form) fn-arena))))
           :in-theory (e/d (fn-ocfg-step) (fn-ocfg-fault fn-ocfg-close fn-ocfg-advance fn-ocfg-reconfigure fn-ocfg-pass fn-ocfg-with-owner)))))
; ---------------------------------------------------------------------------
; THE OPEN establishes it.  host/owner-host.lisp fn-owner-recover-from-store-open
; installs (fn-ock-install REPLAYED OPENED max-conns) where (REPLAYED OPENED) is
; ACL2's (fn-sco-store-open E configs frontier) of the extended checkpoint E the
; Store open produced (host/store-node-host.lisp, the fn-store-sco-open global);
; fn-owner-recover-extended installs fn-ock-recover-extended of the same E.
; Both are fn-lgoc-recover-installs-invariant (PRF-286) through
; fn-ock-install-of-store-open-by-definition.

(defthm fn-ohr-with-owner-store
  (equal (fn-own-store (fn-ocfg-owner (fn-ocfg-with-owner oc o2))) (fn-own-store o2))
  :hints (("Goal" :in-theory (enable fn-ocfg-with-owner))))

(defthm fn-ohr-close-keeps-store
  (equal (fn-own-store (fn-ocfg-owner (fn-ocfg-close oc id))) (fn-own-store (fn-ocfg-owner oc)))
  :hints (("Goal" :in-theory (enable fn-ocfg-close fn-own-close))))

(defthm fn-ohr-advance-keeps-store
  (equal (fn-own-store (fn-ocfg-owner (fn-ocfg-advance oc id))) (fn-own-store (fn-ocfg-owner oc)))
  :hints (("Goal" :in-theory (enable fn-ocfg-advance fn-own-advance-result))))

(defthm fn-ohr-pass-take-keeps-store
  (implies (fn-own-shapep (fn-ocfg-owner oc))
           (equal (fn-own-store (fn-ocfg-owner (fn-ocfg-pass oc (list :take) fn-arena)))
                  (fn-own-store (fn-ocfg-owner oc))))
  :hints (("Goal" :in-theory (enable fn-ocfg-pass fn-own-step))))

(defthm fn-ohr-pass-control-submit-keeps-store
  (implies (fn-own-shapep (fn-ocfg-owner oc))
           (equal (fn-own-store (fn-ocfg-owner (fn-ocfg-pass oc (list :control-submit msgid groups octets) fn-arena)))
                  (fn-own-store (fn-ocfg-owner oc))))
  :hints (("Goal" :in-theory (enable fn-ocfg-pass fn-own-step))))

(defthm fn-ohr-pass-operator-submit-keeps-store
  (implies (fn-own-shapep (fn-ocfg-owner oc))
           (equal (fn-own-store (fn-ocfg-owner (fn-ocfg-pass oc (list :operator-submit msgid groups octets stored) fn-arena)))
                  (fn-own-store (fn-ocfg-owner oc))))
  :hints (("Goal" :in-theory (enable fn-ocfg-pass fn-own-step))))

(defthm fn-ohr-pass-feed-replay-keeps-store
  (implies (fn-own-shapep (fn-ocfg-owner oc))
           (equal (fn-own-store (fn-ocfg-owner (fn-ocfg-pass oc (list :feed-replay peer entries) fn-arena)))
                  (fn-own-store (fn-ocfg-owner oc))))
  :hints (("Goal" :in-theory (enable fn-ocfg-pass fn-own-step))))

(defthm fn-ohr-pass-control-outcome-keeps-store
  (implies (fn-own-shapep (fn-ocfg-owner oc))
           (equal (fn-own-store (fn-ocfg-owner (fn-ocfg-pass oc (list :control-outcome word) fn-arena)))
                  (fn-own-store (fn-ocfg-owner oc))))
  :hints (("Goal" :in-theory (enable fn-ocfg-pass fn-own-step))))

(defthm fn-ohr-pass-bp-transit-outcome-keeps-store
  (implies (fn-own-shapep (fn-ocfg-owner oc))
           (equal (fn-own-store (fn-ocfg-owner (fn-ocfg-pass oc (list :bp-transit-outcome word) fn-arena)))
                  (fn-own-store (fn-ocfg-owner oc))))
  :hints (("Goal" :in-theory (enable fn-ocfg-pass fn-own-step))))

(defthm fn-ohr-pass-feeds-keeps-store
  (implies (fn-own-shapep (fn-ocfg-owner oc))
           (equal (fn-own-store (fn-ocfg-owner (fn-ocfg-pass oc (list :feeds cfg) fn-arena)))
                  (fn-own-store (fn-ocfg-owner oc))))
  :hints (("Goal" :in-theory (enable fn-ocfg-pass fn-own-step))))

(defthm fn-ohr-pass-feed-conn-keeps-store
  (implies (fn-own-shapep (fn-ocfg-owner oc))
           (equal (fn-own-store (fn-ocfg-owner (fn-ocfg-pass oc (list :feed-conn peer conn form) fn-arena)))
                  (fn-own-store (fn-ocfg-owner oc))))
  :hints (("Goal" :in-theory (enable fn-ocfg-pass fn-own-step))))

(defthm fn-ohr-fault-preserves-carried-relation
  (implies (fn-lgoc-invariantp oc)
           (fn-lgoc-invariantp (cdr (fn-ocfg-fault oc id))))
  :hints (("Goal" :use ((:instance fn-ohr-carried-of-same-store (x (cdr (fn-ocfg-fault oc id)))))
           :in-theory (disable fn-ocfg-fault fn-ocfg-close fn-ocfg-advance fn-ocfg-reconfigure fn-ocfg-pass fn-ocfg-with-owner fn-lgoc-invariantp fn-osb-install fn-bs-profile-admittedp))))

(defthm fn-ohr-reconfigure-preserves-carried-relation
  (implies (fn-lgoc-invariantp oc)
           (fn-lgoc-invariantp (fn-ocfg-reconfigure oc id deltas)))
  :hints (("Goal" :use ((:instance fn-ohr-carried-of-same-store (x (fn-ocfg-reconfigure oc id deltas))))
           :in-theory (disable fn-ocfg-fault fn-ocfg-close fn-ocfg-advance fn-ocfg-reconfigure fn-ocfg-pass fn-ocfg-with-owner fn-lgoc-invariantp fn-osb-install fn-bs-profile-admittedp))))

(defthm fn-ohr-configure-preserves-carried-relation
  (implies (fn-lgoc-invariantp oc)
           (fn-lgoc-invariantp (fn-ocfg-with-owner oc (fn-own-configure (fn-ocfg-owner oc) config))))
  :hints (("Goal" :use ((:instance fn-ohr-carried-of-same-store (x (fn-ocfg-with-owner oc (fn-own-configure (fn-ocfg-owner oc) config)))))
           :in-theory (disable fn-ocfg-fault fn-ocfg-close fn-ocfg-advance fn-ocfg-reconfigure fn-ocfg-pass fn-ocfg-with-owner fn-lgoc-invariantp fn-osb-install fn-bs-profile-admittedp))))

(defthm fn-ohr-with-feeds-preserves-carried-relation
  (implies (fn-lgoc-invariantp oc)
           (fn-lgoc-invariantp (fn-ocfg-with-owner oc (fn-own-with-feeds (fn-ocfg-owner oc) feeds))))
  :hints (("Goal" :use ((:instance fn-ohr-carried-of-same-store (x (fn-ocfg-with-owner oc (fn-own-with-feeds (fn-ocfg-owner oc) feeds)))))
           :in-theory (disable fn-ocfg-fault fn-ocfg-close fn-ocfg-advance fn-ocfg-reconfigure fn-ocfg-pass fn-ocfg-with-owner fn-lgoc-invariantp fn-osb-install fn-bs-profile-admittedp))))

(defthm fn-ohr-with-node-secret-preserves-carried-relation
  (implies (fn-lgoc-invariantp oc)
           (fn-lgoc-invariantp (fn-ocfg-with-owner oc (fn-own-with-node-secret (fn-ocfg-owner oc) secret))))
  :hints (("Goal" :use ((:instance fn-ohr-carried-of-same-store (x (fn-ocfg-with-owner oc (fn-own-with-node-secret (fn-ocfg-owner oc) secret)))))
           :in-theory (disable fn-ocfg-fault fn-ocfg-close fn-ocfg-advance fn-ocfg-reconfigure fn-ocfg-pass fn-ocfg-with-owner fn-lgoc-invariantp fn-osb-install fn-bs-profile-admittedp))))

(defthm fn-ohr-osb-install-preserves-carried-relation
  (implies (fn-lgoc-invariantp oc)
           (fn-lgoc-invariantp (fn-ocfg-with-owner oc (mv-nth 1 (fn-osb-install (fn-ocfg-owner oc) profile)))))
  :hints (("Goal" :use ((:instance fn-ohr-carried-of-same-store (x (fn-ocfg-with-owner oc (mv-nth 1 (fn-osb-install (fn-ocfg-owner oc) profile))))))
           :in-theory (disable fn-ocfg-fault fn-ocfg-close fn-ocfg-advance fn-ocfg-reconfigure fn-ocfg-pass fn-ocfg-with-owner fn-lgoc-invariantp fn-osb-install fn-bs-profile-admittedp))))

(defthm fn-ohr-step-reconfigure-preserves-carried-relation
  (implies (fn-lgoc-invariantp oc)
           (fn-lgoc-invariantp (fn-ocfg-step oc (list :reconfigure id deltas) fn-arena)))
  :hints (("Goal" :use ((:instance fn-ohr-carried-of-same-store
                                   (x (fn-ocfg-step oc (list :reconfigure id deltas) fn-arena))))
           :in-theory (e/d (fn-ocfg-step) (fn-ocfg-fault fn-ocfg-close fn-ocfg-advance fn-ocfg-reconfigure fn-ocfg-pass fn-ocfg-with-owner fn-lgoc-invariantp)))))

(defthm fn-ohr-step-close-preserves-carried-relation
  (implies (fn-lgoc-invariantp oc)
           (fn-lgoc-invariantp (fn-ocfg-step oc (list :close id) fn-arena)))
  :hints (("Goal" :use ((:instance fn-ohr-carried-of-same-store
                                   (x (fn-ocfg-step oc (list :close id) fn-arena))))
           :in-theory (e/d (fn-ocfg-step) (fn-ocfg-fault fn-ocfg-close fn-ocfg-advance fn-ocfg-reconfigure fn-ocfg-pass fn-ocfg-with-owner fn-lgoc-invariantp)))))

(defthm fn-ohr-step-advance-preserves-carried-relation
  (implies (fn-lgoc-invariantp oc)
           (fn-lgoc-invariantp (fn-ocfg-step oc (list :advance id) fn-arena)))
  :hints (("Goal" :use ((:instance fn-ohr-carried-of-same-store
                                   (x (fn-ocfg-step oc (list :advance id) fn-arena)))
                 fn-ocl-advance-preserves-historical-relation)
           :in-theory (e/d (fn-ocfg-step) (fn-ocfg-fault fn-ocfg-close fn-ocfg-advance fn-ocfg-reconfigure fn-ocfg-pass fn-ocfg-with-owner fn-lgoc-invariantp)))))

(defthm fn-ohr-step-take-preserves-carried-relation
  (implies (fn-lgoc-invariantp oc)
           (fn-lgoc-invariantp (fn-ocfg-step oc (list :take) fn-arena)))
  :hints (("Goal" :use ((:instance fn-ohr-carried-of-same-store
                                   (x (fn-ocfg-step oc (list :take) fn-arena))))
           :in-theory (e/d (fn-ocfg-step) (fn-ocfg-fault fn-ocfg-close fn-ocfg-advance fn-ocfg-reconfigure fn-ocfg-pass fn-ocfg-with-owner fn-lgoc-invariantp)))))

(defthm fn-ohr-step-control-submit-preserves-carried-relation
  (implies (fn-lgoc-invariantp oc)
           (fn-lgoc-invariantp (fn-ocfg-step oc (list :control-submit msgid groups octets) fn-arena)))
  :hints (("Goal" :use ((:instance fn-ohr-carried-of-same-store
                                   (x (fn-ocfg-step oc (list :control-submit msgid groups octets) fn-arena))))
           :in-theory (e/d (fn-ocfg-step) (fn-ocfg-fault fn-ocfg-close fn-ocfg-advance fn-ocfg-reconfigure fn-ocfg-pass fn-ocfg-with-owner fn-lgoc-invariantp)))))

(defthm fn-ohr-step-operator-submit-preserves-carried-relation
  (implies (fn-lgoc-invariantp oc)
           (fn-lgoc-invariantp (fn-ocfg-step oc (list :operator-submit msgid groups octets stored) fn-arena)))
  :hints (("Goal" :use ((:instance fn-ohr-carried-of-same-store
                                   (x (fn-ocfg-step oc (list :operator-submit msgid groups octets stored) fn-arena))))
           :in-theory (e/d (fn-ocfg-step) (fn-ocfg-fault fn-ocfg-close fn-ocfg-advance fn-ocfg-reconfigure fn-ocfg-pass fn-ocfg-with-owner fn-lgoc-invariantp)))))

(defthm fn-ohr-step-feed-replay-preserves-carried-relation
  (implies (fn-lgoc-invariantp oc)
           (fn-lgoc-invariantp (fn-ocfg-step oc (list :feed-replay peer entries) fn-arena)))
  :hints (("Goal" :use ((:instance fn-ohr-carried-of-same-store
                                   (x (fn-ocfg-step oc (list :feed-replay peer entries) fn-arena))))
           :in-theory (e/d (fn-ocfg-step) (fn-ocfg-fault fn-ocfg-close fn-ocfg-advance fn-ocfg-reconfigure fn-ocfg-pass fn-ocfg-with-owner fn-lgoc-invariantp)))))

(defthm fn-ohr-step-control-outcome-preserves-carried-relation
  (implies (fn-lgoc-invariantp oc)
           (fn-lgoc-invariantp (fn-ocfg-step oc (list :control-outcome word) fn-arena)))
  :hints (("Goal" :use ((:instance fn-ohr-carried-of-same-store
                                   (x (fn-ocfg-step oc (list :control-outcome word) fn-arena))))
           :in-theory (e/d (fn-ocfg-step) (fn-ocfg-fault fn-ocfg-close fn-ocfg-advance fn-ocfg-reconfigure fn-ocfg-pass fn-ocfg-with-owner fn-lgoc-invariantp)))))

(defthm fn-ohr-step-bp-transit-outcome-preserves-carried-relation
  (implies (fn-lgoc-invariantp oc)
           (fn-lgoc-invariantp (fn-ocfg-step oc (list :bp-transit-outcome word) fn-arena)))
  :hints (("Goal" :use ((:instance fn-ohr-carried-of-same-store
                                   (x (fn-ocfg-step oc (list :bp-transit-outcome word) fn-arena))))
           :in-theory (e/d (fn-ocfg-step) (fn-ocfg-fault fn-ocfg-close fn-ocfg-advance fn-ocfg-reconfigure fn-ocfg-pass fn-ocfg-with-owner fn-lgoc-invariantp)))))

(defthm fn-ohr-step-feeds-preserves-carried-relation
  (implies (fn-lgoc-invariantp oc)
           (fn-lgoc-invariantp (fn-ocfg-step oc (list :feeds cfg) fn-arena)))
  :hints (("Goal" :use ((:instance fn-ohr-carried-of-same-store
                                   (x (fn-ocfg-step oc (list :feeds cfg) fn-arena))))
           :in-theory (e/d (fn-ocfg-step) (fn-ocfg-fault fn-ocfg-close fn-ocfg-advance fn-ocfg-reconfigure fn-ocfg-pass fn-ocfg-with-owner fn-lgoc-invariantp)))))

(defthm fn-ohr-step-feed-conn-preserves-carried-relation
  (implies (fn-lgoc-invariantp oc)
           (fn-lgoc-invariantp (fn-ocfg-step oc (list :feed-conn peer conn form) fn-arena)))
  :hints (("Goal" :use ((:instance fn-ohr-carried-of-same-store
                                   (x (fn-ocfg-step oc (list :feed-conn peer conn form) fn-arena))))
           :in-theory (e/d (fn-ocfg-step) (fn-ocfg-fault fn-ocfg-close fn-ocfg-advance fn-ocfg-reconfigure fn-ocfg-pass fn-ocfg-with-owner fn-lgoc-invariantp)))))

; ---------------------------------------------------------------------------
; THE OPEN establishes it.  host/owner-host.lisp fn-owner-recover-from-store-open
; installs (fn-ock-install REPLAYED OPENED max-conns) where (REPLAYED OPENED) is
; ACL2's (fn-sco-store-open E configs frontier) of the extended checkpoint E the
; Store open produced (host/store-node-host.lisp, the fn-store-sco-open global);
; fn-owner-recover-extended installs fn-ock-recover-extended of the same E.
; Both are fn-lgoc-recover-installs-invariant (PRF-286) through
; fn-ock-install-of-store-open-by-definition.
(defthm fn-ohr-store-open-installs-the-carried-relation
  (let* ((e (fn-sco-extend (fn-sco-capture configs prefix) configs suffix))
         (opened (fn-sco-store-open e configs frontier))
         (oc (fn-ock-install (car opened) (cadr opened) max-conns)))
    (implies (not (equal oc :fault))
             (fn-lgoc-invariantp oc)))
  :hints (("Goal" :use ((:instance fn-ock-install-of-store-open-by-definition
                                   (e (fn-sco-extend (fn-sco-capture configs prefix) configs suffix)))
                        fn-lgoc-recover-installs-invariant)
           :in-theory (disable fn-ock-install fn-sco-store-open fn-ock-recover-extended
                               fn-sco-extend fn-sco-capture fn-lgoc-invariantp))))
