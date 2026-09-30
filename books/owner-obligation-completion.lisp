; W9 preservation at the actual durable completion entry.
; Direct carried-path proof: no history abstraction or carry-validity premise
; is needed for this projection. Actual executable guards remain unchanged.
(in-package "ACL2")
(include-book "owner-obligation-writers")

(defthm fn-rov-identity-neutral-keeps-ledger
  (implies (consp (fn-replay-apply-identity-neutral node record))
           (equal (fn-node-retention (fn-replay-apply-identity-neutral node record))
                  (fn-node-retention node)))
  :hints (("Goal" :in-theory (enable fn-replay-apply-identity-neutral))))

(defthm fn-rov-carried-node-prepare-keeps-ledger
 (equal (fn-node-retention
         (fn-irc-node-prepare s generation msgid payload groups id subject evidence charge stamp carry binding))
        (fn-node-retention s))
 :hints (("Goal" :in-theory
          (e/d (fn-irc-node-prepare)
               (fn-node-statep fn-prc-admissiblep fn-accept-prepare fn-node-make-stage)))))
(defthm fn-rov-retention-of-carried-retention-event
  (implies (consp (fn-irc-apply-retention-event node event carry))
           (equal (fn-node-retention (fn-irc-apply-retention-event node event carry))
                  (if (equal (fn-store-event-kind event) :undertake)
                      (fn-retain-admit (fn-node-retention node)
                       (fn-store-event-obligation-id event) (fn-store-event-subject event)
                       :forward (fn-store-event-evidence event) (fn-store-event-charge event))
                    (fn-retain-release (fn-node-retention node)
                     (fn-store-event-obligation-id event) (fn-store-event-subject event)
                     :forward (fn-store-event-evidence event)))))
  :hints (("Goal" :in-theory (e/d (fn-irc-apply-retention-event fn-replay-complete-retention)
                           (fn-retain-admit fn-retain-release fn-retain-admissiblep fn-node-statep)))))

(defthm fn-rov-carried-retention-event-preserves-correspondence
  (implies (and (fn-node-statep node)
                (consp (fn-irc-apply-retention-event node event carry))
                (fn-rov-correspondp view (fn-retain-pins (fn-node-retention node))))
           (fn-rov-correspondp
            (fn-rov-update (fn-node-retention node)
             (fn-node-retention (fn-irc-apply-retention-event node event carry)) view)
            (fn-retain-pins (fn-node-retention (fn-irc-apply-retention-event node event carry)))))
  :hints (("Goal" :in-theory (disable fn-node-statep fn-rov-correspondp
                                     fn-irc-apply-retention-event fn-retain-admit fn-retain-release))))

(defthm fn-rov-carried-record-preserves-correspondence
  (implies (and (fn-node-statep node)
                (consp (fn-irc-apply-record node record carry))
                (fn-rov-correspondp view (fn-retain-pins (fn-node-retention node))))
           (fn-rov-correspondp
            (fn-rov-update (fn-node-retention node)
             (fn-node-retention (fn-irc-apply-record node record carry)) view)
            (fn-retain-pins (fn-node-retention (fn-irc-apply-record node record carry)))))
  :hints (("Goal"
           :use ((:instance fn-rov-node-complete-preserves-correspondence
                   (node (fn-irc-node-prepare
                          (fn-replay-advance-txid node (fn-store-event-txid record))
                          (fn-record-generation (if (fn-hstxa-p record) (fn-replay-composite-held record) record))
                          (fn-record-msgid (if (fn-hstxa-p record) (fn-replay-composite-held record) record))
                          (fn-record-payload (if (fn-hstxa-p record) (fn-replay-composite-held record) record))
                          (fn-record-groups (if (fn-hstxa-p record) (fn-replay-composite-held record) record))
                          (fn-record-obligation-id (if (fn-hstxa-p record) (fn-replay-composite-held record) record))
                          (fn-record-content-subject (if (fn-hstxa-p record) (fn-replay-composite-held record) record))
                          (fn-record-release-evidence (if (fn-hstxa-p record) (fn-replay-composite-held record) record))
                          (fn-record-charge (if (fn-hstxa-p record) (fn-replay-composite-held record) record))
                          (fn-record-stamp (if (fn-hstxa-p record) (fn-replay-composite-held record) record)) carry (fn-held-binding (if (fn-hstxa-p record) (fn-replay-composite-held record) record))))
                   (txid (fn-record-txid (if (fn-hstxa-p record) (fn-replay-composite-held record) record)))
                   (generation (fn-record-generation (if (fn-hstxa-p record) (fn-replay-composite-held record) record)))
                   (status :durable)))
           :in-theory
           (e/d (fn-irc-apply-record fn-rov-carried-node-prepare-keeps-ledger)
                (fn-node-statep fn-rov-correspondp fn-node-complete fn-irc-node-prepare
                 fn-node-durable-completion-promotes-matching-stage
                 fn-node-pending-matchesp fn-replay-apply-identity-neutral
                 fn-irc-apply-retention-event fn-held-p fn-record-p fn-stxa-p fn-hstxa-p
                 fn-store-retention-event-p fn-stxe-p fn-stxk-p fn-cpe-eventp fn-th-topic-eventp)))))

(local
 (defthm fn-rov-node-of-make-v6
   (equal (fn-sn-node
           (fn-sn-make-v6 groups capacity files node keyring index
                          keyring-generation verdicts snapshots identity-next
                          config-history consumer topic event-index))
          node)
   :hints (("Goal" :in-theory (enable fn-sn-make-v6 fn-sn-node)))))
(local
 (defthm fn-rov-node-of-sn-with-consumer
   (equal (fn-sn-node (fn-sn-with-consumer s consumer)) (fn-sn-node s))
   :hints (("Goal" :in-theory '(fn-sn-with-consumer fn-rov-node-of-make-v6)))))
(local
 (defthm fn-rov-node-of-sn-with-topic
   (equal (fn-sn-node (fn-sn-with-topic s topic)) (fn-sn-node s))
   :hints (("Goal" :in-theory '(fn-sn-with-topic fn-rov-node-of-make-v6)))))
(local
 (defthm fn-rov-node-of-sn-advance-identity-next
   (equal (fn-sn-node (fn-sn-advance-identity-next s)) (fn-sn-node s))
   :hints (("Goal" :in-theory '(fn-sn-advance-identity-next fn-rov-node-of-make-v6)))))
(local
 (defthm fn-rov-node-of-sn-update-indexed
   (equal (fn-sn-node (fn-sn-update-indexed s files node index)) node)
   :hints (("Goal" :in-theory '(fn-sn-update-indexed fn-rov-node-of-make-v6)))))
(local
 (defthm fn-rov-node-of-sn-update-accepted
   (equal (fn-sn-node (fn-sn-update-accepted s files node index msgid verdict)) node)
   :hints (("Goal" :in-theory '(fn-sn-update-accepted fn-rov-node-of-make-v6)))))
(local
 (defthm fn-rov-node-of-sn-finish-identity
   (equal (fn-sn-node (fn-sn-finish-identity s files record node)) node)
   :hints (("Goal" :in-theory '(fn-sn-finish-identity fn-rov-node-of-make-v6)))))

(defthm fn-rov-store-of-indexed-refresh
  (equal (fn-own-store (fn-own-refresh-ix owner fn-hist))
         (fn-own-store owner))
  :hints (("Goal" :in-theory (enable fn-own-refresh-ix))))

(defthm fn-rov-carried-finish-preserves-correspondence
  (implies (and (fn-irc-completion-enabledp s carry)
                (fn-rov-correspondp view (fn-retain-pins (fn-node-retention (fn-sn-node s)))))
           (fn-rov-correspondp
            (fn-rov-update (fn-node-retention (fn-sn-node s))
             (fn-node-retention (fn-sn-node (fn-irc-sn-finish-enabled s carry))) view)
            (fn-retain-pins (fn-node-retention (fn-sn-node (fn-irc-sn-finish-enabled s carry))))))
  :hints (("Goal" :in-theory
           (e/d (fn-irc-sn-finish-enabled fn-irc-completion-enabledp
                 fn-irc-completion-core-enabledp)
                (fn-sn-statep fn-node-statep fn-rov-correspondp
                 fn-evc-carried-definitions fn-record-record-vocabulary fn-record-shape-vocabulary
                 fn-store-retention-event-p fn-stxe-p fn-stxk-p fn-stxa-p fn-hstxa-p
                 fn-held-p fn-record-p fn-cpe-eventp fn-th-topic-eventp
                 fn-irc-sn-finish-enabled-is-ccar fn-irc-completion-enabledp-is-ccar
                 fn-irc-completion-core-enabledp-is-ccar
                 fn-node-complete fn-replay-apply-record fn-replay-apply-retention-event
                 fn-irc-apply-record fn-irc-apply-retention-event
                 fn-irc-apply-record-is-replay-apply-record fn-irc-apply-retention-event-is-reference
                 fn-ccar-cpe-projection-step fn-ccar-th-prefix-step
                 fn-node-durable-completion-promotes-matching-stage)))))

(defthm fn-rov-configured-completion-preserves-correspondence
  (implies (fn-rov-correspondp view (fn-retain-pins (fn-rov-oc-ledger oc)))
           (fn-rov-correspondp
            (fn-rov-update (fn-rov-oc-ledger oc)
             (fn-rov-oc-ledger (fn-irc-rix-ocfg-complete oc fn-hist carry)) view)
            (fn-retain-pins (fn-rov-oc-ledger (fn-irc-rix-ocfg-complete oc fn-hist carry)))))
  :hints (("Goal" :in-theory
           (e/d (fn-rov-oc-ledger fn-irc-rix-ocfg-complete
                 fn-irc-rix-own-complete fn-irc-rix-own-complete-enabled)
                (fn-sn-statep fn-prc-carryp fn-rov-correspondp
                 fn-irc-completion-enabledp fn-irc-sn-finish-enabled
                 fn-own-refresh-ix fn-irc-rix-ocfg-complete-is-rix
                 fn-irc-rix-own-complete-is-rix fn-irc-rix-own-complete-enabled-is-rix
                 fn-irc-sn-finish-enabled-is-ccar fn-irc-completion-enabledp-is-ccar)))))

(defthm fn-owner-finish-synced-preserves-obligation-view
  (implies (fn-rov-owner-correspondp state)
           (fn-rov-owner-correspondp (mv-nth 2 (fn-owner-finish-synced fn-hist state))))
  :hints (("Goal" :in-theory
           (e/d (fn-owner-finish-synced fn-owner-retain-carry-put fn-rov-owner-correspondp)
                (put-global fn-owner-install-ocfg
                 fn-sn-statep fn-irc-rix-ocfg-complete fn-irc-rix-ocfg-complete-is-rix fn-prc-refresh)))))
