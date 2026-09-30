; W9 preservation over the actual logical host entry points. The host calls
; these same functions from owner-retain-transitions; there is no adapter twin.
(in-package "ACL2")
(include-book "owner-retain-transitions")
(include-book "retention-obligation-view-node")

(defthm fn-rov-node-of-identity-prepare
  (equal (fn-sn-node (fn-irc-sn-prepare-identity s event carry))
         (fn-sn-node s))
  :hints (("Goal" :in-theory (e/d (fn-irc-sn-prepare-identity fn-sn-update)
                           (fn-sn-statep fn-pcar-stage-record
                            fn-irc-apply-record fn-replay-identity-step)))))

(defthm fn-rov-ledger-of-identity-prepare
  (equal (fn-rov-oc-ledger
           (mv-nth 1 (fn-irc-pout-prepare-identity oc event h carry)))
         (fn-rov-oc-ledger oc))
  :hints (("Goal" :in-theory
           (e/d (fn-rov-oc-ledger fn-irc-pout-prepare-identity
                  fn-irc-oiis-prepare-identity fn-irc-psrv-prepare-identity
                  fn-irc-ocfg-prepare-identity fn-ocfg-with-owner
                  fn-own-refresh-keeps-fields fn-own-store-of-fn-own-make)
                (fn-irc-sn-prepare-identity fn-own-refresh fn-own-make
                 fn-oii-identity-row fn-pout-identity-refusal-kind fn-pout-stagedp)))))

(defthm fn-rov-owner-correspondence-of-other-global-put
  (implies (and (not (equal key 'fn-owner))
                (not (equal key 'fn-owner-obligation-view)))
           (equal (fn-rov-owner-correspondp (f-put-global key value state))
                  (fn-rov-owner-correspondp state)))
  :hints (("Goal" :in-theory (enable fn-rov-owner-correspondp fn-rov-owner-ledger fn-owner-obligation-view))))

(defthm fn-rov-owner-ledger-is-oc-ledger
  (implies (boundp-global 'fn-owner state)
           (equal (fn-rov-owner-ledger state)
                  (fn-rov-oc-ledger (fn-owner-ocfg state))))
  :hints (("Goal" :in-theory (enable fn-rov-owner-ledger fn-owner-ocfg))))

(defthm fn-rov-owner-correspondence-implies-bound
  (implies (fn-rov-owner-correspondp state) (boundp-global 'fn-owner state))
  :hints (("Goal" :in-theory (enable fn-rov-owner-correspondp))))

(defthm fn-rov-owner-ledger-of-other-global-put
  (implies (not (equal key 'fn-owner))
           (equal (fn-rov-owner-ledger (f-put-global key value state))
                  (fn-rov-owner-ledger state)))
  :hints (("Goal" :in-theory (enable fn-rov-owner-ledger))))

(defthm fn-owner-prepare-identity-preserves-obligation-view
  (implies (fn-rov-owner-correspondp state)
           (fn-rov-owner-correspondp
            (mv-nth 2 (fn-owner-prepare-identity event fn-arena state))))
  :hints (("Goal" :in-theory
           (e/d (fn-owner-prepare-identity fn-owner-retain-carry-put)
                (put-global fn-irc-pout-prepare-identity fn-oii-identity-row
                 fn-owner-install-ocfg fn-owner-obligation-view-put
                 fn-rov-oc-ledger fn-rov-owner-ledger fn-rov-owner-correspondp)))))

(defthm fn-owner-prepare-identity-keeps-obligation-view
  (implies (boundp-global 'fn-owner state)
           (equal (fn-owner-obligation-view
                   (mv-nth 2 (fn-owner-prepare-identity event fn-arena state)))
                  (fn-owner-obligation-view state)))
  :hints (("Goal" :in-theory
           (e/d (fn-owner-prepare-identity fn-owner-retain-carry-put)
                (put-global fn-irc-pout-prepare-identity fn-oii-identity-row
                 fn-owner-install-ocfg fn-owner-obligation-view-put
                 fn-rov-oc-ledger fn-rov-owner-ledger fn-rov-owner-correspondp)))))

(defthm fn-owner-prepare-identity-keeps-obligation-ledger
  (implies (boundp-global 'fn-owner state)
           (equal (fn-rov-owner-ledger
                   (mv-nth 2 (fn-owner-prepare-identity event fn-arena state)))
                  (fn-rov-owner-ledger state)))
  :hints (("Goal" :in-theory
           (e/d (fn-owner-prepare-identity fn-owner-retain-carry-put)
                (put-global fn-irc-pout-prepare-identity fn-oii-identity-row
                 fn-owner-install-ocfg fn-owner-obligation-view-put
                 fn-rov-oc-ledger fn-rov-owner-ledger fn-rov-owner-correspondp)))))

(defthm fn-rov-owner-open-ledger
  (equal (fn-rov-owner-ledger (fn-owner-install-open-ocfg oc state))
         (fn-rov-oc-ledger oc))
  :hints (("Goal" :in-theory (e/d (fn-owner-install-open-ocfg)
                           (fn-rov-owner-ledger-is-oc-ledger)))))

(defthm fn-rov-owner-ledger-of-view-put
  (equal (fn-rov-owner-ledger (fn-owner-obligation-view-put view state))
         (fn-rov-owner-ledger state))
  :hints (("Goal" :in-theory (e/d (fn-owner-obligation-view-put)
                                 (put-global fn-rov-owner-ledger-is-oc-ledger)))))
(defthm fn-rov-owner-bound-of-view-put
  (equal (boundp-global 'fn-owner (fn-owner-obligation-view-put view state))
         (boundp-global 'fn-owner state))
  :hints (("Goal" :in-theory (e/d (fn-owner-obligation-view-put)
                                 (put-global boundp-global)))))
