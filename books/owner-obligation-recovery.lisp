; W9 cold initialization and atomic reclaim swap over the actual host entries.
(in-package "ACL2")
(include-book "owner-recovery-retain")
(include-book "owner-obligation-writers")

(defthm fn-rov-swapped-ledger-is-rebuilt-ledger
  (equal (fn-rov-oc-ledger (fn-orcp-swapped-ocfg live rebuilt))
         (fn-rov-oc-ledger rebuilt))
  :hints (("Goal" :in-theory
           (e/d (fn-rov-oc-ledger fn-orcp-swapped-ocfg fn-orcp-swapped-owner
                  fn-orcp-swap-base fn-own-set-conns)
                (fn-orcp-repin-conns)))))

(defthm fn-owner-orcp-swap-installs-obligation-view
  (equal (fn-owner-obligation-view (mv-nth 2 (fn-owner-orcp-swap rebuilt state)))
         (nth 6 rebuilt))
  :hints (("Goal" :in-theory
           (e/d (fn-owner-orcp-swap fn-owner-retain-carry-put fn-owner-put-credits)
                (put-global fn-owner-install-rebuilt-ocfg fn-orcp-swapped-ocfg
                 fn-orcp-release fn-owner-credits)))))

(defthm fn-owner-orcp-swap-installs-obligation-ledger
  (equal (fn-rov-owner-ledger (mv-nth 2 (fn-owner-orcp-swap rebuilt state)))
         (fn-rov-oc-ledger (nth 1 rebuilt)))
  :hints (("Goal" :in-theory
           (e/d (fn-owner-orcp-swap fn-owner-retain-carry-put fn-owner-put-credits)
                (put-global fn-rov-owner-ledger-is-oc-ledger
                 fn-owner-install-rebuilt-ocfg fn-orcp-swapped-ocfg
                 fn-orcp-release fn-owner-credits)))))

(defthm fn-owner-orcp-swap-establishes-obligation-correspondence
  (implies (fn-rov-correspondp (nth 6 rebuilt)
             (fn-retain-pins (fn-rov-oc-ledger (nth 1 rebuilt))))
           (fn-rov-owner-correspondp (mv-nth 2 (fn-owner-orcp-swap rebuilt state))))
  :hints (("Goal" :in-theory
           (e/d (fn-owner-orcp-swap fn-owner-retain-carry-put fn-owner-put-credits)
                (put-global fn-owner-install-rebuilt-ocfg fn-orcp-swapped-ocfg
                 fn-orcp-release fn-owner-credits fn-rov-owner-correspondp
                 fn-rov-owner-ledger-is-oc-ledger)))))

(defthm fn-owner-install-extended-establishes-obligation-correspondence
  (implies (and (not (equal oc :fault))
                (fn-onb-open-okp (fn-ocfg-owner oc)))
           (fn-rov-owner-correspondp
            (mv-nth 5 (fn-owner-install-extended
                       oc extended key fn-arena fn-cat fn-hist state))))
  :hints (("Goal" :in-theory
           (e/d (fn-owner-install-extended fn-owner-retain-carry-put)
                (put-global fn-onb-open-okp fn-owner-install-open-ocfg fn-rov-owner-correspondp
                 fn-rov-oc-ledger fn-sca-load-held-rows-keyed fn-hist-load)))))

; Connect the actual rebuild producer to the actual swap entry. Its recovered
; success is explicit: no arbitrary host-built view is trusted.
(defthm fn-owner-rebuild-then-swap-establishes-obligation-view
  (let ((rebuilt (fn-owner-orcp-rebuild rows configs frontier max-conns)))
    (implies (not (equal (nth 1 rebuilt) :fault))
             (fn-rov-owner-correspondp
              (mv-nth 2 (fn-owner-orcp-swap rebuilt state)))))
  :hints (("Goal" :use ((:instance fn-owner-orcp-rebuild-establishes-obligation-view))
           :in-theory (e/d (fn-rov-oc-ledger)
                           (fn-owner-orcp-rebuild fn-owner-orcp-swap
                            fn-sn-statep fn-rov-owner-correspondp fn-rov-correspondp)))))
