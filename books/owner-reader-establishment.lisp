(in-package "ACL2")
(include-book "config-owner-read-invariants")
(include-book "owner-checkpoint-open")

; Establish the historical reader premise at the actual checkpoint recovery entry.
; Private facts connect the existing live-owner relation to the initial view.
(local (defthm fn-orri-started-view-verdicts
  (implies (fn-sn-statep store)
           (fn-sn-verdict-listp
            (fn-own-view-verdicts
             (fn-own-view (fn-own-configure (fn-own-start store max-conns) post)))))
  :hints (("Goal"
           :in-theory
           (e/d (fn-own-start fn-own-refresh fn-own-configure fn-sn-statep)
                (fn-own-prefix-archive fn-ctl-visible-state fn-ctl-visible-state-of
                 fn-ctl-refresh-visible fn-ctl-refresh-withdrawals
                 fn-ctl-refresh-withdrawn fn-midx-build fn-midx-refresh
                 fn-gidx-build fn-gidx-refresh fn-ctl-subseq-diff
                 fn-node-statep fn-sf-statep fn-statep
                 fn-own-store-idlep fn-sn-verdict-listp))))))
(local (defthm fn-orri-related-store-is-statep
  (implies (fn-ocl-relation oc)
           (fn-sn-statep (fn-own-store (fn-ocfg-owner oc))))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
                           '(fn-ocl-relation fn-cst-relation))))))

(defthm fn-orri-recover-installs-historical-reader-relation
  (let ((oc (fn-ock-recover-extended
             (fn-sco-extend (fn-sco-capture configs prefix) configs suffix)
             configs frontier max-conns)))
    (implies (not (equal oc :fault))
             (fn-ocri-relation oc)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-orri-related-store-is-statep
                           (oc (fn-ock-recover-full configs frontier (append prefix suffix) max-conns)))
                 fn-ock-recover-installs-ocl-relation
                 fn-owner-recover-from-checkpoint-equals-full-recover
                 (:instance fn-cpo-open-success-exact-image (events (append prefix suffix)))
                 (:instance fn-orri-started-view-verdicts
                  (store (fn-sn-open-state
                          (fn-cpo-open-observed configs frontier (append prefix suffix))))
                  (post (fn-oag-post-config
                         (fn-cnode-config
                          (fn-replay-result-node
                           (fn-cpr-replay configs (append prefix suffix))))
                         *fn-record-max-payload*)))
                 (:instance fn-orec-started-owner-fields-unfold
                  (st (fn-sn-open-state
                       (fn-cpo-open-observed configs frontier (append prefix suffix))))
                  (post (fn-oag-post-config
                         (fn-cnode-config
                          (fn-replay-result-node
                           (fn-cpr-replay configs (append prefix suffix))))
                         *fn-record-max-payload*))))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(fn-ocri-relation fn-ocri-viewp fn-ocri-conns-p
              fn-scar-view-indexedp fn-owner-recover-from-checkpoint-equals-full-recover fn-ock-recover-full fn-ock-install
              fn-ocfg-owner fn-ocfg-make fn-sn-open-okp car-cons cdr-cons
              fn-orri-related-store-is-statep
              fn-orri-started-view-verdicts)))))
