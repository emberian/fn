; Guard closure for the exact D1b transition and read-only observation
; selectors called by the native BP service and node caller.
(in-package "ACL2")
(include-book "bp-node-fragment-guards")
(include-book "bp-report-observe")

(verify-guards fn-bpn-report-delete-record)
(verify-guards fn-bpn-report-delete-with-intent)
(verify-guards fn-bpnf-delete-values)
(verify-guards fn-bpnf-delete-frame)
(local
 (defthm fn-bpnrg-pending-has-heldp
   (implies (fn-bpn-report-held-delete-pendingp held)
            (fn-bpnf-heldp held))
   :hints (("Goal" :in-theory (e/d (fn-bpn-report-held-delete-pendingp)
                                       (fn-bpnf-heldp))))))
(local
 (defthm fn-bpn-report-expired-held-shape-for-guard
   (implies (fn-bpn-report-find-expired-held held-list observation)
            (fn-bpnf-heldp
             (fn-bpn-report-find-expired-held held-list observation)))
   :hints (("Goal" :induct (fn-bpn-report-find-expired-held
                            held-list observation)
            :in-theory (e/d (fn-bpn-report-find-expired-held
                             fn-bpnrg-pending-has-heldp)
                            (fn-bpn-report-held-delete-pendingp
                             fn-bpah-held-expiry fn-bpnf-heldp))))))
(verify-guards fn-bpn-report-delete-propose-step
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpn-report-expired-held-shape-for-guard
                            (held-list (fn-bpnf-held-list st)))
                 (:instance fn-bpn-report-held-bundle-for-guard
                            (held (fn-bpn-report-find-expired-held
                                   (fn-bpnf-held-list st) observation)))
                 (:instance fn-bpn-report-primary-for-guard
                            (bundle (fn-bpnf-held-bundle
                                     (fn-bpn-report-find-expired-held
                                      (fn-bpnf-held-list st) observation)))))
           :in-theory (union-theories
                       '((:definition fn-frame-natp)
                         (:definition natp)
                         fn-bpn-bundle-primary-true-list-for-guard)
                       (theory 'minimal-theory)))))
(verify-guards fn-bpn-report-delete-issuedp)
(verify-guards fn-bpn-report-delete-persist-step
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-bpn-machine-statep
                               fn-bpn-machine-recordp
                               fn-bpn-jobp fn-bpn-pendingp
                               fn-bpn-report-apply-delete
                               fn-bpnf-state-with-arrival
                               fn-bpnf-heldp fn-bpb-bundlep
                               fn-bpb-encode fn-bpp-blockp))))
(verify-guards fn-bpn-report-step)
(verify-guards fn-bpn-report-outbox-work)
(local
 (defthm fn-bpnrg-deleted-match-has-heldp
   (implies (fn-bpn-report-deleted-record-matches-heldp record held)
            (fn-bpnf-heldp held))
   :rule-classes nil
   :hints (("Goal" :in-theory
            (e/d (fn-bpn-report-deleted-record-matches-heldp)
                 (fn-bpnf-heldp fn-bpn-report-delete-recordp))))))
(verify-guards fn-bpn-report-outbox-view
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnrg-deleted-match-has-heldp
                            (record (fn-bpn-nth 14 held)))
                 (:instance fn-bpn-report-held-bundle-for-guard))
           :in-theory (union-theories
                       '(fn-bpn-bundle-primary-true-list-for-guard)
                       (theory 'minimal-theory)))))
(verify-guards fn-bpn-report-bundle
  :hints (("Goal" :in-theory (enable fn-bpn-configp))))
(verify-guards fn-bpn-report-job-matchp)
(verify-guards fn-bpn-report-queue-step)
(verify-guards fn-bpn-report-author-step)
(verify-guards fn-bpn-report-correlate-job)
(verify-guards fn-bpn-report-observe-held
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnf-heldp-primary-blockp)
                 (:instance fn-bpn-report-held-bundle-for-guard)
                 (:instance fn-bpn-report-primary-for-guard
                            (bundle (fn-bpnf-held-bundle held)))
                 (:instance fn-bpn-report-primary-flags-natural-for-guard
                            (primary (fn-bpb-bundle-primary
                                      (fn-bpnf-held-bundle held)))))
           :in-theory (disable fn-bpnf-heldp fn-bpb-bundlep
                               fn-bpp-blockp fn-bpn-report-decode
                               fn-bpn-report-held-bundle-for-guard
                               fn-bpn-report-primary-for-guard))))
(verify-guards fn-bpn-report-observe-next-aux)
(verify-guards fn-bpn-report-observe-next)

; The outbox scan's guards (decision-keystones-6): a view is a held row's
; (fn-bpnf-heldp), so the arrival it carries, and the row's, is a natural;
; the scan's carried selection is nil or a view.  The lemmas are stated in
; the shapes the guard conjecture takes (fn-bpn-nth and nth; natp, integerp
; and rationalp), since a natp rewrite does not answer a rationalp goal.
(defthm fn-bpn-report-outbox-view-arrival-is-natp
  (implies (fn-bpn-report-outbox-view held)
           (and (natp (fn-bpn-nth 3 held))
                (natp (fn-bpn-nth 1 (fn-bpn-report-outbox-view held)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnrg-deleted-match-has-heldp
                            (record (fn-bpn-nth 14 held))))
           :in-theory (e/d (fn-bpn-report-outbox-view fn-bpnf-heldp)
                           (fn-bpn-report-deleted-record-matches-heldp
                            fn-bpn-report-decode fn-bpn-report-outbox-work
                            fn-bpp-report-to fn-bpb-bundle-primary
                            fn-bpnf-held-bundle fn-cbor-result-okp)))))
(defthm fn-bpn-report-outbox-view-arrival-is-a-natural-nth
  (implies (fn-bpn-report-outbox-view held)
           (and (integerp (nth 1 (fn-bpn-report-outbox-view held)))
                (<= 0 (nth 1 (fn-bpn-report-outbox-view held)))))
  :hints (("Goal" :use ((:instance fn-bpn-report-outbox-view-arrival-is-natp))
           :in-theory (e/d (fn-bpn-report-outbox-view)
                           (fn-bpn-report-outbox-view-arrival-is-natp
                            fn-bpn-report-deleted-record-matches-heldp
                            fn-bpn-report-decode fn-bpn-report-outbox-work
                            fn-bpp-report-to fn-bpb-bundle-primary
                            fn-bpnf-held-bundle fn-cbor-result-okp fn-bpn-nth)))))
(defthm fn-bpn-report-outbox-view-arrival-is-rational
  (implies (fn-bpn-report-outbox-view held)
           (rationalp (fn-bpn-nth 3 held)))
  :hints (("Goal" :use ((:instance fn-bpn-report-outbox-view-arrival-is-natp))
           :in-theory (disable fn-bpn-report-outbox-view fn-bpn-nth
                               fn-bpn-report-outbox-view-arrival-is-natp))))
(defthm fn-bpn-report-outbox-view-carried-arrival-is-rational
  (implies (fn-bpn-report-outbox-view held)
           (and (rationalp (nth 1 (fn-bpn-report-outbox-view held)))
                (rationalp (fn-bpn-nth 1 (fn-bpn-report-outbox-view held)))))
  :hints (("Goal" :use ((:instance fn-bpn-report-outbox-view-arrival-is-natp)
                        (:instance fn-bpn-report-outbox-view-arrival-is-a-natural-nth))
           :in-theory (disable fn-bpn-report-outbox-view fn-bpn-nth
                               fn-bpn-report-outbox-view-arrival-is-natp
                               fn-bpn-report-outbox-view-arrival-is-a-natural-nth))))
(verify-guards fn-bpn-report-outbox-next-aux
  :hints (("Goal" :in-theory (disable fn-bpn-report-outbox-view))))
(verify-guards fn-bpn-report-outbox-next)
