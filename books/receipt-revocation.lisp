; PRF-1118: present release authority after a durable principal revocation.
; Host: fnn-bpnode-receipt-result calls the gate and record selector through
; fn-owner-bp-receipt-{gatep,release-record} inside owner serialization.
; Old signature observations do not carry old enrollment authority.
(in-package "ACL2")
(include-book "bp-release-authority")
(include-book "hybrid-lifecycle-store-invariants")

(defthm fn-rr-revocation-removes-current-signer-keys
  (let ((tomb (fn-hl-revoke-event sequence txid store-generation g
                                 principal snapshots)))
    (implies tomb
             (equal (fn-bpah-receipt-signer-keys (cons tomb snapshots) principal)
                    nil)))
  :hints (("Goal"
           :use ((:instance fn-hl-revoke-event-is-the-principals-tombstone
                            (keyring-generation g)))
           :in-theory (e/d (fn-bpah-receipt-signer-keys)
                            (fn-hl-revoke-event fn-hsig-keyring-snapshot-value
                             fn-hl-current-for-principal)))))

(local (defthm fn-rr-revocation-principal-is-nonempty
  (implies (fn-hl-revoke-event sequence txid store-generation g principal snapshots)
           (consp principal))
  :hints (("Goal" :in-theory
           (e/d (fn-hl-revoke-event fn-hsig-exact-octets-p)
                (fn-hl-current-for-principal fn-hsig-keyring-snapshot-value
                 fn-stxk-p fn-hl-next-generationp))))))

(local
 (defthm fn-rr-null-signed-has-null-principal
   (implies (not signed) (equal (fn-bpsr-principal signed) nil))
   :hints (("Goal" :in-theory (enable fn-bpsr-principal fn-bpa-nth)))))

(defthm fn-rr-revocation-refuses-new-receipt-release
  (let ((tomb (fn-hl-revoke-event sequence txid store-generation g
                                 principal snapshots)))
    (implies (and tomb
                  (equal (fn-bpsr-principal (fn-bpah-view-signed view))
                         principal))
             (and (not (fn-bpah-receipt-gatep
                        view cfg (cons tomb snapshots) obs))
                  (equal (fn-bpah-receipt-release-record
                          view cfg wf (cons tomb snapshots) obs) nil))))
  :hints (("Goal"
           :use ((:instance fn-rr-revocation-principal-is-nonempty)
                 (:instance fn-bpah-unverified-signed-receipt-releases-nothing
                            (snapshots (cons (fn-hl-revoke-event
                                              sequence txid store-generation g
                                              principal snapshots)
                                             snapshots))))
           :in-theory
           (union-theories
            '(fn-bpah-receipt-signature-verifiedp
              fn-rr-revocation-removes-current-signer-keys
              fn-rr-null-signed-has-null-principal)
            (theory 'minimal-theory)))))

(local (defthm fn-rr-successful-new-snapshot-is-prepended
  (implies (and (fn-stxk-p event)
                (equal (fn-stxk-context-kind
                        (fn-replay-identity-step (fn-sn-identity-context s) event))
                       :ok)
                (not (fn-stxk-find (fn-stxk-keyring-generation event)
                                   (fn-sn-keyring-snapshots s))))
           (equal (fn-stxk-context-snapshots
                   (fn-replay-identity-step (fn-sn-identity-context s) event))
                  (cons event (fn-sn-keyring-snapshots s))))
  :hints (("Goal"
           :in-theory (e/d (fn-replay-identity-step fn-replay-identity-wire
                            fn-sn-identity-context fn-stxk-apply-snapshot
                            fn-stxk-fault fn-stxk-context)
                           (fn-stxk-p fn-stxk-find fn-stxe-p fn-stxa-p
                            fn-hstxa-p fn-sn-keyring-snapshots))))))

(defthm fn-rr-finish-new-snapshot-retains-exact-history
  (let ((event (fn-sn-completion-record s)))
    (implies (and (fn-sn-completion-enabledp s)
                  (fn-stxk-p event)
                  (not (fn-stxk-find (fn-stxk-keyring-generation event)
                                     (fn-sn-keyring-snapshots s))))
             (and (equal (fn-sn-keyring-snapshots (fn-sn-finish s))
                         (cons event (fn-sn-keyring-snapshots s)))
                  (equal (fn-sn-verdicts (fn-sn-finish s))
                         (fn-sn-verdicts s)))))
  :hints (("Goal"
           :use ((:instance fn-hls-snapshot-disjoint-from-other-store-events
                            (event (fn-sn-completion-record s))))
           :in-theory
           (e/d (fn-sn-finish fn-sn-finish-identity
                  fn-sn-completion-enabledp fn-sn-completion-core-enabledp)
                (fn-stxk-p fn-stxe-p fn-hstxa-p fn-stxk-find
                 fn-store-retention-event-p fn-cpe-eventp fn-th-topic-eventp
                 fn-replay-identity-step fn-sn-identity-context
                 fn-sn-completion-record fn-replay-apply-record
                 fn-cpe-projection-step fn-th-prefix-step
                 fn-sf-core-completion fn-sf-emit-success fn-sn-statep
                 fn-stx-index-add fn-sn-composite-delta)))))

(local (defthm fn-rr-enabled-completion-has-a-record
  (implies (fn-sn-completion-enabledp s)
           (fn-sn-completion-record s))
  :hints (("Goal"
           :cases ((fn-sn-completion-record s))
           :in-theory
           (e/d (fn-sn-completion-enabledp fn-sn-completion-core-enabledp
                  fn-sn-record-bindsp)
                (fn-sn-completion-record fn-sn-statep fn-store-retention-event-p
                 fn-stxe-p fn-stxk-p fn-hstxa-p fn-cpe-eventp fn-th-topic-eventp
                 fn-held-p fn-replay-apply-record fn-cpe-projection-step
                 fn-th-prefix-step))))))

; Actual durable completion and the very gate/record selector called under
; the owner's serialization. The completed event is the actual constructor's
; tombstone, not a hypothesized negative authority predicate. Receipt primitive
; observations may have been computed before revocation; OBS is arbitrary.
(defthm fn-rr-durable-revocation-refuses-new-release
  (let* ((snapshots (fn-sn-keyring-snapshots s))
         (tomb (fn-hl-revoke-event sequence txid store-generation g
                                  principal snapshots)))
    (implies (and (fn-sn-completion-enabledp s)
                  (equal (fn-sn-completion-record s) tomb)
                  (not (fn-stxk-find g snapshots))
                  (equal (fn-bpsr-principal (fn-bpah-view-signed view))
                         principal))
             (and
              (not (fn-bpah-receipt-gatep
                    view cfg (fn-sn-keyring-snapshots (fn-sn-finish s)) obs))
              (equal (fn-bpah-receipt-release-record
                      view cfg wf (fn-sn-keyring-snapshots (fn-sn-finish s)) obs)
                     nil)
              (equal (fn-sn-keyring-snapshots (fn-sn-finish s))
                     (cons tomb snapshots))
              (equal (fn-sn-verdicts (fn-sn-finish s)) (fn-sn-verdicts s)))))
  :hints (("Goal"
           :use ((:instance fn-hl-revoke-event-is-the-principals-tombstone
                            (keyring-generation g)
                            (snapshots (fn-sn-keyring-snapshots s)))
                 (:instance fn-rr-revocation-refuses-new-receipt-release
                            (snapshots (fn-sn-keyring-snapshots s))))
           :in-theory
           (union-theories
            '(fn-rr-enabled-completion-has-a-record
              fn-rr-finish-new-snapshot-retains-exact-history)
            (theory 'minimal-theory)))))

(local (defthm fn-rr-snapshot-application-keeps-retention
  (implies (and (fn-stxk-p event)
                (consp (fn-replay-apply-record node event)))
           (equal (fn-node-retention (fn-replay-apply-record node event))
                  (fn-node-retention node)))
  :hints (("Goal"
           :use ((:instance fn-hls-snapshot-disjoint-from-other-store-events))
           :in-theory (e/d (fn-replay-apply-record fn-replay-apply-identity-neutral)
                            (fn-stxk-p fn-store-retention-event-p fn-cpe-eventp
                             fn-th-topic-eventp fn-replay-advance-txid))))))

(defthm fn-rr-finish-snapshot-keeps-all-retention
  (implies (fn-stxk-p (fn-sn-completion-record s))
           (equal (fn-node-retention (fn-sn-node (fn-sn-finish s)))
                  (fn-node-retention (fn-sn-node s))))
  :hints (("Goal"
           :use ((:instance fn-hls-snapshot-disjoint-from-other-store-events
                            (event (fn-sn-completion-record s))))
           :in-theory
           (e/d (fn-sn-finish fn-sn-finish-identity
                  fn-sn-completion-enabledp fn-sn-completion-core-enabledp)
                (fn-stxk-p fn-stxe-p fn-hstxa-p fn-store-retention-event-p
                 fn-cpe-eventp fn-th-topic-eventp fn-replay-apply-record
                 fn-sn-completion-record fn-replay-identity-step
                 fn-cpe-projection-step fn-th-prefix-step
                 fn-sf-core-completion fn-sf-emit-success fn-sn-statep
                 fn-stx-index-add fn-sn-composite-delta)))))
