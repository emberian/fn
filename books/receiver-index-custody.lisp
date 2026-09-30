; Actual registered recipient bridge. No source, consumption, or joined
; scalar is an input; the current pending receipt is read once.
; Carried producer step-domain, canonical demand and terminal joins remain open.
(in-package "ACL2")

(include-book "receiver-turn-controller")

(include-book "index-reader-request")
(include-book "receiver-query-binding")

(defun fn-ric-pending-observation (recipient fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :guard t))
 (mv-let (word receipt) (fn-irr-pending-read recipient fn-index-backing)
  (let* ((request (fn-irr-receipt-request receipt))
         (source (fn-irr-request-input-source request))
         (step (fn-irr-receipt-step receipt))
         (consumed (fn-omk-at 5 step)))
   (if (and (fn-irq-committed-phasep word)
            (fn-omk-widthp request 10) source (natp consumed))
       (mv :committed-input source consumed)
     (mv :unavailable-input nil 0)))))

(defun fn-owner-rx-turn-transfer-pending
 (ticket recipient fn-rx-provider fn-receiver-turn fn-index-backing fn-page-read-pool)
 (declare (xargs :stobjs (fn-rx-provider fn-receiver-turn fn-index-backing fn-page-read-pool)))
 (if (not (fn-owner-rx-turn-consumablep ticket fn-rx-provider fn-receiver-turn fn-page-read-pool))
     (mv :receiver-unavailable fn-rx-provider fn-receiver-turn fn-page-read-pool)
  (mv-let (word source consumed) (fn-ric-pending-observation recipient fn-index-backing)
   (if (not (and (eq word :committed-input)
                 (equal source (fn-rxt-source fn-receiver-turn))))
       (mv :unavailable-recipient fn-rx-provider fn-receiver-turn fn-page-read-pool)
    (let ((pending (fn-rxt-job fn-receiver-turn)))
     (mv-let (range-word next end)
       (fn-rxt-consumed-range (cadr pending) (caddr pending) consumed)
       (if (eq range-word :invalid-receiver-consumption)
           (mv range-word fn-rx-provider fn-receiver-turn fn-page-read-pool)
        (mv-let (fenced fn-rx-provider)
          (fn-rxp-fence (fn-rxp-token fn-rx-provider) fn-rx-provider)
          (if (not (eq fenced :receiver-fenced))
              (mv :receiver-unavailable fn-rx-provider fn-receiver-turn fn-page-read-pool)
           (let* ((job (list :receiver-recipient recipient pending next end))
                  (fn-receiver-turn (update-fn-rxt-job job fn-receiver-turn))
                  (fn-receiver-turn (update-fn-rxt-phase :transferred fn-receiver-turn)))
             (mv :receiver-transferred fn-rx-provider fn-receiver-turn fn-page-read-pool)))))))))))

(defthm fn-owner-rx-turn-transfer-pending-retains-issued-custody
 (let ((answer (fn-owner-rx-turn-transfer-pending ticket recipient fn-rx-provider
                  fn-receiver-turn fn-index-backing fn-page-read-pool)))
  (implies (equal (mv-nth 0 answer) :receiver-transferred)
   (and (null (fn-rxp-capacity (mv-nth 1 answer)))
        (equal (fn-rxt-phase (mv-nth 2 answer)) :transferred)
        (equal (fn-rxt-ticket (mv-nth 2 answer)) (fn-rxt-ticket fn-receiver-turn))
        (equal (fn-rxt-source (mv-nth 2 answer)) (fn-rxt-source fn-receiver-turn))
        (equal (fn-rxt-demand (mv-nth 2 answer)) (fn-rxt-demand fn-receiver-turn))
        (equal (fn-rxt-receipt (mv-nth 2 answer)) (fn-rxt-receipt fn-receiver-turn))
        (equal (mv-nth 3 answer) fn-page-read-pool))))
 :hints (("Goal" :in-theory (e/d (fn-owner-rx-turn-transfer-pending fn-rxp-fence fn-rxc-fence)
         (fn-ric-pending-observation fn-owner-rx-turn-consumablep
          fn-rxt-owned-claim-p fn-rxt-consumed-range fn-rxc-currentp))))
 :rule-classes nil)

