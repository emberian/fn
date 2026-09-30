; Shared-ledger physical-page reservation for the actual builder. Internal D
; is operation-derived by the eventual selected-runtime admission producer;
; shape/fundedp alone is not constructor adequacy and exposes no host tariff.
(in-package "ACL2")
(logic)
(include-book "index-backing-page-owners")
(include-book "index-generation-issuer")
(local (include-book "arithmetic-5/top" :dir :system))

(defun fn-ipa-candidate (fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :guard t))
 (let ((free (fn-ibp-page-free fn-index-backing))
       (high (fn-ibp-page-highwater fn-index-backing))
       (capacity (fn-ibp-pool-capacity fn-index-backing)))
  (cond ((consp free)
         (if (and (natp (car free)) (< (car free) high) (< (car free) (* 64 capacity)))
             (mv :recycled (car free)) (mv :recovery-required nil)))
        ((not (null free)) (mv :recovery-required nil))
        ((< high (* 64 capacity)) (mv :fresh high))
        (t (mv :unavailable nil)))))

; Layout page-request cursor begins with tag/kind/logical-index/oldDescriptor.
; It is established from the builder's retained prior roots, not host fields.
; Receipt13 retains affine identity, current debt and old stamp across every
; constructor/restamp/clear yield. Candidate address changes only on definite
; owner-child registration; a pending reservation blocks another issue.
(defun fn-ipa-reserve (demand fn-index-backing fn-page-read-pool)
 (declare (xargs :stobjs (fn-index-backing fn-page-read-pool) :guard t))
 (let* ((builder (fn-ibp-builder fn-index-backing))
        (request (fn-omk-at 18 builder))
        (kind (fn-omk-at 1 request)) (index (fn-omk-at 2 request)))
  (cond
   ((fn-ibp-page-pending fn-index-backing)
    (mv :busy nil fn-index-backing fn-page-read-pool))
   ((not (and (fn-omk-widthp builder 20) (eq (fn-omk-at 0 builder) :index-builder)
              (eq (fn-omk-at 1 builder) :layout)
              (fn-ibp-generation-tokenp (fn-omk-at 2 builder))
              (eq (fn-omk-at 0 request) :page-request)
              (member-eq kind '(:table :rows)) (natp index)))
    (mv :recovery-required nil fn-index-backing fn-page-read-pool))
   ((not (and (fn-prs-vectorp demand) (equal (fn-prl-nth 4 demand) 1)))
    (mv :unsupported-runtime nil fn-index-backing fn-page-read-pool))
   (t
    (mv-let (candidate physical) (fn-ipa-candidate fn-index-backing)
     (if (not (and (member-eq candidate '(:fresh :recycled)) (natp physical)))
         (mv candidate nil fn-index-backing fn-page-read-pool)
       (let* ((ledger (fn-owner-page-read-ledger fn-page-read-pool))
              (budget (fn-prl-nth 0 ledger)) (charged (fn-prl-nth 1 ledger))
              (old-next (fn-prl-nth 2 ledger)))
        (mv-let (word nonce next-charge)
         (fn-prs-issue budget (fn-prl-baseline ledger) '(0 0 0 0 0)
                       charged old-next (fn-prl-nth 4 budget) demand)
         (if (not (and (eq word :admitted) (posp nonce)))
             (mv word nil fn-index-backing fn-page-read-pool)
           (let* ((fn-page-read-pool
                    (fn-owner-page-read-keep-ledger
                     (fn-prl-build budget next-charge nonce (fn-prl-nth 3 ledger)
                                   (fn-prl-baseline ledger)) fn-page-read-pool))
                  (token (list :index-page nonce (+ 1 (floor physical 64)) (mod physical 64)))
                  (receipt (list :page-reservation old-next nonce physical candidate demand kind
                                 (fn-omk-at 2 builder) index (fn-omk-at 3 request) :charged nil nil))
                  (fn-index-backing (update-fn-ibp-page-pending receipt fn-index-backing)))
            (mv :reserved token fn-index-backing fn-page-read-pool))))))))))
)

; Registration consumes only the current charged reservation.  It does not
; create a registry child: an absent installed segment remains unavailable.
; Recycling requires the separate joined old-stamp capture before overwriting
; its owner row, so this fresh path cannot discard that evidence.
(defun fn-ipa-register-fresh (fuel fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :guard (natp fuel) :verify-guards nil))
 (let* ((receipt (fn-ibp-page-pending fn-index-backing))
        (builder (fn-ibp-builder fn-index-backing))
        (nonce (fn-omk-at 2 receipt)) (physical (fn-omk-at 3 receipt))
        (depth (fn-ibp-slot-depth fn-index-backing)))
  (cond
   ((not (and (fn-omk-widthp receipt 13) (true-listp receipt)
              (eq (fn-omk-at 0 receipt) :page-reservation)
              (posp nonce) (natp physical)
              (eq (fn-omk-at 4 receipt) :fresh)
              (equal (fn-omk-at 7 receipt) (fn-omk-at 2 builder))
              (fn-ibp-generation-tokenp (fn-omk-at 7 receipt))))
    (mv :stale fuel fn-index-backing))
   ((eq (fn-omk-at 10 receipt) :registered)
    (mv :registered fuel fn-index-backing))
   ((not (and (eq (fn-omk-at 10 receipt) :charged)
              (equal physical (fn-ibp-page-highwater fn-index-backing))
              (< physical (* 64 (fn-ibp-pool-capacity fn-index-backing)))
              (null (fn-ibp-page-free fn-index-backing))))
    (mv :recovery-required fuel fn-index-backing))
   ((<= fuel depth) (mv :yield fuel fn-index-backing))
   (t
    (let ((token (list :index-page nonce (+ 1 (floor physical 64)) (mod physical 64))))
     (stobj-let ((fn-ibp-node (fn-ibp-registry fn-index-backing)))
      (word row delta left fn-ibp-node)
      (fn-ibp-node-page-owner-action token :reserve (fn-omk-at 6 receipt)
       physical receipt (fn-omk-at 7 receipt) fuel (floor physical 64) depth fn-ibp-node)
      (let ()
       (if (not (and (eq word :reserved) (consp row) (equal delta 0)))
          (mv word left fn-index-backing)
        (let* ((fn-index-backing
                 (update-fn-ibp-page-highwater (+ 1 physical) fn-index-backing))
               (fn-index-backing
                 (update-fn-ibp-page-pending
                  (update-nth 10 :registered receipt) fn-index-backing)))
         (mv :registered left fn-index-backing))))))))))
(verify-guards fn-ipa-register-fresh
 :hints (("Goal" :in-theory (disable fn-ibp-node-page-owner-action))))
