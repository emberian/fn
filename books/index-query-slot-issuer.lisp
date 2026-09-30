; Actual request allocator pieces. Physical coordinates never use nonce.
; The request host bridge must derive its admission demand from the installed
; runtime census before calling the internal reservation primitive. No
; constructor is licensed by a supplied vector or this component alone.
(in-package "ACL2")
(logic)
(include-book "index-backing-provider")
(include-book "page-read-pool-state")
(local (include-book "arithmetic-5/top" :dir :system))

(defun fn-irq-candidate (fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :guard t))
 (let ((free (fn-ibp-request-free fn-index-backing))
       (high (fn-ibp-request-highwater fn-index-backing))
       (capacity (* 64 (fn-ibp-pool-capacity fn-index-backing))))
  (cond ((consp free)
         (if (and (natp (car free)) (< (car free) high) (< (car free) capacity))
             (mv :recycled (car free)) (mv :recovery-required nil)))
        (free (mv :recovery-required nil))
        ((< high capacity) (mv :fresh high))
        (t (mv :unavailable nil)))))

(defun fn-irq-candidate-token (nonce ordinal generation)
 (declare (xargs :guard (and (posp nonce) (natp ordinal) (posp generation))))
 (fn-ibp-query-token nonce (1+ (floor ordinal 64)) (mod ordinal 64) generation))

; Called ONLY in the actual parent coupled-transition's delta1/:released
; branch AFTER the child slot has cleared. Duplicate/stale release has delta0
; and never calls this helper. Physical ordinal is derived from that core token.
(defun fn-irq-enqueue-released (token fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :guard t))
 (if (not (fn-ibp-query-tokenp token))
     (mv :stale fn-index-backing)
   (let ((ordinal (+ (* 64 (1- (nth 2 token))) (nth 3 token))))
    (if (not (and (< ordinal (fn-ibp-request-highwater fn-index-backing))
                  (< ordinal (* 64 (fn-ibp-pool-capacity fn-index-backing)))))
        (mv :recovery-required fn-index-backing)
      (let ((fn-index-backing
             (update-fn-ibp-request-free
               (cons ordinal (fn-ibp-request-free fn-index-backing)) fn-index-backing)))
        (mv :enqueued fn-index-backing))))))

; PRL receipt reservation is internal: DEMAND is the actual installed
; constructor's result. Request+receipt remain in the one registered pending
; field through yield/capture/refusal; identities are never refunded.
; Receipt retains OLD NEXT as the spent PRL identity. Query nonce is 1+OLD
; NEXT, i.e. returned NEXT, because query segments reserve nonce0 as vacancy;
; this is a derived tagged representation, not an independent identity issuer.
; Full runtime adequacy/source authority is the composed host boundary, not
; an inference from this resource-vector algebra.
(defun fn-irq-reserve-request (id pin publication pre-oc rc effects demand fn-index-backing fn-page-read-pool)
 (declare (xargs :stobjs (fn-index-backing fn-page-read-pool) :guard t))
 (if (fn-ibp-request-pending fn-index-backing)
     (mv :busy nil fn-index-backing fn-page-read-pool)
   (mv-let (candidate-kind ordinal) (fn-irq-candidate fn-index-backing)
    (if (not (member-eq candidate-kind '(:fresh :recycled)))
        (mv candidate-kind nil fn-index-backing fn-page-read-pool)
      (let* ((ledger (fn-owner-page-read-ledger fn-page-read-pool))
             (budget (fn-prl-nth 0 ledger))
             (charged (fn-prl-nth 1 ledger))
             (next (fn-prl-nth 2 ledger)))
       (if (not (and (fn-prs-vectorp demand) (equal (fn-prl-nth 4 demand) 1)))
           (mv :unsupported-runtime nil fn-index-backing fn-page-read-pool)
         (mv-let (word issued next-charge)
          (fn-prs-issue budget (fn-prl-baseline ledger) '(0 0 0 0 0)
                        charged next (fn-prl-nth 4 budget) demand)
          (if (not (eq word :admitted))
              (mv word nil fn-index-backing fn-page-read-pool)
            (let* ((origin (list :index-read issued))
                   (request (list :reader-request id pin publication pre-oc rc effects origin))
                   (receipt (list :index-request-receipt next issued ordinal candidate-kind demand request :reserved nil))
                   (fn-index-backing (update-fn-ibp-request-pending receipt fn-index-backing))
                   (fn-page-read-pool
                    (fn-owner-page-read-keep-ledger
                     (fn-prl-build budget next-charge issued (fn-prl-nth 3 ledger)
                                   (fn-prl-baseline ledger)) fn-page-read-pool)))
              (mv :reserved issued fn-index-backing fn-page-read-pool))))))))))

; Internal final substep of the serialized owner producer transition, after
; its RC owner/credits/exposure installation. It touches ONLY the current
; reserved receipt. No precommit receipt licenses a consumed-read response.
; Repeated commit observes the marker and never repeats owner installation.
(defun fn-irq-commit-current (nonce step fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :guard t))
 (let ((receipt (fn-ibp-request-pending fn-index-backing)))
  (cond ((not (and (posp nonce)
                   (equal (fn-omk-at 0 receipt) :index-request-receipt)
                   (equal (fn-omk-at 2 receipt) nonce)))
         (mv :stale fn-index-backing))
        ((equal (fn-omk-at 7 receipt) :committed)
         (mv :committed fn-index-backing))
        ((not (equal (fn-omk-at 7 receipt) :reserved))
         (mv :recovery-required fn-index-backing))
        (t (let ((fn-index-backing
                  (update-fn-ibp-request-pending
                   (list (fn-omk-at 0 receipt) (fn-omk-at 1 receipt)
                         (fn-omk-at 2 receipt) (fn-omk-at 3 receipt)
                         (fn-omk-at 4 receipt) (fn-omk-at 5 receipt)
                         (fn-omk-at 6 receipt) :committed step) fn-index-backing)))
             (mv :committed fn-index-backing))))))
