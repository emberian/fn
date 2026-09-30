; Actual request allocator pieces. Physical coordinates never use nonce.
; The request host bridge must derive its admission demand from the installed
; runtime census before calling the internal reservation primitive. No
; constructor is licensed by a supplied vector or this component alone.
(in-package "ACL2")
(logic)
(include-book "index-backing-provider")
(include-book "index-publication-shape")
(include-book "page-read-pool-state")
(include-book "index-connection-holder")
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
(defun fn-irq-reserve-request (id holder-token pin publication pre-oc rc effects demand fn-index-backing fn-page-read-pool)
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
       (if (not (and (fn-prs-vectorp demand) (equal (fn-prl-nth 4 demand) 1)
                     (posp (fn-ipub-generation publication))))
           (mv :unsupported-runtime nil fn-index-backing fn-page-read-pool)
         (mv-let (word issued next-charge)
          (fn-prs-issue budget (fn-prl-baseline ledger) '(0 0 0 0 0)
                        charged next (fn-prl-nth 4 budget) demand)
          (if (not (eq word :admitted))
              (mv word nil fn-index-backing fn-page-read-pool)
            ; Persist the SAME pool debit before allocating request/receipt.
            ; A raw escape after debit is recovery, never unfunded retry.
            (let* ((fn-page-read-pool
                    (fn-owner-page-read-keep-ledger
                     (fn-prl-build budget next-charge issued (fn-prl-nth 3 ledger)
                                   (fn-prl-baseline ledger)) fn-page-read-pool))
                   (origin (list :index-read issued))
                   (request (list :reader-request id pin publication pre-oc rc effects origin holder-token))
                   (receipt (list :index-request-receipt next issued ordinal (list candidate-kind (fn-ipub-generation publication)) demand request :reserved nil nil))
                   (fn-index-backing (update-fn-ibp-request-pending receipt fn-index-backing)))
              (mv :reserved issued fn-index-backing fn-page-read-pool))))))))))

; Immutable request identity is distinct from eventual selected query generation.
(defun fn-irq-request-identityp (x)
 (declare (xargs :guard t))
 (and (fn-omk-widthp x 2) (member-eq (fn-omk-at 0 x) '(:fresh :recycled))
      (posp (fn-omk-at 1 x))))
(defun fn-irq-receipt-candidate-kind (receipt)
 (declare (xargs :guard t))
 (let ((x (fn-omk-at 4 receipt)))
  (if (fn-irq-request-identityp x) (fn-omk-at 0 x) nil)))
(defun fn-irq-receipt-request-generation (receipt)
 (declare (xargs :guard t))
 (let ((x (fn-omk-at 4 receipt)))
  (if (fn-irq-request-identityp x) (fn-omk-at 1 x) nil)))

(defun fn-irq-committed-phasep (phase)
 (declare (xargs :guard t))
 (member-eq phase '(:committed :committed-repin-released :committed-repin-held :committed-repin-aborted)))
(defun fn-irq-ready-phasep (phase)
 (declare (xargs :guard t))
 (member-eq phase '(:read-ready :read-ready-repin-released :read-ready-repin-held :read-ready-repin-aborted)))
(defun fn-irq-commit-phase (phase)
 (declare (xargs :guard t))
 (case phase (:read-ready :committed)
             (:read-ready-repin-released :committed-repin-released)
             (:read-ready-repin-held :committed-repin-held)
             (:read-ready-repin-aborted :committed-repin-aborted)
             (otherwise :recovery-required)))

; Internal final substep of the serialized owner producer transition, after
; its RC owner/credits/exposure installation. It touches ONLY the current
; read-ready receipt. No precommit receipt licenses a consumed-read response.
; Repeated commit observes the marker and never repeats owner installation.
(defun fn-irq-commit-current (nonce step fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :guard t))
 (let ((receipt (fn-ibp-request-pending fn-index-backing)))
  (cond ((not (and (posp nonce)
                   (equal (fn-omk-at 0 receipt) :index-request-receipt)
                   (equal (fn-omk-at 2 receipt) nonce)))
         (mv :stale fn-index-backing))
        ((fn-irq-committed-phasep (fn-omk-at 7 receipt))
         (mv (fn-omk-at 7 receipt) fn-index-backing))
        ((not (and (fn-irq-ready-phasep (fn-omk-at 7 receipt))
                   (or (null (fn-omk-at 9 receipt))
                       (fn-ich-tokenp (fn-omk-at 9 receipt)))))
         (mv :recovery-required fn-index-backing))
        (t (let ((fn-index-backing
                  (update-fn-ibp-request-pending
                   (list (fn-omk-at 0 receipt) (fn-omk-at 1 receipt)
                         (fn-omk-at 2 receipt) (fn-omk-at 3 receipt)
                         (fn-omk-at 4 receipt) (fn-omk-at 5 receipt)
                         (fn-omk-at 6 receipt) (fn-irq-commit-phase (fn-omk-at 7 receipt)) step
                         (fn-omk-at 9 receipt)) fn-index-backing)))
             (mv (fn-irq-commit-phase (fn-omk-at 7 receipt)) fn-index-backing))))))
