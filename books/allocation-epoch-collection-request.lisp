; INTERNAL collection request; the native process-wide barrier is a separate
; producer obligation. The ONE existing PRS issuer supplies the nonce.
(in-package "ACL2")
(include-book "allocation-epoch-observation")

; Constant-size immediate arithmetic validation before existing PRS addition.
; It checks only the five carried scalar resource coordinates, not bindings or
; whole store state. The reserved identity component is an installation/join
; obligation: exhaustion fences; this function invents no rescue capacity.
(defun fn-aec-collection-issuer-domainp (budget used charged next domain)
 (declare (xargs :guard t))
 (and (fn-prs-vectorp budget) (fn-prs-vectorp used) (fn-prs-vectorp charged)
      (natp domain) (natp next) (< next domain)
      (fn-aec-nats-below budget domain)
      (fn-aed-add-roomp (fn-prl-nth 0 used) (fn-prl-nth 0 charged) domain)
      (fn-aed-add-roomp (fn-prl-nth 1 used) (fn-prl-nth 1 charged) domain)
      (fn-aed-add-roomp (fn-prl-nth 2 used) (fn-prl-nth 2 charged) domain)
      (fn-aed-add-roomp (fn-prl-nth 3 used) (fn-prl-nth 3 charged) domain)
      (fn-aed-ordinary-roomp (fn-prl-nth 4 used) (fn-prl-nth 4 charged) 1 domain domain)))

(defun fn-aec-collection-issue (ledger domain)
 (declare (xargs :guard t))
 (let* ((budget (fn-prl-nth 0 ledger))
        (used (fn-prl-baseline ledger))
        (charged (fn-prl-nth 1 ledger))
        (next (fn-prl-nth 2 ledger)))
  (if (not (fn-aec-collection-issuer-domainp budget used charged next domain))
      (mv :invalid-resource-state nil ledger)
    (mv-let (word next1 charged1)
     (fn-prs-issue budget used '(0 0 0 0 0) charged next (fn-prl-nth 4 budget) '(0 0 0 0 1))
     (if (eq word :admitted)
         ;; The nonce is actual OLD NEXT, never next1. There is no new binding
         ;; list: the collecting intent/nonce scalar is the retained owner.
         (mv :issued next (fn-prl-build budget charged1 next1
                              (fn-prl-nth 3 ledger) (fn-prl-nth 4 ledger)))
       (mv word nil ledger))))))

(defun fn-aec-pool-collection-request-internal (fn-page-read-pool)
 (declare (xargs :stobjs fn-page-read-pool
  :guard (and (fn-aec-pool-statep fn-page-read-pool)
              (not (eq (fn-prp-alloc-mode fn-page-read-pool) :uninstalled)))
  :guard-hints (("Goal"
   :in-theory (disable fn-aec-pool-collect-prepay-internal fn-aec-pool-statep
                      fn-aec-collection-issue fn-owner-page-read-keep-ledger)
   :use ((:instance fn-aec-pool-prepay-preserves-installed-state (pool fn-page-read-pool))
         (:instance fn-aec-keep-ledger-preserves-installed-state
          (pool (mv-nth 1 (fn-aec-pool-collect-prepay-internal fn-page-read-pool)))
          (ledger (mv-nth 2 (fn-aec-collection-issue
                   (fn-owner-page-read-ledger (mv-nth 1 (fn-aec-pool-collect-prepay-internal fn-page-read-pool)))
                   (fn-aec-at 2 (fn-prp-alloc-installation (mv-nth 1 (fn-aec-pool-collect-prepay-internal fn-page-read-pool)))))))))))))
 (mv-let (prepare fn-page-read-pool) (fn-aec-pool-collect-prepay-internal fn-page-read-pool)
  (if (not (eq prepare :issue-collection-nonce))
      (mv prepare nil nil nil fn-page-read-pool)
    ;; Qcollect has been retained before any ledger/issuer allocation. Invalid
    ;; or refused issuance fences without refund. Raw escapes retain intent.
    (mv-let (word nonce ledger)
     (fn-aec-collection-issue (fn-owner-page-read-ledger fn-page-read-pool)
                              (fn-aec-at 2 (fn-prp-alloc-installation fn-page-read-pool)))
     (if (not (eq word :issued))
         (let ((fn-page-read-pool (fn-aec-pool-uncertain-internal fn-page-read-pool)))
          (mv :recovery-required nil nil nil fn-page-read-pool))
       (let ((fn-page-read-pool (fn-owner-page-read-keep-ledger ledger fn-page-read-pool)))
        (mv-let (issued fn-page-read-pool) (fn-aec-pool-collect-issued-internal nonce fn-page-read-pool)
         (mv issued (fn-aec-at 1 (fn-prp-alloc-installation fn-page-read-pool))
             (fn-prp-alloc-epoch fn-page-read-pool) (fn-prp-alloc-gc-nonce fn-page-read-pool)
             fn-page-read-pool))))))))

(defthm fn-aec-collection-issue-binds-shared-nonce
 (implies (eq (mv-nth 0 (fn-aec-collection-issue ledger domain)) :issued)
  (let ((nonce (mv-nth 1 (fn-aec-collection-issue ledger domain)))
        (next-ledger (mv-nth 2 (fn-aec-collection-issue ledger domain))))
   (and (equal nonce (fn-prl-nth 2 ledger))
        (equal (fn-prl-nth 2 next-ledger) (+ 1 (fn-prl-nth 2 ledger)))
        (equal (fn-prl-nth 0 next-ledger) (fn-prl-nth 0 ledger))
        (equal (fn-prl-nth 1 next-ledger) (fn-prs-plus (fn-prl-nth 1 ledger) '(0 0 0 0 1)))
        (equal (fn-prl-nth 3 next-ledger) (fn-prl-nth 3 ledger))
        (equal (fn-prl-nth 4 next-ledger) (fn-prl-nth 4 ledger)))))
 :hints (("Goal" :in-theory (e/d (fn-prs-issue fn-prl-build fn-prl-nth)
                         (fn-aec-collection-issuer-domainp fn-prs-plus fn-prs-fundedp fn-prs-vectorp))))
 :rule-classes nil)

(defthm fn-aec-collection-refusal-keeps-ledger
 (implies (not (eq (mv-nth 0 (fn-aec-collection-issue ledger domain)) :issued))
          (equal (mv-nth 2 (fn-aec-collection-issue ledger domain)) ledger))
 :hints (("Goal" :in-theory (disable fn-aec-collection-issuer-domainp fn-prs-issue)))
 :rule-classes nil)
