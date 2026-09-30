; INTERNAL same-pool scalar transitions. No host/public installer, tariff,
; observation or turn-settlement authority is provided here. The actual
; process-wide barrier and selected source producer joins remain mandatory.
(in-package "ACL2")
(include-book "allocation-epoch")
(include-book "page-read-pool-state")

(defun fn-aec-pool-statep (fn-page-read-pool)
 (declare (xargs :stobjs fn-page-read-pool))
 (fn-aec-statep (fn-prp-alloc-installation fn-page-read-pool) (fn-prp-alloc-mode fn-page-read-pool) (fn-prp-alloc-epoch fn-page-read-pool) (fn-prp-alloc-occupied fn-page-read-pool) (fn-prp-alloc-allocated fn-page-read-pool) (fn-prp-alloc-active-turns fn-page-read-pool) (fn-prp-alloc-gc-nonce fn-page-read-pool)))

(defun fn-aec-pool-enter-internal (cleanup fn-page-read-pool)
 (declare (xargs :stobjs fn-page-read-pool :guard (and (fn-aec-pool-statep fn-page-read-pool) (booleanp cleanup))))
 (mv-let (word nm na nn)
  (fn-aec-enter (fn-prp-alloc-installation fn-page-read-pool) (fn-prp-alloc-mode fn-page-read-pool) (fn-prp-alloc-epoch fn-page-read-pool) (fn-prp-alloc-occupied fn-page-read-pool) (fn-prp-alloc-allocated fn-page-read-pool) (fn-prp-alloc-active-turns fn-page-read-pool) (fn-prp-alloc-gc-nonce fn-page-read-pool) cleanup)
  (let* ((fn-page-read-pool (update-fn-prp-alloc-mode nm fn-page-read-pool))
         (fn-page-read-pool (update-fn-prp-alloc-allocated na fn-page-read-pool))
         (fn-page-read-pool (update-fn-prp-alloc-active-turns nn fn-page-read-pool)))
   (mv word fn-page-read-pool))))

(defun fn-aec-pool-body-internal (body cleanup fn-page-read-pool)
 (declare (xargs :stobjs fn-page-read-pool :guard (and (fn-aec-pool-statep fn-page-read-pool) (and (natp body) (booleanp cleanup) (not (eq (fn-prp-alloc-mode fn-page-read-pool) :uninstalled))))))
 (mv-let (word nm na)
  (fn-aec-body (fn-prp-alloc-installation fn-page-read-pool) (fn-prp-alloc-mode fn-page-read-pool) (fn-prp-alloc-epoch fn-page-read-pool) (fn-prp-alloc-occupied fn-page-read-pool) (fn-prp-alloc-allocated fn-page-read-pool) (fn-prp-alloc-active-turns fn-page-read-pool) (fn-prp-alloc-gc-nonce fn-page-read-pool) body cleanup)
  (let* ((fn-page-read-pool (update-fn-prp-alloc-mode nm fn-page-read-pool))
         (fn-page-read-pool (update-fn-prp-alloc-allocated na fn-page-read-pool)))
   (mv word fn-page-read-pool))))

(defun fn-aec-pool-consumed-turn-internal ( fn-page-read-pool)
 (declare (xargs :stobjs fn-page-read-pool :guard (and (fn-aec-pool-statep fn-page-read-pool) (and (member-eq (fn-prp-alloc-mode fn-page-read-pool) '(:active :draining :recovery)) (posp (fn-prp-alloc-active-turns fn-page-read-pool))))))
 (mv-let (word nm na nn)
  (fn-aec-leave-owned (fn-prp-alloc-mode fn-page-read-pool) (fn-prp-alloc-allocated fn-page-read-pool) (fn-prp-alloc-active-turns fn-page-read-pool))
  (let* ((fn-page-read-pool (update-fn-prp-alloc-mode nm fn-page-read-pool))
         (fn-page-read-pool (update-fn-prp-alloc-allocated na fn-page-read-pool))
         (fn-page-read-pool (update-fn-prp-alloc-active-turns nn fn-page-read-pool)))
   (mv word fn-page-read-pool))))

(defun fn-aec-pool-collect-prepay-internal ( fn-page-read-pool)
 (declare (xargs :stobjs fn-page-read-pool :guard (and (fn-aec-pool-statep fn-page-read-pool) (not (eq (fn-prp-alloc-mode fn-page-read-pool) :uninstalled)))))
 (mv-let (word nm na)
  (fn-aec-collect-prepay (fn-prp-alloc-installation fn-page-read-pool) (fn-prp-alloc-mode fn-page-read-pool) (fn-prp-alloc-epoch fn-page-read-pool) (fn-prp-alloc-occupied fn-page-read-pool) (fn-prp-alloc-allocated fn-page-read-pool) (fn-prp-alloc-active-turns fn-page-read-pool) (fn-prp-alloc-gc-nonce fn-page-read-pool))
  (let* ((fn-page-read-pool (update-fn-prp-alloc-mode nm fn-page-read-pool))
         (fn-page-read-pool (update-fn-prp-alloc-allocated na fn-page-read-pool)))
   (mv word fn-page-read-pool))))

(defun fn-aec-pool-collect-issued-internal (issued fn-page-read-pool)
 (declare (xargs :stobjs fn-page-read-pool :guard (and (fn-aec-pool-statep fn-page-read-pool) (not (eq (fn-prp-alloc-mode fn-page-read-pool) :uninstalled)))))
 (mv-let (word nm ng)
  (fn-aec-collect-issued (fn-prp-alloc-mode fn-page-read-pool) (fn-prp-alloc-active-turns fn-page-read-pool) (fn-prp-alloc-gc-nonce fn-page-read-pool) issued (fn-aec-at 2 (fn-prp-alloc-installation fn-page-read-pool)))
  (let* ((fn-page-read-pool (update-fn-prp-alloc-mode nm fn-page-read-pool))
         (fn-page-read-pool (update-fn-prp-alloc-gc-nonce ng fn-page-read-pool)))
   (mv word fn-page-read-pool))))

(defun fn-aec-pool-collect-complete-internal (oi oe og status ol fn-page-read-pool)
 (declare (xargs :stobjs fn-page-read-pool :guard (and (fn-aec-pool-statep fn-page-read-pool) (not (eq (fn-prp-alloc-mode fn-page-read-pool) :uninstalled)))))
 (mv-let (word nm ne nl na ng)
  (fn-aec-collect-complete (fn-prp-alloc-installation fn-page-read-pool) (fn-prp-alloc-mode fn-page-read-pool) (fn-prp-alloc-epoch fn-page-read-pool) (fn-prp-alloc-occupied fn-page-read-pool) (fn-prp-alloc-allocated fn-page-read-pool) (fn-prp-alloc-active-turns fn-page-read-pool) (fn-prp-alloc-gc-nonce fn-page-read-pool) oi oe og status ol)
  (let* ((fn-page-read-pool (update-fn-prp-alloc-mode nm fn-page-read-pool))
         (fn-page-read-pool (update-fn-prp-alloc-epoch ne fn-page-read-pool))
         (fn-page-read-pool (update-fn-prp-alloc-occupied nl fn-page-read-pool))
         (fn-page-read-pool (update-fn-prp-alloc-allocated na fn-page-read-pool))
         (fn-page-read-pool (update-fn-prp-alloc-gc-nonce ng fn-page-read-pool)))
   (mv word fn-page-read-pool))))

(defun fn-aec-pool-drain-internal (fn-page-read-pool)
 (declare (xargs :stobjs fn-page-read-pool))
 (update-fn-prp-alloc-mode (fn-aec-drain (fn-prp-alloc-mode fn-page-read-pool)) fn-page-read-pool))

(defun fn-aec-pool-uncertain-internal (fn-page-read-pool)
 (declare (xargs :stobjs fn-page-read-pool
  :guard (and (fn-aec-pool-statep fn-page-read-pool)
              (not (eq (fn-prp-alloc-mode fn-page-read-pool) :uninstalled)))))
 (update-fn-prp-alloc-mode (fn-aec-uncertain) fn-page-read-pool))

(defthm fn-aec-logical-ledger-release-cannot-refund-allocation
 (equal (fn-prp-alloc-allocated (fn-owner-page-read-keep-ledger ledger pool))
        (fn-prp-alloc-allocated pool)))

(defthm fn-aec-pool-uncertainty-retains-charge-and-identities
 (let ((next (fn-aec-pool-uncertain-internal pool)))
  (and (equal (fn-prp-alloc-mode next) :recovery)
       (equal (fn-prp-alloc-installation next) (fn-prp-alloc-installation pool))
       (equal (fn-prp-alloc-epoch next) (fn-prp-alloc-epoch pool))
       (equal (fn-prp-alloc-occupied next) (fn-prp-alloc-occupied pool))
       (equal (fn-prp-alloc-allocated next) (fn-prp-alloc-allocated pool))
       (equal (fn-prp-alloc-active-turns next) (fn-prp-alloc-active-turns pool))
       (equal (fn-prp-alloc-gc-nonce next) (fn-prp-alloc-gc-nonce pool))
       (equal (fn-prp-data next) (fn-prp-data pool))
       (equal (fn-prp-mode next) (fn-prp-mode pool))
       (equal (fn-prp-incoming-slot next) (fn-prp-incoming-slot pool))))
 :rule-classes nil)

(defthm fn-aec-pool-entry-preserves-allocation-state
 (implies (fn-aec-pool-statep pool)
          (fn-aec-pool-statep (mv-nth 1 (fn-aec-pool-enter-internal cleanup pool))))
 :hints (("Goal"
  :in-theory (disable fn-aec-enter fn-aec-statep)
  :use ((:instance fn-aec-enter-preserves-allocation-state
         (i (fn-prp-alloc-installation pool)) (m (fn-prp-alloc-mode pool))
         (e (fn-prp-alloc-epoch pool)) (l (fn-prp-alloc-occupied pool))
         (a (fn-prp-alloc-allocated pool)) (n (fn-prp-alloc-active-turns pool))
         (g (fn-prp-alloc-gc-nonce pool))))))
 :rule-classes nil)

(defthm fn-aec-pool-collection-reset-preserves-allocation-state
 (implies
  (and (fn-aec-pool-statep pool)
       (member-eq (mv-nth 0 (fn-aec-pool-collect-complete-internal oi oe og status ol pool))
                  '(:resume :resource-unavailable)))
  (fn-aec-pool-statep
   (mv-nth 1 (fn-aec-pool-collect-complete-internal oi oe og status ol pool))))
 :hints (("Goal"
  :in-theory (disable fn-aec-collect-complete fn-aec-statep)
  :use ((:instance fn-aec-collector-reset-quiescence-by-definition
         (i (fn-prp-alloc-installation pool)) (m (fn-prp-alloc-mode pool))
         (e (fn-prp-alloc-epoch pool)) (l (fn-prp-alloc-occupied pool))
         (a (fn-prp-alloc-allocated pool)) (n (fn-prp-alloc-active-turns pool))
         (g (fn-prp-alloc-gc-nonce pool)))
        (:instance fn-aec-collector-reset-preserves-state
         (i (fn-prp-alloc-installation pool)) (m (fn-prp-alloc-mode pool))
         (e (fn-prp-alloc-epoch pool)) (l (fn-prp-alloc-occupied pool))
         (a (fn-prp-alloc-allocated pool)) (n (fn-prp-alloc-active-turns pool))
         (g (fn-prp-alloc-gc-nonce pool))))))
 :rule-classes nil)
