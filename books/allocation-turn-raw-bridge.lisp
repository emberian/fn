; Guard-verified internal scheduling receipt callbacks. These declarations
; skip carried-state revalidation only after actual installation establishes
; it. They neither install fn-allocation-turn-slots nor expose the supplied BODY source seam.
(in-package "ACL2")
(include-book "allocation-turn-slots")


(local
 (defthm fn-atsh-enter-funded-pool
  (implies (and (fn-aec-pool-statep fn-page-read-pool)
                (eq (mv-nth 0 (fn-aec-pool-enter-internal nil fn-page-read-pool)) :prepaid))
   (let ((next (mv-nth 1 (fn-aec-pool-enter-internal nil fn-page-read-pool))))
    (and (fn-aec-pool-statep next)
         (eq (fn-prp-alloc-mode next) :active)
         (posp (fn-prp-alloc-active-turns next)))))
  :hints (("Goal"
    :in-theory (disable fn-aec-statep fn-aec-installationp fn-aec-ceiling fn-aec-at)
    :use ((:instance fn-aec-pool-entry-preserves-allocation-state (cleanup nil) (pool fn-page-read-pool)))))))

(local
 (defthm fn-atsh-counter-completion-preserves-state
  (let* ((begin (fn-owner-page-read-counter-begin ledger nonce kind continuation pool))
         (receipt (mv-nth 1 begin)) (begun (mv-nth 2 begin)))
   (implies (eq (mv-nth 0 begin) :counter-publishing)
    (and (eq (mv-nth 0 (fn-owner-page-read-counter-finish receipt begun)) :published)
         (equal (fn-aec-pool-statep (mv-nth 1 (fn-owner-page-read-counter-finish receipt begun)))
                (fn-aec-pool-statep pool)))))
  :hints (("Goal" :in-theory
           (e/d (fn-owner-page-read-counter-begin fn-owner-page-read-counter-finish
                 fn-aec-pool-statep fn-prb-keep-current-bindings fn-prb-data6 fn-prl-build fn-prl-nth
                 fn-prb-fixed-widthp fn-prb-counter-receiptp fn-prb-counter-receipt-matchesp)
                (fn-aec-statep nth update-nth))))))
(local
 (defthm fn-atsh-counter-begin-preserves-state
  (implies (fn-aec-pool-statep pool)
   (fn-aec-pool-statep (mv-nth 2 (fn-owner-page-read-counter-begin ledger nonce kind continuation pool))))
  :hints (("Goal" :in-theory
    (e/d (fn-owner-page-read-counter-begin fn-aec-pool-statep)
         (fn-aec-statep fn-prb-keep-current-bindings fn-prb-data6))
    :use ((:instance fn-aec-raw-uncertainty-preserves-state
           (i (fn-prp-alloc-installation pool)) (m (fn-prp-alloc-mode pool))
           (e (fn-prp-alloc-epoch pool)) (l (fn-prp-alloc-occupied pool))
           (a (fn-prp-alloc-allocated pool)) (n (fn-prp-alloc-active-turns pool))
           (g (fn-prp-alloc-gc-nonce pool))))))))
(local
 (defthm fn-atsh-mode-store-preserves-pool-state
  (equal (fn-aec-pool-statep (update-fn-prp-mode mode pool)) (fn-aec-pool-statep pool))
  :hints (("Goal" :in-theory (e/d (fn-aec-pool-statep) (fn-aec-statep))))))
(local
 (defthm fn-atsh-mode-store-preserves-allocation-mode
  (equal (fn-prp-alloc-mode (update-fn-prp-mode mode pool)) (fn-prp-alloc-mode pool))))
(local
 (defthm fn-atsh-consume-preserves-pool-state
  (implies (and (fn-aec-pool-statep fn-page-read-pool)
                (member-eq (fn-prp-alloc-mode fn-page-read-pool) '(:active :draining :recovery))
                (posp (fn-prp-alloc-active-turns fn-page-read-pool)))
   (fn-aec-pool-statep (mv-nth 1 (fn-aec-pool-consumed-turn-internal fn-page-read-pool))))
  :hints (("Goal" :in-theory (disable fn-aec-statep)
           :use ((:instance fn-aec-consumed-turn-settlement-preserves-state
             (i (fn-prp-alloc-installation fn-page-read-pool)) (m (fn-prp-alloc-mode fn-page-read-pool))
             (e (fn-prp-alloc-epoch fn-page-read-pool)) (l (fn-prp-alloc-occupied fn-page-read-pool))
             (a (fn-prp-alloc-allocated fn-page-read-pool)) (n (fn-prp-alloc-active-turns fn-page-read-pool))
             (g (fn-prp-alloc-gc-nonce fn-page-read-pool))))))))

(local
 (defthm fn-atsh-uncertain-state-frame
  (implies (and (fn-aec-pool-statep pool)
                (not (eq (fn-prp-alloc-mode pool) :uninstalled)))
           (fn-aec-pool-statep (fn-aec-pool-uncertain-internal pool)))
  :hints (("Goal" :in-theory
    (e/d (fn-aec-pool-uncertain-internal fn-aec-pool-statep)
         (fn-aec-statep))
    :use ((:instance fn-aec-raw-uncertainty-preserves-state
           (i (fn-prp-alloc-installation pool)) (m (fn-prp-alloc-mode pool))
           (e (fn-prp-alloc-epoch pool)) (l (fn-prp-alloc-occupied pool))
           (a (fn-prp-alloc-allocated pool)) (n (fn-prp-alloc-active-turns pool))
           (g (fn-prp-alloc-gc-nonce pool))))))))

(local
 (defthm fn-atsh-counter-begin-refusal-keeps-pool
  (implies (not (eq (mv-nth 0 (fn-owner-page-read-counter-begin ledger nonce kind continuation pool))
                    :counter-publishing))
           (equal (mv-nth 2 (fn-owner-page-read-counter-begin ledger nonce kind continuation pool)) pool))
  :hints (("Goal" :in-theory (enable fn-owner-page-read-counter-begin)))))

(defthm fn-atsh-entry-preserves-carried-pool-state
 (implies (fn-aec-pool-statep fn-page-read-pool)
  (fn-aec-pool-statep (mv-nth 3 (fn-ats-enter-internal slot role fn-allocation-turn-slots fn-page-read-pool))))
 :hints (("Goal" :in-theory
   (disable fn-aec-pool-statep fn-aec-statep fn-aec-pool-enter-internal
            fn-aec-pool-consumed-turn-internal fn-aec-pool-uncertain-internal fn-aec-collection-issue
            fn-owner-page-read-counter-begin fn-owner-page-read-counter-finish update-fn-prp-mode fn-prp-alloc-mode)
   :use ((:instance fn-aec-pool-entry-preserves-allocation-state (cleanup nil) (pool fn-page-read-pool))
         (:instance fn-atsh-enter-funded-pool))))
 :rule-classes nil)

(defthm fn-atsh-finish-preserves-carried-pool-state
 (implies (fn-aec-pool-statep fn-page-read-pool)
  (fn-aec-pool-statep (mv-nth 2 (fn-ats-finish-owned slot nonce fn-allocation-turn-slots fn-page-read-pool))))
 :hints (("Goal" :in-theory
   (disable fn-aec-pool-statep fn-aec-statep fn-aec-pool-consumed-turn-internal)))
 :rule-classes nil)

(defthm fn-atsh-uncertain-preserves-carried-pool-state
 (implies (and (fn-aec-pool-statep fn-page-read-pool)
               (not (eq (fn-prp-alloc-mode fn-page-read-pool) :uninstalled)))
  (fn-aec-pool-statep (mv-nth 2 (fn-ats-uncertain-internal fn-allocation-turn-slots fn-page-read-pool))))
 :hints (("Goal" :in-theory (disable fn-aec-installationp fn-aec-at fn-aec-ceiling)))
 :rule-classes nil)

(local
 (defthm fn-atsh-counter-transaction-scalar-frame
  (implies (and (natp index) (not (member-equal index '(0 1 4))))
   (and (equal (nth index (mv-nth 2 (fn-owner-page-read-counter-begin ledger nonce kind continuation pool)))
               (nth index pool))
        (equal (nth index (mv-nth 1 (fn-owner-page-read-counter-finish receipt pool)))
               (nth index pool))))
  :hints (("Goal" :in-theory
           (e/d (fn-owner-page-read-counter-begin fn-owner-page-read-counter-finish)
                (fn-prb-keep-current-bindings fn-prb-data6 nth update-nth
                 fn-prb-fixed-widthp fn-prb-counter-receipt-matchesp fn-prb-data-revision))))))

(defthm fn-atsh-entry-preserves-installed-roots
 (mv-let (word nonce next-fn-allocation-turn-slots next-fn-page-read-pool) (fn-ats-enter-internal slot role fn-allocation-turn-slots fn-page-read-pool)
  (declare (ignore word nonce))
  (and (equal (fn-ats-association next-fn-allocation-turn-slots) (fn-ats-association fn-allocation-turn-slots))
       (equal (fn-ats-count next-fn-allocation-turn-slots) (fn-ats-count fn-allocation-turn-slots))
       (equal (nth 2 next-fn-allocation-turn-slots) (nth 2 fn-allocation-turn-slots))
       (equal (fn-prp-alloc-installation next-fn-page-read-pool) (fn-prp-alloc-installation fn-page-read-pool))
       (equal (fn-prp-alloc-epoch next-fn-page-read-pool) (fn-prp-alloc-epoch fn-page-read-pool))
       (equal (fn-prp-alloc-occupied next-fn-page-read-pool) (fn-prp-alloc-occupied fn-page-read-pool))
       (equal (fn-prp-incoming-slot next-fn-page-read-pool) (fn-prp-incoming-slot fn-page-read-pool))))
 :hints (("Goal" :in-theory
   (disable nth update-nth fn-aec-enter fn-aec-leave-owned fn-aec-collection-issue
            fn-owner-page-read-counter-begin fn-owner-page-read-counter-finish)))
 :rule-classes nil)

(defthm fn-atsh-finish-preserves-installed-roots
 (mv-let (word next-fn-allocation-turn-slots next-fn-page-read-pool) (fn-ats-finish-owned slot nonce fn-allocation-turn-slots fn-page-read-pool)
  (declare (ignore word))
  (and (equal (fn-ats-association next-fn-allocation-turn-slots) (fn-ats-association fn-allocation-turn-slots))
       (equal (fn-ats-count next-fn-allocation-turn-slots) (fn-ats-count fn-allocation-turn-slots))
       (equal (nth 2 next-fn-allocation-turn-slots) (nth 2 fn-allocation-turn-slots))
       (equal (nth 3 next-fn-allocation-turn-slots) (nth 3 fn-allocation-turn-slots))
       (equal (fn-prp-data next-fn-page-read-pool) (fn-prp-data fn-page-read-pool))
       (equal (fn-prp-alloc-installation next-fn-page-read-pool) (fn-prp-alloc-installation fn-page-read-pool))
       (equal (fn-prp-alloc-epoch next-fn-page-read-pool) (fn-prp-alloc-epoch fn-page-read-pool))
       (equal (fn-prp-alloc-occupied next-fn-page-read-pool) (fn-prp-alloc-occupied fn-page-read-pool))
       (equal (fn-prp-mode next-fn-page-read-pool) (fn-prp-mode fn-page-read-pool))
       (equal (fn-prp-incoming-slot next-fn-page-read-pool) (fn-prp-incoming-slot fn-page-read-pool))))
 :hints (("Goal" :in-theory (disable nth update-nth fn-aec-leave-owned)))
 :rule-classes nil)

