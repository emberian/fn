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
 (defthm fn-atsh-ledger-preserves-pool-state
  (equal (fn-aec-pool-statep (fn-owner-page-read-keep-ledger ledger fn-page-read-pool))
         (fn-aec-pool-statep fn-page-read-pool))
  :hints (("Goal" :in-theory (disable fn-aec-pool-statep fn-owner-page-read-keep-ledger)
           :use ((:instance fn-aec-keep-ledger-preserves-installed-state (pool fn-page-read-pool)))))))

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

(defthm fn-atsh-entry-preserves-carried-pool-state
 (implies (fn-aec-pool-statep fn-page-read-pool)
  (fn-aec-pool-statep (mv-nth 3 (fn-ats-enter-internal slot role fn-allocation-turn-slots fn-page-read-pool))))
 :hints (("Goal" :in-theory
   (disable fn-aec-pool-statep fn-aec-statep fn-aec-pool-enter-internal
            fn-aec-pool-consumed-turn-internal fn-aec-collection-issue
            fn-owner-page-read-keep-ledger)
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

(defthm fn-atsh-entry-preserves-installed-roots
 (mv-let (word nonce next-fn-allocation-turn-slots next-fn-page-read-pool) (fn-ats-enter-internal slot role fn-allocation-turn-slots fn-page-read-pool)
  (declare (ignore word nonce))
  (and (equal (fn-ats-association next-fn-allocation-turn-slots) (fn-ats-association fn-allocation-turn-slots))
       (equal (fn-ats-count next-fn-allocation-turn-slots) (fn-ats-count fn-allocation-turn-slots))
       (equal (nth 2 next-fn-allocation-turn-slots) (nth 2 fn-allocation-turn-slots))
       (equal (fn-prp-alloc-installation next-fn-page-read-pool) (fn-prp-alloc-installation fn-page-read-pool))
       (equal (fn-prp-alloc-epoch next-fn-page-read-pool) (fn-prp-alloc-epoch fn-page-read-pool))
       (equal (fn-prp-alloc-occupied next-fn-page-read-pool) (fn-prp-alloc-occupied fn-page-read-pool))
       (equal (fn-prp-mode next-fn-page-read-pool) (fn-prp-mode fn-page-read-pool))
       (equal (fn-prp-incoming-slot next-fn-page-read-pool) (fn-prp-incoming-slot fn-page-read-pool))))
 :hints (("Goal" :in-theory
   (disable nth update-nth fn-aec-enter fn-aec-leave-owned fn-aec-collection-issue)))
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

