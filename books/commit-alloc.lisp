; Composition facts for B's persistent allocator and hashing core children.
; These preserve concrete table shape; they make no ownership/durability claim.
(in-package "ACL2")
(include-book "alloc")
(include-book "blake3")
(local (in-theory (disable fn2-extentsp fn2-extents-wfp fn2-extents-rows
 fn2-alloc-edgesp fn2-alloc-edges-wfp fn2-alloc-edges-rows fn2-b3p fn2-b3-wfp fn2-b3-rows
 fn2-extents-installed-root fn2-extents-selectable-checkpoint fn2-extents-recovery-base
 fn2-extents-prepared-successor fn2-extents-reservation fn2-extents-obligation
 fn2-extents-promised-read fn2-extents-borrow fn2-extents-outstanding-io fn2-extents-recovery-candidate
 fn2-extents-state fn2-extents-next-free fn2-extents-counter fn2-extents-epoch
 fn2-alloc-total-free fn2-alloc-total-reserved fn2-alloc-total-allocated fn2-alloc-total-retired
 fn2-alloc-current-epoch fn2-alloc-next-counter fn2-alloc-epoch-begun fn2-alloc-free-head
 fn2-alloc-ready fn2-alloc-blocked fn2-alloc-quarantined fn2-alloc-cut fn2-alloc-coverage
 fn2-alloc-last-retirement fn2-alloc-retired-head fn2-alloc-retired-tail fn2-alloc-pending
 fn2-alloc-edges-state fn2-alloc-edges-kind fn2-alloc-edges-holder fn2-alloc-edges-extent
 fn2-alloc-edges-epoch fn2-alloc-edges-counter)))

(defthm fn2-alloc-init-links-rows
 (equal (fn2-extents-rows (fn2-alloc-init-links n fn2-extents))
        (fn2-extents-rows fn2-extents))
 :hints (("Goal" :in-theory (enable fn2-alloc-init-links))))
(defthm fn2-alloc-account-type
 (implies (fn2-extentsp fn2-extents)
          (fn2-extentsp (fn2-alloc-account i old-state old-reason fn2-extents)))
 :hints (("Goal" :in-theory (enable fn2-alloc-total-free fn2-alloc-total-reserved
  fn2-alloc-total-allocated fn2-alloc-total-retired fn2-alloc-ready fn2-alloc-blocked fn2-alloc-quarantined))))
(defthm fn2-alloc-account-wfp
 (implies (fn2-extents-wfp fn2-extents)
          (fn2-extents-wfp (fn2-alloc-account i old-state old-reason fn2-extents))))
(defthm fn2-alloc-account-rows
 (equal (fn2-extents-rows (fn2-alloc-account i old-state old-reason fn2-extents))
        (fn2-extents-rows fn2-extents)))
(in-theory (disable fn2-alloc-account))

(defthm fn2-alloc-init-type
 (implies (and (fn2-extentsp fn2-extents) (unsigned-byte-p 32 n))
          (fn2-extentsp (fn2-alloc-init n fn2-extents))))
(defthm fn2-alloc-init-wfp
 (implies (unsigned-byte-p 32 n) (fn2-extents-wfp (fn2-alloc-init n fn2-extents))))
(defthm fn2-alloc-init-rows
 (implies (unsigned-byte-p 32 n) (equal (fn2-extents-rows (fn2-alloc-init n fn2-extents)) n)))
(in-theory (disable fn2-alloc-init))

(defthm fn2-b3-table-init-type
 (implies (and (fn2-b3p fn2-b3) (unsigned-byte-p 32 n))
          (fn2-b3p (fn2-b3-table-init n fn2-b3)))
 :hints (("Goal" :in-theory (enable fn2-b3-table-init))))

(defthm fn2-b3-table-init-wfp
 (implies (unsigned-byte-p 32 n)
          (fn2-b3-wfp (fn2-b3-table-init n fn2-b3)))
 :hints (("Goal" :in-theory (enable fn2-b3-table-init))))

(defthm fn2-alloc-begin-epoch-type
 (implies (and (fn2-extentsp fn2-extents) (fn2-extents-wfp fn2-extents) (unsigned-byte-p 60 epoch))
  (fn2-extentsp (mv-nth 1 (fn2-alloc-begin-epoch epoch fn2-extents)))))
(defthm fn2-alloc-begin-epoch-wfp
 (implies (fn2-extents-wfp fn2-extents) (fn2-extents-wfp (mv-nth 1 (fn2-alloc-begin-epoch epoch fn2-extents)))))
(defthm fn2-alloc-begin-epoch-rows
 (equal (fn2-extents-rows (mv-nth 1 (fn2-alloc-begin-epoch epoch fn2-extents))) (fn2-extents-rows fn2-extents)))
(in-theory (disable fn2-alloc-begin-epoch))

(defthm fn2-alloc-reserve-type
 (implies (and (fn2-extentsp fn2-extents) (fn2-extents-wfp fn2-extents) )
  (fn2-extentsp (mv-nth 5 (fn2-alloc-reserve fn2-extents)))))
(defthm fn2-alloc-reserve-wfp
 (implies (fn2-extents-wfp fn2-extents) (fn2-extents-wfp (mv-nth 5 (fn2-alloc-reserve fn2-extents)))))
(defthm fn2-alloc-reserve-rows
 (equal (fn2-extents-rows (mv-nth 5 (fn2-alloc-reserve fn2-extents))) (fn2-extents-rows fn2-extents)))
(in-theory (disable fn2-alloc-reserve))

(defthm fn2-alloc-free-head-range
 (implies (fn2-extentsp fn2-extents)
          (unsigned-byte-p 32 (fn2-alloc-free-head fn2-extents)))
 :hints (("Goal" :in-theory (enable fn2-alloc-free-head))))
(defthm fn2-alloc-free-type
 (implies (and (fn2-extentsp fn2-extents) (fn2-extents-wfp fn2-extents)
               (fn2-alloc-slotp i fn2-extents) (unsigned-byte-p 32 i))
          (fn2-extentsp (fn2-alloc-free i fn2-extents)))
 :hints (("Goal" :in-theory (e/d (fn2-alloc-free fn2-alloc-slotp)
                                (fn2-alloc-unlink)))))
(defthm fn2-alloc-free-wfp
 (implies (and (fn2-extentsp fn2-extents) (fn2-extents-wfp fn2-extents)
               (fn2-alloc-slotp i fn2-extents) (unsigned-byte-p 32 i))
          (fn2-extents-wfp (fn2-alloc-free i fn2-extents)))
 :hints (("Goal" :in-theory (e/d (fn2-alloc-free fn2-alloc-slotp)
                                (fn2-alloc-unlink)))))
(defthm fn2-alloc-free-rows
 (equal (fn2-extents-rows (fn2-alloc-free i fn2-extents))
        (fn2-extents-rows fn2-extents))
 :hints (("Goal" :in-theory (e/d (fn2-alloc-free) (fn2-alloc-unlink)))))
(in-theory (disable fn2-alloc-free))

(defthm fn2-alloc-cancel-reservation-type
 (implies (and (fn2-extentsp fn2-extents) (fn2-extents-wfp fn2-extents) (unsigned-byte-p 32 i))
  (fn2-extentsp (mv-nth 1 (fn2-alloc-cancel-reservation i epoch counter fn2-extents))))
 :hints (("Goal" :in-theory (enable fn2-alloc-slotp fn2-alloc-handle-code))))
(defthm fn2-alloc-cancel-reservation-wfp
 (implies (and (fn2-extentsp fn2-extents) (fn2-extents-wfp fn2-extents) (unsigned-byte-p 32 i))
  (fn2-extents-wfp (mv-nth 1 (fn2-alloc-cancel-reservation i epoch counter fn2-extents))))
 :hints (("Goal" :in-theory (enable fn2-alloc-slotp fn2-alloc-handle-code))))
(defthm fn2-alloc-cancel-reservation-rows
 (equal (fn2-extents-rows (mv-nth 1 (fn2-alloc-cancel-reservation i epoch counter fn2-extents))) (fn2-extents-rows fn2-extents))
 :hints (("Goal" :in-theory (enable fn2-alloc-slotp fn2-alloc-handle-code))))
(in-theory (disable fn2-alloc-cancel-reservation))

(defthm fn2-alloc-commit-allocation-type
 (implies (and (fn2-extentsp fn2-extents) (fn2-extents-wfp fn2-extents) (unsigned-byte-p 8 owner-kind) (unsigned-byte-p 60 owner-id))
  (fn2-extentsp (mv-nth 1 (fn2-alloc-commit-allocation i epoch counter owner-kind owner-id fn2-extents)))))
(defthm fn2-alloc-commit-allocation-wfp
 (implies (fn2-extents-wfp fn2-extents) (fn2-extents-wfp (mv-nth 1 (fn2-alloc-commit-allocation i epoch counter owner-kind owner-id fn2-extents)))))
(defthm fn2-alloc-commit-allocation-rows
 (equal (fn2-extents-rows (mv-nth 1 (fn2-alloc-commit-allocation i epoch counter owner-kind owner-id fn2-extents))) (fn2-extents-rows fn2-extents)))
(in-theory (disable fn2-alloc-commit-allocation))

(defthm fn2-alloc-edge-count-range
 (implies (and (fn2-extentsp fn2-extents) (fn2-extents-wfp fn2-extents) (fn2-alloc-slotp i fn2-extents))
  (unsigned-byte-p 32 (fn2-alloc-edge-count i kind fn2-extents))))
(in-theory (disable fn2-alloc-edge-count))
(defthm fn2-alloc-edge-add-type
 (implies (and (fn2-extentsp fn2-extents) (fn2-extents-wfp fn2-extents) (fn2-alloc-edgesp fn2-alloc-edges) (fn2-alloc-edges-wfp fn2-alloc-edges) (unsigned-byte-p 60 holder) (unsigned-byte-p 60 epoch) (unsigned-byte-p 60 counter))
  (fn2-extentsp (mv-nth 1 (fn2-alloc-edge-add edge holder i epoch counter kind fn2-extents fn2-alloc-edges)))) :hints (("Goal" :use fn2-alloc-edge-count-range)))
(defthm fn2-alloc-edge-add-wfp
 (implies (and (fn2-extentsp fn2-extents) (fn2-extents-wfp fn2-extents) (fn2-alloc-edgesp fn2-alloc-edges) (fn2-alloc-edges-wfp fn2-alloc-edges))
  (fn2-extents-wfp (mv-nth 1 (fn2-alloc-edge-add edge holder i epoch counter kind fn2-extents fn2-alloc-edges)))) :hints (("Goal" :use fn2-alloc-edge-count-range)))
(defthm fn2-alloc-edge-add-rows
 (equal (fn2-extents-rows (mv-nth 1 (fn2-alloc-edge-add edge holder i epoch counter kind fn2-extents fn2-alloc-edges))) (fn2-extents-rows fn2-extents)))
(defthm fn2-alloc-edge-add-edges-type
 (implies (and (fn2-extentsp fn2-extents) (fn2-extents-wfp fn2-extents) (fn2-alloc-edgesp fn2-alloc-edges) (fn2-alloc-edges-wfp fn2-alloc-edges) (unsigned-byte-p 60 holder) (unsigned-byte-p 60 epoch) (unsigned-byte-p 60 counter))
  (fn2-alloc-edgesp (mv-nth 2 (fn2-alloc-edge-add edge holder i epoch counter kind fn2-extents fn2-alloc-edges)))))
(defthm fn2-alloc-edge-add-edges-wfp
 (implies (and (fn2-extentsp fn2-extents) (fn2-extents-wfp fn2-extents) (fn2-alloc-edgesp fn2-alloc-edges) (fn2-alloc-edges-wfp fn2-alloc-edges))
  (fn2-alloc-edges-wfp (mv-nth 2 (fn2-alloc-edge-add edge holder i epoch counter kind fn2-extents fn2-alloc-edges)))))
(defthm fn2-alloc-edge-add-edges-rows
 (equal (fn2-alloc-edges-rows (mv-nth 2 (fn2-alloc-edge-add edge holder i epoch counter kind fn2-extents fn2-alloc-edges))) (fn2-alloc-edges-rows fn2-alloc-edges)))
(in-theory (disable fn2-alloc-edge-add))
(defthm fn2-alloc-edge-drop-type
 (implies (and (fn2-extentsp fn2-extents) (fn2-extents-wfp fn2-extents) (fn2-alloc-edgesp fn2-alloc-edges) (fn2-alloc-edges-wfp fn2-alloc-edges))
  (fn2-extentsp (mv-nth 1 (fn2-alloc-edge-drop edge holder i epoch counter kind fn2-extents fn2-alloc-edges)))) :hints (("Goal" :use fn2-alloc-edge-count-range)))
(defthm fn2-alloc-edge-drop-wfp
 (implies (and (fn2-extentsp fn2-extents) (fn2-extents-wfp fn2-extents) (fn2-alloc-edgesp fn2-alloc-edges) (fn2-alloc-edges-wfp fn2-alloc-edges))
  (fn2-extents-wfp (mv-nth 1 (fn2-alloc-edge-drop edge holder i epoch counter kind fn2-extents fn2-alloc-edges)))) :hints (("Goal" :use fn2-alloc-edge-count-range)))
(defthm fn2-alloc-edge-drop-rows
 (equal (fn2-extents-rows (mv-nth 1 (fn2-alloc-edge-drop edge holder i epoch counter kind fn2-extents fn2-alloc-edges))) (fn2-extents-rows fn2-extents)))
(defthm fn2-alloc-edge-drop-edges-type
 (implies (and (fn2-extentsp fn2-extents) (fn2-extents-wfp fn2-extents) (fn2-alloc-edgesp fn2-alloc-edges) (fn2-alloc-edges-wfp fn2-alloc-edges))
  (fn2-alloc-edgesp (mv-nth 2 (fn2-alloc-edge-drop edge holder i epoch counter kind fn2-extents fn2-alloc-edges)))))
(defthm fn2-alloc-edge-drop-edges-wfp
 (implies (and (fn2-extentsp fn2-extents) (fn2-extents-wfp fn2-extents) (fn2-alloc-edgesp fn2-alloc-edges) (fn2-alloc-edges-wfp fn2-alloc-edges))
  (fn2-alloc-edges-wfp (mv-nth 2 (fn2-alloc-edge-drop edge holder i epoch counter kind fn2-extents fn2-alloc-edges)))))
(defthm fn2-alloc-edge-drop-edges-rows
 (equal (fn2-alloc-edges-rows (mv-nth 2 (fn2-alloc-edge-drop edge holder i epoch counter kind fn2-extents fn2-alloc-edges))) (fn2-alloc-edges-rows fn2-alloc-edges)))
(in-theory (disable fn2-alloc-edge-drop))

; BH1 now exports the incremental BLAKE3 shape contracts, including digest
; rows and hasher word-array length. Consumers use those shared contracts.
