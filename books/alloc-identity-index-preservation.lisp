; General proof consumers of the actual bounded transitions. Source obligations:
; neither this file nor its dependency theorems have been admitted yet.
(in-package "ACL2")
(include-book "alloc-identity-index-invariant")
(fn2-book-layer :b)

; No result predicate is assumed: actual PREPARE mints the captured subject
; and empty examined prefix; actual STEP extends it by one physical bucket.
(defthm fn2-alloc-identity-prepare-preserves-maintained
 (implies (fn2-alloc-identity-maintained-p fn2-extents)
  (fn2-alloc-identity-maintained-p
   (mv-nth 1 (fn2-alloc-identity-prepare kind owner ogen source op i previous row-state epoch counter cut fn2-extents))))
 :hints (("Goal" :in-theory (enable fn2-alloc-identity-prepare fn2-alloc-identity-maintained-p
                                   fn2-alloc-identity-probe-provenance-p fn2-alloc-identity-captured-subject-p))))
(defthm fn2-alloc-identity-step-preserves-maintained
 (implies (fn2-alloc-identity-maintained-p fn2-extents)
  (fn2-alloc-identity-maintained-p
   (mv-nth 1 (fn2-alloc-identity-step kind owner ogen source fn2-extents))))
 :hints (("Goal" :in-theory (enable fn2-alloc-identity-step fn2-alloc-identity-maintained-p
                                   fn2-alloc-identity-probe-provenance-p))))

; Insertion needs the produced probe provenance, not just existing-map
; refinement. The forged-READY fixture removes precisely that hypothesis.
(defthm fn2-alloc-identity-commit-adopt-preserves-maintained
 (implies (fn2-alloc-identity-maintained-p fn2-extents)
  (fn2-alloc-identity-maintained-p
   (mv-nth 1 (fn2-alloc-identity-commit-adopt kind owner ogen source fn2-extents))))
 :hints (("Goal" :in-theory (enable fn2-alloc-identity-commit-adopt
                                   fn2-alloc-identity-maintained-p fn2-alloc-identity-probe-provenance-p))))
(defthm fn2-alloc-identity-commit-free-preserves-maintained
 (implies (fn2-alloc-identity-maintained-p fn2-extents)
  (fn2-alloc-identity-maintained-p
   (mv-nth 1 (fn2-alloc-identity-commit-free kind owner ogen source fn2-extents))))
 :hints (("Goal" :in-theory (enable fn2-alloc-identity-commit-free
                                   fn2-alloc-identity-maintained-p fn2-alloc-identity-probe-provenance-p))))
(defthm fn2-alloc-identity-transfer-preserves-maintained
 (implies (fn2-alloc-identity-maintained-p fn2-extents)
  (fn2-alloc-identity-maintained-p
   (mv-nth 1 (fn2-alloc-identity-transfer kind owner ogen source new-kind new-owner new-gen fn2-extents))))
 :hints (("Goal" :in-theory (enable fn2-alloc-identity-transfer fn2-alloc-identity-maintained-p))))
