; Frames for the actual frozen lifecycle entries, not checkpoint closure evidence.

(in-package "ACL2")

(include-book "alloc")

(fn2-book-layer :b)

(defthm fn2-alloc-begin-epoch-frozen-frame
 (implies (fn2-alloc-frozenp fn2-extents)
  (equal (mv-nth 1 (fn2-alloc-begin-epoch epoch fn2-extents)) fn2-extents))
 :hints (("Goal" :in-theory (enable fn2-alloc-begin-epoch fn2-alloc-frozenp))))

(defthm fn2-alloc-reserve-frozen-frame
 (implies (fn2-alloc-frozenp fn2-extents)
  (equal (mv-nth 5 (fn2-alloc-reserve fn2-extents)) fn2-extents))
 :hints (("Goal" :in-theory (enable fn2-alloc-reserve fn2-alloc-frozenp))))

(defthm fn2-alloc-adopt-frozen-frame
 (implies (fn2-alloc-frozenp fn2-extents)
  (equal (mv-nth 1 (fn2-alloc-adopt i epoch counter fn2-extents)) fn2-extents))
 :hints (("Goal" :in-theory (enable fn2-alloc-adopt fn2-alloc-frozenp))))

(defthm fn2-alloc-commit-allocation-frozen-frame
 (implies (fn2-alloc-frozenp fn2-extents)
  (equal (mv-nth 1 (fn2-alloc-commit-allocation i epoch counter owner-kind owner-id fn2-extents)) fn2-extents))
 :hints (("Goal" :in-theory (enable fn2-alloc-commit-allocation fn2-alloc-frozenp))))

(defthm fn2-alloc-retire-frozen-frame
 (implies (fn2-alloc-frozenp fn2-extents)
  (equal (mv-nth 1 (fn2-alloc-retire i epoch counter commit fn2-extents)) fn2-extents))
 :hints (("Goal" :in-theory (enable fn2-alloc-retire fn2-alloc-frozenp))))

(defthm fn2-alloc-cancel-reservation-frozen-frame
 (implies (fn2-alloc-frozenp fn2-extents)
  (equal (mv-nth 1 (fn2-alloc-cancel-reservation i epoch counter fn2-extents)) fn2-extents))
 :hints (("Goal" :in-theory (enable fn2-alloc-cancel-reservation fn2-alloc-frozenp))))

(defthm fn2-alloc-checkpoint-drain-frozen-frame
 (implies (fn2-alloc-frozenp fn2-extents)
  (equal (mv-nth 1 (fn2-alloc-checkpoint-drain cut budget fn2-extents)) fn2-extents))
 :hints (("Goal" :in-theory (enable fn2-alloc-checkpoint-drain fn2-alloc-frozenp))))
