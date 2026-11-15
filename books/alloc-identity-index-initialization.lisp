; Bootstrap proof boundary: active CLEARING is not a usable dictionary.
; All observations here are logical/test-only and never served scans.
(in-package "ACL2")
(include-book "alloc-identity-index-invariant")
(fn2-book-layer :b)
(defun fn2-alloc-identity-all-free-p (n fn2-extents)
 (declare (xargs :stobjs fn2-extents :verify-guards nil :measure (nfix n)))
 (if (zp n) t
  (and (= (fn2-extents-state (- n 1) fn2-extents) *fn2-extent-state-free*)
       (fn2-alloc-identity-all-free-p (- n 1) fn2-extents))))
(defun fn2-alloc-identity-empty-prefix-p (n fn2-extents)
 (declare (xargs :stobjs fn2-extents :verify-guards nil :measure (nfix n)))
 (if (zp n) t
  (and (= (fn2-alloc-identity-statesi (- n 1) fn2-extents) *fn2-alloc-identity-bucket-empty*)
       (fn2-alloc-identity-empty-prefix-p (- n 1) fn2-extents))))
(defun fn2-alloc-identity-clearing-p (fn2-extents)
 (declare (xargs :stobjs fn2-extents :verify-guards nil))
 (and (fn2-extentsp fn2-extents) (fn2-extents-wfp fn2-extents)
      (fn2-alloc-identity-geometry-p fn2-extents)
      (fn2-alloc-identity-owner-p (fn2-alloc-identity-owner-kind fn2-extents)
       (fn2-alloc-identity-owner-slot fn2-extents) (fn2-alloc-identity-owner-gen fn2-extents)
       (fn2-alloc-identity-source-generation fn2-extents) fn2-extents)
      (= (fn2-alloc-identity-phase fn2-extents) *fn2-alloc-identity-phase-clearing*)
      (= (fn2-alloc-identity-op fn2-extents) *fn2-alloc-identity-op-none*)
      (= (fn2-alloc-identity-count fn2-extents) 0)
      (<= (fn2-alloc-identity-probe fn2-extents) (fn2-extents-rows fn2-extents))
      (fn2-alloc-identity-all-free-p (fn2-extents-rows fn2-extents) fn2-extents)
      (fn2-alloc-identity-empty-prefix-p (fn2-alloc-identity-probe fn2-extents) fn2-extents)))

; All-FREE follows from actual fresh allocator initialization, not from the
; scalar total-free counter alone. The hypothesis-removal control retains
; TYPE/WFP and accepted BEGIN while falsifying only that semantic fact.
(defthm fn2-alloc-identity-begin-produces-clearing
 (implies (and (fn2-extentsp fn2-extents) (fn2-extents-wfp fn2-extents)
               (fn2-alloc-identity-all-free-p (fn2-extents-rows fn2-extents) fn2-extents)
               (equal (car (fn2-alloc-identity-begin kind owner ogen source fn2-extents)) :more))
  (fn2-alloc-identity-clearing-p
   (mv-nth 1 (fn2-alloc-identity-begin kind owner ogen source fn2-extents))))
 :hints (("Goal" :in-theory (enable fn2-alloc-identity-begin fn2-alloc-identity-clearing-p))))
(defthm fn2-alloc-identity-clear-step-preserves-initialization
 (implies (fn2-alloc-identity-clearing-p fn2-extents)
  (if (equal (car (fn2-alloc-identity-clear-step kind owner ogen source fn2-extents)) :active)
   (fn2-alloc-identity-maintained-p
    (mv-nth 1 (fn2-alloc-identity-clear-step kind owner ogen source fn2-extents)))
   (fn2-alloc-identity-clearing-p
    (mv-nth 1 (fn2-alloc-identity-clear-step kind owner ogen source fn2-extents)))))
 :hints (("Goal" :in-theory (enable fn2-alloc-identity-clear-step fn2-alloc-identity-clearing-p
                                   fn2-alloc-identity-maintained-p))))
