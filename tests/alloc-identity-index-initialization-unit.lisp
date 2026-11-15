; Actual BEGIN/CLEAR controls. CORRUPT removes the actual all-FREE premise
; using explicit malformed semantic counters; it is not a valid cold prefix.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "../books/alloc-identity-index-initialization")
(include-book "alloc-identity-index-unit")
(defun fn2-aii-body (corrupt fn2-extents)
 (declare (xargs :stobjs fn2-extents :verify-guards nil))
 (b* (((mv start fn2-extents) (fn2-aiu-start 2 fn2-extents))
      ((mv adopted fn2-extents) (fn2-aiu-adopt 0 0 0 fn2-extents))
      ((mv ended fn2-extents) (fn2-alloc-identity-end 7 2 3 4 fn2-extents))
      (fn2-extents (if corrupt
       (update-fn2-alloc-total-reserved 0 (update-fn2-alloc-total-free 2 fn2-extents))
       (fn2-alloc-init 2 fn2-extents)))
      ; Stale USED bytes are legal while inactive and must be cleared. They
      ; do not stand for an allocator row or authorize a LIVE insertion.
      (fn2-extents (update-fn2-alloc-identity-statesi 0 *fn2-alloc-identity-bucket-used* fn2-extents))
      (typed (and (fn2-extentsp fn2-extents) (fn2-extents-wfp fn2-extents)))
      (fresh (fn2-alloc-identity-all-free-p 2 fn2-extents))
      ((mv begun fn2-extents) (fn2-alloc-identity-begin 7 2 3 4 fn2-extents))
      (clearing0 (fn2-alloc-identity-clearing-p fn2-extents))
      ((mv first fn2-extents) (fn2-alloc-identity-clear-step 7 2 3 4 fn2-extents))
      (clearing1 (fn2-alloc-identity-clearing-p fn2-extents))
      ((mv last fn2-extents) (fn2-alloc-identity-clear-step 7 2 3 4 fn2-extents)))
  (mv (and start adopted (eq ended :ok) typed (eq begun :more)
           (eq first :more) (eq last :active)
           (if corrupt
            (and (not fresh) (not clearing0) (not clearing1)
                 (not (fn2-alloc-identity-maintained-p fn2-extents)))
            (and fresh clearing0 clearing1 (fn2-alloc-identity-maintained-p fn2-extents)))) fn2-extents)))
(defun fn2-aii-run (corrupt)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-extents
  (mv-let (answer fn2-extents) (fn2-aii-body corrupt fn2-extents) answer)))
(assert-event (fn2-aii-run nil))
(assert-event (fn2-aii-run t))
