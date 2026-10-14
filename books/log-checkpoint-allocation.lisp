; Allocation-state observations shared with the eventual adopt/replay path.
(in-package "ACL2")
(include-book "log-checkpoint-values")

(defun fn-lc-largest-physical-id (segs)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp segs) (max (nfix (mbe :logic (caar segs) :exec (fn-lc-head (fn-lc-head segs)))) (fn-lc-largest-physical-id (mbe :logic (cdr segs) :exec (fn-lc-rest segs)))) 0))
(defun fn-lc-allocation-header (header segs)
  (declare (xargs :guard (fn-lc-headerp header) :verify-guards nil))
  (let ((next (max (fn-lc-header-next-id header)
                   (if (consp segs) (+ 1 (fn-lc-largest-physical-id segs)) 0))))
    (update-nth 3 (or (fn-lc-header-exhaustedp header)
                      (< 18446744073709551615 next))
                (update-nth 2 (min 18446744073709551615 next) header))))

; Search mutant: omit the physical reservation reconciliation at open.
; No column adoption/replay is pretended here; this is exactly the root-only
; allocation arm whose half-written reservation tooth must be falsified.
(defun fn-lc-mutant-root-only-open (disk r mode segs)
  (declare (xargs :guard t :verify-guards nil))
  (let ((header (fn-lc-adopted-header disk r mode)))
    (if (fn-lc-headerp header) (list :ok header segs) (list :refused header segs))))
