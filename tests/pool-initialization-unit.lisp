(in-package "ACL2")
(include-book "../books/pool-initialization")
(defun fn2-pool-carve-witness (left)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-pool
    (mv-let (snapshot fn2-pool)
      (let* ((fn2-pool (fn2-pool-columns-init 1 fn2-pool))
             (fn2-pool (fn2-pool-carve-slots left 0 0 64 0 1 fn2-pool)))
        (mv (fn2-pool-row-snapshot 0 fn2-pool) fn2-pool))
      snapshot)))
; Whole row-span and byte-span hypotheses, plus the formula's conclusion.
(assert-event
 (and (natp 1) (natp 0) (posp 64) (<= (+ 0 1) 1)
      (<= (+ 0 (* 1 64)) 1152921504606846976)
      (equal (fn2-pool-carve-witness 1)
             (list 1 0 64 *fn2-pool-state-free* 0 0 0 0 0 0 0 0 0 0 0 0 *fn2-none* 0))))
; Remove only the allocated-row extent bound: the implementation terminates
; the chain at the actual array end, rather than naming nonexistent row 1.
(assert-event
 (and (natp 2) (natp 0) (posp 64)
      (not (<= (+ 0 2) 1))
      (<= (+ 0 (* 2 64)) 1152921504606846976)
      (not (equal (fn2-pool-carve-witness 2)
                  (list 1 0 64 *fn2-pool-state-free* 0 0 0 0 0 0 0 0 0 0 0 0 1 0)))))
