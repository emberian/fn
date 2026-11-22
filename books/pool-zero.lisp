; Zero a bounded range of an owned pool workspace.
(in-package "ACL2")
(include-book "pool")
(fn2-book-layer :b)

; Zero N bytes starting at POS. Callers supply their work bound and write
; at or below the fill, so zeroing may scrub existing bytes or append.
(defun fn2-run-zero (n slot gen pos okind oslot ogen fn2-pool)
 (declare (xargs :stobjs fn2-pool :measure (nfix n)
  :guard (and (fn2-pool-wfp fn2-pool) (natp n) (natp pos))))
 (if (zp n) (mv :ok fn2-pool)
  (mv-let (code fn2-pool) (fn2-pool-write slot gen pos 0 okind oslot ogen fn2-pool)
   (if (eq code :ok) (fn2-run-zero (- n 1) slot gen (+ 1 pos) okind oslot ogen fn2-pool)
    (mv code fn2-pool)))))
(fn2-pool-preserves fn2-run-zero (n slot gen pos okind oslot ogen fn2-pool) :position 1
 :hints (("Goal" :in-theory (disable fn2-pool-rows))))
