(in-package "ACL2")
(include-book "format-base")
(fn2-book-layer :b)

(defun fn2-checkpoint-restore-zero-range (left at slot gen okind oslot ogen fn2-pool)
 (declare (xargs :stobjs fn2-pool :measure (nfix left)
  :guard (and (fn2-pool-wfp fn2-pool) (natp left)
              (<= left *fn2-format-sector-size*) (natp at))))
 (if (zp left) :ok
  (mv-let (code byte) (fn2-pool-read slot gen at okind oslot ogen fn2-pool)
   (cond ((not (eq code :ok)) code)
         ((not (equal byte 0)) :padding)
         (t (fn2-checkpoint-restore-zero-range (- left 1) (+ at 1)
                slot gen okind oslot ogen fn2-pool))))))
