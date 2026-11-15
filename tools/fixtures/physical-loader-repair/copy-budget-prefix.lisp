 ; COPY charges both the source read and destination write. This is the
 ; actual payload count used below, not a second phase implementation.
(defun fn2-run-load-copy-count (budget copied)
 (declare (xargs :guard (and (natp budget) (natp copied) (< copied *fn2-commit-unit-bytes*))))
 (min (floor budget 2) (- *fn2-commit-unit-bytes* copied)))
(defthm fn2-run-load-copy-count-bound
 (implies (and (natp budget) (natp copied) (< copied *fn2-commit-unit-bytes*))
  (and (natp (fn2-run-load-copy-count budget copied))
       (<= (* 2 (fn2-run-load-copy-count budget copied)) budget)
       (<= (+ copied (fn2-run-load-copy-count budget copied)) *fn2-commit-unit-bytes*)))
 :hints (("Goal" :in-theory (enable fn2-run-load-copy-count))) :rule-classes nil)
