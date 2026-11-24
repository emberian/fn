; Inputs to the second checker after the adapter's single-byte write.
(in-package "ACL2")
(include-book "ribbon-false-neg-finish-proof")

(defun-nx fn2-ribbon-flipped-pool (off x pool)
  (let ((byte (mv-nth 1 (fn2-pool-read 0 1 off 9 0 1 pool))))
    (mv-nth 1 (fn2-pool-write 0 1 off (logxor (nfix x) (nfix byte)) 9 0 1 pool))))

(defmacro fn2-ribbon-read-page (pool)
  `(fn2-run-read-bytes *fn2-run-page-size* 0 1 0 9 0 1 ,pool))

(defun-nx fn2-ribbon-rechecked-state (keys off x)
  (let ((st (fn2-ribbon-final-check keys)))
    (fn2-ribbon-call-with-state fn2-rba-check (0 1) st
                                (6 (fn2-ribbon-flipped-pool off x (mv-nth 6 st))))))
