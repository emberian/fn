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

(defun fn2-pool-init-multiclass-witness ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-pool
    (mv-let (result fn2-pool)
      (let* ((classes '((0 . 64) (2 . 128) (1 . 256)))
             (antecedent (and (fn2-poolp fn2-pool) (fn2-pool-profilep classes)
                              (unsigned-byte-p 60 7) (unsigned-byte-p 60 9) (<= 7 9)))
             (fn2-pool (fn2-pool-init classes 7 9 fn2-pool)))
        (mv (list antecedent (fn2-pool-semanticp fn2-pool)
                  (fn2-pool-class-snapshot 0 fn2-pool)
                  (fn2-pool-class-snapshot 1 fn2-pool)
                  (fn2-pool-class-snapshot 2 fn2-pool)
                  (list (fn2-pool-base 0 fn2-pool) (fn2-pool-base 1 fn2-pool) (fn2-pool-base 2 fn2-pool))
                  (list (fn2-pool-next-free 0 fn2-pool) (fn2-pool-next-free 1 fn2-pool) (fn2-pool-next-free 2 fn2-pool))
                  (fn2-pool-nslots fn2-pool) (fn2-pool-nclasses fn2-pool)
                  (fn2-pool-gen-limit fn2-pool) (fn2-pool-retired-count fn2-pool)
                  (fn2-pool-capacity-bytes fn2-pool)) fn2-pool))
      result)))
(assert-event
 (equal (fn2-pool-init-multiclass-witness)
        (list t t (list *fn2-none* 0 64) '(0 2 128) '(2 1 256)
              '(0 128 256) (list 1 *fn2-none* *fn2-none*) 3 3 9 0 512)))
