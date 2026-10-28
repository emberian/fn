(in-package "ACL2")
(include-book "../books/blake3")

; Test fixture only: pool octets repeat 0..250, as in the official vectors.
(defun fn2-b3-unit-fill (i n fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil
                  :measure (nfix (- (nfix n) (nfix i)))))
  (if (or (not (natp i)) (not (natp n)) (>= i n)) fn2-pool
    (mv-let (code fn2-pool) (fn2-pool-write 0 1 i (mod i 251) 1 0 1 fn2-pool)
      (declare (ignore code))
      (fn2-b3-unit-fill (+ i 1) n fn2-pool))))
(defun fn2-b3-unit-one (n split expected fn2-b3 fn2-pool)
  (declare (xargs :stobjs (fn2-b3 fn2-pool) :verify-guards nil))
  (let ((fn2-b3 (fn2-b3-init 0 0 0 0 0 0 0 0 0 0 fn2-b3)))
    (mv-let (code count fn2-b3) (fn2-b3-update 0 0 1 0 split 1 0 1 fn2-b3 fn2-pool)
      (let ((first-ok (and (eq code :ok) (equal count split))))
        (mv-let (code count fn2-b3)
          (fn2-b3-update 0 0 1 split (- n split) 1 0 1 fn2-b3 fn2-pool)
          (mv (and first-ok (eq code :ok) (equal count (- n split))
                   (equal (mv-list 8 (fn2-b3-finalize 0 fn2-b3)) expected)) fn2-b3))))))
(defun fn2-b3-unit ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-b3
    (mv-let (ok fn2-b3)
      (with-local-stobj fn2-pool
        (mv-let (ok fn2-b3 fn2-pool)
          (let* ((fn2-b3 (fn2-b3-table-init 1 fn2-b3))
                 (fn2-pool (fn2-pool-init '((1 . 2048)) 1 100 fn2-pool)))
            (mv-let (code slot gen fn2-pool) (fn2-pool-reserve 0 1 0 1 fn2-pool)
              (declare (ignore code slot gen))
              (let ((fn2-pool (fn2-b3-unit-fill 0 2048 fn2-pool)))
                (mv-let (a fn2-b3) (fn2-b3-unit-one 0 0
                  '(3108574127 2795633141 3930931360 1237965878 3374697371 3071459757 3398671052 1647452132) fn2-b3 fn2-pool)
                  (mv-let (b fn2-b3) (fn2-b3-unit-one 1 1
                    '(3755883053 4049673201 896436300 1932959919 2810695021 3249874765 3492086353 333615861) fn2-b3 fn2-pool)
                    (mv-let (c fn2-b3) (fn2-b3-unit-one 1024 63
                      '(960962882 111449584 3733191923 1249151416 838340032 1437208001 308124440 4149904668) fn2-b3 fn2-pool)
                      (mv-let (d fn2-b3) (fn2-b3-unit-one 1025 1024
                        '(2927100624 3005737799 1741663823 1059520180 692180354 3657416982 4223110268 1149520769) fn2-b3 fn2-pool)
                        (mv (and a b c d) fn2-b3 fn2-pool))))))))
          (mv ok fn2-b3)))
      ok)))
(assert-event (fn2-b3-unit))
(assert-event (and (eq (symbol-class 'fn2-b3-init (w state)) :common-lisp-compliant)
                   (eq (symbol-class 'fn2-b3-update (w state)) :common-lisp-compliant)
                   (eq (symbol-class 'fn2-b3-update-const (w state)) :common-lisp-compliant)
                   (eq (symbol-class 'fn2-b3-finalize (w state)) :common-lisp-compliant)))

; Evaluated whole antecedents and conclusions of both owed statements.
; The negative incremental witness removes the per-update budget hypothesis.
(assert-event
 (let* ((splits '((0) (1)))
        (hyp (fn2-b3-incremental-hyps splits))
        (conclusion (fn2-b3-incremental-resultp splits)))
   (and hyp conclusion)))
(assert-event
 (let* ((splits (list (make-list 4097 :initial-element 0)))
        (hyp (fn2-b3-incremental-hyps splits))
        (conclusion (fn2-b3-incremental-resultp splits)))
   (and (not hyp) (not conclusion))))
; The negative subtree witness removes the absolute right chunk counter.
(assert-event
 (let* ((blocks (list (make-list 16 :initial-element (make-list 4096 :initial-element 0)) '((1))))
        (positive-hyp (fn2-b3-subtree-hyps blocks '(0 64)))
        (positive-conclusion (fn2-b3-subtree-resultp blocks '(0 64)))
        (negative-hyp (fn2-b3-subtree-hyps blocks '(0 0)))
        (negative-conclusion (fn2-b3-subtree-resultp blocks '(0 0))))
   (and positive-hyp positive-conclusion (not negative-hyp) (not negative-conclusion))))
