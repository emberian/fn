; Concrete buffer writer: whole-antecedent witness and a source-range tooth.
(in-package "ACL2")
(include-book "../../books/checkpoint-payloads-exec")
(include-book "must-fail-checked")

(defun cplxt-write (x a n base)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-octets
    (mv-let (r fn-octets)
      (let ((fn-octets (fn-octets-from-list x fn-octets)))
        (mv-let (ref trailer fn-octets)
          (fn-cpl-x-write-frame a n base fn-octets)
          (mv (list ref trailer (fn-octets-list fn-octets)) fn-octets)))
      r)))

(assert-event
 (let* ((x '(9 1 2 3 8)) (a 1) (n 3) (base 70)
        (p (fn-shr-win a n x)) (r (cplxt-write x a n base)))
   (and (fn-octets-p x) (natp a) (natp n) (natp base)
        (<= (+ a n) (len x)) (< (+ 1 n) 18446744073709551616)
        (equal (car r) (list (+ base 37) (len p)))
        (equal (cadr r) (fn-cpl-trailer p))
        (equal (caddr r) (append x (fn-cpl-frame p)))
        (equal (fn-cpl-pack-words (cadr r) 4) (fn-cpl-trailer-words-impl p)))))

; Removing source containment is false: after two source bytes the back-copy
; reads the newly appended header's first byte, 70, rather than a source byte.
; This is a logical corrupted-input witness, never a native call past a guard.
(defthm cplxt-source-containment-removal
  (let* ((x '(1 2)) (a 0) (n 3) (base 70)
         (p (fn-shr-win a n x))
         (r (fn-cpl-x-write-frame a n base x)))
    (and (fn-octets-p x) (natp a) (natp n) (natp base)
         (< (+ 1 n) 18446744073709551616)
         (not (<= (+ a n) (len x)))
         (not (equal (mv-nth 2 r) (fn-cpl-write-frame p x)))
         (not (equal (fn-cpl-pack-words (mv-nth 1 r) 4)
                     (fn-cpl-trailer-words-impl p)))))
  :rule-classes nil)
