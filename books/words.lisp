;; Fixed-width word operations shared by the simulator's PRNG (sim/prng.lisp) and the
;; books that hash (C's ribbon filter): u32 reduction, the u32 product with no
;; intermediate above 2^49 (SBCL fixnums), and the 32-bit mixing finalizer.
(in-package "ACL2")
(include-book "arithmetic-3/floor-mod/floor-mod" :dir :system)

(defun fn2-u32 (x)
  (declare (xargs :guard (integerp x)))
  (mod (ifix x) 4294967296))
(defthm fn2-u32-type
  (unsigned-byte-p 32 (fn2-u32 x)))
(defthm fn2-u32-natp
  (natp (fn2-u32 x)) :rule-classes :type-prescription)
(defthm fn2-u32-bound
  (< (fn2-u32 x) 4294967296) :rule-classes :linear)
(in-theory (disable fn2-u32))

(defun fn2-u32-mul (a b)
  (declare (xargs :guard (and (unsigned-byte-p 32 a) (unsigned-byte-p 32 b))))
  (let* ((al (mod a 65536)) (ah (floor a 65536))
         (bl (mod b 65536)) (bh (floor b 65536))
         (cross (mod (+ (* al bh) (* ah bl)) 65536)))
    (fn2-u32 (+ (* al bl) (* 65536 cross)))))
(defthm fn2-u32-mul-type
  (unsigned-byte-p 32 (fn2-u32-mul a b)))
(in-theory (disable fn2-u32-mul))

;; MurmurHash3's 32-bit finalizer (fmix32).
(defun fn2-prng-mix32 (x)
  (declare (xargs :guard (unsigned-byte-p 32 x)))
  (let* ((x (fn2-u32 (logxor x (ash x -16))))
         (x (fn2-u32-mul x 2246822507))
         (x (fn2-u32 (logxor x (ash x -13))))
         (x (fn2-u32-mul x 3266489909)))
    (fn2-u32 (logxor x (ash x -16)))))
(defthm fn2-prng-mix32-type
  (unsigned-byte-p 32 (fn2-prng-mix32 x)))
(in-theory (disable fn2-prng-mix32))

(assert-event (and (equal (fn2-u32-mul 4294967295 4294967295) 1)
                   (equal (fn2-prng-mix32 0) 0)
                   (equal (fn2-prng-mix32 1) 1364076727)))
