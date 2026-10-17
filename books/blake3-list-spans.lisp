; Generic algebra for the list-span view shared by the octet-buffer and
; string BLAKE3 refinements.  Callers include this book locally so these
; rewrite rules help their internal correspondence proofs without changing
; the exported rule set.
(in-package "ACL2")
(include-book "blake3")

(local (include-book "arithmetic/top" :dir :system))

(local
 (defthm fn-b3-span-nthx-of-firstn
   (equal (fn-b3-nthx j (fn-b3-firstn n l))
          (if (< (nfix j) (nfix n)) (fn-b3-nthx j l) 0))
   :hints (("Goal" :induct (list (fn-b3-nthx j l) (fn-b3-firstn n l))))))

(local
 (defthm fn-b3-span-nthx-of-nthcdrx
   (equal (fn-b3-nthx j (fn-b3-nthcdrx a l))
          (fn-b3-nthx (+ (nfix a) (nfix j)) l))
   :hints (("Goal" :induct (fn-b3-nthcdrx a l)))))

(local
 (defthm fn-b3-span-nthcdrx-of-firstn
   (equal (fn-b3-nthcdrx k (fn-b3-firstn n l))
          (fn-b3-firstn (- (nfix n) (nfix k)) (fn-b3-nthcdrx k l)))
   :hints (("Goal" :induct (list (fn-b3-nthcdrx k l) (fn-b3-firstn n l))))))

(local
 (defthm fn-b3-span-nthcdrx-of-nthcdrx
   (equal (fn-b3-nthcdrx k (fn-b3-nthcdrx p l))
          (fn-b3-nthcdrx (+ (nfix k) (nfix p)) l))
   :hints (("Goal" :induct (fn-b3-nthcdrx p l)))))

(local
 (defthm fn-b3-span-firstn-of-firstn
   (implies (<= (nfix k) (nfix n))
            (equal (fn-b3-firstn k (fn-b3-firstn n l))
                   (fn-b3-firstn k l)))
   :hints (("Goal" :induct (list (fn-b3-firstn k l) (fn-b3-firstn n l))))))
