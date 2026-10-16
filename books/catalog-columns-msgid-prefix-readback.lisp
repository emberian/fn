; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-old-scalar-readers")

(local (defthm fn-lbmpr-take-append-prefix
 (implies (and (natp n) (<= n (len xs)))
  (equal (take n (append xs ys)) (take n xs)))
 :hints (("Goal" :induct (take n xs) :in-theory (enable take binary-append len)))))

(local (defthm fn-lbmpr-nthcdr-append-prefix
 (implies (and (natp off) (<= off (len xs)))
  (equal (nthcdr off (append xs ys)) (append (nthcdr off xs) ys)))
 :hints (("Goal" :induct (nthcdr off xs) :in-theory (enable nthcdr binary-append len)))))

(local (defthm fn-lbmpr-len-nthcdr
 (equal (len (nthcdr off xs)) (nfix (- (len xs) (nfix off))))
 :hints (("Goal" :induct (nthcdr off xs) :in-theory (enable nthcdr len nfix)))))

(local (defthm fn-lbmpr-len-append
 (equal (len (append xs ys)) (+ (len xs) (len ys)))
 :hints (("Goal" :induct (len xs) :in-theory (enable binary-append len)))))

(defthm fn-lbc-msgid-pool-range-of-append-row-prefix
 (implies (and (natp off) (natp n) (<= (+ off n) (fn-lbc-msgid-pool-count fn-lbc)))
  (equal (fn-lbc-msgid-pool-range off n (fn-lbc-append-row row log fn-lbc))
         (fn-lbc-msgid-pool-range off n fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-msgid-pool-range-by-model fn-lbc-msgid-pool-model-of-append-row
     fn-lbc-msgid-pool-count-is-model-length fn-lbmpr-take-append-prefix
     fn-lbmpr-nthcdr-append-prefix fn-lbmpr-len-nthcdr fn-lbmpr-len-append nfix)))))
