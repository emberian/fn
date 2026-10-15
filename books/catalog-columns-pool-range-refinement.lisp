; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-record-projections")

(local (defthm fn-lbpr-take-fixed-full-length
 (equal (take (len xs) (true-list-fix xs)) (true-list-fix xs))
 :hints (("Goal" :induct (len xs) :in-theory (enable take len true-list-fix)))))

(local (defthm fn-lbpr-len-append
 (equal (len (append xs ys)) (+ (len xs) (len ys)))
 :hints (("Goal" :induct (len xs) :in-theory (enable binary-append len)))))

(local (defthm fn-lbpr-car-nthcdr
 (implies (natp off) (equal (car (nthcdr off xs)) (nth off xs)))
 :hints (("Goal" :induct (nthcdr off xs) :in-theory (enable nthcdr nth)))))

(local (defthm fn-lbpr-cdr-nthcdr
 (implies (natp off) (equal (cdr (nthcdr off xs)) (nthcdr (+ 1 off) xs)))
 :hints (("Goal" :induct (nthcdr off xs) :in-theory (enable nthcdr nth)))))

(local (defthm fn-lbpr-nthcdr-append-at-length
 (equal (nthcdr (len xs) (append xs ys)) ys)
 :hints (("Goal" :induct (len xs) :in-theory (enable nthcdr binary-append len)))))

(local (defthm fn-lbpr-take-full-length
 (equal (take (len xs) xs) (true-list-fix xs))
 :hints (("Goal" :induct (len xs) :in-theory (enable take len true-list-fix)))))

(local (defthm fn-lbpr-len-true-list-fix
 (equal (len (true-list-fix xs)) (len xs))
 :hints (("Goal" :induct (len xs) :in-theory (enable len true-list-fix)))))

(local (defthm fn-lbpr-true-list-fix-idempotent
 (equal (true-list-fix (true-list-fix xs)) (true-list-fix xs))
 :hints (("Goal" :induct (len xs) :in-theory (enable true-list-fix)))))

(defthm fn-lbc-msgid-pool-range-is-model-slice
 (implies (and (natp off) (natp n)
               (<= (+ off n) (fn-lbc-msgid-pool-count fn-lbc)))
  (equal (fn-lbc-msgid-pool-range off n fn-lbc)
         (take n (nthcdr off (fn-lbc-msgid-pool-model fn-lbc)))))
 :hints (("Goal" :induct (fn-lbc-msgid-pool-range off n fn-lbc)
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbc-msgid-pool-range fn-lbc-msgid-pool-octet-is-model-nth
     fn-lbc-msgid-pool-count-is-model-length fn-lbpr-car-nthcdr fn-lbpr-cdr-nthcdr take)))))

(defthm fn-lbc-msgid-pool-range-of-appended-bytes
 (equal (fn-lbc-msgid-pool-range (fn-lbc-msgid-pool-count fn-lbc) (len bytes)
         (fn-lbc-msgid-pool-append bytes fn-lbc))
        (true-list-fix bytes))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-msgid-pool-range-is-model-slice
          (off (fn-lbc-msgid-pool-count fn-lbc)) (n (len bytes))
          (fn-lbc (fn-lbc-msgid-pool-append bytes fn-lbc))))
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbc-msgid-pool-range-is-model-slice fn-lbc-msgid-pool-count-of-append
     fn-lbc-msgid-pool-append-is-model-append fn-lbc-msgid-pool-count-is-model-length
     fn-lbpr-nthcdr-append-at-length fn-lbpr-take-full-length fn-lbpr-len-true-list-fix
     fn-lbpr-true-list-fix-idempotent fn-lbpr-take-fixed-full-length fn-lbpr-len-append (:type-prescription fn-lbc-msgid-pool-count-natural))))))

(defthm fn-lbc-overview-pool-range-is-model-slice
 (implies (and (natp off) (natp n)
               (<= (+ off n) (fn-lbc-overview-pool-count fn-lbc)))
  (equal (fn-lbc-overview-pool-range off n fn-lbc)
         (take n (nthcdr off (fn-lbc-overview-pool-model fn-lbc)))))
 :hints (("Goal" :induct (fn-lbc-overview-pool-range off n fn-lbc)
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbc-overview-pool-range fn-lbc-overview-pool-octet-is-model-nth
     fn-lbc-overview-pool-count-is-model-length fn-lbpr-car-nthcdr fn-lbpr-cdr-nthcdr take)))))

(defthm fn-lbc-overview-pool-range-of-appended-bytes
 (equal (fn-lbc-overview-pool-range (fn-lbc-overview-pool-count fn-lbc) (len bytes)
         (fn-lbc-overview-pool-append bytes fn-lbc))
        (true-list-fix bytes))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-overview-pool-range-is-model-slice
          (off (fn-lbc-overview-pool-count fn-lbc)) (n (len bytes))
          (fn-lbc (fn-lbc-overview-pool-append bytes fn-lbc))))
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbc-overview-pool-range-is-model-slice fn-lbc-overview-pool-count-of-append
     fn-lbc-overview-pool-append-is-model-append fn-lbc-overview-pool-count-is-model-length
     fn-lbpr-nthcdr-append-at-length fn-lbpr-take-full-length fn-lbpr-len-true-list-fix
     fn-lbpr-true-list-fix-idempotent fn-lbpr-take-fixed-full-length fn-lbpr-len-append (:type-prescription fn-lbc-overview-pool-count-natural))))))
