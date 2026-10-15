; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-nov-text-readback")

(defthm fn-lbc-overview-pool-range-by-store
 (implies (and (natp off) (natp n))
  (equal (fn-lbc-overview-pool-range off n fn-lbc)
   (if (<= (+ off n) (len (nth *fn-lbc-overview-store* fn-lbc)))
    (take n (nthcdr off (strip-cars (nth *fn-lbc-overview-store* fn-lbc)))) nil)))
 :hints (("Goal" :do-not-induct t :cases ((<= (+ off n) (fn-lbc-overview-pool-count fn-lbc)))
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbc-overview-pool-range fn-lbc-overview-pool-range-is-model-slice
     fn-lbc-overview-pool-model fn-lbc-overview-pool-count fn-lbc-overview-store
     fn-lbc-overview-octets-count-is-len)))))

(defthm fn-lb-nov-span-bytes-corr-of-same-pool-store
 (implies (equal (nth *fn-lbc-overview-store* new) (nth *fn-lbc-overview-store* fn-lbc))
  (equal (fn-lb-nov-span-bytes-corr spans texts new)
         (fn-lb-nov-span-bytes-corr spans texts fn-lbc)))
 :hints (("Goal" :induct (fn-lb-nov-span-bytes-corr spans texts fn-lbc)
  :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
   '(fn-lb-nov-span-bytes-corr fn-lbc-overview-pool-range-by-store)) '((:definition nfix) (tau-system))))))

(defthm fn-lbc-nov-span-bytes-corr-of-append-nov
 (equal (fn-lb-nov-span-bytes-corr spans texts (fn-lbc-append-nov nov fn-lbc))
        (fn-lb-nov-span-bytes-corr spans texts
          (fn-lbc-append-nov-texts (fn-lbc-nov-texts nov) fn-lbc)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lb-nov-span-bytes-corr-of-same-pool-store
    (new (fn-lbc-append-nov nov fn-lbc))
    (fn-lbc (fn-lbc-append-nov-texts (fn-lbc-nov-texts nov) fn-lbc))))
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbc-append-nov update-fn-lbc-nov-store fn-dm-nth-update-nth)))))

(defthm fn-lbc-new-nov-spans-read-appended-bytes
 (implies (fn-lbc-nov-pool-fitp nov (fn-lbc-overview-pool-count fn-lbc))
  (fn-lb-nov-span-bytes-corr
   (fn-lbc-nov-spans (fn-lbc-nov-texts nov) (fn-lbc-overview-pool-count fn-lbc))
   (fn-lbc-nov-texts nov) (fn-lbc-append-nov nov fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-nov-pool-fitp fn-lbc-nov-span-bytes-corr-of-append-nov
     fn-lbc-nov-text-spans-read-appended-bytes)))))
