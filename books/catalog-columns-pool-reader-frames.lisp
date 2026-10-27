; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-pool-range-refinement")

(defthm fn-lbc-overview-pool-range-of-append-nov-texts-prefix
 (implies (and (natp off) (natp n) (<= (+ off n) (fn-lbc-overview-pool-count fn-lbc)))
  (equal (fn-lbc-overview-pool-range off n (fn-lbc-append-nov-texts texts fn-lbc))
         (fn-lbc-overview-pool-range off n fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-append-nov-texts texts fn-lbc)
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbc-append-nov-texts fn-lbc-overview-pool-range-of-append-prefix
     fn-lbc-overview-pool-count-of-append)))))

(local (defthm fn-lbpf-overview-octet-by-store
 (equal (fn-lbc-overview-pool-octet i fn-lbc)
  (if (natp i) (nth i (strip-cars (nth *fn-lbc-overview-store* fn-lbc))) nil))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-overview-pool-octet-is-model-nth fn-lbc-overview-pool-model))))))

(local (defthm fn-lbpf-overview-count-by-store
 (equal (fn-lbc-overview-pool-count fn-lbc) (len (nth *fn-lbc-overview-store* fn-lbc)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-overview-pool-count fn-lbc-overview-store fn-lbc-overview-octets-count-is-len))))))

(local (defthm fn-lbpf-overview-range-of-other-field-update
 (implies (and (natp off) (natp n) (natp field) (not (equal field *fn-lbc-overview-store*)))
  (equal (fn-lbc-overview-pool-range off n (update-nth field value fn-lbc))
         (fn-lbc-overview-pool-range off n fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-overview-pool-range off n fn-lbc)
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbc-overview-pool-range fn-lbpf-overview-octet-by-store fn-lbpf-overview-count-by-store
     fn-dm-nth-update-nth))))))

(defthm fn-lbc-overview-pool-range-of-append-nov-prefix
 (implies (and (natp off) (natp n) (<= (+ off n) (fn-lbc-overview-pool-count fn-lbc)))
  (equal (fn-lbc-overview-pool-range off n (fn-lbc-append-nov nov fn-lbc))
         (fn-lbc-overview-pool-range off n fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbc-append-nov update-fn-lbc-nov-store fn-lbpf-overview-range-of-other-field-update
     fn-lbc-overview-pool-range-of-append-nov-texts-prefix)))))

(local (defthm fn-lbpf-overview-count-of-membership-store-update
  (equal (fn-lbc-overview-pool-count (update-nth *fn-lbc-membership-store* value fn-lbc))
         (fn-lbc-overview-pool-count fn-lbc))
  :hints (("Goal" :do-not-induct t :in-theory
   (union-theories (theory 'ground-zero)
    '(fn-lbpf-overview-count-by-store fn-dm-nth-update-nth))))))

(defthm fn-lbc-overview-pool-range-of-append-memberships-prefix
 (implies (and (natp off) (natp n) (<= (+ off n) (fn-lbc-overview-pool-count fn-lbc)))
  (equal (fn-lbc-overview-pool-range off n (fn-lbc-append-memberships items numbersp fn-lbc))
         (fn-lbc-overview-pool-range off n fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-append-memberships items numbersp fn-lbc)
  :in-theory (set-difference-theories
   (union-theories (theory 'ground-zero)
    '(fn-lbc-append-memberships update-fn-lbc-membership-store
      fn-lbpf-overview-range-of-other-field-update fn-lbpf-overview-count-of-membership-store-update
      fn-lbc-overview-pool-range-of-append-prefix fn-lbc-overview-pool-count-of-append
      fn-dm-nth-update-nth)) '((tau-system))))))
