; Structural span bounds are monotone as the actual native pool grows.
(in-package "ACL2")
(include-book "catalog-columns-storage-invariants")
(include-book "catalog-columns-pool-text-properties")

(defthm fn-lb-column-span-in-poolp-monotone
 (implies (and (fn-lb-column-span-in-poolp start length old)
               (<= (nfix old) (nfix new)))
          (fn-lb-column-span-in-poolp start length new))
 :hints (("Goal" :in-theory (enable fn-lb-column-span-in-poolp))))

(defthm fn-lb-column-nov-record-layoutp-monotone
 (implies (and (fn-lb-column-nov-record-layoutp record old) (<= (nfix old) (nfix new)))
          (fn-lb-column-nov-record-layoutp record new))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
 :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
  '(fn-lb-column-nov-record-layoutp fn-lb-column-span-in-poolp)) '(nfix (tau-system))))))

(defthm fn-lb-column-nov-records-layoutp-monotone
 (implies (and (fn-lb-column-nov-records-layoutp records old) (<= (nfix old) (nfix new)))
          (fn-lb-column-nov-records-layoutp records new))
 :hints (("Goal" :induct (fn-lb-column-nov-records-layoutp records old)
 :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
  '(fn-lb-column-nov-records-layoutp fn-lb-column-nov-record-layoutp fn-lb-column-span-in-poolp)) '(nfix (tau-system))))))

(defthm fn-lb-column-nov-records-layoutp-of-text-pool-growth
 (implies (fn-lb-column-nov-records-layoutp records (fn-lbc-overview-pool-count fn-lbc))
          (fn-lb-column-nov-records-layoutp records
           (fn-lbc-overview-pool-count (fn-lbc-append-nov-texts texts fn-lbc))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lb-column-nov-records-layoutp-monotone
         (old (fn-lbc-overview-pool-count fn-lbc))
         (new (fn-lbc-overview-pool-count (fn-lbc-append-nov-texts texts fn-lbc)))))
 :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-overview-pool-count-of-append-nov-texts
    (:type-prescription fn-lbc-overview-pool-count-natural) nfix)))))

(defthm fn-lb-column-membership-record-layoutp-monotone
 (implies (and (fn-lb-column-membership-record-layoutp record old) (<= (nfix old) (nfix new)))
          (fn-lb-column-membership-record-layoutp record new))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
 :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
  '(fn-lb-column-membership-record-layoutp fn-lb-column-span-in-poolp)) '(nfix (tau-system))))))

(defthm fn-lb-column-membership-records-layoutp-monotone
 (implies (and (fn-lb-column-membership-records-layoutp records old) (<= (nfix old) (nfix new)))
          (fn-lb-column-membership-records-layoutp records new))
 :hints (("Goal" :induct (fn-lb-column-membership-records-layoutp records old)
 :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
  '(fn-lb-column-membership-records-layoutp fn-lb-column-membership-record-layoutp fn-lb-column-span-in-poolp)) '(nfix (tau-system))))))

(defthm fn-lb-column-membership-records-layoutp-of-text-pool-growth
 (implies (fn-lb-column-membership-records-layoutp records (fn-lbc-overview-pool-count fn-lbc))
          (fn-lb-column-membership-records-layoutp records
           (fn-lbc-overview-pool-count (fn-lbc-append-nov-texts texts fn-lbc))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lb-column-membership-records-layoutp-monotone
         (old (fn-lbc-overview-pool-count fn-lbc))
         (new (fn-lbc-overview-pool-count (fn-lbc-append-nov-texts texts fn-lbc)))))
 :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-overview-pool-count-of-append-nov-texts
    (:type-prescription fn-lbc-overview-pool-count-natural) nfix)))))
