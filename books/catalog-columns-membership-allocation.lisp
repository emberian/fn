; Actual membership append preserves retained and newly allocated spans.
(in-package "ACL2")
(include-book "catalog-columns-nov-allocation")

(local (defthm fn-lbma-overview-count-of-membership-index-update
  (equal (fn-lbc-overview-pool-count (update-nth *fn-lbc-membership-store* value fn-lbc))
         (fn-lbc-overview-pool-count fn-lbc))
  :hints (("Goal" :do-not-induct t
   :in-theory (union-theories (theory 'ground-zero)
    '(fn-lbc-overview-pool-count fn-lbc-overview-store fn-dm-nth-update-nth nth))))))

(local (defthm fn-lbma-membership-layoutp-of-append-one
  (implies (and (fn-lb-column-membership-records-layoutp records limit)
                (fn-lb-column-membership-record-layoutp record limit))
   (fn-lb-column-membership-records-layoutp (append records (list record)) limit))
  :hints (("Goal" :induct (len records)
   :in-theory (union-theories (theory 'ground-zero)
    '(fn-lb-column-membership-records-layoutp binary-append))))))

(defthm fn-lbc-encoded-membership-record-is-in-pool
  (implies (natp offset)
   (fn-lb-column-membership-record-layoutp
    (list (fn-lbc-u64 offset) (fn-lbc-u64 (len bytes)) number)
    (+ offset (len bytes))))
  :hints (("Goal" :do-not-induct t
   :in-theory (union-theories (theory 'ground-zero)
    '(fn-lb-column-membership-record-layoutp fn-lbc-clamped-span-in-pool nth)))))

(local (defthm fn-lbma-membership-layoutp-after-byte-growth
  (implies (fn-lb-column-membership-records-layoutp records (fn-lbc-overview-pool-count fn-lbc))
   (fn-lb-column-membership-records-layoutp records
     (+ (len bytes) (fn-lbc-overview-pool-count fn-lbc))))
  :hints (("Goal" :do-not-induct t
   :use ((:instance fn-lb-column-membership-records-layoutp-monotone
     (old (fn-lbc-overview-pool-count fn-lbc))
     (new (+ (len bytes) (fn-lbc-overview-pool-count fn-lbc)))))
   :in-theory (union-theories (theory 'ground-zero)
     '((:type-prescription fn-lbc-overview-pool-count-natural) nfix))))))

(local (defthm fn-lbma-append-encoded-membership-layoutp
  (implies (and (natp offset) (fn-lb-column-membership-records-layoutp records offset))
   (fn-lb-column-membership-records-layoutp
    (append records (list (list (fn-lbc-u64 offset) (fn-lbc-u64 (len bytes)) number)))
    (+ offset (len bytes))))
  :hints (("Goal" :do-not-induct t
   :use ((:instance fn-lb-column-membership-records-layoutp-monotone
           (old offset) (new (+ offset (len bytes))))
         (:instance fn-lbc-encoded-membership-record-is-in-pool)
         (:instance fn-lbma-membership-layoutp-of-append-one
           (record (list (fn-lbc-u64 offset) (fn-lbc-u64 (len bytes)) number))
           (limit (+ offset (len bytes)))))
   :in-theory (union-theories (theory 'ground-zero) '(nfix))))))

(defthm fn-lbc-membership-records-layoutp-of-append-memberships
  (implies
   (fn-lb-column-membership-records-layoutp (nth *fn-lbc-membership-store* fn-lbc)
                                        (fn-lbc-overview-pool-count fn-lbc))
   (fn-lb-column-membership-records-layoutp
    (nth *fn-lbc-membership-store* (fn-lbc-append-memberships items numbersp fn-lbc))
    (fn-lbc-overview-pool-count (fn-lbc-append-memberships items numbersp fn-lbc))))
  :hints (("Goal" :induct (fn-lbc-append-memberships items numbersp fn-lbc)
   :do-not '(preprocess)
   :in-theory (set-difference-theories
    (union-theories (theory 'ground-zero)
     '(fn-lbc-append-memberships fn-lbc-membership-store update-fn-lbc-membership-store
       fn-lbc-memberships-append-is-append fn-dm-nth-update-nth
       fn-lbwf-overview-pool-append-field fn-lbc-overview-pool-count-of-append
       fn-lbma-overview-count-of-membership-index-update fn-lbma-membership-layoutp-of-append-one
       fn-lbc-encoded-membership-record-is-in-pool fn-lbma-membership-layoutp-after-byte-growth fn-lbma-append-encoded-membership-layoutp
       (:type-prescription fn-lbc-overview-pool-count-natural)
       commutativity-of-+ associativity-of-+)) '((tau-system))))))
