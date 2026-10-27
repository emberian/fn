; Growth by either record writer preserves the other record type.
(in-package "ACL2")
(include-book "catalog-columns-membership-allocation")

(local (defthm fn-lbx-overview-count-of-nov-index-update
 (equal (fn-lbc-overview-pool-count (update-nth *fn-lbc-nov-store* value fn-lbc))
        (fn-lbc-overview-pool-count fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory
 (union-theories (theory 'ground-zero)
  '(fn-lbc-overview-pool-count fn-lbc-overview-store fn-dm-nth-update-nth nth))))))

(local (defthm fn-lbx-overview-count-of-membership-index-update
 (equal (fn-lbc-overview-pool-count (update-nth *fn-lbc-membership-store* value fn-lbc))
        (fn-lbc-overview-pool-count fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory
 (union-theories (theory 'ground-zero)
  '(fn-lbc-overview-pool-count fn-lbc-overview-store fn-dm-nth-update-nth nth))))))

(defthm fn-lbc-overview-pool-count-of-append-nov
 (equal (fn-lbc-overview-pool-count (fn-lbc-append-nov nov fn-lbc))
        (+ (fn-lbc-overview-pool-count fn-lbc)
           (len (fn-lbc-texts-octets-model (fn-lbc-nov-texts nov)))))
 :hints (("Goal" :do-not-induct t :in-theory
 (union-theories (theory 'ground-zero)
  '(fn-lbc-append-nov update-fn-lbc-nov-store
    fn-lbx-overview-count-of-nov-index-update fn-lbc-overview-pool-count-of-append-nov-texts)))))

(defthm fn-lbc-overview-pool-count-of-append-memberships-monotone
 (<= (fn-lbc-overview-pool-count fn-lbc)
     (fn-lbc-overview-pool-count (fn-lbc-append-memberships items numbersp fn-lbc)))
 :rule-classes :linear
 :hints (("Goal" :induct (fn-lbc-append-memberships items numbersp fn-lbc)
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbc-append-memberships update-fn-lbc-membership-store
     fn-lbx-overview-count-of-membership-index-update fn-lbc-overview-pool-count-of-append)))))

(defthm fn-lbc-nov-records-layoutp-of-append-memberships
 (implies (fn-lb-column-nov-records-layoutp (nth *fn-lbc-nov-store* fn-lbc)
                                              (fn-lbc-overview-pool-count fn-lbc))
  (fn-lb-column-nov-records-layoutp
   (nth *fn-lbc-nov-store* (fn-lbc-append-memberships items numbersp fn-lbc))
   (fn-lbc-overview-pool-count (fn-lbc-append-memberships items numbersp fn-lbc))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lb-column-nov-records-layoutp-monotone
    (records (nth *fn-lbc-nov-store* fn-lbc))
    (old (fn-lbc-overview-pool-count fn-lbc))
    (new (fn-lbc-overview-pool-count (fn-lbc-append-memberships items numbersp fn-lbc)))))
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbwf-append-memberships-field fn-lbc-overview-pool-count-of-append-memberships-monotone
     (:type-prescription fn-lbc-overview-pool-count-natural) nfix)))))

(defthm fn-lbc-membership-records-layoutp-of-append-nov
 (implies (fn-lb-column-membership-records-layoutp (nth *fn-lbc-membership-store* fn-lbc)
                                              (fn-lbc-overview-pool-count fn-lbc))
  (fn-lb-column-membership-records-layoutp
   (nth *fn-lbc-membership-store* (fn-lbc-append-nov nov fn-lbc))
   (fn-lbc-overview-pool-count (fn-lbc-append-nov nov fn-lbc))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lb-column-membership-records-layoutp-monotone
    (records (nth *fn-lbc-membership-store* fn-lbc))
    (old (fn-lbc-overview-pool-count fn-lbc))
    (new (fn-lbc-overview-pool-count (fn-lbc-append-nov nov fn-lbc)))))
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbwf-append-nov-field fn-lbc-overview-pool-count-of-append-nov
     (:type-prescription fn-lbc-overview-pool-count-natural) nfix)))))
