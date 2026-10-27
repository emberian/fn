; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-pool-layout")

(local (defthm fn-lbpe-count-by-store
 (equal (fn-lbc-overview-pool-count fn-lbc) (len (nth *fn-lbc-overview-store* fn-lbc)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-overview-pool-count fn-lbc-overview-store fn-lbc-overview-octets-count-is-len))))))

(local (defthm fn-lbpe-pool-layout-by-fields
 (implies (and (equal (nth *fn-lbc-overview-store* new) (nth *fn-lbc-overview-store* fn-lbc))
               (equal (nth *fn-lbc-nov-store* new) (nth *fn-lbc-nov-store* fn-lbc))
               (equal (nth *fn-lbc-membership-store* new) (nth *fn-lbc-membership-store* fn-lbc)))
  (equal (fn-lb-columns-pool-layoutp new) (fn-lb-columns-pool-layoutp fn-lbc)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lb-columns-pool-layoutp fn-lbpe-count-by-store))))))

(defthm fn-lb-columns-pool-layoutp-of-number-put-row
 (equal (fn-lb-columns-pool-layoutp (fn-lbc-number-put-row numbers i fn-lbc))
        (fn-lb-columns-pool-layoutp fn-lbc))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbpe-pool-layout-by-fields (new (fn-lbc-number-put-row numbers i fn-lbc))))
  :in-theory (union-theories (theory 'ground-zero) '(fn-lbwf-number-put-row-field)))))

(defthm fn-lb-columns-pool-layoutp-of-rebuild-summaries
 (equal (fn-lb-columns-pool-layoutp (fn-lbc-rebuild-summaries groups rows fn-lbc))
        (fn-lb-columns-pool-layoutp fn-lbc))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbpe-pool-layout-by-fields (new (fn-lbc-rebuild-summaries groups rows fn-lbc))))
  :in-theory (union-theories (theory 'ground-zero) '(fn-lbwf-rebuild-summaries-field)))))

(defthm fn-lb-columns-pool-layoutp-of-reserve-slots
 (equal (fn-lb-columns-pool-layoutp (fn-lbc-reserve-slots n fn-lbc))
        (fn-lb-columns-pool-layoutp fn-lbc))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbpe-pool-layout-by-fields (new (fn-lbc-reserve-slots n fn-lbc))))
  :in-theory (union-theories (theory 'ground-zero) '(fn-lbwf-reserve-slots-field)))))

(defthm fn-lb-columns-pool-layoutp-of-index-slots
 (equal (fn-lb-columns-pool-layoutp (fn-lbc-index-slots i n fn-lbc))
        (fn-lb-columns-pool-layoutp fn-lbc))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbpe-pool-layout-by-fields (new (fn-lbc-index-slots i n fn-lbc))))
  :in-theory (union-theories (theory 'ground-zero) '(fn-lbwf-index-slots-field)))))

(defthm fn-lb-columns-pool-layoutp-of-rebuild-rows
 (implies (fn-lb-columns-pool-layoutp fn-lbc)
  (fn-lb-columns-pool-layoutp (fn-lbc-rebuild-rows rows log fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-rebuild-rows rows log fn-lbc)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-lbc-rebuild-rows fn-lb-columns-pool-layoutp-of-append-row
     fn-lb-columns-pool-layoutp-of-number-put-row car-cons cdr-cons)))))

(defthm fn-lb-columns-pool-layoutp-of-clear-columns
 (fn-lb-columns-pool-layoutp (fn-lbc-clear-columns fn-lbc))
 :hints (("Goal" :do-not-induct t
  :use fn-lb-columns-storage-layoutp-of-clear-columns
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-lb-columns-storage-layoutp fn-lb-columns-pool-layoutp)))))

(local (defthm fn-lbpe-pool-layoutp-of-summary-groups-update
 (equal (fn-lb-columns-pool-layoutp (update-fn-lbc-summary-groups groups fn-lbc))
        (fn-lb-columns-pool-layoutp fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lb-columns-pool-layoutp fn-lbpe-count-by-store
     update-fn-lbc-summary-groups fn-dm-nth-update-nth nth))))))

(defthm fn-lb-columns-pool-layoutp-of-open-rebuild
 (fn-lb-columns-pool-layoutp (fn-lbc-open-rebuild rows log fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-lbc-open-rebuild fn-lb-columns-pool-layoutp-of-clear-columns
     fn-lb-columns-pool-layoutp-of-rebuild-rows fn-lb-columns-pool-layoutp-of-rebuild-summaries
     fn-lbpe-pool-layoutp-of-summary-groups-update fn-lb-columns-pool-layoutp-of-reserve-slots
     fn-lb-columns-pool-layoutp-of-index-slots)))))
