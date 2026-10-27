; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-record-reader-frames")

(local (defthm fn-lbmrf-len-append
 (equal (len (append xs ys)) (+ (len xs) (len ys)))
 :hints (("Goal" :induct (len xs) :in-theory (enable binary-append len)))))

(local (defthm fn-lbmrf-nth-append-prefix
 (implies (and (natp i) (< i (len xs)))
  (equal (nth i (append xs ys)) (nth i xs)))
 :hints (("Goal" :induct (nth i xs) :in-theory (enable nth binary-append len)))))

(local (defthm fn-lbmrf-nfix-when-natural
 (implies (natp x) (equal (nfix x) x))
 :hints (("Goal" :in-theory (enable nfix)))))

(defthm fn-lbc-membership-store-length-of-append-memberships
 (equal (len (nth *fn-lbc-membership-store* (fn-lbc-append-memberships items numbersp fn-lbc)))
        (+ (len (nth *fn-lbc-membership-store* fn-lbc)) (len items)))
 :hints (("Goal" :induct (fn-lbc-append-memberships items numbersp fn-lbc)
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbc-append-memberships fn-lbc-membership-store update-fn-lbc-membership-store
     fn-lbc-memberships-append-is-append fn-dm-nth-update-nth fn-lbwf-overview-pool-append-field
     fn-lbmrf-len-append len)))))

(defthm fn-lbc-membership-store-nth-of-append-memberships-prefix
 (implies (and (natp i) (< i (len (nth *fn-lbc-membership-store* fn-lbc))))
  (equal (nth i (nth *fn-lbc-membership-store* (fn-lbc-append-memberships items numbersp fn-lbc)))
         (nth i (nth *fn-lbc-membership-store* fn-lbc))))
 :hints (("Goal" :induct (fn-lbc-append-memberships items numbersp fn-lbc)
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbc-append-memberships fn-lbc-membership-store update-fn-lbc-membership-store
     fn-lbc-memberships-append-is-append fn-dm-nth-update-nth fn-lbwf-overview-pool-append-field
     fn-lbmrf-len-append fn-lbmrf-nth-append-prefix len)))))

(defthm fn-lbc-membership-group-of-append-nov-texts-prefix
 (implies (and (natp i) (< i (len (nth *fn-lbc-membership-store* fn-lbc)))
               (fn-lb-column-membership-record-layoutp
                 (nth i (nth *fn-lbc-membership-store* fn-lbc))
                 (fn-lbc-overview-pool-count fn-lbc)))
  (equal (fn-lbc-membership-group i (fn-lbc-append-nov-texts texts fn-lbc))
         (fn-lbc-membership-group i fn-lbc)))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :in-theory (set-difference-theories
   (union-theories (theory 'ground-zero) '(fn-lbc-membership-group fn-lbc-membership-field-group-start-by-definition fn-lbc-membership-field-group-length-by-definition fn-lb-column-membership-record-layoutp fn-lb-column-span-in-poolp fn-lbmrf-nfix-when-natural (:type-prescription fn-lbc-overview-pool-count-natural) fn-lbc-overview-pool-range-of-append-nov-texts-prefix fn-lbwf-append-nov-texts-field)) '((:definition nfix) (tau-system))))))

(defthm fn-lbc-membership-group-of-append-nov-prefix
 (implies (and (natp i) (< i (len (nth *fn-lbc-membership-store* fn-lbc)))
               (fn-lb-column-membership-record-layoutp
                 (nth i (nth *fn-lbc-membership-store* fn-lbc))
                 (fn-lbc-overview-pool-count fn-lbc)))
  (equal (fn-lbc-membership-group i (fn-lbc-append-nov nov fn-lbc))
         (fn-lbc-membership-group i fn-lbc)))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :in-theory (set-difference-theories
   (union-theories (theory 'ground-zero) '(fn-lbc-membership-group fn-lbc-membership-field-group-start-by-definition fn-lbc-membership-field-group-length-by-definition fn-lb-column-membership-record-layoutp fn-lb-column-span-in-poolp fn-lbmrf-nfix-when-natural (:type-prescription fn-lbc-overview-pool-count-natural) fn-lbc-overview-pool-range-of-append-nov-prefix fn-lbwf-append-nov-field)) '((:definition nfix) (tau-system))))))

(defthm fn-lbc-membership-group-of-append-memberships-prefix
 (implies (and (natp i) (< i (len (nth *fn-lbc-membership-store* fn-lbc)))
               (fn-lb-column-membership-record-layoutp
                 (nth i (nth *fn-lbc-membership-store* fn-lbc))
                 (fn-lbc-overview-pool-count fn-lbc)))
  (equal (fn-lbc-membership-group i (fn-lbc-append-memberships items numbersp fn-lbc))
         (fn-lbc-membership-group i fn-lbc)))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :in-theory (set-difference-theories
   (union-theories (theory 'ground-zero) '(fn-lbc-membership-group fn-lbc-membership-field-group-start-by-definition fn-lbc-membership-field-group-length-by-definition fn-lb-column-membership-record-layoutp fn-lb-column-span-in-poolp fn-lbmrf-nfix-when-natural (:type-prescription fn-lbc-overview-pool-count-natural) fn-lbc-overview-pool-range-of-append-memberships-prefix fn-lbc-membership-store-length-of-append-memberships fn-lbc-membership-store-nth-of-append-memberships-prefix)) '((:definition nfix) (tau-system))))))
