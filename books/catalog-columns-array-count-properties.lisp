; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-array-reader-frames")

(defthm fn-lbc-nov-record-count-is-store-length
 (equal (fn-lbc-nov-record-count fn-lbc) (len (nth *fn-lbc-nov-store* fn-lbc)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-nov-record-count fn-lbc-nov-store fn-lbc-nov-count-is-len)))))

(defthm fn-lbc-nov-record-count-natural
 (natp (fn-lbc-nov-record-count fn-lbc)) :rule-classes :type-prescription
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-nov-record-count-is-store-length)))))

(defthm fn-lb-column-nov-record-layoutp-from-pool-layout
 (implies (and (fn-lb-columns-pool-layoutp fn-lbc) (natp i)
               (< i (fn-lbc-nov-record-count fn-lbc)))
  (fn-lb-column-nov-record-layoutp (nth i (nth *fn-lbc-nov-store* fn-lbc))
                                    (fn-lbc-overview-pool-count fn-lbc)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lb-columns-pool-layoutp fn-lbc-nov-record-count-is-store-length
     fn-lb-column-nov-record-layoutp-of-nth)))))

(defthm fn-lbc-membership-record-count-is-store-length
 (equal (fn-lbc-membership-record-count fn-lbc) (len (nth *fn-lbc-membership-store* fn-lbc)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-membership-record-count fn-lbc-membership-store fn-lbc-memberships-count-is-len)))))

(defthm fn-lbc-membership-record-count-natural
 (natp (fn-lbc-membership-record-count fn-lbc)) :rule-classes :type-prescription
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-membership-record-count-is-store-length)))))

(defthm fn-lb-column-membership-record-layoutp-from-pool-layout
 (implies (and (fn-lb-columns-pool-layoutp fn-lbc) (natp i)
               (< i (fn-lbc-membership-record-count fn-lbc)))
  (fn-lb-column-membership-record-layoutp (nth i (nth *fn-lbc-membership-store* fn-lbc))
                                    (fn-lbc-overview-pool-count fn-lbc)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lb-columns-pool-layoutp fn-lbc-membership-record-count-is-store-length
     fn-lb-column-membership-record-layoutp-of-nth)))))

(local (defthm fn-lbac-len-append-one
 (equal (len (append xs (list x))) (+ 1 (len xs)))
 :hints (("Goal" :induct (len xs) :in-theory (enable binary-append len)))))

(defthm fn-lbc-nov-record-count-of-append-nov
 (equal (fn-lbc-nov-record-count (fn-lbc-append-nov nov fn-lbc))
        (+ 1 (fn-lbc-nov-record-count fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-nov-record-count-is-store-length fn-lbc-nov-store-of-append-nov
     fn-lbac-len-append-one)))))

(defthm fn-lbc-membership-record-count-of-append-memberships
 (equal (fn-lbc-membership-record-count (fn-lbc-append-memberships items numbersp fn-lbc))
        (+ (fn-lbc-membership-record-count fn-lbc) (len items)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-membership-record-count-is-store-length fn-lbc-membership-store-length-of-append-memberships)))))
