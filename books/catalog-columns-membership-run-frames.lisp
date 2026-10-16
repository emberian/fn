; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-membership-reader-frames")

(defthm fn-lbc-membership-run-of-append-nov-texts-prefix
 (implies (and (natp start) (natp count)
               (<= (+ start count) (len (nth *fn-lbc-membership-store* fn-lbc)))
               (fn-lb-column-membership-records-layoutp
                 (nth *fn-lbc-membership-store* fn-lbc) (fn-lbc-overview-pool-count fn-lbc)))
  (equal (fn-lbc-membership-run start count numbersp (fn-lbc-append-nov-texts texts fn-lbc))
         (fn-lbc-membership-run start count numbersp fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-membership-run start count numbersp fn-lbc)
  :do-not '(preprocess)
  :in-theory (set-difference-theories
   (union-theories (theory 'ground-zero) '(fn-lbc-membership-run fn-lbc-membership-group-of-append-nov-texts-prefix fn-lb-column-membership-record-layoutp-of-nth fn-lbc-membership-field-number-by-definition fn-lbwf-append-nov-texts-field)) '((tau-system))))))

(defthm fn-lbc-membership-run-of-append-nov-prefix
 (implies (and (natp start) (natp count)
               (<= (+ start count) (len (nth *fn-lbc-membership-store* fn-lbc)))
               (fn-lb-column-membership-records-layoutp
                 (nth *fn-lbc-membership-store* fn-lbc) (fn-lbc-overview-pool-count fn-lbc)))
  (equal (fn-lbc-membership-run start count numbersp (fn-lbc-append-nov nov fn-lbc))
         (fn-lbc-membership-run start count numbersp fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-membership-run start count numbersp fn-lbc)
  :do-not '(preprocess)
  :in-theory (set-difference-theories
   (union-theories (theory 'ground-zero) '(fn-lbc-membership-run fn-lbc-membership-group-of-append-nov-prefix fn-lb-column-membership-record-layoutp-of-nth fn-lbc-membership-field-number-by-definition fn-lbwf-append-nov-field)) '((tau-system))))))

(defthm fn-lbc-membership-run-of-append-memberships-prefix
 (implies (and (natp start) (natp count)
               (<= (+ start count) (len (nth *fn-lbc-membership-store* fn-lbc)))
               (fn-lb-column-membership-records-layoutp
                 (nth *fn-lbc-membership-store* fn-lbc) (fn-lbc-overview-pool-count fn-lbc)))
  (equal (fn-lbc-membership-run start count numbersp (fn-lbc-append-memberships items write-numbersp fn-lbc))
         (fn-lbc-membership-run start count numbersp fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-membership-run start count numbersp fn-lbc)
  :do-not '(preprocess)
  :in-theory (set-difference-theories
   (union-theories (theory 'ground-zero) '(fn-lbc-membership-run fn-lbc-membership-group-of-append-memberships-prefix fn-lb-column-membership-record-layoutp-of-nth fn-lbc-membership-field-number-by-definition fn-lbc-membership-store-length-of-append-memberships fn-lbc-membership-store-nth-of-append-memberships-prefix)) '((tau-system))))))
