; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-row-cell-extras")

(defthm fn-lbc-nov-at-of-append-nov-allocated
 (implies (and (fn-lb-columns-pool-layoutp fn-lbc) (natp i)
               (< i (fn-lbc-nov-record-count fn-lbc)))
  (equal (fn-lbc-nov-at i (fn-lbc-append-nov nov fn-lbc)) (fn-lbc-nov-at i fn-lbc)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lb-column-nov-record-layoutp-from-pool-layout)
        (:instance fn-lbc-nov-at-of-append-nov-prefix))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-lbc-nov-record-count-is-store-length)))))

(defthm fn-lbc-membership-run-of-append-nov-allocated
 (implies (and (fn-lb-columns-pool-layoutp fn-lbc) (natp start) (natp count)
               (<= (+ start count) (fn-lbc-membership-record-count fn-lbc)))
  (equal (fn-lbc-membership-run start count numbersp (fn-lbc-append-nov nov fn-lbc))
         (fn-lbc-membership-run start count numbersp fn-lbc)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-membership-run-of-append-nov-prefix))
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lb-columns-pool-layoutp fn-lbc-membership-record-count-is-store-length)))))

(defthm fn-lbc-nov-at-of-append-nov-texts-allocated
 (implies (and (fn-lb-columns-pool-layoutp fn-lbc) (natp i)
               (< i (fn-lbc-nov-record-count fn-lbc)))
  (equal (fn-lbc-nov-at i (fn-lbc-append-nov-texts texts fn-lbc)) (fn-lbc-nov-at i fn-lbc)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lb-column-nov-record-layoutp-from-pool-layout)
        (:instance fn-lbc-nov-at-of-append-nov-texts-prefix))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-lbc-nov-record-count-is-store-length)))))

(defthm fn-lbc-membership-run-of-append-nov-texts-allocated
 (implies (and (fn-lb-columns-pool-layoutp fn-lbc) (natp start) (natp count)
               (<= (+ start count) (fn-lbc-membership-record-count fn-lbc)))
  (equal (fn-lbc-membership-run start count numbersp (fn-lbc-append-nov-texts texts fn-lbc))
         (fn-lbc-membership-run start count numbersp fn-lbc)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-membership-run-of-append-nov-texts-prefix))
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lb-columns-pool-layoutp fn-lbc-membership-record-count-is-store-length)))))

(defthm fn-lbc-nov-at-of-append-memberships-allocated
 (implies (and (fn-lb-columns-pool-layoutp fn-lbc) (natp i)
               (< i (fn-lbc-nov-record-count fn-lbc)))
  (equal (fn-lbc-nov-at i (fn-lbc-append-memberships items numbersp fn-lbc)) (fn-lbc-nov-at i fn-lbc)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lb-column-nov-record-layoutp-from-pool-layout)
        (:instance fn-lbc-nov-at-of-append-memberships-prefix))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-lbc-nov-record-count-is-store-length)))))

(defthm fn-lbc-membership-run-of-append-memberships-allocated
 (implies (and (fn-lb-columns-pool-layoutp fn-lbc) (natp start) (natp count)
               (<= (+ start count) (fn-lbc-membership-record-count fn-lbc)))
  (equal (fn-lbc-membership-run start count numbersp (fn-lbc-append-memberships items write-numbersp fn-lbc))
         (fn-lbc-membership-run start count numbersp fn-lbc)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-membership-run-of-append-memberships-prefix))
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lb-columns-pool-layoutp fn-lbc-membership-record-count-is-store-length)))))
