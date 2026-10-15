; Carried pool allocation, composed through the actual row writer.
(in-package "ACL2")
(include-book "catalog-columns-cross-store-allocation")

(defun-nx fn-lb-columns-pool-layoutp (fn-lbc)
 (and (fn-lb-column-nov-records-layoutp (nth *fn-lbc-nov-store* fn-lbc)
                                      (fn-lbc-overview-pool-count fn-lbc))
      (fn-lb-column-membership-records-layoutp (nth *fn-lbc-membership-store* fn-lbc)
                                             (fn-lbc-overview-pool-count fn-lbc))))

(local (defthm fn-lbpl-overview-count-by-nth
 (equal (fn-lbc-overview-pool-count fn-lbc) (len (nth *fn-lbc-overview-store* fn-lbc)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-overview-pool-count fn-lbc-overview-store fn-lbc-overview-octets-count-is-len))))))

(local (defthm fn-lbpl-overview-count-of-other-field-update
 (implies (and (natp field) (not (equal field *fn-lbc-overview-store*)))
  (equal (fn-lbc-overview-pool-count (update-nth field value fn-lbc))
         (fn-lbc-overview-pool-count fn-lbc)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbpl-overview-count-by-nth fn-dm-nth-update-nth))))))

(defthm fn-lbc-overview-pool-count-of-msgid-pool-append
 (equal (fn-lbc-overview-pool-count (fn-lbc-msgid-pool-append bytes fn-lbc))
        (fn-lbc-overview-pool-count fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbpl-overview-count-by-nth fn-lbwf-msgid-pool-append-field)))))

(defthm fn-lbc-overview-pool-count-of-escape-store-put
 (equal (fn-lbc-overview-pool-count (fn-lbc-escape-store-put i cell fn-lbc))
        (fn-lbc-overview-pool-count fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbpl-overview-count-by-nth fn-lbwf-escape-store-put-field)))))

(defthm fn-lb-columns-pool-layoutp-of-append-nov
 (implies (fn-lb-columns-pool-layoutp fn-lbc)
  (fn-lb-columns-pool-layoutp (fn-lbc-append-nov nov fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lb-columns-pool-layoutp fn-lbc-nov-records-layoutp-of-append-nov fn-lbc-membership-records-layoutp-of-append-nov)))))

(defthm fn-lb-columns-pool-layoutp-of-append-memberships
 (implies (fn-lb-columns-pool-layoutp fn-lbc)
  (fn-lb-columns-pool-layoutp (fn-lbc-append-memberships items numbersp fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lb-columns-pool-layoutp fn-lbc-nov-records-layoutp-of-append-memberships fn-lbc-membership-records-layoutp-of-append-memberships)))))

(defthm fn-lb-columns-pool-layoutp-of-msgid-pool-append
 (implies (fn-lb-columns-pool-layoutp fn-lbc)
  (fn-lb-columns-pool-layoutp (fn-lbc-msgid-pool-append bytes fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lb-columns-pool-layoutp fn-lbwf-msgid-pool-append-field fn-lbc-overview-pool-count-of-msgid-pool-append)))))

(defthm fn-lb-columns-pool-layoutp-of-escape-store-put
 (implies (fn-lb-columns-pool-layoutp fn-lbc)
  (fn-lb-columns-pool-layoutp (fn-lbc-escape-store-put i cell fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lb-columns-pool-layoutp fn-lbwf-escape-store-put-field fn-lbc-overview-pool-count-of-escape-store-put)))))

(local (defthm fn-lbpl-pool-layoutp-of-row-directory-update
  (equal (fn-lb-columns-pool-layoutp
           (update-fn-lbc-directory-store directory
            (update-fn-lbc-row-store rows fn-lbc)))
         (fn-lb-columns-pool-layoutp fn-lbc))
  :hints (("Goal" :do-not '(preprocess) :do-not-induct t
   :in-theory (union-theories (theory 'ground-zero)
    '(fn-lb-columns-pool-layoutp fn-lbpl-overview-count-by-nth nth
      update-fn-lbc-directory-store update-fn-lbc-row-store fn-dm-nth-update-nth))))))

(defthm fn-lb-columns-pool-layoutp-of-append-row
 (implies (fn-lb-columns-pool-layoutp fn-lbc)
  (fn-lb-columns-pool-layoutp (fn-lbc-append-row row log fn-lbc)))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-lbc-append-row fn-lbpl-pool-layoutp-of-row-directory-update
     fn-lb-columns-pool-layoutp-of-append-nov fn-lb-columns-pool-layoutp-of-append-memberships
     fn-lb-columns-pool-layoutp-of-msgid-pool-append fn-lb-columns-pool-layoutp-of-escape-store-put
     car-cons cdr-cons
     (:executable-counterpart member-equal) (:executable-counterpart equal)
     (:executable-counterpart natp) (:executable-counterpart nfix))))))
