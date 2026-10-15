; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-pool-reader-frames")

(local (defthm fn-lbrf-nfix-when-natural
 (implies (natp x) (equal (nfix x) x))
 :hints (("Goal" :in-theory (enable nfix)))))

(local (defthm fn-lbrf-nfix-idempotent
 (equal (nfix (nfix x)) (nfix x))
 :hints (("Goal" :in-theory (enable nfix)))))

(local (defthm fn-lbrf-len-append
 (equal (len (append xs ys)) (+ (len xs) (len ys)))
 :hints (("Goal" :induct (len xs) :in-theory (enable binary-append len)))))

(local (defthm fn-lbrf-nth-append-prefix
 (implies (and (natp i) (< i (len xs)))
  (equal (nth i (append xs ys)) (nth i xs)))
 :hints (("Goal" :induct (nth i xs) :in-theory (enable nth binary-append len)))))

(defthm fn-lb-column-nov-record-layoutp-of-nth
 (implies (and (fn-lb-column-nov-records-layoutp records limit)
               (natp i) (< i (len records)))
  (fn-lb-column-nov-record-layoutp (nth i records) limit))
 :hints (("Goal" :induct (nth i records) :in-theory
  (union-theories (theory 'ground-zero) '(fn-lb-column-nov-records-layoutp nth)))))

(defthm fn-lb-column-membership-record-layoutp-of-nth
 (implies (and (fn-lb-column-membership-records-layoutp records limit)
               (natp i) (< i (len records)))
  (fn-lb-column-membership-record-layoutp (nth i records) limit))
 :hints (("Goal" :induct (nth i records) :in-theory
  (union-theories (theory 'ground-zero) '(fn-lb-column-membership-records-layoutp nth)))))

(defthm fn-lbc-nov-at-of-append-nov-texts-prefix
 (implies (and (natp i) (< i (len (nth *fn-lbc-nov-store* fn-lbc)))
               (fn-lb-column-nov-record-layoutp (nth i (nth *fn-lbc-nov-store* fn-lbc))
                                                (fn-lbc-overview-pool-count fn-lbc)))
  (equal (fn-lbc-nov-at i (fn-lbc-append-nov-texts texts fn-lbc)) (fn-lbc-nov-at i fn-lbc)))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :in-theory (set-difference-theories
   (union-theories (theory 'ground-zero) '(fn-lbc-nov-at fn-lbc-nov-text fn-lb-column-nov-record-layoutp fn-lb-column-span-in-poolp fn-lbrf-nfix-idempotent fn-lbrf-nfix-when-natural fn-lbc-overview-pool-range-of-append-nov-texts-prefix (:type-prescription fn-lbc-overview-pool-count-natural) fn-lbc-nov-field-tomb-by-definition fn-lbc-nov-field-ok-by-definition fn-lbc-nov-field-subject-start-by-definition fn-lbc-nov-field-subject-length-by-definition fn-lbc-nov-field-from-start-by-definition fn-lbc-nov-field-from-length-by-definition fn-lbc-nov-field-date-start-by-definition fn-lbc-nov-field-date-length-by-definition fn-lbc-nov-field-msgid-start-by-definition fn-lbc-nov-field-msgid-length-by-definition fn-lbc-nov-field-references-start-by-definition fn-lbc-nov-field-references-length-by-definition fn-lbwf-append-nov-texts-field)) '((:definition nfix) (tau-system))))))

(defthm fn-lbc-nov-at-of-append-memberships-prefix
 (implies (and (natp i) (< i (len (nth *fn-lbc-nov-store* fn-lbc)))
               (fn-lb-column-nov-record-layoutp (nth i (nth *fn-lbc-nov-store* fn-lbc))
                                                (fn-lbc-overview-pool-count fn-lbc)))
  (equal (fn-lbc-nov-at i (fn-lbc-append-memberships items numbersp fn-lbc)) (fn-lbc-nov-at i fn-lbc)))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :in-theory (set-difference-theories
   (union-theories (theory 'ground-zero) '(fn-lbc-nov-at fn-lbc-nov-text fn-lb-column-nov-record-layoutp fn-lb-column-span-in-poolp fn-lbrf-nfix-idempotent fn-lbrf-nfix-when-natural fn-lbc-overview-pool-range-of-append-memberships-prefix (:type-prescription fn-lbc-overview-pool-count-natural) fn-lbc-nov-field-tomb-by-definition fn-lbc-nov-field-ok-by-definition fn-lbc-nov-field-subject-start-by-definition fn-lbc-nov-field-subject-length-by-definition fn-lbc-nov-field-from-start-by-definition fn-lbc-nov-field-from-length-by-definition fn-lbc-nov-field-date-start-by-definition fn-lbc-nov-field-date-length-by-definition fn-lbc-nov-field-msgid-start-by-definition fn-lbc-nov-field-msgid-length-by-definition fn-lbc-nov-field-references-start-by-definition fn-lbc-nov-field-references-length-by-definition fn-lbwf-append-memberships-field)) '((:definition nfix) (tau-system))))))

(defthm fn-lbc-nov-store-of-append-nov
  (equal (nth *fn-lbc-nov-store* (fn-lbc-append-nov nov fn-lbc))
   (append (nth *fn-lbc-nov-store* fn-lbc)
    (list (cons (fn-hnov-tomb nov)
           (cons (fn-hnov-ok nov)
            (fn-lbc-nov-spans (fn-lbc-nov-texts nov) (fn-lbc-overview-pool-count fn-lbc)))))))
  :hints (("Goal" :do-not-induct t :in-theory
   (union-theories (theory 'ground-zero)
    '(fn-lbc-append-nov fn-lbc-nov-store update-fn-lbc-nov-store fn-lbc-nov-append-is-append
      fn-dm-nth-update-nth fn-lbwf-append-nov-texts-field)))))

(defthm fn-lbc-nov-at-of-append-nov-prefix
 (implies (and (natp i) (< i (len (nth *fn-lbc-nov-store* fn-lbc)))
               (fn-lb-column-nov-record-layoutp (nth i (nth *fn-lbc-nov-store* fn-lbc))
                                                (fn-lbc-overview-pool-count fn-lbc)))
  (equal (fn-lbc-nov-at i (fn-lbc-append-nov nov fn-lbc)) (fn-lbc-nov-at i fn-lbc)))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :in-theory (set-difference-theories
   (union-theories (theory 'ground-zero) '(fn-lbc-nov-at fn-lbc-nov-text fn-lb-column-nov-record-layoutp fn-lb-column-span-in-poolp fn-lbrf-nfix-idempotent fn-lbrf-nfix-when-natural fn-lbc-overview-pool-range-of-append-nov-prefix (:type-prescription fn-lbc-overview-pool-count-natural) fn-lbc-nov-field-tomb-by-definition fn-lbc-nov-field-ok-by-definition fn-lbc-nov-field-subject-start-by-definition fn-lbc-nov-field-subject-length-by-definition fn-lbc-nov-field-from-start-by-definition fn-lbc-nov-field-from-length-by-definition fn-lbc-nov-field-date-start-by-definition fn-lbc-nov-field-date-length-by-definition fn-lbc-nov-field-msgid-start-by-definition fn-lbc-nov-field-msgid-length-by-definition fn-lbc-nov-field-references-start-by-definition fn-lbc-nov-field-references-length-by-definition fn-lbc-nov-store-of-append-nov fn-lbrf-len-append fn-lbrf-nth-append-prefix)) '((:definition nfix) (tau-system))))))
