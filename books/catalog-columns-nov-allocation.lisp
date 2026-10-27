; Actual NOV append establishes bounds for new and retained spans.
(in-package "ACL2")
(include-book "catalog-columns-nov-span-properties")

(local (defthm fn-lbnr-pairs-give-nov-record-layout
 (implies (fn-lb-span-pairs-layoutp spans limit)
          (fn-lb-column-nov-record-layoutp (cons tomb (cons ok spans)) limit))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :expand ((fn-lb-span-pairs-layoutp spans limit) (fn-lb-span-pairs-layoutp (cdr (cdr spans)) limit) (fn-lb-span-pairs-layoutp (cdr (cdr (cdr (cdr spans)))) limit) (fn-lb-span-pairs-layoutp (cdr (cdr (cdr (cdr (cdr (cdr spans)))))) limit) (fn-lb-span-pairs-layoutp (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr spans)))))))) limit))
  :in-theory (set-difference-theories
   (union-theories (theory 'ground-zero) '(fn-lb-column-nov-record-layoutp fn-lb-column-span-in-poolp nth))
   '((:definition nfix) (tau-system)))))))

(defthm fn-lbc-nov-spans-length
 (equal (len (fn-lbc-nov-spans texts offset)) (* 2 (len texts)))
 :hints (("Goal" :induct (fn-lbc-nov-spans texts offset)
  :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-nov-spans len)))))

(defthm fn-lbc-encoded-nov-record-is-in-pool
 (implies (natp offset)
  (fn-lb-column-nov-record-layoutp
   (cons tomb (cons ok (fn-lbc-nov-spans texts offset)))
   (+ offset (len (fn-lbc-texts-octets-model texts)))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbnr-pairs-give-nov-record-layout
          (spans (fn-lbc-nov-spans texts offset))
          (limit (+ offset (len (fn-lbc-texts-octets-model texts))))))
  :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-nov-spans-are-in-pool)))))

(local (defthm fn-lbnr-records-layoutp-of-append-one
  (implies (and (fn-lb-column-nov-records-layoutp records limit)
                (fn-lb-column-nov-record-layoutp record limit))
   (fn-lb-column-nov-records-layoutp (append records (list record)) limit))
  :hints (("Goal" :induct (len records)
   :in-theory (union-theories (theory 'ground-zero)
    '(fn-lb-column-nov-records-layoutp binary-append))))))

(local (defthm fn-lbnr-overview-count-of-nov-index-update
  (equal (fn-lbc-overview-pool-count (update-nth *fn-lbc-nov-store* value fn-lbc))
         (fn-lbc-overview-pool-count fn-lbc))
  :hints (("Goal" :do-not-induct t
   :in-theory (union-theories (theory 'ground-zero)
    '(fn-lbc-overview-pool-count fn-lbc-overview-store fn-dm-nth-update-nth nth))))))

(defthm fn-lbc-nov-records-layoutp-of-append-nov
  (implies
   (fn-lb-column-nov-records-layoutp (nth *fn-lbc-nov-store* fn-lbc)
                                  (fn-lbc-overview-pool-count fn-lbc))
   (fn-lb-column-nov-records-layoutp
    (nth *fn-lbc-nov-store* (fn-lbc-append-nov nov fn-lbc))
    (fn-lbc-overview-pool-count (fn-lbc-append-nov nov fn-lbc))))
  :hints (("Goal" :do-not '(preprocess) :do-not-induct t
   :use ((:instance fn-lb-column-nov-records-layoutp-of-text-pool-growth
           (records (nth *fn-lbc-nov-store* fn-lbc)) (texts (fn-lbc-nov-texts nov))))
   :in-theory (union-theories (theory 'ground-zero)
    '(fn-lbc-append-nov fn-lbc-nov-store update-fn-lbc-nov-store fn-dm-nth-update-nth
      fn-lbc-nov-append-is-append fn-lbwf-append-nov-texts-field
      fn-lbnr-overview-count-of-nov-index-update fn-lbnr-records-layoutp-of-append-one
      fn-lbc-encoded-nov-record-is-in-pool fn-lbc-overview-pool-count-of-append-nov-texts
      (:type-prescription fn-lbc-overview-pool-count-natural))))))
