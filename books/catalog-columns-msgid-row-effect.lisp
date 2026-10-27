; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-pool-model-frames")

(defthm fn-lbc-msgid-pool-model-of-row-store-update
 (equal (fn-lbc-msgid-pool-model (update-fn-lbc-row-store value fn-lbc))
        (fn-lbc-msgid-pool-model fn-lbc))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-msgid-pool-model-frame-by-definition
          (new (update-fn-lbc-row-store value fn-lbc))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-lbc-nth-of-other-row-store-update-by-definition
     (:executable-counterpart natp) (:executable-counterpart equal))))))

(defthm fn-lbc-msgid-pool-model-of-directory-store-update
 (equal (fn-lbc-msgid-pool-model (update-fn-lbc-directory-store value fn-lbc))
        (fn-lbc-msgid-pool-model fn-lbc))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-msgid-pool-model-frame-by-definition
          (new (update-fn-lbc-directory-store value fn-lbc))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-lbc-nth-of-other-directory-store-update-by-definition
     (:executable-counterpart natp) (:executable-counterpart equal))))))

(defthm fn-lbc-overview-pool-model-of-row-store-update
 (equal (fn-lbc-overview-pool-model (update-fn-lbc-row-store value fn-lbc))
        (fn-lbc-overview-pool-model fn-lbc))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-overview-pool-model-frame-by-definition
          (new (update-fn-lbc-row-store value fn-lbc))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-lbc-nth-of-other-row-store-update-by-definition
     (:executable-counterpart natp) (:executable-counterpart equal))))))

(defthm fn-lbc-overview-pool-model-of-directory-store-update
 (equal (fn-lbc-overview-pool-model (update-fn-lbc-directory-store value fn-lbc))
        (fn-lbc-overview-pool-model fn-lbc))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-overview-pool-model-frame-by-definition
          (new (update-fn-lbc-directory-store value fn-lbc))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-lbc-nth-of-other-directory-store-update-by-definition
     (:executable-counterpart natp) (:executable-counterpart equal))))))

(defthm fn-lbc-msgid-pool-model-of-append-row
 (equal (fn-lbc-msgid-pool-model (fn-lbc-append-row row log fn-lbc))
        (append (fn-lbc-msgid-pool-model fn-lbc)
                (true-list-fix (fn-record-string-octets (fn-record-msgid row)))))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-lbc-append-row fn-lbc-msgid-pool-model-frame-of-escape-store-put
     fn-lbc-msgid-pool-model-of-row-store-update fn-lbc-msgid-pool-model-of-directory-store-update
     fn-lbc-msgid-pool-append-is-model-append fn-lbc-msgid-pool-model-frame-of-append-nov
     fn-lbc-msgid-pool-model-frame-of-append-memberships
     fn-lbc-msgid-pool-model-frame-of-overview-pool-append
     fn-lbc-msgid-pool-model-frame-of-append-nov-texts car-cons cdr-cons)))) )
