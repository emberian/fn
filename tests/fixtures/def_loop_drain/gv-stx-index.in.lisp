(in-package "ACL2")
(include-book "def-loop-fixture-dep")

(fn-payload-kind fn-stx-index-of-store :wire "its articles are the octet model's; opens pass rows' bytes, or no keyring and build (fn-stx-index-empty)")

(fn-payload-kind fn-stx-index-of-store-loop :wire "fn-stx-index-of-store's loop twin: the same articles")

(defun fn-stx-index-of-store-loop (rev keyring index)
  (declare (xargs :guard (fn-prin-keyringp keyring)))
  (if (consp rev)
      (fn-stx-index-of-store-loop (cdr rev) keyring
                                  (fn-stx-index-add index
                                                    (fn-stx-delta (fn-article-payload (car rev))
                                                                  keyring)))
    index))

(defun fn-stx-index-of-store (articles keyring)
  (declare (xargs :guard (fn-prin-keyringp keyring) :verify-guards nil))
  (mbe :logic
       (if (consp articles)
           (fn-stx-index-add (fn-stx-index-of-store (cdr articles) keyring)
                             (fn-stx-delta (fn-article-payload (car articles))
                                           keyring))
         (fn-stx-index-empty))
       :exec (fn-stx-index-of-store-loop (fn-ag-rev-onto articles nil) keyring
                                         (fn-stx-index-empty))))

(encapsulate ()
  (local
   (defthm fn-stx-index-of-store-loop-of-rev-onto
     (equal (fn-stx-index-of-store-loop (fn-ag-rev-onto xs zs) keyring (fn-stx-index-empty))
            (fn-stx-index-of-store-loop zs keyring (fn-stx-index-of-store xs keyring)))
     :hints (("Goal" :induct (fn-ag-rev-onto xs zs)
                     :in-theory (disable fn-stx-index-add fn-stx-delta fn-stx-index-empty
                                         (:e fn-stx-index-empty))))))
  (verify-guards fn-stx-index-of-store
    :hints (("Goal" :in-theory (disable fn-stx-index-add fn-stx-delta fn-ag-rev-onto)
                    :use ((:instance fn-stx-index-of-store-loop-of-rev-onto
                                     (xs articles) (zs nil)))))))

(defthm fn-stx-index-of-store-without-a-keyring
  (equal (fn-stx-index-of-store articles nil) (fn-stx-index-empty))
  :hints (("Goal" :induct (fn-stx-index-of-store articles nil)
           :in-theory (enable fn-stx-delta fn-stx-verifiedp fn-prin-verifiedp))))

(defthm fn-stx-index-bindings-agree
  (and (equal (fn-stx-index-lookup (fn-stx-index-of-store articles keyring) id)
              (fn-lace-lookup (fn-stx-lace-of-store articles keyring) id))
       (iff (fn-stx-alist-get
             id (fn-stx-index-bindings (fn-stx-index-of-store articles keyring)))
            (member-equal id (fn-lace-ids (fn-stx-lace-of-store articles
                                                                keyring)))))
  :hints (("Goal" :induct (fn-stx-index-of-store articles keyring)
           :in-theory (e/d ((:d fn-stx-index-of-store) (:d fn-stx-lace-of-store)
                            (:d fn-stx-index-add)
                            (:d fn-stx-index-lookup) (:d fn-stx-alist-get))
                           (fn-stx-delta (:d fn-lace-slot-conflictp)
                            (:d fn-lace-equivocatorp) (:d fn-lace-same-slotp))))))

(defthm fn-stx-index-slots-agree
  (and (equal (fn-stx-index-slot-first (fn-stx-index-of-store articles keyring) k)
              (fn-stx-lace-slot-first (fn-stx-lace-of-store articles keyring) k))
       (iff (fn-stx-alist-get
             k (fn-stx-index-slots (fn-stx-index-of-store articles keyring)))
            (fn-stx-lace-slot-first (fn-stx-lace-of-store articles keyring) k)))
  :hints (("Goal" :induct (fn-stx-index-of-store articles keyring)
           :in-theory (e/d ((:d fn-stx-index-of-store) (:d fn-stx-lace-of-store)
                            (:d fn-stx-index-add)
                            (:d fn-stx-index-slot-first) (:d fn-stx-alist-get)
                            (:d fn-stx-lace-slot-first))
                           (fn-stx-delta (:d fn-lace-slot-conflictp)
                            (:d fn-lace-equivocatorp) (:d fn-lace-same-slotp))))))

(defthm fn-stx-index-equivocators-agree
  (iff (fn-stx-index-equivocatorp (fn-stx-index-of-store articles keyring) p i)
       (fn-lace-equivocatorp (fn-stx-lace-of-store articles keyring) p i))
  :hints (("Goal" :induct (fn-stx-index-of-store articles keyring)
           :in-theory (e/d ((:d fn-stx-index-of-store)
                            (:d fn-stx-lace-of-store))
                           (fn-stx-index-equivocator-fan
                            fn-stx-delta
                            (:d fn-stx-index-add)
                            (:d fn-stx-index-add1)
                            (:d fn-stx-index-equivocatorp)
                            (:d fn-stx-records-scan)
                            (:d fn-lace-slot-conflictp)
                            (:d fn-lace-equivocatorp)
                            (:d fn-lace-same-slotp)
                            (:d fn-stx-lace-slot-first)
                            fn-stx-slot-conflictp-of-append
                            fn-stx-scan-of-append-rest
                            fn-stx-slot-conflictp-of-singleton)))
          ("Subgoal *1/1"
           :use ((:instance fn-stx-index-equivocatorp-of-add
                            (index (fn-stx-index-of-store (cdr articles)
                                                          keyring))
                            (lace (fn-stx-lace-of-store (cdr articles) keyring))
                            (delta (fn-stx-delta
                                    (fn-article-payload (car articles))
                                    keyring)))))))

(local (defthm fn-stx-pol-column-of-store-is-the-fold
  (equal (cdr (fn-stx-alist-get (cons group authority)
                                (fn-stx-index-policies (fn-stx-index-of-store articles keyring))))
         (fn-stx-pol-fold (fn-stx-pol-filter (fn-stx-lace-of-store articles keyring) group authority)
                          nil))
  :hints (("Goal" :induct (fn-stx-index-of-store articles keyring)
           :in-theory (e/d ((:d fn-stx-index-of-store) (:d fn-stx-lace-of-store)
                            (:d fn-stx-index-add) (:d fn-stx-alist-get)
                            fn-stx-pol-filter-of-append fn-stx-pol-fold-of-append)
                           (fn-stx-delta fn-stx-policy-key fn-stx-policy-entry-add fn-stmt-p
                            fn-stx-pol-filter))))))

(defthm fn-stx-index-policy-agrees
  (equal (fn-stx-index-policy-current (fn-stx-index-of-store articles keyring) group authority)
         (fn-pol-current (fn-stx-lace-of-store articles keyring) keyring group authority))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-stx-pol-fold-keeps-okp (p nil) (e nil)
                            (c (fn-stx-pol-filter (fn-stx-lace-of-store articles keyring) group authority)))
                 (:instance fn-stx-pol-conflict-case
                            (cands (fn-stx-pol-filter (fn-stx-lace-of-store articles keyring) group authority))
                            (e (fn-stx-pol-fold (fn-stx-pol-filter (fn-stx-lace-of-store articles keyring) group authority) nil)))
                 (:instance fn-stx-pol-no-conflict-case
                            (cands (fn-stx-pol-filter (fn-stx-lace-of-store articles keyring) group authority))
                            (e (fn-stx-pol-fold (fn-stx-pol-filter (fn-stx-lace-of-store articles keyring) group authority) nil))))
           :in-theory (e/d (fn-stx-index-policy-current fn-pol-current)
                           (fn-pol-slot-lessp fn-stmt-p fn-pol-latest fn-pol-same-slot-conflictp
                            fn-stx-pol-conflictp fn-stx-pol-not-above fn-stx-pol-fold fn-stx-pol-filter
                            fn-stx-pol-entry-okp fn-pol-candidates fn-stx-lace-of-store fn-stx-index-of-store
                            fn-stx-pol-fold-keeps-okp fn-stx-pol-conflict-case fn-stx-pol-no-conflict-case)))))
