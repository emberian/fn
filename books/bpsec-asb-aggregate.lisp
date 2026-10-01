; Carried span bounds for saved metadata and scheduled reversal work.
; Ghost traversal only: the host calls STEP, never these whole-list predicates.
(in-package "ACL2")
(include-book "bpsec-asb-body")

(defun fn-bps-tree-boundedp (value cursor)
  (declare (xargs :guard t))
  (if (consp value)
      (if (member-equal (car value) '(:bytes-span :text-span))
          (fn-bps-span-in-sourcep value cursor)
        (and (fn-bps-tree-boundedp (car value) cursor)
             (fn-bps-tree-boundedp (cdr value) cursor)))
    (not (member-equal value '(:bytes-span :text-span)))))

(defun fn-bps-values-boundedp (values cursor)
  (declare (xargs :guard t))
  (if (consp values)
      (and (fn-bps-tree-boundedp (car values) cursor)
           (fn-bps-values-boundedp (cdr values) cursor))
    (null values)))

(defun fn-bps-asb-aggregatep (cursor)
  (declare (xargs :guard t))
  (and (fn-bps-tree-boundedp (fn-bps-get :source cursor) cursor)
       (fn-bps-tree-boundedp (fn-bps-get :pending cursor) cursor)
       (fn-bps-tree-boundedp (fn-bps-get :id cursor) cursor)
       (fn-bps-values-boundedp (fn-bps-get :targets cursor) cursor)
       (fn-bps-values-boundedp (fn-bps-get :params cursor) cursor)
       (fn-bps-values-boundedp (fn-bps-get :pairs cursor) cursor)
       (fn-bps-values-boundedp (fn-bps-get :results cursor) cursor)
       (fn-bps-values-boundedp (fn-bps-get :scan cursor) cursor)
       (fn-bps-values-boundedp (fn-bps-get :reverse cursor) cursor)))

(defun fn-bps-asb-aggregate-contextp (cursor)
  (declare (xargs :guard t))
  (and (fn-bps-asb-body-contextp cursor) (fn-bps-asb-aggregatep cursor)))

(local
 (defthm fn-bps-aggregate-get-other-put-by-definition
   (implies (not (equal key changed))
            (equal (fn-bps-get key (fn-bps-put changed value cursor)) (fn-bps-get key cursor)))
   :hints (("Goal" :induct (fn-bps-put changed value cursor)))))
(local
 (defthm fn-bps-aggregate-get-put-choice-by-definition
   (or (equal (fn-bps-get key (fn-bps-put key value cursor)) value)
       (equal (fn-bps-get key (fn-bps-put key value cursor)) nil))
   :rule-classes nil
   :hints (("Goal" :induct (fn-bps-put key value cursor)))))
(local
 (defthm fn-bps-tree-is-not-span-keyword-by-definition
   (implies (fn-bps-tree-boundedp value cursor)
            (not (member-equal value '(:bytes-span :text-span))))))
(local
 (defthm fn-bps-tree-cons-by-definition
   (implies (and (fn-bps-tree-boundedp a cursor) (fn-bps-tree-boundedp b cursor))
            (fn-bps-tree-boundedp (cons a b) cursor))))
(local
 (defthm fn-bps-values-implies-tree-by-definition
   (implies (fn-bps-values-boundedp values cursor)
            (fn-bps-tree-boundedp values cursor))
   :hints (("Goal" :induct (fn-bps-values-boundedp values cursor)))))
(local
 (defthm fn-bps-tree-uint-by-definition
   (implies (fn-bps-uintp value) (fn-bps-tree-boundedp value cursor))
   :hints (("Goal" :in-theory (enable fn-bps-uintp)))))
(local
 (defthm fn-bps-tree-body-by-definition
   (implies (fn-bps-asb-body-boundedp cursor)
            (fn-bps-tree-boundedp (fn-bps-get :body cursor) cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-asb-body-boundedp fn-bps-span-in-sourcep fn-bps-spanp fn-bps-field)
                                 (fn-bps-get fn-bps-asb-extentp fn-bps-uintp))))))
(local
 (defthm fn-bps-tree-other-put-by-definition
   (implies (not (member-equal changed '(:start :length :backing)))
            (equal (fn-bps-tree-boundedp tree (fn-bps-put changed value cursor))
                   (fn-bps-tree-boundedp tree cursor)))
   :hints (("Goal" :induct (fn-bps-tree-boundedp tree cursor)
            :in-theory (e/d (fn-bps-tree-boundedp fn-bps-span-in-sourcep fn-bps-asb-extentp)
                            (fn-bps-get fn-bps-put fn-bps-spanp fn-bps-field fn-bps-uintp))))))
(local
 (defthm fn-bps-values-other-put-by-definition
   (implies (not (member-equal changed '(:start :length :backing)))
            (equal (fn-bps-values-boundedp values (fn-bps-put changed value cursor))
                   (fn-bps-values-boundedp values cursor)))
   :hints (("Goal" :induct (fn-bps-values-boundedp values cursor)
            :in-theory (e/d (fn-bps-values-boundedp) (fn-bps-tree-boundedp fn-bps-put))))))
(local
 (defthm fn-bps-aggregate-other-put-by-definition
   (implies (not (member-equal changed '(:start :length :backing :source :pending :id
                                       :targets :params :pairs :results :scan :reverse)))
            (equal (fn-bps-asb-aggregatep (fn-bps-put changed value cursor))
                   (fn-bps-asb-aggregatep cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-asb-aggregatep)
                                 (fn-bps-get fn-bps-put fn-bps-tree-boundedp fn-bps-values-boundedp))))))
(local
 (defthm fn-bps-aggregate-put-source-by-definition
   (implies (and (fn-bps-asb-aggregatep cursor) (fn-bps-tree-boundedp value cursor))
            (fn-bps-asb-aggregatep (fn-bps-put :source value cursor)))
   :hints (("Goal" :use ((:instance fn-bps-aggregate-get-put-choice-by-definition (key :source)))
            :in-theory (e/d (fn-bps-asb-aggregatep) (fn-bps-get fn-bps-put))))))
(local
 (defthm fn-bps-aggregate-put-pending-by-definition
   (implies (and (fn-bps-asb-aggregatep cursor) (fn-bps-tree-boundedp value cursor))
            (fn-bps-asb-aggregatep (fn-bps-put :pending value cursor)))
   :hints (("Goal" :use ((:instance fn-bps-aggregate-get-put-choice-by-definition (key :pending)))
            :in-theory (e/d (fn-bps-asb-aggregatep) (fn-bps-get fn-bps-put))))))
(local
 (defthm fn-bps-aggregate-put-id-by-definition
   (implies (and (fn-bps-asb-aggregatep cursor) (fn-bps-tree-boundedp value cursor))
            (fn-bps-asb-aggregatep (fn-bps-put :id value cursor)))
   :hints (("Goal" :use ((:instance fn-bps-aggregate-get-put-choice-by-definition (key :id)))
            :in-theory (e/d (fn-bps-asb-aggregatep) (fn-bps-get fn-bps-put))))))
(local
 (defthm fn-bps-aggregate-put-targets-by-definition
   (implies (and (fn-bps-asb-aggregatep cursor) (fn-bps-values-boundedp value cursor))
            (fn-bps-asb-aggregatep (fn-bps-put :targets value cursor)))
   :hints (("Goal" :use ((:instance fn-bps-aggregate-get-put-choice-by-definition (key :targets)))
            :in-theory (e/d (fn-bps-asb-aggregatep) (fn-bps-get fn-bps-put))))))
(local
 (defthm fn-bps-aggregate-put-params-by-definition
   (implies (and (fn-bps-asb-aggregatep cursor) (fn-bps-values-boundedp value cursor))
            (fn-bps-asb-aggregatep (fn-bps-put :params value cursor)))
   :hints (("Goal" :use ((:instance fn-bps-aggregate-get-put-choice-by-definition (key :params)))
            :in-theory (e/d (fn-bps-asb-aggregatep) (fn-bps-get fn-bps-put))))))
(local
 (defthm fn-bps-aggregate-put-pairs-by-definition
   (implies (and (fn-bps-asb-aggregatep cursor) (fn-bps-values-boundedp value cursor))
            (fn-bps-asb-aggregatep (fn-bps-put :pairs value cursor)))
   :hints (("Goal" :use ((:instance fn-bps-aggregate-get-put-choice-by-definition (key :pairs)))
            :in-theory (e/d (fn-bps-asb-aggregatep) (fn-bps-get fn-bps-put))))))
(local
 (defthm fn-bps-aggregate-put-results-by-definition
   (implies (and (fn-bps-asb-aggregatep cursor) (fn-bps-values-boundedp value cursor))
            (fn-bps-asb-aggregatep (fn-bps-put :results value cursor)))
   :hints (("Goal" :use ((:instance fn-bps-aggregate-get-put-choice-by-definition (key :results)))
            :in-theory (e/d (fn-bps-asb-aggregatep) (fn-bps-get fn-bps-put))))))
(local
 (defthm fn-bps-aggregate-put-scan-by-definition
   (implies (and (fn-bps-asb-aggregatep cursor) (fn-bps-values-boundedp value cursor))
            (fn-bps-asb-aggregatep (fn-bps-put :scan value cursor)))
   :hints (("Goal" :use ((:instance fn-bps-aggregate-get-put-choice-by-definition (key :scan)))
            :in-theory (e/d (fn-bps-asb-aggregatep) (fn-bps-get fn-bps-put))))))
(local
 (defthm fn-bps-aggregate-put-reverse-by-definition
   (implies (and (fn-bps-asb-aggregatep cursor) (fn-bps-values-boundedp value cursor))
            (fn-bps-asb-aggregatep (fn-bps-put :reverse value cursor)))
   :hints (("Goal" :use ((:instance fn-bps-aggregate-get-put-choice-by-definition (key :reverse)))
            :in-theory (e/d (fn-bps-asb-aggregatep) (fn-bps-get fn-bps-put))))))
(local (defthm fn-bps-tree-nil-by-definition (fn-bps-tree-boundedp nil cursor)))
(local (defthm fn-bps-values-nil-by-definition (fn-bps-values-boundedp nil cursor)))
(local (defthm fn-bps-aggregate-source-projection-by-definition
 (implies (fn-bps-asb-aggregatep cursor) (fn-bps-tree-boundedp (fn-bps-get :source cursor) cursor))
 :hints (("Goal" :in-theory (e/d (fn-bps-asb-aggregatep) (fn-bps-tree-boundedp fn-bps-values-boundedp fn-bps-get))))))
(local (defthm fn-bps-aggregate-pending-projection-by-definition
 (implies (fn-bps-asb-aggregatep cursor) (fn-bps-tree-boundedp (fn-bps-get :pending cursor) cursor))
 :hints (("Goal" :in-theory (e/d (fn-bps-asb-aggregatep) (fn-bps-tree-boundedp fn-bps-values-boundedp fn-bps-get))))))
(local (defthm fn-bps-aggregate-id-projection-by-definition
 (implies (fn-bps-asb-aggregatep cursor) (fn-bps-tree-boundedp (fn-bps-get :id cursor) cursor))
 :hints (("Goal" :in-theory (e/d (fn-bps-asb-aggregatep) (fn-bps-tree-boundedp fn-bps-values-boundedp fn-bps-get))))))
(local (defthm fn-bps-aggregate-targets-projection-by-definition
 (implies (fn-bps-asb-aggregatep cursor) (fn-bps-values-boundedp (fn-bps-get :targets cursor) cursor))
 :hints (("Goal" :in-theory (e/d (fn-bps-asb-aggregatep) (fn-bps-tree-boundedp fn-bps-values-boundedp fn-bps-get))))))
(local (defthm fn-bps-aggregate-params-projection-by-definition
 (implies (fn-bps-asb-aggregatep cursor) (fn-bps-values-boundedp (fn-bps-get :params cursor) cursor))
 :hints (("Goal" :in-theory (e/d (fn-bps-asb-aggregatep) (fn-bps-tree-boundedp fn-bps-values-boundedp fn-bps-get))))))
(local (defthm fn-bps-aggregate-pairs-projection-by-definition
 (implies (fn-bps-asb-aggregatep cursor) (fn-bps-values-boundedp (fn-bps-get :pairs cursor) cursor))
 :hints (("Goal" :in-theory (e/d (fn-bps-asb-aggregatep) (fn-bps-tree-boundedp fn-bps-values-boundedp fn-bps-get))))))
(local (defthm fn-bps-aggregate-results-projection-by-definition
 (implies (fn-bps-asb-aggregatep cursor) (fn-bps-values-boundedp (fn-bps-get :results cursor) cursor))
 :hints (("Goal" :in-theory (e/d (fn-bps-asb-aggregatep) (fn-bps-tree-boundedp fn-bps-values-boundedp fn-bps-get))))))
(local (defthm fn-bps-aggregate-scan-projection-by-definition
 (implies (fn-bps-asb-aggregatep cursor) (fn-bps-values-boundedp (fn-bps-get :scan cursor) cursor))
 :hints (("Goal" :in-theory (e/d (fn-bps-asb-aggregatep) (fn-bps-tree-boundedp fn-bps-values-boundedp fn-bps-get))))))
(local (defthm fn-bps-aggregate-reverse-projection-by-definition
 (implies (fn-bps-asb-aggregatep cursor) (fn-bps-values-boundedp (fn-bps-get :reverse cursor) cursor))
 :hints (("Goal" :in-theory (e/d (fn-bps-asb-aggregatep) (fn-bps-tree-boundedp fn-bps-values-boundedp fn-bps-get))))))
(local
 (defthm fn-bps-values-cons-by-definition
   (equal (fn-bps-values-boundedp (cons a b) cursor)
          (and (fn-bps-tree-boundedp a cursor) (fn-bps-values-boundedp b cursor)))))
(local
 (defthm fn-bps-values-car-by-definition
   (implies (and (fn-bps-values-boundedp values cursor) (consp values))
            (fn-bps-tree-boundedp (car values) cursor))))
(local
 (defthm fn-bps-values-cdr-by-definition
   (implies (fn-bps-values-boundedp values cursor)
            (fn-bps-values-boundedp (cdr values) cursor))))
(local
 (defthm fn-bps-tree-atom-by-definition
   (implies (atom value)
            (equal (fn-bps-tree-boundedp value cursor)
                   (not (member-equal value '(:bytes-span :text-span)))))))
(local
 (defthm fn-bps-stop-fn-bps-tree-boundedp-frame-by-definition
   (equal (fn-bps-tree-boundedp tree (fn-bps-stop status reason cursor)) (fn-bps-tree-boundedp tree cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-stop)
                                 (fn-bps-tree-boundedp fn-bps-values-boundedp fn-bps-get fn-bps-put fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))
(local
 (defthm fn-bps-stop-fn-bps-values-boundedp-frame-by-definition
   (equal (fn-bps-values-boundedp stored (fn-bps-stop status reason cursor)) (fn-bps-values-boundedp stored cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-stop)
                                 (fn-bps-tree-boundedp fn-bps-values-boundedp fn-bps-get fn-bps-put fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))
(local
 (defthm fn-bps-stage-fn-bps-tree-boundedp-frame-by-definition
   (equal (fn-bps-tree-boundedp tree (fn-bps-stage stage cursor)) (fn-bps-tree-boundedp tree cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-stage)
                                 (fn-bps-tree-boundedp fn-bps-values-boundedp fn-bps-get fn-bps-put fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))
(local
 (defthm fn-bps-stage-fn-bps-values-boundedp-frame-by-definition
   (equal (fn-bps-values-boundedp stored (fn-bps-stage stage cursor)) (fn-bps-values-boundedp stored cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-stage)
                                 (fn-bps-tree-boundedp fn-bps-values-boundedp fn-bps-get fn-bps-put fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))
(local
 (defthm fn-bps-charge-fn-bps-tree-boundedp-frame-by-definition
   (equal (fn-bps-tree-boundedp tree (fn-bps-charge count cursor)) (fn-bps-tree-boundedp tree cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-charge)
                                 (fn-bps-tree-boundedp fn-bps-values-boundedp fn-bps-get fn-bps-put fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-stage fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))
(local
 (defthm fn-bps-charge-fn-bps-values-boundedp-frame-by-definition
   (equal (fn-bps-values-boundedp stored (fn-bps-charge count cursor)) (fn-bps-values-boundedp stored cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-charge)
                                 (fn-bps-tree-boundedp fn-bps-values-boundedp fn-bps-get fn-bps-put fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-stage fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))
(local
 (defthm fn-bps-reverse-start-fn-bps-tree-boundedp-frame-by-definition
   (equal (fn-bps-tree-boundedp tree (fn-bps-reverse-start values after cursor)) (fn-bps-tree-boundedp tree cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-reverse-start)
                                 (fn-bps-tree-boundedp fn-bps-values-boundedp fn-bps-get fn-bps-put fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))
(local
 (defthm fn-bps-reverse-start-fn-bps-values-boundedp-frame-by-definition
   (equal (fn-bps-values-boundedp stored (fn-bps-reverse-start values after cursor)) (fn-bps-values-boundedp stored cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-reverse-start)
                                 (fn-bps-tree-boundedp fn-bps-values-boundedp fn-bps-get fn-bps-put fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))
(local
 (defthm fn-bps-next-param-or-results-fn-bps-tree-boundedp-frame-by-definition
   (equal (fn-bps-tree-boundedp tree (fn-bps-next-param-or-results cursor)) (fn-bps-tree-boundedp tree cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-next-param-or-results)
                                 (fn-bps-tree-boundedp fn-bps-values-boundedp fn-bps-get fn-bps-put fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))
(local
 (defthm fn-bps-next-param-or-results-fn-bps-values-boundedp-frame-by-definition
   (equal (fn-bps-values-boundedp stored (fn-bps-next-param-or-results cursor)) (fn-bps-values-boundedp stored cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-next-param-or-results)
                                 (fn-bps-tree-boundedp fn-bps-values-boundedp fn-bps-get fn-bps-put fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))
(local
 (defthm fn-bps-next-pair-fn-bps-tree-boundedp-frame-by-definition
   (equal (fn-bps-tree-boundedp tree (fn-bps-next-pair cursor)) (fn-bps-tree-boundedp tree cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-next-pair)
                                 (fn-bps-tree-boundedp fn-bps-values-boundedp fn-bps-get fn-bps-put fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))
(local
 (defthm fn-bps-next-pair-fn-bps-values-boundedp-frame-by-definition
   (equal (fn-bps-values-boundedp stored (fn-bps-next-pair cursor)) (fn-bps-values-boundedp stored cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-next-pair)
                                 (fn-bps-tree-boundedp fn-bps-values-boundedp fn-bps-get fn-bps-put fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))
(local
 (defthm fn-bps-finish-value-fn-bps-tree-boundedp-frame-by-definition
   (equal (fn-bps-tree-boundedp tree (fn-bps-finish-value value cursor)) (fn-bps-tree-boundedp tree cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-finish-value)
                                 (fn-bps-tree-boundedp fn-bps-values-boundedp fn-bps-get fn-bps-put fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))
(local
 (defthm fn-bps-finish-value-fn-bps-values-boundedp-frame-by-definition
   (equal (fn-bps-values-boundedp stored (fn-bps-finish-value value cursor)) (fn-bps-values-boundedp stored cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-finish-value)
                                 (fn-bps-tree-boundedp fn-bps-values-boundedp fn-bps-get fn-bps-put fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))
(local
 (defthm fn-bps-result-array-fn-bps-tree-boundedp-frame-by-definition
   (equal (fn-bps-tree-boundedp tree (fn-bps-result-array count cursor)) (fn-bps-tree-boundedp tree cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-result-array)
                                 (fn-bps-tree-boundedp fn-bps-values-boundedp fn-bps-get fn-bps-put fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))
(local
 (defthm fn-bps-result-array-fn-bps-values-boundedp-frame-by-definition
   (equal (fn-bps-values-boundedp stored (fn-bps-result-array count cursor)) (fn-bps-values-boundedp stored cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-result-array)
                                 (fn-bps-tree-boundedp fn-bps-values-boundedp fn-bps-get fn-bps-put fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))
(local
 (defthm fn-bps-bytes-start-fn-bps-tree-boundedp-frame-by-definition
   (equal (fn-bps-tree-boundedp tree (fn-bps-bytes-start length textp cursor)) (fn-bps-tree-boundedp tree cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-bytes-start)
                                 (fn-bps-tree-boundedp fn-bps-values-boundedp fn-bps-get fn-bps-put fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))
(local
 (defthm fn-bps-bytes-start-fn-bps-values-boundedp-frame-by-definition
   (equal (fn-bps-values-boundedp stored (fn-bps-bytes-start length textp cursor)) (fn-bps-values-boundedp stored cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-bytes-start)
                                 (fn-bps-tree-boundedp fn-bps-values-boundedp fn-bps-get fn-bps-put fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))
(local
 (defthm fn-bps-typed-head-fn-bps-tree-boundedp-frame-by-definition
   (equal (fn-bps-tree-boundedp tree (fn-bps-typed-head major value cursor)) (fn-bps-tree-boundedp tree cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-typed-head)
                                 (fn-bps-tree-boundedp fn-bps-values-boundedp fn-bps-get fn-bps-put fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))
(local
 (defthm fn-bps-typed-head-fn-bps-values-boundedp-frame-by-definition
   (equal (fn-bps-values-boundedp stored (fn-bps-typed-head major value cursor)) (fn-bps-values-boundedp stored cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-typed-head)
                                 (fn-bps-tree-boundedp fn-bps-values-boundedp fn-bps-get fn-bps-put fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))
(local
 (defthm fn-bps-accept-head-fn-bps-tree-boundedp-frame-by-definition
   (equal (fn-bps-tree-boundedp tree (fn-bps-accept-head major value cursor)) (fn-bps-tree-boundedp tree cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-accept-head)
                                 (fn-bps-tree-boundedp fn-bps-values-boundedp fn-bps-get fn-bps-put fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))
(local
 (defthm fn-bps-accept-head-fn-bps-values-boundedp-frame-by-definition
   (equal (fn-bps-values-boundedp stored (fn-bps-accept-head major value cursor)) (fn-bps-values-boundedp stored cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-accept-head)
                                 (fn-bps-tree-boundedp fn-bps-values-boundedp fn-bps-get fn-bps-put fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))
(local
 (defthm fn-bps-internal-step-fn-bps-tree-boundedp-frame-by-definition
   (equal (fn-bps-tree-boundedp tree (fn-bps-internal-step cursor)) (fn-bps-tree-boundedp tree cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-internal-step)
                                 (fn-bps-tree-boundedp fn-bps-values-boundedp fn-bps-get fn-bps-put fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-asb-octet (:definition nfix)))))))
(local
 (defthm fn-bps-internal-step-fn-bps-values-boundedp-frame-by-definition
   (equal (fn-bps-values-boundedp stored (fn-bps-internal-step cursor)) (fn-bps-values-boundedp stored cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-internal-step)
                                 (fn-bps-tree-boundedp fn-bps-values-boundedp fn-bps-get fn-bps-put fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-asb-octet (:definition nfix)))))))
(local
 (defthm fn-bps-asb-octet-fn-bps-tree-boundedp-frame-by-definition
   (equal (fn-bps-tree-boundedp tree (fn-bps-asb-octet octet cursor)) (fn-bps-tree-boundedp tree cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-asb-octet)
                                 (fn-bps-tree-boundedp fn-bps-values-boundedp fn-bps-get fn-bps-put fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step (:definition nfix)))))))
(local
 (defthm fn-bps-asb-octet-fn-bps-values-boundedp-frame-by-definition
   (equal (fn-bps-values-boundedp stored (fn-bps-asb-octet octet cursor)) (fn-bps-values-boundedp stored cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-asb-octet)
                                 (fn-bps-tree-boundedp fn-bps-values-boundedp fn-bps-get fn-bps-put fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step (:definition nfix)))))))
(local
 (defthm fn-bps-stop-preserves-aggregate-by-definition
   (implies (and (fn-bps-asb-aggregatep cursor))
            (fn-bps-asb-aggregatep (fn-bps-stop status reason cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-stop fn-bps-values-boundedp)
                                 (fn-bps-asb-head-profilep fn-bps-asb-aggregatep fn-bps-tree-boundedp fn-bps-values-boundedp fn-bps-asb-body-boundedp fn-bps-get fn-bps-put fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-uintp (:definition nfix) fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet))))))
(local
 (defthm fn-bps-stage-preserves-aggregate-by-definition
   (implies (and (fn-bps-asb-aggregatep cursor))
            (fn-bps-asb-aggregatep (fn-bps-stage stage cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-stage fn-bps-values-boundedp)
                                 (fn-bps-asb-head-profilep fn-bps-asb-aggregatep fn-bps-tree-boundedp fn-bps-values-boundedp fn-bps-asb-body-boundedp fn-bps-get fn-bps-put fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-uintp (:definition nfix) fn-bps-stop fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet))))))
(local
 (defthm fn-bps-charge-preserves-aggregate-by-definition
   (implies (and (fn-bps-asb-aggregatep cursor))
            (fn-bps-asb-aggregatep (fn-bps-charge count cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-charge fn-bps-values-boundedp)
                                 (fn-bps-asb-head-profilep fn-bps-asb-aggregatep fn-bps-tree-boundedp fn-bps-values-boundedp fn-bps-asb-body-boundedp fn-bps-get fn-bps-put fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-uintp (:definition nfix) fn-bps-stop fn-bps-stage fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet))))))
(local
 (defthm fn-bps-reverse-start-preserves-aggregate-by-definition
   (implies (and (fn-bps-asb-aggregatep cursor) (fn-bps-values-boundedp values cursor))
            (fn-bps-asb-aggregatep (fn-bps-reverse-start values after cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-reverse-start fn-bps-values-boundedp)
                                 (fn-bps-asb-head-profilep fn-bps-asb-aggregatep fn-bps-tree-boundedp fn-bps-values-boundedp fn-bps-asb-body-boundedp fn-bps-get fn-bps-put fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-uintp (:definition nfix) fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet))))))
(local
 (defthm fn-bps-next-param-or-results-preserves-aggregate-by-definition
   (implies (and (fn-bps-asb-aggregatep cursor))
            (fn-bps-asb-aggregatep (fn-bps-next-param-or-results cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-next-param-or-results fn-bps-values-boundedp)
                                 (fn-bps-asb-head-profilep fn-bps-asb-aggregatep fn-bps-tree-boundedp fn-bps-values-boundedp fn-bps-asb-body-boundedp fn-bps-get fn-bps-put fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-uintp (:definition nfix) fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet))))))
(local
 (defthm fn-bps-next-pair-preserves-aggregate-by-definition
   (implies (and (fn-bps-asb-aggregatep cursor))
            (fn-bps-asb-aggregatep (fn-bps-next-pair cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-next-pair fn-bps-values-boundedp)
                                 (fn-bps-asb-head-profilep fn-bps-asb-aggregatep fn-bps-tree-boundedp fn-bps-values-boundedp fn-bps-asb-body-boundedp fn-bps-get fn-bps-put fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-uintp (:definition nfix) fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet))))))
(local
 (defthm fn-bps-finish-value-preserves-aggregate-by-definition
   (implies (and (fn-bps-asb-aggregatep cursor) (fn-bps-tree-boundedp value cursor))
            (fn-bps-asb-aggregatep (fn-bps-finish-value value cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-finish-value fn-bps-values-boundedp)
                                 (fn-bps-asb-head-profilep fn-bps-asb-aggregatep fn-bps-tree-boundedp fn-bps-values-boundedp fn-bps-asb-body-boundedp fn-bps-get fn-bps-put fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-uintp (:definition nfix) fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet))))))
(local
 (defthm fn-bps-result-array-preserves-aggregate-by-definition
   (implies (and (fn-bps-asb-aggregatep cursor))
            (fn-bps-asb-aggregatep (fn-bps-result-array count cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-result-array fn-bps-values-boundedp)
                                 (fn-bps-asb-head-profilep fn-bps-asb-aggregatep fn-bps-tree-boundedp fn-bps-values-boundedp fn-bps-asb-body-boundedp fn-bps-get fn-bps-put fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-uintp (:definition nfix) fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet))))))
(local
 (defthm fn-bps-bytes-start-preserves-aggregate-by-definition
   (implies (and (fn-bps-asb-aggregatep cursor))
            (fn-bps-asb-aggregatep (fn-bps-bytes-start length textp cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-bytes-start fn-bps-values-boundedp)
                                 (fn-bps-asb-head-profilep fn-bps-asb-aggregatep fn-bps-tree-boundedp fn-bps-values-boundedp fn-bps-asb-body-boundedp fn-bps-get fn-bps-put fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-uintp (:definition nfix) fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet))))))
(local
 (defthm fn-bps-typed-head-preserves-aggregate-by-definition
   (implies (and (fn-bps-asb-aggregatep cursor) (fn-bps-uintp value))
            (fn-bps-asb-aggregatep (fn-bps-typed-head major value cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-typed-head fn-bps-values-boundedp)
                                 (fn-bps-asb-head-profilep fn-bps-asb-aggregatep fn-bps-tree-boundedp fn-bps-values-boundedp fn-bps-asb-body-boundedp fn-bps-get fn-bps-put fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-uintp (:definition nfix) fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet))))))
(local
 (defthm fn-bps-accept-head-preserves-aggregate-by-definition
   (implies (and (fn-bps-asb-aggregatep cursor) (fn-bps-uintp value))
            (fn-bps-asb-aggregatep (fn-bps-accept-head major value cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-accept-head fn-bps-values-boundedp)
                                 (fn-bps-asb-head-profilep fn-bps-asb-aggregatep fn-bps-tree-boundedp fn-bps-values-boundedp fn-bps-asb-body-boundedp fn-bps-get fn-bps-put fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-uintp (:definition nfix) fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-internal-step fn-bps-asb-octet))))))
(local
 (defthm fn-bps-internal-step-preserves-aggregate-by-definition
   (implies (and (fn-bps-asb-aggregatep cursor) (fn-bps-asb-body-boundedp cursor))
            (fn-bps-asb-aggregatep (fn-bps-internal-step cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-internal-step fn-bps-values-boundedp)
                                 (fn-bps-asb-head-profilep fn-bps-asb-aggregatep fn-bps-tree-boundedp fn-bps-values-boundedp fn-bps-asb-body-boundedp fn-bps-get fn-bps-put fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-uintp (:definition nfix) fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-asb-octet))))))
(local
 (defthm fn-bps-aggregate-ready-value-uint-by-definition
   (implies (and (fn-bps-asb-head-profilep cursor)
                 (eq (fn-bps-field 0 (fn-bps-head-feed (fn-bps-get :head cursor) octet)) :ready))
            (fn-bps-uintp
             (fn-bps-field 1 (fn-bps-field 1 (fn-bps-head-feed (fn-bps-get :head cursor) octet)))))
   :hints (("Goal" :use ((:instance fn-bps-head-feed-ready-is-typed-uint64
                                   (head (fn-bps-get :head cursor))))
            :in-theory (e/d (fn-bps-asb-head-profilep fn-bps-ready-headp)
                            (fn-bps-head-feed fn-bps-get fn-bps-field fn-bps-head-profilep fn-bps-uintp
                             fn-bps-head-feed-ready-is-typed-uint64))))))

(local
 (defthm fn-bps-asb-octet-preserves-aggregate-by-definition
   (implies (and (fn-bps-asb-aggregatep cursor) (fn-bps-asb-head-profilep cursor))
            (fn-bps-asb-aggregatep (fn-bps-asb-octet octet cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-asb-octet fn-bps-values-boundedp)
                                 (fn-bps-asb-head-profilep fn-bps-asb-aggregatep fn-bps-tree-boundedp fn-bps-values-boundedp fn-bps-asb-body-boundedp fn-bps-get fn-bps-put fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-uintp (:definition nfix) fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step))))))
(local
 (defthm fn-bps-aggregate-internal-next-context-by-definition
   (implies (and (fn-bps-asb-body-contextp cursor)
                 (eq (fn-bps-get :status cursor) :more)
                 (or (fn-bps-internal-stagep (fn-bps-get :stage cursor))
                     (and (eq (fn-bps-get :stage cursor) :body)
                          (zp (nfix (fn-bps-get :body-left cursor))))))
            (fn-bps-asb-body-contextp
             (fn-bps-internal-step (if (eq (fn-bps-get :stage cursor) :body)
                                      (fn-bps-stage :body-finish cursor) cursor))))
   :hints (("Goal" :use ((:instance fn-bps-asb-drive-preserves-body-context
                                   (octets nil) (quantum 1)))
            :expand ((fn-bps-asb-drive cursor nil 1)
                     (:free (next) (fn-bps-asb-drive next nil 0)))
            :in-theory (e/d (fn-bps-asb-drive fn-bps-field)
                            (fn-bps-asb-drive-preserves-body-context fn-bps-asb-body-contextp
                             fn-bps-get fn-bps-stage fn-bps-internal-stagep fn-bps-internal-step
                             fn-bps-asb-octet fn-bps-asb-drive-rest-is-exact-unconsumed-suffix))))))

(local
 (defthm fn-bps-aggregate-octet-next-context-by-definition
   (implies (and (fn-bps-asb-body-contextp cursor)
                 (eq (fn-bps-get :status cursor) :more)
                 (not (or (fn-bps-internal-stagep (fn-bps-get :stage cursor))
                          (and (eq (fn-bps-get :stage cursor) :body)
                               (zp (nfix (fn-bps-get :body-left cursor))))))
                 (< (nfix (fn-bps-get :offset cursor))
                    (+ (nfix (fn-bps-get :start cursor)) (nfix (fn-bps-get :length cursor)))))
            (fn-bps-asb-body-contextp (fn-bps-asb-octet octet cursor)))
   :hints (("Goal" :use ((:instance fn-bps-asb-drive-preserves-body-context
                                   (octets (list octet)) (quantum 1)))
            :expand ((fn-bps-asb-drive cursor (list octet) 1)
                     (:free (next) (fn-bps-asb-drive next nil 0)))
            :in-theory (e/d (fn-bps-asb-drive fn-bps-field)
                            (fn-bps-asb-drive-preserves-body-context fn-bps-asb-body-contextp
                             fn-bps-get fn-bps-stage fn-bps-internal-stagep fn-bps-internal-step
                             fn-bps-asb-octet fn-bps-asb-drive-rest-is-exact-unconsumed-suffix))))))

(local
 (defthm fn-bps-aggregate-internal-plain-context-by-definition
   (implies (and (fn-bps-asb-body-contextp cursor) (eq (fn-bps-get :status cursor) :more)
                 (fn-bps-internal-stagep (fn-bps-get :stage cursor))
                 (not (eq (fn-bps-get :stage cursor) :body)))
            (fn-bps-asb-body-contextp (fn-bps-internal-step cursor)))
   :hints (("Goal" :use ((:instance fn-bps-aggregate-internal-next-context-by-definition))
            :in-theory (disable fn-bps-asb-body-contextp fn-bps-get fn-bps-internal-stagep
                                fn-bps-internal-step fn-bps-stage fn-bps-aggregate-internal-next-context-by-definition)))))

(local
 (defthm fn-bps-aggregate-internal-finish-context-by-definition
   (implies (and (fn-bps-asb-body-contextp cursor) (eq (fn-bps-get :status cursor) :more)
                 (eq (fn-bps-get :stage cursor) :body)
                 (zp (nfix (fn-bps-get :body-left cursor))))
            (fn-bps-asb-body-contextp (fn-bps-internal-step (fn-bps-stage :body-finish cursor))))
   :hints (("Goal" :use ((:instance fn-bps-aggregate-internal-next-context-by-definition))
            :in-theory (disable fn-bps-asb-body-contextp fn-bps-get fn-bps-internal-stagep
                                fn-bps-internal-step fn-bps-stage fn-bps-aggregate-internal-next-context-by-definition)))))


(local
 (defthm fn-bps-aggregate-context-projections-by-definition
   (implies (fn-bps-asb-aggregate-contextp cursor)
            (and (fn-bps-asb-body-contextp cursor) (fn-bps-asb-aggregatep cursor)
                 (fn-bps-asb-body-boundedp cursor) (fn-bps-asb-head-profilep cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-asb-aggregate-contextp fn-bps-asb-body-contextp)
                                 (fn-bps-asb-aggregatep fn-bps-asb-extentp fn-bps-asb-positionp
                                  fn-bps-asb-head-profilep fn-bps-asb-body-boundedp))))))
(local
 (defthm fn-bps-aggregate-context-other-put-by-definition
   (implies (not (member-equal changed '(:body :backing :start :length :offset :head :source :pending :id
                                       :targets :params :pairs :results :scan :reverse)))
            (equal (fn-bps-asb-aggregate-contextp (fn-bps-put changed value cursor))
                   (fn-bps-asb-aggregate-contextp cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-asb-aggregate-contextp fn-bps-asb-body-contextp
                                  fn-bps-asb-extentp fn-bps-asb-positionp fn-bps-asb-head-profilep
                                  fn-bps-asb-body-boundedp fn-bps-span-in-sourcep)
                                 (fn-bps-asb-aggregatep fn-bps-get fn-bps-put fn-bps-head-profilep
                                  fn-bps-spanp fn-bps-field fn-bps-uintp))))))
(local
 (defthm fn-bps-stop-preserves-aggregate-context-by-definition
   (equal (fn-bps-asb-aggregate-contextp (fn-bps-stop status reason cursor))
          (fn-bps-asb-aggregate-contextp cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-stop) (fn-bps-asb-aggregate-contextp fn-bps-put))))))

(local
 (defthm fn-bps-aggregate-body-context-projections-by-definition
   (implies (fn-bps-asb-body-contextp cursor)
            (and (fn-bps-asb-body-boundedp cursor) (fn-bps-asb-head-profilep cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-asb-body-contextp)
                                 (fn-bps-asb-extentp fn-bps-asb-positionp fn-bps-asb-head-profilep fn-bps-asb-body-boundedp))))))
(local
 (defthm fn-bps-aggregate-stage-body-bounded-by-definition
   (equal (fn-bps-asb-body-boundedp (fn-bps-stage stage cursor)) (fn-bps-asb-body-boundedp cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-asb-body-boundedp fn-bps-stage fn-bps-span-in-sourcep fn-bps-asb-extentp)
                                 (fn-bps-get fn-bps-put fn-bps-spanp fn-bps-field fn-bps-uintp))))))
(defthm fn-bps-asb-drive-preserves-aggregate-context
  (implies (fn-bps-asb-aggregate-contextp cursor)
           (fn-bps-asb-aggregate-contextp (car (fn-bps-asb-drive cursor octets quantum))))
  :hints (("Goal" :induct (fn-bps-asb-drive cursor octets quantum)
           :in-theory (e/d (fn-bps-asb-drive fn-bps-field fn-bps-asb-aggregate-contextp)
                           (fn-bps-asb-body-contextp fn-bps-asb-aggregatep fn-bps-get fn-bps-stop fn-bps-stage
                            fn-bps-internal-stagep fn-bps-internal-step fn-bps-asb-octet
                            fn-bps-asb-drive-rest-is-exact-unconsumed-suffix)))))

(defthm fn-bps-asb-start-establishes-aggregate-context
  (implies (and (fn-bps-uintp start-offset) (fn-bps-uintp declared-length)
                (<= (+ start-offset declared-length) *fn-bpc-max-uint*))
           (fn-bps-asb-aggregate-contextp
            (fn-bps-asb-start kind backing-id start-offset declared-length limits)))
  :hints (("Goal" :use ((:instance fn-bps-asb-start-establishes-body-context))
           :in-theory (e/d (fn-bps-asb-aggregate-contextp fn-bps-asb-aggregatep fn-bps-asb-start
                            fn-bps-get fn-bps-put fn-bps-stop)
                           (fn-bps-asb-body-contextp fn-bps-limitsp fn-bps-field fn-bps-head-start
                            fn-bps-asb-start-establishes-body-context)))))

(defthm fn-bps-asb-step-preserves-aggregate-context
  (implies (fn-bps-asb-aggregate-contextp cursor)
           (fn-bps-asb-aggregate-contextp (fn-bps-field 2 (fn-bps-asb-step cursor window quantum))))
  :hints (("Goal" :in-theory (e/d (fn-bps-asb-step fn-bps-field)
                                (fn-bps-asb-aggregate-contextp fn-bps-get fn-bps-stop fn-bps-asb-drive)))))
