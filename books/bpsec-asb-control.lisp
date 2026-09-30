; Carried finite grammar-control invariant of the actual ASB cursor.
; This is one mutable field, not the complete grammar/value/provider invariant.
(in-package "ACL2")
(include-book "bpsec-asb")

(defconst *fn-bps-asb-stages*
  '(:targets-array :target :target-duplicate :reverse :context :flags
    :source-array :source-scheme :source-ssp :source-node :source-service
    :params-array :results-array :target-result-array :pair-array :pair-id
    :pair-value :body :body-finish :done))

(defun fn-bps-asb-stagep (stage)
  (declare (xargs :guard t))
  (if (member-equal stage *fn-bps-asb-stages*) t nil))

(defun fn-bps-asb-controlp (cursor)
  (declare (xargs :guard t))
  (fn-bps-asb-stagep (fn-bps-get :stage cursor)))

(local
 (defthm fn-bps-control-get-other-put-by-definition
   (implies (not (equal wanted changed))
            (equal (fn-bps-get wanted (fn-bps-put changed value cursor))
                   (fn-bps-get wanted cursor)))
   :hints (("Goal" :induct (fn-bps-put changed value cursor)))))

(local
 (defthm fn-bps-control-get-present-put-by-definition
   (implies (fn-bps-get key cursor)
            (equal (fn-bps-get key (fn-bps-put key value cursor)) value))
   :hints (("Goal" :induct (fn-bps-put key value cursor)))))

(local
 (defthm fn-bps-asb-stagep-is-nonempty-by-definition
   (implies (fn-bps-asb-stagep stage) (not (equal stage nil)))))

(local
 (defthm fn-bps-put-preserves-other-control-by-definition
   (implies (not (equal changed :stage))
            (equal (fn-bps-asb-controlp (fn-bps-put changed value cursor))
                   (fn-bps-asb-controlp cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-asb-controlp)
                                 (fn-bps-asb-stagep fn-bps-put fn-bps-get))))))

(local
 (defthm fn-bps-control-put-supported-stage-by-definition
   (implies (fn-bps-asb-stagep (fn-bps-get :stage cursor))
            (equal (fn-bps-get :stage (fn-bps-put :stage value cursor)) value))
   :hints (("Goal" :use ((:instance fn-bps-control-get-present-put-by-definition (key :stage))
                         (:instance fn-bps-asb-stagep-is-nonempty-by-definition
                                    (stage (fn-bps-get :stage cursor))))
            :in-theory (disable fn-bps-asb-stagep fn-bps-put fn-bps-get)))))

(local
 (defthm fn-bps-stage-establishes-control-by-definition
   (implies (and (fn-bps-asb-controlp cursor) (fn-bps-asb-stagep stage))
            (fn-bps-asb-controlp (fn-bps-stage stage cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-stage fn-bps-asb-controlp)
                                 (fn-bps-asb-stagep fn-bps-put fn-bps-get))))))

(local
 (defthm fn-bps-stop-preserves-control-by-definition
   (implies (fn-bps-asb-controlp cursor)
            (fn-bps-asb-controlp (fn-bps-stop status reason cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-stop) (fn-bps-asb-controlp fn-bps-asb-stagep fn-bps-stage fn-bps-put fn-bps-get fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-charge-preserves-control-by-definition
   (implies (fn-bps-asb-controlp cursor)
            (fn-bps-asb-controlp (fn-bps-charge count cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-charge) (fn-bps-asb-controlp fn-bps-asb-stagep fn-bps-stage fn-bps-put fn-bps-get fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-reverse-start-preserves-control-by-definition
   (implies (fn-bps-asb-controlp cursor)
            (fn-bps-asb-controlp (fn-bps-reverse-start values after cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-reverse-start) (fn-bps-asb-controlp fn-bps-asb-stagep fn-bps-stage fn-bps-put fn-bps-get fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-charge fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-next-param-or-results-preserves-control-by-definition
   (implies (fn-bps-asb-controlp cursor)
            (fn-bps-asb-controlp (fn-bps-next-param-or-results cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-next-param-or-results) (fn-bps-asb-controlp fn-bps-asb-stagep fn-bps-stage fn-bps-put fn-bps-get fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-charge fn-bps-reverse-start fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-next-pair-preserves-control-by-definition
   (implies (fn-bps-asb-controlp cursor)
            (fn-bps-asb-controlp (fn-bps-next-pair cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-next-pair) (fn-bps-asb-controlp fn-bps-asb-stagep fn-bps-stage fn-bps-put fn-bps-get fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-finish-value-preserves-control-by-definition
   (implies (fn-bps-asb-controlp cursor)
            (fn-bps-asb-controlp (fn-bps-finish-value value cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-finish-value) (fn-bps-asb-controlp fn-bps-asb-stagep fn-bps-stage fn-bps-put fn-bps-get fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-result-array-preserves-control-by-definition
   (implies (fn-bps-asb-controlp cursor)
            (fn-bps-asb-controlp (fn-bps-result-array count cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-result-array) (fn-bps-asb-controlp fn-bps-asb-stagep fn-bps-stage fn-bps-put fn-bps-get fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-bytes-start-preserves-control-by-definition
   (implies (fn-bps-asb-controlp cursor)
            (fn-bps-asb-controlp (fn-bps-bytes-start length textp cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-bytes-start) (fn-bps-asb-controlp fn-bps-asb-stagep fn-bps-stage fn-bps-put fn-bps-get fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-typed-head-preserves-control-by-definition
   (implies (fn-bps-asb-controlp cursor)
            (fn-bps-asb-controlp (fn-bps-typed-head major value cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-typed-head) (fn-bps-asb-controlp fn-bps-asb-stagep fn-bps-stage fn-bps-put fn-bps-get fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-accept-head-preserves-control-by-definition
   (implies (fn-bps-asb-controlp cursor)
            (fn-bps-asb-controlp (fn-bps-accept-head major value cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-accept-head) (fn-bps-asb-controlp fn-bps-asb-stagep fn-bps-stage fn-bps-put fn-bps-get fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-internal-step-preserves-control-by-definition
   (implies (fn-bps-asb-controlp cursor)
            (fn-bps-asb-controlp (fn-bps-internal-step cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-internal-step) (fn-bps-asb-controlp fn-bps-asb-stagep fn-bps-stage fn-bps-put fn-bps-get fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-asb-octet-preserves-control-by-definition
   (implies (fn-bps-asb-controlp cursor)
            (fn-bps-asb-controlp (fn-bps-asb-octet octet cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-asb-octet) (fn-bps-asb-controlp fn-bps-asb-stagep fn-bps-stage fn-bps-put fn-bps-get fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step (:definition nfix)))))))

(local
 (defthm fn-bps-control-cons-by-definition
   (equal (fn-bps-asb-controlp (cons (cons key value) cursor))
          (if (equal key :stage) (fn-bps-asb-stagep value)
            (fn-bps-asb-controlp cursor)))
   :hints (("Goal" :in-theory (disable fn-bps-asb-stagep)))))

(defthm fn-bps-asb-start-establishes-grammar-control
  (fn-bps-asb-controlp (fn-bps-asb-start kind backing-id start-offset declared-length limits))
  :hints (("Goal" :in-theory (e/d (fn-bps-asb-start)
                                 (fn-bps-asb-controlp fn-bps-stop fn-bps-uintp fn-bps-limitsp
                                  member-equal (:definition nfix))))))

(defthm fn-bps-asb-drive-preserves-grammar-control
  (implies (fn-bps-asb-controlp cursor)
           (fn-bps-asb-controlp (car (fn-bps-asb-drive cursor octets quantum))))
  :hints (("Goal" :induct (fn-bps-asb-drive cursor octets quantum)
           :in-theory (e/d (fn-bps-asb-drive fn-bps-field)
                           (fn-bps-asb-controlp fn-bps-asb-stagep fn-bps-get fn-bps-put
                            fn-bps-stop fn-bps-stage fn-bps-internal-step fn-bps-asb-octet
                            fn-bps-internal-stagep fn-bps-asb-drive-rest-is-exact-unconsumed-suffix)))))

(defthm fn-bps-asb-step-preserves-grammar-control
  (implies (fn-bps-asb-controlp cursor)
           (fn-bps-asb-controlp (fn-bps-field 2 (fn-bps-asb-step cursor window quantum))))
  :hints (("Goal" :in-theory (e/d (fn-bps-asb-step fn-bps-field)
                                 (fn-bps-asb-controlp fn-bps-asb-stagep fn-bps-get fn-bps-stop
                                  fn-bps-asb-drive fn-bps-asb-drive-rest-is-exact-unconsumed-suffix)))))
