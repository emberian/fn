; Actual ASB readonly subject and consumed-prefix position boundary.
; Preserved IDs/offsets do not prove immutable provider bytes or pinned lifetime.
(in-package "ACL2")
(include-book "bpsec-asb")

(defun fn-bps-asb-readonly-keyp (key)
  (declare (xargs :guard t))
  (if (member-equal key '(:kind :backing :start :length :limits)) t nil))

(defun fn-bps-asb-coordinate (cursor)
  (declare (xargs :guard t))
  (list (fn-bps-get :kind cursor) (fn-bps-get :backing cursor)
        (fn-bps-get :start cursor) (fn-bps-get :length cursor) (fn-bps-get :limits cursor)))

(local
 (defthm fn-bps-position-get-other-put-by-definition
   (implies (not (equal key changed))
            (equal (fn-bps-get key (fn-bps-put changed value cursor)) (fn-bps-get key cursor)))
   :hints (("Goal" :induct (fn-bps-put changed value cursor)))))

(local
 (defthm fn-bps-position-get-present-put-by-definition
   (implies (fn-bps-get key cursor)
            (equal (fn-bps-get key (fn-bps-put key value cursor)) value))
   :hints (("Goal" :induct (fn-bps-put key value cursor)))))

(local
 (defthm fn-bps-stop-preserves-readonly-by-definition
   (implies (fn-bps-asb-readonly-keyp key)
            (equal (fn-bps-get key (fn-bps-stop status reason cursor)) (fn-bps-get key cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-stop fn-bps-asb-readonly-keyp)
                                 (fn-bps-put fn-bps-get fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-stage-preserves-readonly-by-definition
   (implies (fn-bps-asb-readonly-keyp key)
            (equal (fn-bps-get key (fn-bps-stage stage cursor)) (fn-bps-get key cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-stage fn-bps-asb-readonly-keyp)
                                 (fn-bps-put fn-bps-get fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-charge-preserves-readonly-by-definition
   (implies (fn-bps-asb-readonly-keyp key)
            (equal (fn-bps-get key (fn-bps-charge count cursor)) (fn-bps-get key cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-charge fn-bps-asb-readonly-keyp)
                                 (fn-bps-put fn-bps-get fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-stage fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-reverse-start-preserves-readonly-by-definition
   (implies (fn-bps-asb-readonly-keyp key)
            (equal (fn-bps-get key (fn-bps-reverse-start values after cursor)) (fn-bps-get key cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-reverse-start fn-bps-asb-readonly-keyp)
                                 (fn-bps-put fn-bps-get fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-next-param-or-results-preserves-readonly-by-definition
   (implies (fn-bps-asb-readonly-keyp key)
            (equal (fn-bps-get key (fn-bps-next-param-or-results cursor)) (fn-bps-get key cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-next-param-or-results fn-bps-asb-readonly-keyp)
                                 (fn-bps-put fn-bps-get fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-next-pair-preserves-readonly-by-definition
   (implies (fn-bps-asb-readonly-keyp key)
            (equal (fn-bps-get key (fn-bps-next-pair cursor)) (fn-bps-get key cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-next-pair fn-bps-asb-readonly-keyp)
                                 (fn-bps-put fn-bps-get fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-finish-value-preserves-readonly-by-definition
   (implies (fn-bps-asb-readonly-keyp key)
            (equal (fn-bps-get key (fn-bps-finish-value value cursor)) (fn-bps-get key cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-finish-value fn-bps-asb-readonly-keyp)
                                 (fn-bps-put fn-bps-get fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-result-array-preserves-readonly-by-definition
   (implies (fn-bps-asb-readonly-keyp key)
            (equal (fn-bps-get key (fn-bps-result-array count cursor)) (fn-bps-get key cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-result-array fn-bps-asb-readonly-keyp)
                                 (fn-bps-put fn-bps-get fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-bytes-start-preserves-readonly-by-definition
   (implies (fn-bps-asb-readonly-keyp key)
            (equal (fn-bps-get key (fn-bps-bytes-start length textp cursor)) (fn-bps-get key cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-bytes-start fn-bps-asb-readonly-keyp)
                                 (fn-bps-put fn-bps-get fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-typed-head-preserves-readonly-by-definition
   (implies (fn-bps-asb-readonly-keyp key)
            (equal (fn-bps-get key (fn-bps-typed-head major value cursor)) (fn-bps-get key cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-typed-head fn-bps-asb-readonly-keyp)
                                 (fn-bps-put fn-bps-get fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-accept-head-preserves-readonly-by-definition
   (implies (fn-bps-asb-readonly-keyp key)
            (equal (fn-bps-get key (fn-bps-accept-head major value cursor)) (fn-bps-get key cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-accept-head fn-bps-asb-readonly-keyp)
                                 (fn-bps-put fn-bps-get fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-internal-step-preserves-readonly-by-definition
   (implies (fn-bps-asb-readonly-keyp key)
            (equal (fn-bps-get key (fn-bps-internal-step cursor)) (fn-bps-get key cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-internal-step fn-bps-asb-readonly-keyp)
                                 (fn-bps-put fn-bps-get fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-asb-octet-preserves-readonly-by-definition
   (implies (fn-bps-asb-readonly-keyp key)
            (equal (fn-bps-get key (fn-bps-asb-octet octet cursor)) (fn-bps-get key cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-asb-octet fn-bps-asb-readonly-keyp)
                                 (fn-bps-put fn-bps-get fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step (:definition nfix)))))))

(local
 (defthm fn-bps-stop-preserves-offset-by-definition
   (equal (fn-bps-get :offset (fn-bps-stop status reason cursor)) (fn-bps-get :offset cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-stop)
                                 (fn-bps-put fn-bps-get fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-stage-preserves-offset-by-definition
   (equal (fn-bps-get :offset (fn-bps-stage stage cursor)) (fn-bps-get :offset cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-stage)
                                 (fn-bps-put fn-bps-get fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-charge-preserves-offset-by-definition
   (equal (fn-bps-get :offset (fn-bps-charge count cursor)) (fn-bps-get :offset cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-charge)
                                 (fn-bps-put fn-bps-get fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-stage fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-reverse-start-preserves-offset-by-definition
   (equal (fn-bps-get :offset (fn-bps-reverse-start values after cursor)) (fn-bps-get :offset cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-reverse-start)
                                 (fn-bps-put fn-bps-get fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-next-param-or-results-preserves-offset-by-definition
   (equal (fn-bps-get :offset (fn-bps-next-param-or-results cursor)) (fn-bps-get :offset cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-next-param-or-results)
                                 (fn-bps-put fn-bps-get fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-next-pair-preserves-offset-by-definition
   (equal (fn-bps-get :offset (fn-bps-next-pair cursor)) (fn-bps-get :offset cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-next-pair)
                                 (fn-bps-put fn-bps-get fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-finish-value-preserves-offset-by-definition
   (equal (fn-bps-get :offset (fn-bps-finish-value value cursor)) (fn-bps-get :offset cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-finish-value)
                                 (fn-bps-put fn-bps-get fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-result-array-preserves-offset-by-definition
   (equal (fn-bps-get :offset (fn-bps-result-array count cursor)) (fn-bps-get :offset cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-result-array)
                                 (fn-bps-put fn-bps-get fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-bytes-start-preserves-offset-by-definition
   (equal (fn-bps-get :offset (fn-bps-bytes-start length textp cursor)) (fn-bps-get :offset cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-bytes-start)
                                 (fn-bps-put fn-bps-get fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-typed-head-preserves-offset-by-definition
   (equal (fn-bps-get :offset (fn-bps-typed-head major value cursor)) (fn-bps-get :offset cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-typed-head)
                                 (fn-bps-put fn-bps-get fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-accept-head-preserves-offset-by-definition
   (equal (fn-bps-get :offset (fn-bps-accept-head major value cursor)) (fn-bps-get :offset cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-accept-head)
                                 (fn-bps-put fn-bps-get fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-internal-step-preserves-offset-by-definition
   (equal (fn-bps-get :offset (fn-bps-internal-step cursor)) (fn-bps-get :offset cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-internal-step)
                                 (fn-bps-put fn-bps-get fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-asb-octet-increments-offset-by-definition
   (implies (natp (fn-bps-get :offset cursor))
            (equal (fn-bps-get :offset (fn-bps-asb-octet octet cursor))
                   (1+ (fn-bps-get :offset cursor))))
   :hints (("Goal" :in-theory (e/d (fn-bps-asb-octet)
                                 (fn-bps-put fn-bps-get fn-bps-field fn-bps-head-feed fn-cbor-octetp
                                  fn-bpp-vcharp fn-bps-stop fn-bps-stage fn-bps-accept-head))))))

(defthm fn-bps-asb-drive-preserves-readonly-subject
  (implies (fn-bps-asb-readonly-keyp key)
           (equal (fn-bps-get key (car (fn-bps-asb-drive cursor octets quantum)))
                  (fn-bps-get key cursor)))
  :hints (("Goal" :induct (fn-bps-asb-drive cursor octets quantum)
           :in-theory (e/d (fn-bps-asb-drive fn-bps-field)
                           (fn-bps-asb-readonly-keyp fn-bps-get fn-bps-stop fn-bps-stage
                            fn-bps-internal-step fn-bps-internal-stagep fn-bps-asb-octet
                            fn-bps-asb-drive-rest-is-exact-unconsumed-suffix)))))

(defthm fn-bps-asb-step-preserves-source-coordinate
  (equal (fn-bps-asb-coordinate (fn-bps-field 2 (fn-bps-asb-step cursor window quantum)))
         (fn-bps-asb-coordinate cursor))
  :hints (("Goal" :in-theory (e/d (fn-bps-asb-step fn-bps-field fn-bps-asb-coordinate)
                                 (fn-bps-get fn-bps-stop fn-bps-asb-drive
                                  fn-bps-asb-drive-rest-is-exact-unconsumed-suffix)))))

(local
 (defthm fn-bps-position-consumed-natural-by-definition
   (natp (fn-bps-field 1 (fn-bps-asb-drive cursor octets quantum)))
   :rule-classes (:rewrite :type-prescription)
   :hints (("Goal" :induct (fn-bps-asb-drive cursor octets quantum)
            :in-theory (e/d (fn-bps-asb-drive fn-bps-field)
                            (fn-bps-get fn-bps-stop fn-bps-internal-stagep fn-bps-internal-step
                             fn-bps-stage fn-bps-asb-octet
                             fn-bps-asb-drive-rest-is-exact-unconsumed-suffix))))))

(defthm fn-bps-asb-drive-offset-is-consumed-prefix
  (implies (natp (fn-bps-get :offset cursor))
           (equal (fn-bps-get :offset (car (fn-bps-asb-drive cursor octets quantum)))
                  (+ (fn-bps-get :offset cursor)
                     (fn-bps-field 1 (fn-bps-asb-drive cursor octets quantum)))))
  :hints (("Goal" :induct (fn-bps-asb-drive cursor octets quantum)
           :in-theory (e/d (fn-bps-asb-drive fn-bps-field)
                           (fn-bps-get fn-bps-stop fn-bps-stage fn-bps-internal-step
                            fn-bps-internal-stagep fn-bps-asb-octet
                            fn-bps-asb-drive-rest-is-exact-unconsumed-suffix)))))

(defthm fn-bps-asb-step-offset-is-consumed-prefix
  (implies (natp (fn-bps-get :offset cursor))
           (equal (fn-bps-get :offset (fn-bps-field 2 (fn-bps-asb-step cursor window quantum)))
                  (+ (fn-bps-get :offset cursor)
                     (fn-bps-field 3 (fn-bps-asb-step cursor window quantum)))))
  :hints (("Goal" :in-theory (e/d (fn-bps-asb-step fn-bps-field)
                                 (fn-bps-get fn-bps-stop fn-bps-asb-drive
                                  fn-bps-asb-drive-rest-is-exact-unconsumed-suffix)))))

; Ghost range invariant. The served path carries it; it does not revalidate.
(defun fn-bps-asb-positionp (cursor)
  (declare (xargs :guard t))
  (let ((start (fn-bps-get :start cursor))
        (length (fn-bps-get :length cursor))
        (offset (fn-bps-get :offset cursor)))
    (and (natp start) (natp length) (natp offset)
         (<= start offset) (<= offset (+ start length)))))

(defthm fn-bps-asb-start-establishes-source-range
  (implies (and (natp start-offset) (natp declared-length))
           (fn-bps-asb-positionp
            (fn-bps-asb-start kind backing-id start-offset declared-length limits)))
  :hints (("Goal" :in-theory (e/d (fn-bps-asb-start fn-bps-asb-positionp fn-bps-get fn-bps-stop fn-bps-put)
                                 (fn-bps-limitsp fn-bps-uintp fn-bps-field)))))

(local
 (defthm fn-bps-position-drive-offset-upper-bound-by-definition
   (implies (and (natp (fn-bps-get :start cursor))
                 (natp (fn-bps-get :length cursor))
                 (natp (fn-bps-get :offset cursor))
                 (<= (fn-bps-get :offset cursor)
                     (+ (fn-bps-get :start cursor) (fn-bps-get :length cursor))))
            (<= (fn-bps-get :offset (car (fn-bps-asb-drive cursor octets quantum)))
                (+ (fn-bps-get :start cursor) (fn-bps-get :length cursor))))
   :hints (("Goal" :induct (fn-bps-asb-drive cursor octets quantum)
            :in-theory (e/d (fn-bps-asb-drive fn-bps-field)
                            (fn-bps-get fn-bps-stop fn-bps-stage fn-bps-internal-step
                             fn-bps-internal-stagep fn-bps-asb-octet
                             fn-bps-asb-drive-offset-is-consumed-prefix
                             fn-bps-asb-drive-rest-is-exact-unconsumed-suffix))))))

(defthm fn-bps-asb-drive-preserves-source-range
  (implies (fn-bps-asb-positionp cursor)
           (fn-bps-asb-positionp (car (fn-bps-asb-drive cursor octets quantum))))
  :hints (("Goal" :use ((:instance fn-bps-position-drive-offset-upper-bound-by-definition))
           :in-theory (e/d (fn-bps-asb-positionp)
                           (fn-bps-asb-drive fn-bps-get fn-bps-field
                            fn-bps-position-drive-offset-upper-bound-by-definition)))))

(defthm fn-bps-asb-step-preserves-source-range
  (implies (fn-bps-asb-positionp cursor)
           (fn-bps-asb-positionp (fn-bps-field 2 (fn-bps-asb-step cursor window quantum))))
  :hints (("Goal" :in-theory (e/d (fn-bps-asb-step fn-bps-field fn-bps-asb-positionp)
                                 (fn-bps-asb-drive fn-bps-get fn-bps-stop
                                  fn-bps-asb-drive-rest-is-exact-unconsumed-suffix)))))
