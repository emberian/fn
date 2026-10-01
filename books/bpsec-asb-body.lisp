; Actual ASB body-span extent, separate from physical backing bytes/lifetime.
(in-package "ACL2")
(include-book "bpsec-asb-position")
(include-book "bpsec-asb-head-invariant")

(defun fn-bps-asb-extentp (cursor)
  (declare (xargs :guard t))
  (let ((start (fn-bps-get :start cursor)) (length (fn-bps-get :length cursor)))
    (and (fn-bps-uintp start) (fn-bps-uintp length)
         (<= (+ start length) *fn-bpc-max-uint*))))

(defun fn-bps-span-in-sourcep (span cursor)
  (declare (xargs :guard t))
  (or (null span)
      (and (fn-bps-asb-extentp cursor) (fn-bps-spanp span)
           (equal (fn-bps-field 1 span) (fn-bps-get :backing cursor))
           (<= (nfix (fn-bps-get :start cursor)) (fn-bps-field 2 span))
           (<= (+ (fn-bps-field 2 span) (fn-bps-field 3 span))
               (+ (nfix (fn-bps-get :start cursor)) (nfix (fn-bps-get :length cursor)))))))

(defun fn-bps-asb-body-boundedp (cursor)
  (declare (xargs :guard t))
  (fn-bps-span-in-sourcep (fn-bps-get :body cursor) cursor))

(defun fn-bps-asb-body-contextp (cursor)
  (declare (xargs :guard t))
  (and (fn-bps-asb-extentp cursor) (fn-bps-asb-positionp cursor)
       (fn-bps-asb-head-profilep cursor) (fn-bps-asb-body-boundedp cursor)))

(defun fn-bps-asb-body-inputp (cursor)
  (declare (xargs :guard t))
  (and (fn-bps-asb-extentp cursor) (fn-bps-asb-body-boundedp cursor)
       (natp (fn-bps-get :offset cursor))
       (<= (nfix (fn-bps-get :start cursor)) (fn-bps-get :offset cursor))))

(local
 (defthm fn-bps-body-get-other-put-by-definition
   (implies (not (equal key changed))
            (equal (fn-bps-get key (fn-bps-put changed value cursor)) (fn-bps-get key cursor)))
   :hints (("Goal" :induct (fn-bps-put changed value cursor)))))
(local
 (defthm fn-bps-body-get-present-put-by-definition
   (implies (fn-bps-get key cursor)
            (equal (fn-bps-get key (fn-bps-put key value cursor)) value))
   :hints (("Goal" :induct (fn-bps-put key value cursor)))))
(local
 (defthm fn-bps-body-other-put-by-definition
   (implies (not (member-equal changed '(:body :backing :start :length)))
            (equal (fn-bps-asb-body-boundedp (fn-bps-put changed value cursor))
                   (fn-bps-asb-body-boundedp cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-asb-body-boundedp fn-bps-span-in-sourcep fn-bps-asb-extentp)
                                 (fn-bps-get fn-bps-put fn-bps-spanp fn-bps-field fn-bps-uintp))))))
(local
 (defthm fn-bps-body-extent-other-put-by-definition
   (implies (not (member-equal changed '(:start :length)))
            (equal (fn-bps-asb-extentp (fn-bps-put changed value cursor)) (fn-bps-asb-extentp cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-asb-extentp)
                                 (fn-bps-get fn-bps-put fn-bps-uintp))))))
(local
 (defthm fn-bps-body-context-other-put-by-definition
   (implies (not (member-equal changed '(:body :backing :start :length :offset :head)))
            (equal (fn-bps-asb-body-contextp (fn-bps-put changed value cursor))
                   (fn-bps-asb-body-contextp cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-asb-body-contextp fn-bps-asb-extentp
                                  fn-bps-asb-positionp fn-bps-asb-head-profilep
                                  fn-bps-asb-body-boundedp fn-bps-span-in-sourcep)
                                 (fn-bps-get fn-bps-put fn-bps-head-profilep fn-bps-spanp
                                  fn-bps-field fn-bps-uintp))))))
(local
 (defthm fn-bps-stop-preserves-body-context-by-definition
   (equal (fn-bps-asb-body-contextp (fn-bps-stop status reason cursor))
          (fn-bps-asb-body-contextp cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-stop) (fn-bps-asb-body-contextp fn-bps-put))))))

(local
 (defthm fn-bps-stop-preserves-body-span-by-definition
   (equal (fn-bps-asb-body-boundedp (fn-bps-stop status reason cursor))
          (fn-bps-asb-body-boundedp cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-stop)
                                 (fn-bps-asb-body-boundedp fn-bps-put fn-bps-get fn-bps-field
                                  fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp
                                  fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-internal-step fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-stage-preserves-body-span-by-definition
   (equal (fn-bps-asb-body-boundedp (fn-bps-stage stage cursor))
          (fn-bps-asb-body-boundedp cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-stage)
                                 (fn-bps-asb-body-boundedp fn-bps-put fn-bps-get fn-bps-field
                                  fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp
                                  fn-bps-stop fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-internal-step fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-charge-preserves-body-span-by-definition
   (equal (fn-bps-asb-body-boundedp (fn-bps-charge count cursor))
          (fn-bps-asb-body-boundedp cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-charge)
                                 (fn-bps-asb-body-boundedp fn-bps-put fn-bps-get fn-bps-field
                                  fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp
                                  fn-bps-stop fn-bps-stage fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-internal-step fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-reverse-start-preserves-body-span-by-definition
   (equal (fn-bps-asb-body-boundedp (fn-bps-reverse-start values after cursor))
          (fn-bps-asb-body-boundedp cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-reverse-start)
                                 (fn-bps-asb-body-boundedp fn-bps-put fn-bps-get fn-bps-field
                                  fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp
                                  fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-internal-step fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-next-param-or-results-preserves-body-span-by-definition
   (equal (fn-bps-asb-body-boundedp (fn-bps-next-param-or-results cursor))
          (fn-bps-asb-body-boundedp cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-next-param-or-results)
                                 (fn-bps-asb-body-boundedp fn-bps-put fn-bps-get fn-bps-field
                                  fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp
                                  fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-internal-step fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-next-pair-preserves-body-span-by-definition
   (equal (fn-bps-asb-body-boundedp (fn-bps-next-pair cursor))
          (fn-bps-asb-body-boundedp cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-next-pair)
                                 (fn-bps-asb-body-boundedp fn-bps-put fn-bps-get fn-bps-field
                                  fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp
                                  fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-finish-value fn-bps-result-array fn-bps-internal-step fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-finish-value-preserves-body-span-by-definition
   (equal (fn-bps-asb-body-boundedp (fn-bps-finish-value value cursor))
          (fn-bps-asb-body-boundedp cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-finish-value)
                                 (fn-bps-asb-body-boundedp fn-bps-put fn-bps-get fn-bps-field
                                  fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp
                                  fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-result-array fn-bps-internal-step fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-result-array-preserves-body-span-by-definition
   (equal (fn-bps-asb-body-boundedp (fn-bps-result-array count cursor))
          (fn-bps-asb-body-boundedp cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-result-array)
                                 (fn-bps-asb-body-boundedp fn-bps-put fn-bps-get fn-bps-field
                                  fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp
                                  fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-internal-step fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-internal-step-preserves-body-span-by-definition
   (equal (fn-bps-asb-body-boundedp (fn-bps-internal-step cursor))
          (fn-bps-asb-body-boundedp cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-internal-step)
                                 (fn-bps-asb-body-boundedp fn-bps-put fn-bps-get fn-bps-field
                                  fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp
                                  fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-body-input-other-put-by-definition
   (implies (not (member-equal changed '(:body :backing :start :length :offset)))
            (equal (fn-bps-asb-body-inputp (fn-bps-put changed value cursor))
                   (fn-bps-asb-body-inputp cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-asb-body-inputp)
                                 (fn-bps-asb-extentp fn-bps-asb-body-boundedp
                                  fn-bps-get fn-bps-put (:definition nfix)))))))

(local
 (defthm fn-bps-body-input-offset-increase-by-definition
   (implies (fn-bps-asb-body-inputp cursor)
            (fn-bps-asb-body-inputp
             (fn-bps-put :offset (1+ (nfix (fn-bps-get :offset cursor))) cursor)))
   :hints (("Goal" :use ((:instance fn-bps-body-get-present-put-by-definition
                                   (key :offset)
                                   (value (1+ (nfix (fn-bps-get :offset cursor))))))
            :in-theory (e/d (fn-bps-asb-body-inputp)
                            (fn-bps-asb-extentp fn-bps-asb-body-boundedp
                             fn-bps-get fn-bps-put))))))

(local
 (defthm fn-bps-body-get-put-choice-by-definition
   (or (equal (fn-bps-get key (fn-bps-put key value cursor)) value)
       (equal (fn-bps-get key (fn-bps-put key value cursor)) nil))
   :rule-classes nil
   :hints (("Goal" :induct (fn-bps-put key value cursor)))))

(local
 (defthm fn-bps-bytes-start-bounds-body-span-by-definition
   (implies (and (fn-bps-asb-extentp cursor) (fn-bps-asb-body-boundedp cursor)
                 (natp (fn-bps-get :offset cursor))
                 (<= (nfix (fn-bps-get :start cursor)) (fn-bps-get :offset cursor))
                 (fn-bps-uintp length))
            (fn-bps-asb-body-boundedp (fn-bps-bytes-start length textp cursor)))
   :hints (("Goal" :use ((:instance fn-bps-body-get-put-choice-by-definition
                                   (key :body)
                                   (value (fn-bps-span-make (if textp :text-span :bytes-span)
                                                          (fn-bps-get :backing cursor)
                                                          (fn-bps-get :offset cursor) length))
                                   (cursor (fn-bps-put :body-left length
                                             (fn-bps-put :body-index 0
                                              (fn-bps-put :delimiter nil
                                               (fn-bps-stage :body cursor)))))))
            :in-theory (e/d (fn-bps-bytes-start fn-bps-asb-body-boundedp fn-bps-span-in-sourcep
                             fn-bps-asb-extentp fn-bps-spanp fn-bps-span-make fn-bps-uintp
                             fn-bps-stage fn-bps-stop fn-bps-field)
                            (fn-bps-put fn-bps-get fn-bps-head-start))))))

(local
 (defthm fn-bps-stop-preserves-body-input-by-definition
   (equal (fn-bps-asb-body-inputp (fn-bps-stop status reason cursor)) (fn-bps-asb-body-inputp cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-stop)
                                 (fn-bps-asb-body-inputp fn-bps-put fn-bps-get fn-bps-field
                                  fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp
                                  fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-internal-step fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-stage-preserves-body-input-by-definition
   (equal (fn-bps-asb-body-inputp (fn-bps-stage stage cursor)) (fn-bps-asb-body-inputp cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-stage)
                                 (fn-bps-asb-body-inputp fn-bps-put fn-bps-get fn-bps-field
                                  fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp
                                  fn-bps-stop fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-internal-step fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-charge-preserves-body-input-by-definition
   (equal (fn-bps-asb-body-inputp (fn-bps-charge count cursor)) (fn-bps-asb-body-inputp cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-charge)
                                 (fn-bps-asb-body-inputp fn-bps-put fn-bps-get fn-bps-field
                                  fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp
                                  fn-bps-stop fn-bps-stage fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-internal-step fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-reverse-start-preserves-body-input-by-definition
   (equal (fn-bps-asb-body-inputp (fn-bps-reverse-start values after cursor)) (fn-bps-asb-body-inputp cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-reverse-start)
                                 (fn-bps-asb-body-inputp fn-bps-put fn-bps-get fn-bps-field
                                  fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp
                                  fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-internal-step fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-next-param-or-results-preserves-body-input-by-definition
   (equal (fn-bps-asb-body-inputp (fn-bps-next-param-or-results cursor)) (fn-bps-asb-body-inputp cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-next-param-or-results)
                                 (fn-bps-asb-body-inputp fn-bps-put fn-bps-get fn-bps-field
                                  fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp
                                  fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-internal-step fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-next-pair-preserves-body-input-by-definition
   (equal (fn-bps-asb-body-inputp (fn-bps-next-pair cursor)) (fn-bps-asb-body-inputp cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-next-pair)
                                 (fn-bps-asb-body-inputp fn-bps-put fn-bps-get fn-bps-field
                                  fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp
                                  fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-finish-value fn-bps-result-array fn-bps-internal-step fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-finish-value-preserves-body-input-by-definition
   (equal (fn-bps-asb-body-inputp (fn-bps-finish-value value cursor)) (fn-bps-asb-body-inputp cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-finish-value)
                                 (fn-bps-asb-body-inputp fn-bps-put fn-bps-get fn-bps-field
                                  fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp
                                  fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-result-array fn-bps-internal-step fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-result-array-preserves-body-input-by-definition
   (equal (fn-bps-asb-body-inputp (fn-bps-result-array count cursor)) (fn-bps-asb-body-inputp cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-result-array)
                                 (fn-bps-asb-body-inputp fn-bps-put fn-bps-get fn-bps-field
                                  fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp
                                  fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-internal-step fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-internal-step-preserves-body-input-by-definition
   (equal (fn-bps-asb-body-inputp (fn-bps-internal-step cursor)) (fn-bps-asb-body-inputp cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-internal-step)
                                 (fn-bps-asb-body-inputp fn-bps-put fn-bps-get fn-bps-field
                                  fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp
                                  fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-bytes-start-preserves-source-fields-by-definition
   (implies (member-equal key '(:start :length :backing :offset))
            (equal (fn-bps-get key (fn-bps-bytes-start length textp cursor)) (fn-bps-get key cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-bytes-start fn-bps-stage fn-bps-stop)
                                 (fn-bps-get fn-bps-put fn-bps-field (:definition nfix)))))))

(local
 (defthm fn-bps-bytes-start-preserves-body-input-by-definition
   (implies (and (fn-bps-asb-body-inputp cursor) (fn-bps-uintp length))
            (fn-bps-asb-body-inputp (fn-bps-bytes-start length textp cursor)))
   :hints (("Goal" :use ((:instance fn-bps-bytes-start-bounds-body-span-by-definition))
            :in-theory (e/d (fn-bps-asb-body-inputp fn-bps-asb-extentp fn-bps-uintp)
                            (fn-bps-asb-body-boundedp fn-bps-bytes-start fn-bps-get fn-bps-put))))))

(local
 (defthm fn-bps-typed-head-preserves-body-input-by-definition
   (implies (and (fn-bps-asb-body-inputp cursor) (fn-bps-uintp value))
            (fn-bps-asb-body-inputp (fn-bps-typed-head major value cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-typed-head)
                                 (fn-bps-asb-body-inputp fn-bps-get fn-bps-put fn-bps-field
                                  fn-bps-stop fn-bps-finish-value fn-bps-bytes-start fn-bps-uintp
                                  (:definition nfix)))))))

(local
 (defthm fn-bps-accept-head-preserves-body-input-by-definition
   (implies (and (fn-bps-asb-body-inputp cursor) (fn-bps-uintp value))
            (fn-bps-asb-body-inputp (fn-bps-accept-head major value cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-accept-head)
                                 (fn-bps-asb-body-inputp fn-bps-get fn-bps-put fn-bps-field
                                  fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-next-param-or-results
                                  fn-bps-next-pair fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head
                                  fn-bps-uintp (:definition nfix)))))))

(local
 (defthm fn-bps-body-ready-value-uint-by-definition
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
 (defthm fn-bps-asb-octet-preserves-body-input-by-definition
   (implies (and (fn-bps-asb-body-inputp cursor) (fn-bps-asb-head-profilep cursor))
            (fn-bps-asb-body-inputp (fn-bps-asb-octet octet cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-asb-octet)
                                 (fn-bps-asb-body-inputp fn-bps-asb-head-profilep fn-bps-get fn-bps-put
                                  fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp
                                  fn-bps-stop fn-bps-stage fn-bps-accept-head fn-bps-uintp
                                  (:definition nfix)))))))

; Derive transition head facts from the already proved ACTUAL drive at one
; scheduling unit, rather than reopening every private head helper here.
(local
 (defthm fn-bps-body-internal-next-head-by-definition
   (implies (and (fn-bps-asb-head-profilep cursor)
                 (eq (fn-bps-get :status cursor) :more)
                 (or (fn-bps-internal-stagep (fn-bps-get :stage cursor))
                     (and (eq (fn-bps-get :stage cursor) :body)
                          (zp (nfix (fn-bps-get :body-left cursor))))))
            (fn-bps-asb-head-profilep
             (fn-bps-internal-step (if (eq (fn-bps-get :stage cursor) :body)
                                      (fn-bps-stage :body-finish cursor) cursor))))
   :hints (("Goal" :use ((:instance fn-bps-asb-drive-preserves-head-profile
                                   (octets nil) (quantum 1)))
            :expand ((fn-bps-asb-drive cursor nil 1)
                     (:free (next) (fn-bps-asb-drive next nil 0)))
            :in-theory (e/d (fn-bps-asb-drive fn-bps-field)
                            (fn-bps-asb-drive-preserves-head-profile fn-bps-asb-head-profilep
                             fn-bps-get fn-bps-stage fn-bps-internal-stagep fn-bps-internal-step
                             fn-bps-asb-octet fn-bps-asb-drive-rest-is-exact-unconsumed-suffix))))))

(local
 (defthm fn-bps-body-octet-next-head-by-definition
   (implies (and (fn-bps-asb-head-profilep cursor)
                 (eq (fn-bps-get :status cursor) :more)
                 (not (or (fn-bps-internal-stagep (fn-bps-get :stage cursor))
                          (and (eq (fn-bps-get :stage cursor) :body)
                               (zp (nfix (fn-bps-get :body-left cursor))))))
                 (< (nfix (fn-bps-get :offset cursor))
                    (+ (nfix (fn-bps-get :start cursor)) (nfix (fn-bps-get :length cursor)))))
            (fn-bps-asb-head-profilep (fn-bps-asb-octet octet cursor)))
   :hints (("Goal" :use ((:instance fn-bps-asb-drive-preserves-head-profile
                                   (octets (list octet)) (quantum 1)))
            :expand ((fn-bps-asb-drive cursor (list octet) 1)
                     (:free (next) (fn-bps-asb-drive next nil 0)))
            :in-theory (e/d (fn-bps-asb-drive fn-bps-field)
                            (fn-bps-asb-drive-preserves-head-profile fn-bps-asb-head-profilep
                             fn-bps-get fn-bps-stage fn-bps-internal-stagep fn-bps-internal-step
                             fn-bps-asb-octet fn-bps-asb-drive-rest-is-exact-unconsumed-suffix))))))

(local
 (defthm fn-bps-body-internal-plain-head-by-definition
   (implies (and (fn-bps-asb-head-profilep cursor) (eq (fn-bps-get :status cursor) :more)
                 (fn-bps-internal-stagep (fn-bps-get :stage cursor))
                 (not (eq (fn-bps-get :stage cursor) :body)))
            (fn-bps-asb-head-profilep (fn-bps-internal-step cursor)))
   :hints (("Goal" :use ((:instance fn-bps-body-internal-next-head-by-definition))
            :in-theory (disable fn-bps-asb-head-profilep fn-bps-get fn-bps-internal-stagep
                                fn-bps-internal-step fn-bps-stage fn-bps-body-internal-next-head-by-definition)))))

(local
 (defthm fn-bps-body-internal-finish-head-by-definition
   (implies (and (fn-bps-asb-head-profilep cursor) (eq (fn-bps-get :status cursor) :more)
                 (eq (fn-bps-get :stage cursor) :body)
                 (zp (nfix (fn-bps-get :body-left cursor))))
            (fn-bps-asb-head-profilep (fn-bps-internal-step (fn-bps-stage :body-finish cursor))))
   :hints (("Goal" :use ((:instance fn-bps-body-internal-next-head-by-definition))
            :in-theory (disable fn-bps-asb-head-profilep fn-bps-get fn-bps-internal-stagep
                                fn-bps-internal-step fn-bps-stage fn-bps-body-internal-next-head-by-definition)))))

(local
 (defthm fn-bps-asb-drive-preserves-body-input-by-definition
   (implies (and (fn-bps-asb-body-inputp cursor) (fn-bps-asb-head-profilep cursor))
            (fn-bps-asb-body-inputp (car (fn-bps-asb-drive cursor octets quantum))))
   :hints (("Goal" :induct (fn-bps-asb-drive cursor octets quantum)
            :in-theory (e/d (fn-bps-asb-drive fn-bps-field)
                            (fn-bps-asb-body-inputp fn-bps-asb-head-profilep fn-bps-get
                             fn-bps-stop fn-bps-stage fn-bps-internal-stagep fn-bps-internal-step
                             fn-bps-asb-octet fn-bps-asb-drive-rest-is-exact-unconsumed-suffix))))))

(local
 (defthm fn-bps-asb-start-body-nil-by-definition
   (fn-bps-asb-body-boundedp (fn-bps-asb-start kind backing-id start-offset declared-length limits))
   :hints (("Goal" :in-theory (e/d (fn-bps-asb-start fn-bps-asb-body-boundedp
                                  fn-bps-span-in-sourcep fn-bps-get fn-bps-stop fn-bps-put)
                                 (fn-bps-limitsp fn-bps-uintp fn-bps-field fn-bps-head-start))))))

(defthm fn-bps-asb-start-establishes-body-context
  (implies (and (fn-bps-uintp start-offset) (fn-bps-uintp declared-length)
                (<= (+ start-offset declared-length) *fn-bpc-max-uint*))
           (fn-bps-asb-body-contextp
            (fn-bps-asb-start kind backing-id start-offset declared-length limits)))
  :hints (("Goal" :use ((:instance fn-bps-asb-start-establishes-source-range)
                        (:instance fn-bps-asb-start-establishes-head-profile)
                        (:instance fn-bps-asb-start-body-nil-by-definition))
           :in-theory (e/d (fn-bps-asb-body-contextp fn-bps-asb-extentp fn-bps-asb-start fn-bps-uintp
                            fn-bps-get fn-bps-stop fn-bps-put)
                           (fn-bps-asb-positionp fn-bps-asb-head-profilep fn-bps-asb-body-boundedp
                            fn-bps-asb-start-establishes-source-range fn-bps-asb-start-establishes-head-profile
                            fn-bps-asb-start-body-nil-by-definition fn-bps-limitsp fn-bps-field fn-bps-head-start)))))

(defthm fn-bps-asb-drive-preserves-body-context
  (implies (fn-bps-asb-body-contextp cursor)
           (fn-bps-asb-body-contextp (car (fn-bps-asb-drive cursor octets quantum))))
  :hints (("Goal" :use ((:instance fn-bps-asb-drive-preserves-source-range)
                        (:instance fn-bps-asb-drive-preserves-head-profile)
                        (:instance fn-bps-asb-drive-preserves-body-input-by-definition))
           :in-theory (e/d (fn-bps-asb-body-contextp fn-bps-asb-body-inputp fn-bps-asb-positionp)
                           (fn-bps-asb-extentp fn-bps-asb-head-profilep fn-bps-asb-body-boundedp
                            fn-bps-get fn-bps-asb-drive fn-bps-field
                            fn-bps-asb-drive-preserves-source-range fn-bps-asb-drive-preserves-head-profile
                            fn-bps-asb-drive-preserves-body-input-by-definition)))))

(defthm fn-bps-asb-step-preserves-body-context
  (implies (fn-bps-asb-body-contextp cursor)
           (fn-bps-asb-body-contextp (fn-bps-field 2 (fn-bps-asb-step cursor window quantum))))
  :hints (("Goal" :in-theory (e/d (fn-bps-asb-step fn-bps-field)
                                 (fn-bps-asb-body-contextp fn-bps-get fn-bps-stop fn-bps-asb-drive
                                  fn-bps-asb-drive-rest-is-exact-unconsumed-suffix)))))
