; Nested typed CBOR-head invariant for the actual bounded ASB cursor.
; Ghost predicates are not served per-step revalidation.
(in-package "ACL2")
(include-book "bpsec-asb")
(include-book "bpsec-head-invariant")

(defun fn-bps-asb-head-profilep (cursor)
  (declare (xargs :guard t))
  (fn-bps-head-profilep (fn-bps-get :head cursor)))

(local
 (defthm fn-bps-head-profile-nonnil-by-definition
   (implies (fn-bps-head-profilep head) (not (equal head nil)))
   :hints (("Goal" :in-theory (enable fn-bps-head-profilep fn-bps-headp)))))

(local
 (defthm fn-bps-headslot-get-other-put-by-definition
   (implies (not (equal key changed))
            (equal (fn-bps-get key (fn-bps-put changed value cursor)) (fn-bps-get key cursor)))
   :hints (("Goal" :induct (fn-bps-put changed value cursor)))))

(local
 (defthm fn-bps-headslot-get-present-put-by-definition
   (implies (fn-bps-get key cursor)
            (equal (fn-bps-get key (fn-bps-put key value cursor)) value))
   :hints (("Goal" :induct (fn-bps-put key value cursor)))))

(local
 (defthm fn-bps-headslot-other-put-profile-by-definition
   (implies (not (equal changed :head))
            (equal (fn-bps-asb-head-profilep (fn-bps-put changed value cursor))
                   (fn-bps-asb-head-profilep cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-asb-head-profilep)
                                 (fn-bps-head-profilep fn-bps-put fn-bps-get))))))

(local
 (defthm fn-bps-headslot-current-profile-by-definition
   (equal (fn-bps-head-profilep (fn-bps-get :head cursor))
          (fn-bps-asb-head-profilep cursor))
   :hints (("Goal" :in-theory (enable fn-bps-asb-head-profilep)))))

(local
 (defthm fn-bps-headslot-replace-profile-by-definition
   (implies (and (fn-bps-asb-head-profilep cursor) (fn-bps-head-profilep value))
            (fn-bps-asb-head-profilep (fn-bps-put :head value cursor)))
   :hints (("Goal" :use ((:instance fn-bps-head-profile-nonnil-by-definition
                                   (head (fn-bps-get :head cursor)))
                          (:instance fn-bps-headslot-get-present-put-by-definition (key :head)))
            :in-theory (e/d (fn-bps-asb-head-profilep)
                            (fn-bps-head-profilep fn-bps-put fn-bps-get
                             fn-bps-headslot-current-profile-by-definition))))))

(local
 (defthm fn-bps-stop-preserves-head-profile-by-definition
   (implies (fn-bps-asb-head-profilep cursor)
            (fn-bps-asb-head-profilep (fn-bps-stop status reason cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-stop)
                                 (fn-bps-asb-head-profilep fn-bps-put fn-bps-get fn-bps-field fn-bps-head-profilep
                                  fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp
                                  fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-stage-preserves-head-profile-by-definition
   (implies (fn-bps-asb-head-profilep cursor)
            (fn-bps-asb-head-profilep (fn-bps-stage stage cursor)))
   :hints (("Goal" :use ((:instance fn-bps-head-profile-nonnil-by-definition
                                  (head (fn-bps-get :head cursor)))
                                 (:instance fn-bps-headslot-get-present-put-by-definition
                                  (key :head) (value (fn-bps-head-start))
                                  (cursor (fn-bps-put :stage stage cursor))))
            :in-theory (e/d (fn-bps-stage fn-bps-asb-head-profilep)
                                 (fn-bps-headslot-current-profile-by-definition fn-bps-put fn-bps-get fn-bps-field fn-bps-head-profilep
                                  fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp
                                  fn-bps-stop fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-charge-preserves-head-profile-by-definition
   (implies (fn-bps-asb-head-profilep cursor)
            (fn-bps-asb-head-profilep (fn-bps-charge count cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-charge)
                                 (fn-bps-asb-head-profilep fn-bps-put fn-bps-get fn-bps-field fn-bps-head-profilep
                                  fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp
                                  fn-bps-stop fn-bps-stage fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-reverse-start-preserves-head-profile-by-definition
   (implies (fn-bps-asb-head-profilep cursor)
            (fn-bps-asb-head-profilep (fn-bps-reverse-start values after cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-reverse-start)
                                 (fn-bps-asb-head-profilep fn-bps-put fn-bps-get fn-bps-field fn-bps-head-profilep
                                  fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp
                                  fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-next-param-or-results-preserves-head-profile-by-definition
   (implies (fn-bps-asb-head-profilep cursor)
            (fn-bps-asb-head-profilep (fn-bps-next-param-or-results cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-next-param-or-results)
                                 (fn-bps-asb-head-profilep fn-bps-put fn-bps-get fn-bps-field fn-bps-head-profilep
                                  fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp
                                  fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-next-pair-preserves-head-profile-by-definition
   (implies (fn-bps-asb-head-profilep cursor)
            (fn-bps-asb-head-profilep (fn-bps-next-pair cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-next-pair)
                                 (fn-bps-asb-head-profilep fn-bps-put fn-bps-get fn-bps-field fn-bps-head-profilep
                                  fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp
                                  fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-finish-value-preserves-head-profile-by-definition
   (implies (fn-bps-asb-head-profilep cursor)
            (fn-bps-asb-head-profilep (fn-bps-finish-value value cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-finish-value)
                                 (fn-bps-asb-head-profilep fn-bps-put fn-bps-get fn-bps-field fn-bps-head-profilep
                                  fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp
                                  fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-result-array-preserves-head-profile-by-definition
   (implies (fn-bps-asb-head-profilep cursor)
            (fn-bps-asb-head-profilep (fn-bps-result-array count cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-result-array)
                                 (fn-bps-asb-head-profilep fn-bps-put fn-bps-get fn-bps-field fn-bps-head-profilep
                                  fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp
                                  fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-bytes-start-preserves-head-profile-by-definition
   (implies (fn-bps-asb-head-profilep cursor)
            (fn-bps-asb-head-profilep (fn-bps-bytes-start length textp cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-bytes-start)
                                 (fn-bps-asb-head-profilep fn-bps-put fn-bps-get fn-bps-field fn-bps-head-profilep
                                  fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp
                                  fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-typed-head-preserves-head-profile-by-definition
   (implies (fn-bps-asb-head-profilep cursor)
            (fn-bps-asb-head-profilep (fn-bps-typed-head major value cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-typed-head)
                                 (fn-bps-asb-head-profilep fn-bps-put fn-bps-get fn-bps-field fn-bps-head-profilep
                                  fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp
                                  fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-accept-head-preserves-head-profile-by-definition
   (implies (fn-bps-asb-head-profilep cursor)
            (fn-bps-asb-head-profilep (fn-bps-accept-head major value cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-accept-head)
                                 (fn-bps-asb-head-profilep fn-bps-put fn-bps-get fn-bps-field fn-bps-head-profilep
                                  fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp
                                  fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-internal-step-preserves-head-profile-by-definition
   (implies (fn-bps-asb-head-profilep cursor)
            (fn-bps-asb-head-profilep (fn-bps-internal-step cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-internal-step)
                                 (fn-bps-asb-head-profilep fn-bps-put fn-bps-get fn-bps-field fn-bps-head-profilep
                                  fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp
                                  fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-asb-octet-preserves-head-profile-by-definition
   (implies (fn-bps-asb-head-profilep cursor)
            (fn-bps-asb-head-profilep (fn-bps-asb-octet octet cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-asb-octet)
                                 (fn-bps-asb-head-profilep fn-bps-put fn-bps-get fn-bps-field fn-bps-head-profilep
                                  fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp
                                  fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step (:definition nfix)))))))

(local
 (defthm fn-bps-headslot-cons-profile-by-definition
   (equal (fn-bps-asb-head-profilep (cons entry rest))
          (if (and (consp entry) (equal (car entry) :head))
              (fn-bps-head-profilep (cdr entry)) (fn-bps-asb-head-profilep rest)))
   :hints (("Goal" :in-theory (e/d (fn-bps-asb-head-profilep fn-bps-get)
                                 (fn-bps-head-profilep fn-bps-headslot-current-profile-by-definition))))))

(defthm fn-bps-asb-start-establishes-head-profile
  (fn-bps-asb-head-profilep (fn-bps-asb-start kind backing-id start-offset declared-length limits))
  :hints (("Goal" :in-theory (e/d (fn-bps-asb-start)
                                 (fn-bps-asb-head-profilep fn-bps-get fn-bps-head-profilep fn-bps-head-start fn-bps-field
                                  fn-bps-headslot-current-profile-by-definition
                                  fn-bps-stop fn-bps-limitsp fn-bps-uintp)))))

(defthm fn-bps-asb-drive-preserves-head-profile
  (implies (fn-bps-asb-head-profilep cursor)
           (fn-bps-asb-head-profilep (car (fn-bps-asb-drive cursor octets quantum))))
  :hints (("Goal" :induct (fn-bps-asb-drive cursor octets quantum)
           :in-theory (e/d (fn-bps-asb-drive fn-bps-field)
                           (fn-bps-asb-head-profilep fn-bps-get fn-bps-stop fn-bps-stage
                            fn-bps-internal-step fn-bps-internal-stagep fn-bps-asb-octet
                            fn-bps-asb-drive-rest-is-exact-unconsumed-suffix)))))

(defthm fn-bps-asb-step-preserves-head-profile
  (implies (fn-bps-asb-head-profilep cursor)
           (fn-bps-asb-head-profilep (fn-bps-field 2 (fn-bps-asb-step cursor window quantum))))
  :hints (("Goal" :in-theory (e/d (fn-bps-asb-step fn-bps-field)
                                 (fn-bps-asb-head-profilep fn-bps-get fn-bps-stop fn-bps-asb-drive
                                  fn-bps-asb-drive-rest-is-exact-unconsumed-suffix)))))
