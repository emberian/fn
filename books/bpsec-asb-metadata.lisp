; Preservation of the actual ASB cursor's tracked operator metadata charge.
; This is not an allocation/cost theorem or a served invariant revalidation.
(in-package "ACL2")
(include-book "bpsec-asb")

(defun fn-bps-asb-metadatap (cursor)
  (declare (xargs :guard t))
  (let ((charge (fn-bps-get :charge cursor)))
    (and (natp charge)
         (<= charge (nfix (fn-bps-field 6 (fn-bps-get :limits cursor)))))))

(local
 (defthm fn-bps-metadata-get-other-put-by-definition
   (implies (not (equal key changed))
            (equal (fn-bps-get key (fn-bps-put changed value cursor)) (fn-bps-get key cursor)))
   :hints (("Goal" :induct (fn-bps-put changed value cursor)))))

(local
 (defthm fn-bps-metadata-get-present-put-by-definition
   (implies (fn-bps-get key cursor)
            (equal (fn-bps-get key (fn-bps-put key value cursor)) value))
   :hints (("Goal" :induct (fn-bps-put key value cursor)))))

(local
 (defthm fn-bps-metadata-other-put-by-definition
   (implies (and (not (equal changed :charge)) (not (equal changed :limits)))
            (equal (fn-bps-asb-metadatap (fn-bps-put changed value cursor))
                   (fn-bps-asb-metadatap cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-asb-metadatap)
                                 (fn-bps-get fn-bps-put fn-bps-field (:definition nfix)))))))

(local
 (defthm fn-bps-stop-preserves-metadata-by-definition
   (implies (fn-bps-asb-metadatap cursor)
            (fn-bps-asb-metadatap (fn-bps-stop status reason cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-stop)
                                 (fn-bps-asb-metadatap fn-bps-get fn-bps-put))))))

(local
 (defthm fn-bps-charge-preserves-metadata-by-definition
   (implies (fn-bps-asb-metadatap cursor)
            (fn-bps-asb-metadatap (fn-bps-charge count cursor)))
   :hints (("Goal" :use ((:instance fn-bps-metadata-get-present-put-by-definition
                                   (key :charge)
                                   (value (+ (nfix count) (nfix (fn-bps-get :charge cursor))))))
            :in-theory (e/d (fn-bps-charge fn-bps-asb-metadatap fn-bps-stop)
                            (fn-bps-get fn-bps-put fn-bps-field))))))

(local
 (defthm fn-bps-stage-preserves-metadata-by-definition
   (implies (fn-bps-asb-metadatap cursor)
            (fn-bps-asb-metadatap (fn-bps-stage stage cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-stage)
                                 (fn-bps-asb-metadatap fn-bps-put fn-bps-get fn-bps-field
                                  fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp
                                  fn-bps-stop fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-reverse-start-preserves-metadata-by-definition
   (implies (fn-bps-asb-metadatap cursor)
            (fn-bps-asb-metadatap (fn-bps-reverse-start values after cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-reverse-start)
                                 (fn-bps-asb-metadatap fn-bps-put fn-bps-get fn-bps-field
                                  fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp
                                  fn-bps-stop fn-bps-charge fn-bps-stage fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-next-param-or-results-preserves-metadata-by-definition
   (implies (fn-bps-asb-metadatap cursor)
            (fn-bps-asb-metadatap (fn-bps-next-param-or-results cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-next-param-or-results)
                                 (fn-bps-asb-metadatap fn-bps-put fn-bps-get fn-bps-field
                                  fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp
                                  fn-bps-stop fn-bps-charge fn-bps-stage fn-bps-reverse-start fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-next-pair-preserves-metadata-by-definition
   (implies (fn-bps-asb-metadatap cursor)
            (fn-bps-asb-metadatap (fn-bps-next-pair cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-next-pair)
                                 (fn-bps-asb-metadatap fn-bps-put fn-bps-get fn-bps-field
                                  fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp
                                  fn-bps-stop fn-bps-charge fn-bps-stage fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-finish-value-preserves-metadata-by-definition
   (implies (fn-bps-asb-metadatap cursor)
            (fn-bps-asb-metadatap (fn-bps-finish-value value cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-finish-value)
                                 (fn-bps-asb-metadatap fn-bps-put fn-bps-get fn-bps-field
                                  fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp
                                  fn-bps-stop fn-bps-charge fn-bps-stage fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-result-array-preserves-metadata-by-definition
   (implies (fn-bps-asb-metadatap cursor)
            (fn-bps-asb-metadatap (fn-bps-result-array count cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-result-array)
                                 (fn-bps-asb-metadatap fn-bps-put fn-bps-get fn-bps-field
                                  fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp
                                  fn-bps-stop fn-bps-charge fn-bps-stage fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-bytes-start-preserves-metadata-by-definition
   (implies (fn-bps-asb-metadatap cursor)
            (fn-bps-asb-metadatap (fn-bps-bytes-start length textp cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-bytes-start)
                                 (fn-bps-asb-metadatap fn-bps-put fn-bps-get fn-bps-field
                                  fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp
                                  fn-bps-stop fn-bps-charge fn-bps-stage fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-typed-head-preserves-metadata-by-definition
   (implies (fn-bps-asb-metadatap cursor)
            (fn-bps-asb-metadatap (fn-bps-typed-head major value cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-typed-head)
                                 (fn-bps-asb-metadatap fn-bps-put fn-bps-get fn-bps-field
                                  fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp
                                  fn-bps-stop fn-bps-charge fn-bps-stage fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-accept-head-preserves-metadata-by-definition
   (implies (fn-bps-asb-metadatap cursor)
            (fn-bps-asb-metadatap (fn-bps-accept-head major value cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-accept-head)
                                 (fn-bps-asb-metadatap fn-bps-put fn-bps-get fn-bps-field
                                  fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp
                                  fn-bps-stop fn-bps-charge fn-bps-stage fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-internal-step fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-internal-step-preserves-metadata-by-definition
   (implies (fn-bps-asb-metadatap cursor)
            (fn-bps-asb-metadatap (fn-bps-internal-step cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-internal-step)
                                 (fn-bps-asb-metadatap fn-bps-put fn-bps-get fn-bps-field
                                  fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp
                                  fn-bps-stop fn-bps-charge fn-bps-stage fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-asb-octet (:definition nfix)))))))

(local
 (defthm fn-bps-asb-octet-preserves-metadata-by-definition
   (implies (fn-bps-asb-metadatap cursor)
            (fn-bps-asb-metadatap (fn-bps-asb-octet octet cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-asb-octet)
                                 (fn-bps-asb-metadatap fn-bps-put fn-bps-get fn-bps-field
                                  fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp
                                  fn-bps-stop fn-bps-charge fn-bps-stage fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step (:definition nfix)))))))

(defthm fn-bps-asb-start-establishes-metadata-budget
  (fn-bps-asb-metadatap (fn-bps-asb-start kind backing-id start-offset declared-length limits))
  :hints (("Goal" :in-theory (e/d (fn-bps-asb-start fn-bps-asb-metadatap
                                  fn-bps-get fn-bps-put fn-bps-stop)
                                 (fn-bps-limitsp fn-bps-uintp fn-bps-field)))))

(defthm fn-bps-asb-drive-preserves-metadata-budget
  (implies (fn-bps-asb-metadatap cursor)
           (fn-bps-asb-metadatap (car (fn-bps-asb-drive cursor octets quantum))))
  :hints (("Goal" :induct (fn-bps-asb-drive cursor octets quantum)
           :in-theory (e/d (fn-bps-asb-drive fn-bps-field)
                           (fn-bps-asb-metadatap fn-bps-get fn-bps-stop fn-bps-stage
                            fn-bps-internal-step fn-bps-internal-stagep fn-bps-asb-octet
                            fn-bps-asb-drive-rest-is-exact-unconsumed-suffix)))))

(defthm fn-bps-asb-step-preserves-metadata-budget
  (implies (fn-bps-asb-metadatap cursor)
           (fn-bps-asb-metadatap (fn-bps-field 2 (fn-bps-asb-step cursor window quantum))))
  :hints (("Goal" :in-theory (e/d (fn-bps-asb-step fn-bps-field)
                                 (fn-bps-asb-metadatap fn-bps-get fn-bps-stop fn-bps-asb-drive
                                  fn-bps-asb-drive-rest-is-exact-unconsumed-suffix)))))
