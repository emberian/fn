; Fixed ASB cursor spine is a carried representation invariant.
; This ghost recognizer is never called to revalidate a served parser step.
; Mutable grammar/value-field invariants and immutable provider remain separate.
(in-package "ACL2")
(include-book "bpsec-asb")

(defconst *fn-bps-asb-spine*
  '(:status :reason :stage :kind :backing :start :offset :length :limits
    :head :charge :targets :target-count :remaining :pending :scan :reverse
    :after :context :flags :source :scheme :params :pairs :results
    :result-remaining :id :seen :variant :iv :body :body-left :body-index :delimiter))

(defun fn-bps-cursor-spinep (keys cursor)
  (declare (xargs :guard t))
  (if (consp keys)
      (and (consp cursor) (consp (car cursor))
           (equal (caar cursor) (car keys))
           (fn-bps-cursor-spinep (cdr keys) (cdr cursor)))
    (and (null keys) (null cursor))))

(local
 (defthm fn-bps-put-preserves-spine-by-definition
   (implies (fn-bps-cursor-spinep keys cursor)
            (fn-bps-cursor-spinep keys (fn-bps-put key value cursor)))
   :hints (("Goal" :induct (fn-bps-cursor-spinep keys cursor)))))

(local
 (defthm fn-bps-stop-preserves-spine-by-definition
   (implies (fn-bps-cursor-spinep keys cursor)
            (fn-bps-cursor-spinep keys (fn-bps-stop status reason cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-stop) (fn-bps-cursor-spinep fn-bps-put fn-bps-get fn-bps-field fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp (:definition nfix)))))))

(local
 (defthm fn-bps-stage-preserves-spine-by-definition
   (implies (fn-bps-cursor-spinep keys cursor)
            (fn-bps-cursor-spinep keys (fn-bps-stage stage cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-stage) (fn-bps-cursor-spinep fn-bps-put fn-bps-get fn-bps-field fn-bps-stop fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp (:definition nfix)))))))

(local
 (defthm fn-bps-charge-preserves-spine-by-definition
   (implies (fn-bps-cursor-spinep keys cursor)
            (fn-bps-cursor-spinep keys (fn-bps-charge count cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-charge) (fn-bps-cursor-spinep fn-bps-put fn-bps-get fn-bps-field fn-bps-stop fn-bps-stage fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp (:definition nfix)))))))

(local
 (defthm fn-bps-reverse-start-preserves-spine-by-definition
   (implies (fn-bps-cursor-spinep keys cursor)
            (fn-bps-cursor-spinep keys (fn-bps-reverse-start values after cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-reverse-start) (fn-bps-cursor-spinep fn-bps-put fn-bps-get fn-bps-field fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp (:definition nfix)))))))

(local
 (defthm fn-bps-next-param-or-results-preserves-spine-by-definition
   (implies (fn-bps-cursor-spinep keys cursor)
            (fn-bps-cursor-spinep keys (fn-bps-next-param-or-results cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-next-param-or-results) (fn-bps-cursor-spinep fn-bps-put fn-bps-get fn-bps-field fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp (:definition nfix)))))))

(local
 (defthm fn-bps-next-pair-preserves-spine-by-definition
   (implies (fn-bps-cursor-spinep keys cursor)
            (fn-bps-cursor-spinep keys (fn-bps-next-pair cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-next-pair) (fn-bps-cursor-spinep fn-bps-put fn-bps-get fn-bps-field fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp (:definition nfix)))))))

(local
 (defthm fn-bps-finish-value-preserves-spine-by-definition
   (implies (fn-bps-cursor-spinep keys cursor)
            (fn-bps-cursor-spinep keys (fn-bps-finish-value value cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-finish-value) (fn-bps-cursor-spinep fn-bps-put fn-bps-get fn-bps-field fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp (:definition nfix)))))))

(local
 (defthm fn-bps-result-array-preserves-spine-by-definition
   (implies (fn-bps-cursor-spinep keys cursor)
            (fn-bps-cursor-spinep keys (fn-bps-result-array count cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-result-array) (fn-bps-cursor-spinep fn-bps-put fn-bps-get fn-bps-field fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp (:definition nfix)))))))

(local
 (defthm fn-bps-bytes-start-preserves-spine-by-definition
   (implies (fn-bps-cursor-spinep keys cursor)
            (fn-bps-cursor-spinep keys (fn-bps-bytes-start length textp cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-bytes-start) (fn-bps-cursor-spinep fn-bps-put fn-bps-get fn-bps-field fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp (:definition nfix)))))))

(local
 (defthm fn-bps-typed-head-preserves-spine-by-definition
   (implies (fn-bps-cursor-spinep keys cursor)
            (fn-bps-cursor-spinep keys (fn-bps-typed-head major value cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-typed-head) (fn-bps-cursor-spinep fn-bps-put fn-bps-get fn-bps-field fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp (:definition nfix)))))))

(local
 (defthm fn-bps-accept-head-preserves-spine-by-definition
   (implies (fn-bps-cursor-spinep keys cursor)
            (fn-bps-cursor-spinep keys (fn-bps-accept-head major value cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-accept-head) (fn-bps-cursor-spinep fn-bps-put fn-bps-get fn-bps-field fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-internal-step fn-bps-asb-octet fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp (:definition nfix)))))))

(local
 (defthm fn-bps-internal-step-preserves-spine-by-definition
   (implies (fn-bps-cursor-spinep keys cursor)
            (fn-bps-cursor-spinep keys (fn-bps-internal-step cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-internal-step) (fn-bps-cursor-spinep fn-bps-put fn-bps-get fn-bps-field fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-asb-octet fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp (:definition nfix)))))))

(local
 (defthm fn-bps-asb-octet-preserves-spine-by-definition
   (implies (fn-bps-cursor-spinep keys cursor)
            (fn-bps-cursor-spinep keys (fn-bps-asb-octet octet cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-asb-octet) (fn-bps-cursor-spinep fn-bps-put fn-bps-get fn-bps-field fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp (:definition nfix)))))))

(local
 (defthm fn-bps-spine-cons-by-definition
   (equal (fn-bps-cursor-spinep (cons key keys) (cons (cons key value) cursor))
          (fn-bps-cursor-spinep keys cursor))))

(defthm fn-bps-asb-start-establishes-fixed-spine
  (fn-bps-cursor-spinep *fn-bps-asb-spine*
                        (fn-bps-asb-start kind backing-id start-offset declared-length limits))
  :hints (("Goal" :in-theory (e/d (fn-bps-asb-start)
                                 (fn-bps-cursor-spinep fn-bps-limitsp fn-bps-stop fn-bps-uintp
                                  member-equal (:definition nfix))))))

(defthm fn-bps-asb-drive-preserves-cursor-spine
  (implies (fn-bps-cursor-spinep keys cursor)
           (fn-bps-cursor-spinep keys (car (fn-bps-asb-drive cursor octets quantum))))
  :hints (("Goal" :induct (fn-bps-asb-drive cursor octets quantum)
           :in-theory (e/d (fn-bps-asb-drive fn-bps-field)
                           (fn-bps-cursor-spinep fn-bps-put fn-bps-get fn-bps-stop fn-bps-stage
                            fn-bps-internal-step fn-bps-internal-stagep fn-bps-asb-octet
                            fn-bps-asb-drive-rest-is-exact-unconsumed-suffix)))))

(defthm fn-bps-asb-step-preserves-cursor-spine
  (implies (fn-bps-cursor-spinep keys cursor)
           (fn-bps-cursor-spinep keys (fn-bps-field 2 (fn-bps-asb-step cursor window quantum))))
  :hints (("Goal" :in-theory (e/d (fn-bps-asb-step fn-bps-field)
                                 (fn-bps-cursor-spinep fn-bps-put fn-bps-get fn-bps-stop
                                  fn-bps-asb-drive fn-bps-asb-drive-rest-is-exact-unconsumed-suffix)))))
