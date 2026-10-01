; Carried uint64 target/pending types through actual ASB scheduling.
; RFC9172 section3.6 block numbers, not block types or list positions.
(in-package "ACL2")
(include-book "bpsec-asb-head-invariant")
(include-book "bpsec-asb-spine")

(defun fn-bps-asb-target-typesp (cursor)
  (declare (xargs :guard t))
  (let ((stage (fn-bps-get :stage cursor)))
    (and (fn-bps-uint-listp (fn-bps-get :targets cursor))
         (or (null (fn-bps-get :pending cursor)) (fn-bps-uintp (fn-bps-get :pending cursor)))
         (implies (eq stage :target-duplicate)
                  (and (fn-bps-uintp (fn-bps-get :pending cursor))
                       (fn-bps-uint-listp (fn-bps-get :scan cursor))))
         (implies (and (eq stage :reverse) (eq (fn-bps-get :after cursor) :targets-done))
                  (and (fn-bps-uint-listp (fn-bps-get :scan cursor))
                       (fn-bps-uint-listp (fn-bps-get :reverse cursor)))))))

(defun fn-bps-asb-target-type-contextp (cursor)
  (declare (xargs :guard t))
  (and (fn-bps-asb-target-typesp cursor) (fn-bps-asb-head-profilep cursor)
       (fn-bps-cursor-spinep *fn-bps-asb-spine* cursor)))

(local
 (defthm fn-bps-target-types-get-other-put-by-definition
   (implies (not (equal key changed))
            (equal (fn-bps-get key (fn-bps-put changed value cursor)) (fn-bps-get key cursor)))
   :hints (("Goal" :induct (fn-bps-put changed value cursor)))))
(local
 (defthm fn-bps-target-types-get-put-choice-by-definition
   (or (equal (fn-bps-get key (fn-bps-put key value cursor)) value)
       (equal (fn-bps-get key (fn-bps-put key value cursor)) nil))
   :rule-classes nil
   :hints (("Goal" :induct (fn-bps-put key value cursor)))))
(local
 (defthm fn-bps-target-types-get-present-put-by-definition
   (implies (fn-bps-get key cursor)
            (equal (fn-bps-get key (fn-bps-put key value cursor)) value))
   :hints (("Goal" :induct (fn-bps-put key value cursor)))))
(local
 (defthm fn-bps-target-types-nonnil-uint-by-definition
   (implies (fn-bps-uintp value) (not (equal value nil)))
   :hints (("Goal" :in-theory (enable fn-bps-uintp)))))
(local
 (defthm fn-bps-target-types-cons-by-definition
   (equal (fn-bps-uint-listp (cons a b))
          (and (fn-bps-uintp a) (fn-bps-uint-listp b)))))
(local
 (defthm fn-bps-target-types-cdr-by-definition
   (implies (fn-bps-uint-listp values) (fn-bps-uint-listp (cdr values)))))
(local
 (defthm fn-bps-target-types-car-by-definition
   (implies (and (fn-bps-uint-listp values) (consp values)) (fn-bps-uintp (car values)))))
(local
 (defthm fn-bps-target-types-put-other-by-definition
   (implies (not (member-equal changed '(:targets :pending :stage :after :scan :reverse)))
            (equal (fn-bps-asb-target-typesp (fn-bps-put changed value cursor))
                   (fn-bps-asb-target-typesp cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-asb-target-typesp)
                                 (fn-bps-get fn-bps-put fn-bps-uintp fn-bps-uint-listp))))))
(local
 (defthm fn-bps-target-types-put-targets-by-definition
   (implies (and (fn-bps-asb-target-typesp cursor) (fn-bps-uint-listp value))
            (fn-bps-asb-target-typesp (fn-bps-put :targets value cursor)))
   :hints (("Goal" :use ((:instance fn-bps-target-types-get-put-choice-by-definition (key :targets)))
            :in-theory (e/d (fn-bps-asb-target-typesp)
                            (fn-bps-get fn-bps-put fn-bps-uintp fn-bps-uint-listp))))))
(local
 (defthm fn-bps-target-types-put-pending-by-definition
   (implies (and (fn-bps-asb-target-typesp cursor) (fn-bps-uintp value))
            (fn-bps-asb-target-typesp (fn-bps-put :pending value cursor)))
   :hints (("Goal" :use ((:instance fn-bps-target-types-get-put-choice-by-definition (key :pending)))
            :in-theory (e/d (fn-bps-asb-target-typesp)
                            (fn-bps-get fn-bps-put fn-bps-uintp fn-bps-uint-listp))))))
(local
 (defthm fn-bps-target-types-put-scan-by-definition
   (implies (and (fn-bps-asb-target-typesp cursor) (fn-bps-uint-listp value))
            (fn-bps-asb-target-typesp (fn-bps-put :scan value cursor)))
   :hints (("Goal" :use ((:instance fn-bps-target-types-get-put-choice-by-definition (key :scan)))
            :in-theory (e/d (fn-bps-asb-target-typesp)
                            (fn-bps-get fn-bps-put fn-bps-uintp fn-bps-uint-listp))))))
(local
 (defthm fn-bps-target-types-put-reverse-by-definition
   (implies (and (fn-bps-asb-target-typesp cursor) (fn-bps-uint-listp value))
            (fn-bps-asb-target-typesp (fn-bps-put :reverse value cursor)))
   :hints (("Goal" :use ((:instance fn-bps-target-types-get-put-choice-by-definition (key :reverse)))
            :in-theory (e/d (fn-bps-asb-target-typesp)
                            (fn-bps-get fn-bps-put fn-bps-uintp fn-bps-uint-listp))))))
(local
 (defthm fn-bps-target-types-stage-passive-by-definition
   (implies (and (fn-bps-asb-target-typesp cursor)
                 (not (member-equal stage '(:target-duplicate :reverse))))
            (fn-bps-asb-target-typesp (fn-bps-stage stage cursor)))
   :hints (("Goal" :use ((:instance fn-bps-target-types-get-put-choice-by-definition (key :stage) (value stage)))
            :in-theory (e/d (fn-bps-asb-target-typesp fn-bps-stage)
                            (fn-bps-get fn-bps-put fn-bps-uintp fn-bps-uint-listp fn-bps-head-start))))))
(local
 (defthm fn-bps-target-types-after-passive-by-definition
   (implies (and (fn-bps-asb-target-typesp cursor) (not (equal value :targets-done)))
            (fn-bps-asb-target-typesp (fn-bps-put :after value cursor)))
   :hints (("Goal" :use ((:instance fn-bps-target-types-get-put-choice-by-definition (key :after)))
            :in-theory (e/d (fn-bps-asb-target-typesp)
                            (fn-bps-get fn-bps-put fn-bps-uintp fn-bps-uint-listp))))))
(local
 (defthm fn-bps-target-types-put-preserves-spine-by-definition
   (implies (fn-bps-cursor-spinep keys cursor)
            (fn-bps-cursor-spinep keys (fn-bps-put key value cursor)))
   :hints (("Goal" :induct (fn-bps-cursor-spinep keys cursor)))))
(local
 (defthm fn-bps-target-types-spine-key-put-by-definition
   (implies (and (fn-bps-cursor-spinep keys cursor) (member-equal key keys))
            (equal (fn-bps-get key (fn-bps-put key value cursor)) value))
   :hints (("Goal" :induct (fn-bps-cursor-spinep keys cursor)))))
(local
 (defthm fn-bps-target-types-target-head-by-definition
   (implies (and (fn-bps-asb-target-typesp cursor) (fn-bps-uintp value)
                 (fn-bps-cursor-spinep *fn-bps-asb-spine* cursor))
            (fn-bps-asb-target-typesp
              (fn-bps-put :pending value
                (fn-bps-put :scan (fn-bps-get :targets cursor)
                  (fn-bps-stage :target-duplicate cursor)))))
   :hints (("Goal" :use ((:instance fn-bps-target-types-spine-key-put-by-definition
                             (keys *fn-bps-asb-spine*) (key :scan)
                             (value (fn-bps-get :targets cursor))
                             (cursor (fn-bps-stage :target-duplicate cursor)))
                      (:instance fn-bps-target-types-spine-key-put-by-definition
                             (keys *fn-bps-asb-spine*) (key :pending)
                             (cursor (fn-bps-put :scan (fn-bps-get :targets cursor)
                                       (fn-bps-stage :target-duplicate cursor)))))
            :in-theory (e/d (fn-bps-asb-target-typesp fn-bps-stage)
                                 (fn-bps-get fn-bps-put fn-bps-uintp fn-bps-uint-listp
                                  fn-bps-cursor-spinep))))))
(local
 (defthm fn-bps-stop-preserves-target-types-by-definition
   (implies (and (fn-bps-asb-target-typesp cursor))
            (fn-bps-asb-target-typesp (fn-bps-stop status reason cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-stop)
                                 (fn-bps-stage fn-bps-asb-target-typesp fn-bps-get fn-bps-put fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-uintp fn-bps-uint-listp (:definition nfix) fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet))))))
(local
 (defthm fn-bps-charge-preserves-target-types-by-definition
   (implies (and (fn-bps-asb-target-typesp cursor))
            (fn-bps-asb-target-typesp (fn-bps-charge count cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-charge)
                                 (fn-bps-stage fn-bps-asb-target-typesp fn-bps-get fn-bps-put fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-uintp fn-bps-uint-listp (:definition nfix) fn-bps-stop fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet))))))
(local
 (defthm fn-bps-reverse-start-preserves-target-types-by-definition
   (implies (and (fn-bps-asb-target-typesp cursor) (implies (equal after :targets-done) (fn-bps-uint-listp values)))
            (fn-bps-asb-target-typesp (fn-bps-reverse-start values after cursor)))
   :hints (("Goal" :use ((:instance fn-bps-target-types-get-put-choice-by-definition
                             (key :stage) (value :reverse))
                      (:instance fn-bps-target-types-get-put-choice-by-definition
                             (key :after) (value after) (cursor (fn-bps-stage :reverse cursor)))
                      (:instance fn-bps-target-types-get-put-choice-by-definition
                             (key :reverse) (value nil)
                             (cursor (fn-bps-put :after after (fn-bps-stage :reverse cursor))))
                      (:instance fn-bps-target-types-get-put-choice-by-definition
                             (key :scan) (value values)
                             (cursor (fn-bps-put :reverse nil (fn-bps-put :after after (fn-bps-stage :reverse cursor))))))
            :in-theory (e/d (fn-bps-reverse-start fn-bps-asb-target-typesp fn-bps-stage)
                                 (fn-bps-get fn-bps-put fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-uintp fn-bps-uint-listp (:definition nfix) fn-bps-stop fn-bps-charge fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet))))))
(local
 (defthm fn-bps-next-param-or-results-preserves-target-types-by-definition
   (implies (and (fn-bps-asb-target-typesp cursor))
            (fn-bps-asb-target-typesp (fn-bps-next-param-or-results cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-next-param-or-results)
                                 (fn-bps-stage fn-bps-asb-target-typesp fn-bps-get fn-bps-put fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-uintp fn-bps-uint-listp (:definition nfix) fn-bps-stop fn-bps-charge fn-bps-reverse-start fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet))))))
(local
 (defthm fn-bps-next-pair-preserves-target-types-by-definition
   (implies (and (fn-bps-asb-target-typesp cursor))
            (fn-bps-asb-target-typesp (fn-bps-next-pair cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-next-pair)
                                 (fn-bps-stage fn-bps-asb-target-typesp fn-bps-get fn-bps-put fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-uintp fn-bps-uint-listp (:definition nfix) fn-bps-stop fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet))))))
(local
 (defthm fn-bps-finish-value-preserves-target-types-by-definition
   (implies (and (fn-bps-asb-target-typesp cursor))
            (fn-bps-asb-target-typesp (fn-bps-finish-value value cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-finish-value)
                                 (fn-bps-stage fn-bps-asb-target-typesp fn-bps-get fn-bps-put fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-uintp fn-bps-uint-listp (:definition nfix) fn-bps-stop fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet))))))
(local
 (defthm fn-bps-result-array-preserves-target-types-by-definition
   (implies (and (fn-bps-asb-target-typesp cursor))
            (fn-bps-asb-target-typesp (fn-bps-result-array count cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-result-array)
                                 (fn-bps-stage fn-bps-asb-target-typesp fn-bps-get fn-bps-put fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-uintp fn-bps-uint-listp (:definition nfix) fn-bps-stop fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet))))))
(local
 (defthm fn-bps-bytes-start-preserves-target-types-by-definition
   (implies (and (fn-bps-asb-target-typesp cursor))
            (fn-bps-asb-target-typesp (fn-bps-bytes-start length textp cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-bytes-start)
                                 (fn-bps-stage fn-bps-asb-target-typesp fn-bps-get fn-bps-put fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-uintp fn-bps-uint-listp (:definition nfix) fn-bps-stop fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet))))))
(local
 (defthm fn-bps-typed-head-preserves-target-types-by-definition
   (implies (and (fn-bps-asb-target-typesp cursor) (fn-bps-uintp value))
            (fn-bps-asb-target-typesp (fn-bps-typed-head major value cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-typed-head)
                                 (fn-bps-stage fn-bps-asb-target-typesp fn-bps-get fn-bps-put fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-uintp fn-bps-uint-listp (:definition nfix) fn-bps-stop fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-accept-head fn-bps-internal-step fn-bps-asb-octet))))))
(local
 (defthm fn-bps-accept-head-preserves-target-types-by-definition
   (implies (and (fn-bps-cursor-spinep *fn-bps-asb-spine* cursor) (fn-bps-asb-target-typesp cursor) (fn-bps-uintp value))
            (fn-bps-asb-target-typesp (fn-bps-accept-head major value cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-accept-head)
                                 (fn-bps-cursor-spinep fn-bps-stage fn-bps-asb-target-typesp fn-bps-get fn-bps-put fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-uintp fn-bps-uint-listp (:definition nfix) fn-bps-stop fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-internal-step fn-bps-asb-octet))))))
(local
 (defthm fn-bps-target-types-put-scan-conditional-by-definition
   (implies (and (fn-bps-asb-target-typesp cursor) (implies (or (equal (fn-bps-get :stage cursor) :target-duplicate) (and (equal (fn-bps-get :stage cursor) :reverse) (equal (fn-bps-get :after cursor) :targets-done))) (fn-bps-uint-listp value)))
            (fn-bps-asb-target-typesp (fn-bps-put :scan value cursor)))
   :hints (("Goal" :use ((:instance fn-bps-target-types-get-put-choice-by-definition (key :scan)))
            :in-theory (e/d (fn-bps-asb-target-typesp)
                            (fn-bps-get fn-bps-put fn-bps-uintp fn-bps-uint-listp))))))
(local
 (defthm fn-bps-target-types-put-reverse-conditional-by-definition
   (implies (and (fn-bps-asb-target-typesp cursor) (implies (and (equal (fn-bps-get :stage cursor) :reverse) (equal (fn-bps-get :after cursor) :targets-done)) (fn-bps-uint-listp value)))
            (fn-bps-asb-target-typesp (fn-bps-put :reverse value cursor)))
   :hints (("Goal" :use ((:instance fn-bps-target-types-get-put-choice-by-definition (key :reverse)))
            :in-theory (e/d (fn-bps-asb-target-typesp)
                            (fn-bps-get fn-bps-put fn-bps-uintp fn-bps-uint-listp))))))
(local
 (defthm fn-bps-target-types-projections-by-definition
   (implies (fn-bps-asb-target-typesp cursor)
            (and (fn-bps-uint-listp (fn-bps-get :targets cursor))
                 (or (null (fn-bps-get :pending cursor)) (fn-bps-uintp (fn-bps-get :pending cursor)))
                 (implies (equal (fn-bps-get :stage cursor) :target-duplicate)
                          (and (fn-bps-uintp (fn-bps-get :pending cursor))
                               (fn-bps-uint-listp (fn-bps-get :scan cursor))))
                 (implies (and (equal (fn-bps-get :stage cursor) :reverse) (equal (fn-bps-get :after cursor) :targets-done))
                          (and (fn-bps-uint-listp (fn-bps-get :scan cursor))
                               (fn-bps-uint-listp (fn-bps-get :reverse cursor))))))
   :hints (("Goal" :in-theory (e/d (fn-bps-asb-target-typesp) (fn-bps-get fn-bps-uintp fn-bps-uint-listp))))))
(local
 (defthm fn-bps-internal-step-preserves-target-types-by-definition
   (implies (and (fn-bps-asb-target-typesp cursor))
            (fn-bps-asb-target-typesp (fn-bps-internal-step cursor)))
   :hints (("Goal" :cases ((equal (fn-bps-get :after cursor) :targets-done))
            :in-theory (e/d (fn-bps-internal-step)
                                 (fn-bps-stage fn-bps-asb-target-typesp fn-bps-get fn-bps-put fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-uintp fn-bps-uint-listp (:definition nfix) fn-bps-stop fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-asb-octet))))))
(local
 (defthm fn-bps-target-types-ready-value-uint-by-definition
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
 (defthm fn-bps-asb-octet-preserves-target-types-by-definition
   (implies (and (fn-bps-cursor-spinep *fn-bps-asb-spine* cursor) (fn-bps-asb-target-typesp cursor) (fn-bps-asb-head-profilep cursor))
            (fn-bps-asb-target-typesp (fn-bps-asb-octet octet cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-asb-octet)
                                 (fn-bps-asb-head-profilep fn-bps-cursor-spinep fn-bps-stage fn-bps-asb-target-typesp fn-bps-get fn-bps-put fn-bps-field fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp fn-bps-uintp fn-bps-uint-listp (:definition nfix) fn-bps-stop fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head fn-bps-internal-step))))))
(local
 (defthm fn-bps-target-types-internal-next-head-by-definition
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
 (defthm fn-bps-target-types-octet-next-head-by-definition
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
 (defthm fn-bps-target-types-internal-plain-head-by-definition
   (implies (and (fn-bps-asb-head-profilep cursor) (eq (fn-bps-get :status cursor) :more)
                 (fn-bps-internal-stagep (fn-bps-get :stage cursor))
                 (not (eq (fn-bps-get :stage cursor) :body)))
            (fn-bps-asb-head-profilep (fn-bps-internal-step cursor)))
   :hints (("Goal" :use ((:instance fn-bps-target-types-internal-next-head-by-definition))
            :in-theory (disable fn-bps-asb-head-profilep fn-bps-get fn-bps-internal-stagep
                                fn-bps-internal-step fn-bps-stage fn-bps-target-types-internal-next-head-by-definition)))))

(local
 (defthm fn-bps-target-types-internal-finish-head-by-definition
   (implies (and (fn-bps-asb-head-profilep cursor) (eq (fn-bps-get :status cursor) :more)
                 (eq (fn-bps-get :stage cursor) :body)
                 (zp (nfix (fn-bps-get :body-left cursor))))
            (fn-bps-asb-head-profilep (fn-bps-internal-step (fn-bps-stage :body-finish cursor))))
   :hints (("Goal" :use ((:instance fn-bps-target-types-internal-next-head-by-definition))
            :in-theory (disable fn-bps-asb-head-profilep fn-bps-get fn-bps-internal-stagep
                                fn-bps-internal-step fn-bps-stage fn-bps-target-types-internal-next-head-by-definition)))))

(local
 (defthm fn-bps-target-types-internal-next-spine-by-definition
   (implies (and (fn-bps-cursor-spinep *fn-bps-asb-spine* cursor)
                 (eq (fn-bps-get :status cursor) :more)
                 (or (fn-bps-internal-stagep (fn-bps-get :stage cursor))
                     (and (eq (fn-bps-get :stage cursor) :body)
                          (zp (nfix (fn-bps-get :body-left cursor))))))
            (fn-bps-cursor-spinep *fn-bps-asb-spine*
             (fn-bps-internal-step (if (eq (fn-bps-get :stage cursor) :body)
                                      (fn-bps-stage :body-finish cursor) cursor))))
   :hints (("Goal" :use ((:instance fn-bps-asb-drive-preserves-cursor-spine
                                   (keys *fn-bps-asb-spine*) (octets nil) (quantum 1)))
            :expand ((fn-bps-asb-drive cursor nil 1)
                     (:free (next) (fn-bps-asb-drive next nil 0)))
            :in-theory (e/d (fn-bps-asb-drive fn-bps-field)
                            (fn-bps-asb-drive-preserves-cursor-spine fn-bps-cursor-spinep
                             fn-bps-get fn-bps-stage fn-bps-internal-stagep fn-bps-internal-step
                             fn-bps-asb-octet fn-bps-asb-drive-rest-is-exact-unconsumed-suffix))))))

(local
 (defthm fn-bps-target-types-octet-next-spine-by-definition
   (implies (and (fn-bps-cursor-spinep *fn-bps-asb-spine* cursor)
                 (eq (fn-bps-get :status cursor) :more)
                 (not (or (fn-bps-internal-stagep (fn-bps-get :stage cursor))
                          (and (eq (fn-bps-get :stage cursor) :body)
                               (zp (nfix (fn-bps-get :body-left cursor))))))
                 (< (nfix (fn-bps-get :offset cursor))
                    (+ (nfix (fn-bps-get :start cursor)) (nfix (fn-bps-get :length cursor)))))
            (fn-bps-cursor-spinep *fn-bps-asb-spine* (fn-bps-asb-octet octet cursor)))
   :hints (("Goal" :use ((:instance fn-bps-asb-drive-preserves-cursor-spine
                                   (keys *fn-bps-asb-spine*) (octets (list octet)) (quantum 1)))
            :expand ((fn-bps-asb-drive cursor (list octet) 1)
                     (:free (next) (fn-bps-asb-drive next nil 0)))
            :in-theory (e/d (fn-bps-asb-drive fn-bps-field)
                            (fn-bps-asb-drive-preserves-cursor-spine fn-bps-cursor-spinep
                             fn-bps-get fn-bps-stage fn-bps-internal-stagep fn-bps-internal-step
                             fn-bps-asb-octet fn-bps-asb-drive-rest-is-exact-unconsumed-suffix))))))

(local
 (defthm fn-bps-target-types-internal-plain-spine-by-definition
   (implies (and (fn-bps-cursor-spinep *fn-bps-asb-spine* cursor) (eq (fn-bps-get :status cursor) :more)
                 (fn-bps-internal-stagep (fn-bps-get :stage cursor))
                 (not (eq (fn-bps-get :stage cursor) :body)))
            (fn-bps-cursor-spinep *fn-bps-asb-spine* (fn-bps-internal-step cursor)))
   :hints (("Goal" :use ((:instance fn-bps-target-types-internal-next-spine-by-definition))
            :in-theory (disable fn-bps-cursor-spinep fn-bps-get fn-bps-internal-stagep
                                fn-bps-internal-step fn-bps-stage fn-bps-target-types-internal-next-spine-by-definition)))))

(local
 (defthm fn-bps-target-types-internal-finish-spine-by-definition
   (implies (and (fn-bps-cursor-spinep *fn-bps-asb-spine* cursor) (eq (fn-bps-get :status cursor) :more)
                 (eq (fn-bps-get :stage cursor) :body)
                 (zp (nfix (fn-bps-get :body-left cursor))))
            (fn-bps-cursor-spinep *fn-bps-asb-spine* (fn-bps-internal-step (fn-bps-stage :body-finish cursor))))
   :hints (("Goal" :use ((:instance fn-bps-target-types-internal-next-spine-by-definition))
            :in-theory (disable fn-bps-cursor-spinep fn-bps-get fn-bps-internal-stagep
                                fn-bps-internal-step fn-bps-stage fn-bps-target-types-internal-next-spine-by-definition)))))


(local
 (defthm fn-bps-target-types-stop-context-by-definition
   (implies (fn-bps-asb-target-type-contextp cursor)
            (fn-bps-asb-target-type-contextp (fn-bps-stop status reason cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-stop fn-bps-asb-target-type-contextp fn-bps-asb-head-profilep)
                                 (fn-bps-get fn-bps-put fn-bps-asb-target-typesp fn-bps-head-profilep fn-bps-cursor-spinep))))))

(defthm fn-bps-asb-start-establishes-target-types
  (fn-bps-asb-target-type-contextp (fn-bps-asb-start kind backing-id start-offset declared-length limits))
  :hints (("Goal" :use ((:instance fn-bps-asb-start-establishes-fixed-spine)
                        (:instance fn-bps-asb-start-establishes-head-profile))
           :in-theory (e/d (fn-bps-asb-target-type-contextp fn-bps-asb-target-typesp fn-bps-asb-start fn-bps-stop fn-bps-get fn-bps-put)
                           (fn-bps-cursor-spinep fn-bps-asb-head-profilep fn-bps-limitsp fn-bps-uintp fn-bps-field fn-bps-head-start
                            fn-bps-asb-start-establishes-fixed-spine fn-bps-asb-start-establishes-head-profile)))))

(defthm fn-bps-asb-drive-preserves-target-types
  (implies (fn-bps-asb-target-type-contextp cursor)
           (fn-bps-asb-target-type-contextp (car (fn-bps-asb-drive cursor octets quantum))))
  :hints (("Goal" :induct (fn-bps-asb-drive cursor octets quantum)
           :in-theory (e/d (fn-bps-asb-drive fn-bps-field fn-bps-asb-target-type-contextp)
                           (fn-bps-asb-target-typesp fn-bps-asb-head-profilep fn-bps-cursor-spinep fn-bps-get
                            fn-bps-stop fn-bps-stage fn-bps-internal-stagep fn-bps-internal-step fn-bps-asb-octet
                            fn-bps-asb-drive-rest-is-exact-unconsumed-suffix)))))

(defthm fn-bps-asb-step-preserves-target-types
  (implies (fn-bps-asb-target-type-contextp cursor)
           (fn-bps-asb-target-type-contextp (fn-bps-field 2 (fn-bps-asb-step cursor window quantum))))
  :hints (("Goal" :in-theory (e/d (fn-bps-asb-step fn-bps-field)
                                (fn-bps-asb-target-type-contextp fn-bps-get fn-bps-stop fn-bps-asb-drive)))))
