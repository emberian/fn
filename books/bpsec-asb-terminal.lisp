; Actual terminal parsing consumes the declared ASB data extent exactly.
; This is structural completion, never cryptographic verification.
(in-package "ACL2")
(include-book "bpsec-asb")

(defun fn-bps-asb-terminalp (cursor)
  (declare (xargs :guard t))
  (implies (eq (fn-bps-get :status cursor) :parsed)
           (and (eq (fn-bps-get :stage cursor) :done)
                (equal (fn-bps-get :offset cursor)
                       (+ (nfix (fn-bps-get :start cursor)) (nfix (fn-bps-get :length cursor)))))))

(local
 (defthm fn-bps-terminal-get-other-put-by-definition
   (implies (not (equal key changed))
            (equal (fn-bps-get key (fn-bps-put changed value cursor)) (fn-bps-get key cursor)))
   :hints (("Goal" :induct (fn-bps-put changed value cursor)))))
(local
 (defthm fn-bps-terminal-get-put-choice-by-definition
   (or (equal (fn-bps-get key (fn-bps-put key value cursor)) value)
       (equal (fn-bps-get key (fn-bps-put key value cursor)) nil))
   :rule-classes nil
   :hints (("Goal" :induct (fn-bps-put key value cursor)))))
(local
 (defthm fn-bps-terminal-get-present-put-by-definition
   (implies (fn-bps-get key cursor)
            (equal (fn-bps-get key (fn-bps-put key value cursor)) value))
   :hints (("Goal" :induct (fn-bps-put key value cursor)))))
(local
 (defthm fn-bps-terminal-stop-not-parsed-by-definition
   (implies (not (equal status :parsed))
            (not (equal (fn-bps-get :status (fn-bps-stop status reason cursor)) :parsed)))
   :hints (("Goal" :use ((:instance fn-bps-terminal-get-put-choice-by-definition
                                   (key :status) (value status)))
            :in-theory (e/d (fn-bps-stop) (fn-bps-put fn-bps-get))))))
(local
 (defthm fn-bps-terminal-stop-parsed-fields-by-definition
   (implies (member-equal key '(:stage :offset :start :length))
            (equal (fn-bps-get key (fn-bps-stop status reason cursor)) (fn-bps-get key cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-stop) (fn-bps-put fn-bps-get))))))
(local
 (defthm fn-bps-terminal-not-parsed-sufficient-by-definition
   (implies (not (equal (fn-bps-get :status cursor) :parsed)) (fn-bps-asb-terminalp cursor))))
(local
 (defthm fn-bps-terminal-stop-nonparsed-by-definition
   (implies (not (equal status :parsed)) (fn-bps-asb-terminalp (fn-bps-stop status reason cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-asb-terminalp) (fn-bps-stop fn-bps-get))))))
(local
 (defthm fn-bps-stage-does-not-parse-by-definition
   (implies (not (equal (fn-bps-get :status cursor) :parsed))
            (not (equal (fn-bps-get :status (fn-bps-stage stage cursor)) :parsed)))
   :hints (("Goal" :in-theory (e/d (fn-bps-stage)
                                 (fn-bps-get fn-bps-put fn-bps-field fn-bps-stop fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head (:definition nfix)))))))
(local
 (defthm fn-bps-charge-does-not-parse-by-definition
   (implies (not (equal (fn-bps-get :status cursor) :parsed))
            (not (equal (fn-bps-get :status (fn-bps-charge count cursor)) :parsed)))
   :hints (("Goal" :in-theory (e/d (fn-bps-charge)
                                 (fn-bps-get fn-bps-put fn-bps-field fn-bps-stop fn-bps-stage fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head (:definition nfix)))))))
(local
 (defthm fn-bps-reverse-start-does-not-parse-by-definition
   (implies (not (equal (fn-bps-get :status cursor) :parsed))
            (not (equal (fn-bps-get :status (fn-bps-reverse-start values after cursor)) :parsed)))
   :hints (("Goal" :in-theory (e/d (fn-bps-reverse-start)
                                 (fn-bps-get fn-bps-put fn-bps-field fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head (:definition nfix)))))))
(local
 (defthm fn-bps-next-param-or-results-does-not-parse-by-definition
   (implies (not (equal (fn-bps-get :status cursor) :parsed))
            (not (equal (fn-bps-get :status (fn-bps-next-param-or-results cursor)) :parsed)))
   :hints (("Goal" :in-theory (e/d (fn-bps-next-param-or-results)
                                 (fn-bps-get fn-bps-put fn-bps-field fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head (:definition nfix)))))))
(local
 (defthm fn-bps-next-pair-does-not-parse-by-definition
   (implies (not (equal (fn-bps-get :status cursor) :parsed))
            (not (equal (fn-bps-get :status (fn-bps-next-pair cursor)) :parsed)))
   :hints (("Goal" :in-theory (e/d (fn-bps-next-pair)
                                 (fn-bps-get fn-bps-put fn-bps-field fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head (:definition nfix)))))))
(local
 (defthm fn-bps-finish-value-does-not-parse-by-definition
   (implies (not (equal (fn-bps-get :status cursor) :parsed))
            (not (equal (fn-bps-get :status (fn-bps-finish-value value cursor)) :parsed)))
   :hints (("Goal" :in-theory (e/d (fn-bps-finish-value)
                                 (fn-bps-get fn-bps-put fn-bps-field fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head (:definition nfix)))))))
(local
 (defthm fn-bps-result-array-does-not-parse-by-definition
   (implies (not (equal (fn-bps-get :status cursor) :parsed))
            (not (equal (fn-bps-get :status (fn-bps-result-array count cursor)) :parsed)))
   :hints (("Goal" :in-theory (e/d (fn-bps-result-array)
                                 (fn-bps-get fn-bps-put fn-bps-field fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-bytes-start fn-bps-typed-head fn-bps-accept-head (:definition nfix)))))))
(local
 (defthm fn-bps-bytes-start-does-not-parse-by-definition
   (implies (not (equal (fn-bps-get :status cursor) :parsed))
            (not (equal (fn-bps-get :status (fn-bps-bytes-start length textp cursor)) :parsed)))
   :hints (("Goal" :in-theory (e/d (fn-bps-bytes-start)
                                 (fn-bps-get fn-bps-put fn-bps-field fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-typed-head fn-bps-accept-head (:definition nfix)))))))
(local
 (defthm fn-bps-typed-head-does-not-parse-by-definition
   (implies (not (equal (fn-bps-get :status cursor) :parsed))
            (not (equal (fn-bps-get :status (fn-bps-typed-head major value cursor)) :parsed)))
   :hints (("Goal" :in-theory (e/d (fn-bps-typed-head)
                                 (fn-bps-get fn-bps-put fn-bps-field fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-accept-head (:definition nfix)))))))
(local
 (defthm fn-bps-accept-head-does-not-parse-by-definition
   (implies (not (equal (fn-bps-get :status cursor) :parsed))
            (not (equal (fn-bps-get :status (fn-bps-accept-head major value cursor)) :parsed)))
   :hints (("Goal" :in-theory (e/d (fn-bps-accept-head)
                                 (fn-bps-get fn-bps-put fn-bps-field fn-bps-stop fn-bps-stage fn-bps-charge fn-bps-reverse-start fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value fn-bps-result-array fn-bps-bytes-start fn-bps-typed-head (:definition nfix)))))))

(local
 (defthm fn-bps-head-feed-never-parsed-by-definition
   (not (equal (fn-bps-field 0 (fn-bps-head-feed head octet)) :parsed))
   :hints (("Goal" :in-theory (e/d (fn-bps-head-feed fn-bps-field)
                                 (fn-bps-headp fn-bps-head-width fn-bps-head-minimum fn-cbor-octetp))))))
(local
 (defthm fn-bps-asb-octet-does-not-parse-by-definition
   (implies (not (equal (fn-bps-get :status cursor) :parsed))
            (not (equal (fn-bps-get :status (fn-bps-asb-octet octet cursor)) :parsed)))
   :hints (("Goal" :in-theory (e/d (fn-bps-asb-octet)
                                 (fn-bps-get fn-bps-put fn-bps-field fn-bps-stop fn-bps-stage
                                  fn-bps-accept-head fn-bps-head-feed fn-cbor-octetp fn-bpp-vcharp (:definition nfix)))))))
(local
 (defthm fn-bps-internal-step-establishes-terminal-by-definition
   (implies (not (equal (fn-bps-get :status cursor) :parsed))
            (fn-bps-asb-terminalp (fn-bps-internal-step cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-internal-step fn-bps-asb-terminalp)
                                 (fn-bps-get fn-bps-put fn-bps-field fn-bps-stop fn-bps-stage fn-bps-reverse-start
                                  fn-bps-next-param-or-results fn-bps-next-pair fn-bps-finish-value (:definition nfix)))))))
(local
 (defthm fn-bps-stage-status-by-definition
   (equal (fn-bps-get :status (fn-bps-stage stage cursor)) (fn-bps-get :status cursor))
   :hints (("Goal" :in-theory (e/d (fn-bps-stage) (fn-bps-get fn-bps-put))))))

(defthm fn-bps-asb-start-establishes-terminal-boundary
  (fn-bps-asb-terminalp (fn-bps-asb-start kind backing-id start-offset declared-length limits))
  :hints (("Goal" :in-theory (e/d (fn-bps-asb-start fn-bps-asb-terminalp fn-bps-stop fn-bps-get fn-bps-put)
                                (fn-bps-limitsp fn-bps-uintp fn-bps-field fn-bps-head-start)))))

(defthm fn-bps-asb-drive-preserves-terminal-boundary
  (implies (fn-bps-asb-terminalp cursor)
           (fn-bps-asb-terminalp (car (fn-bps-asb-drive cursor octets quantum))))
  :hints (("Goal" :induct (fn-bps-asb-drive cursor octets quantum)
           :in-theory (e/d (fn-bps-asb-drive fn-bps-field)
                           (fn-bps-asb-terminalp fn-bps-get fn-bps-stop fn-bps-stage
                            fn-bps-internal-stagep fn-bps-internal-step fn-bps-asb-octet
                            fn-bps-asb-drive-rest-is-exact-unconsumed-suffix)))))

(defthm fn-bps-asb-step-preserves-terminal-boundary
  (implies (fn-bps-asb-terminalp cursor)
           (fn-bps-asb-terminalp (fn-bps-field 2 (fn-bps-asb-step cursor window quantum))))
  :hints (("Goal" :in-theory (e/d (fn-bps-asb-step fn-bps-field)
                                (fn-bps-asb-terminalp fn-bps-get fn-bps-stop fn-bps-asb-drive)))))
