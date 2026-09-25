; fn: portable FN-Authorship carrier for the selected hybrid source signature.
; This is deliberately not an FN-Statement: the two profiles sign different
; subjects.  The host receives only bounded plans from this book.

(in-package "ACL2")
(include-book "hybrid-signature")
(include-book "stx-carrier")
(include-book "injection-shape")
(include-book "article-fields")

(defconst *fn-hc-version* 1)
; Carrier v2 carries a source over the v1 length field's 65535 octets.  Its
; nine items have the v1 shape and widths; only item 1 says 2.  The version
; a source is signed under is `fn-hsig-source-version''s, and a received
; carrier is decoded at exactly that version.
(defconst *fn-hc-v2-version* 2)
(defconst *fn-hc-suite* 1)
(defconst *fn-hc-max-binary-octets* 5405)
(defconst *fn-hc-max-field-octets* 8192)
(defconst *fn-hc-item-count* 9)

(defconst *fn-hc-name*
  '(102 110 45 97 117 116 104 111 114 115 104 105 112)) ; fn-authorship
(defconst *fn-hc-path-name* '(112 97 116 104))
(defconst *fn-hc-xref-name* '(120 114 101 102))
(defconst *fn-hc-injection-date-name*
  '(105 110 106 101 99 116 105 111 110 45 100 97 116 101))
(defconst *fn-hc-injection-info-name*
  '(105 110 106 101 99 116 105 111 110 45 105 110 102 111))
(defconst *fn-hc-statement-name*
  '(102 110 45 115 116 97 116 101 109 101 110 116))
(defconst *fn-hc-policy-name* '(102 110 45 112 111 108 105 99 121))

(defun fn-hc-ok (value)
  (declare (xargs :guard t))
  (list :ok value))
(defun fn-hc-error (reason original)
  (declare (xargs :guard t))
  (list :unverified reason original))
(defun fn-hc-okp (x)
  (declare (xargs :guard t))
  (and (consp x) (equal (car x) :ok)))
(defun fn-hc-value (x)
  (declare (xargs :guard t))
  (if (and (consp x) (consp (cdr x))) (cadr x) nil))

(defun fn-hc-versionp (version)
  (declare (xargs :guard t))
  (or (equal version *fn-hc-version*)
      (equal version *fn-hc-v2-version*)))

(defun fn-hc-items-at (version principal keys signatures)
  (declare (xargs :guard t
                  :guard-hints
                  (("Goal" :in-theory (enable fn-hsig-exact-octets-p
                                               fn-hsig-keyset-p
                                               fn-hsig-signatures-p)))))
  (if (and (fn-hc-versionp version)
           (fn-hsig-exact-octets-p principal 32)
           (fn-hsig-keyset-p keys)
           (fn-hsig-signatures-p signatures))
      (list (cons :uint version)
            (cons :uint *fn-hc-suite*)
            (cons :bytes principal)
            (cons :uint *fn-hsig-ed25519-algorithm*)
            (cons :bytes (cdr (car keys)))
            (cons :uint *fn-hsig-ml-dsa-65-algorithm*)
            (cons :bytes (cdr (cadr keys)))
            (cons :bytes (cdr (car signatures)))
            (cons :bytes (cdr (cadr signatures))))
    nil))

(defun fn-hc-items (principal keys signatures)
  (declare (xargs :guard t))
  (fn-hc-items-at *fn-hc-version* principal keys signatures))

(defun fn-hc-encode-at (version principal keys signatures)
  (declare (xargs :guard t
                  :guard-hints
                  (("Goal" :in-theory (enable fn-stmt-item-listp
                                               fn-cbor-valuep
                                               fn-cbor-valuep-bounded
                                               fn-hsig-exact-octets-p
                                               fn-hsig-keyset-p
                                               fn-hsig-signatures-p
                                               fn-hc-versionp
                                               fn-hc-items-at)))))
  (let ((items (fn-hc-items-at version principal keys signatures)))
    (if items
        (let ((octets (fn-stmt-encode-items items)))
          (if (fn-cbor-at-mostp octets *fn-hc-max-binary-octets*)
              octets nil))
      nil)))

(defun fn-hc-encode (principal keys signatures)
  (declare (xargs :guard t))
  (fn-hc-encode-at *fn-hc-version* principal keys signatures))

(defun fn-hc-items-value-at (version items)
  (declare (xargs :guard t))
  (if (and (fn-hc-versionp version)
           (true-listp items) (equal (len items) *fn-hc-item-count*)
           (fn-stmt-uint-item-p (nth 0 items))
           (equal (cdr (nth 0 items)) version)
           (fn-stmt-uint-item-p (nth 1 items))
           (equal (cdr (nth 1 items)) *fn-hc-suite*)
           (fn-stmt-bytes-item-p (nth 2 items))
           (fn-hsig-exact-octets-p (cdr (nth 2 items)) 32)
           (fn-stmt-uint-item-p (nth 3 items))
           (equal (cdr (nth 3 items)) *fn-hsig-ed25519-algorithm*)
           (fn-stmt-bytes-item-p (nth 4 items))
           (fn-hsig-exact-octets-p (cdr (nth 4 items))
                                    *fn-hsig-ed25519-public-key-octets*)
           (fn-stmt-uint-item-p (nth 5 items))
           (equal (cdr (nth 5 items)) *fn-hsig-ml-dsa-65-algorithm*)
           (fn-stmt-bytes-item-p (nth 6 items))
           (fn-hsig-exact-octets-p (cdr (nth 6 items))
                                    *fn-hsig-ml-dsa-65-public-key-octets*)
           (fn-stmt-bytes-item-p (nth 7 items))
           (fn-hsig-exact-octets-p (cdr (nth 7 items))
                                    *fn-hsig-ed25519-signature-octets*)
           (fn-stmt-bytes-item-p (nth 8 items))
           (fn-hsig-exact-octets-p (cdr (nth 8 items))
                                    *fn-hsig-ml-dsa-65-signature-octets*))
      (list (cdr (nth 2 items))
            (list (cons :ed25519 (cdr (nth 4 items)))
                  (cons :ml-dsa-65 (cdr (nth 6 items))))
            (list (cons :ed25519 (cdr (nth 7 items)))
                  (cons :ml-dsa-65 (cdr (nth 8 items)))))
    nil))

(defun fn-hc-items-value (items)
  (declare (xargs :guard t))
  (fn-hc-items-value-at *fn-hc-version* items))

; A carrier whose version item is not VERSION is a :profile refusal.
(defun fn-hc-decode-at (version octets)
  (declare (xargs :guard t))
  (if (not (fn-cbor-at-mostp octets *fn-hc-max-binary-octets*))
      (fn-hc-error :binary-limit octets)
    (let ((decoded (fn-stmt-decode-items *fn-hc-item-count* octets)))
      (if (not (fn-stmt-okp decoded))
          (fn-hc-error :codec octets)
        (let ((value (fn-hc-items-value-at version (fn-stmt-value decoded))))
          (if value (fn-hc-ok value)
            (fn-hc-error :profile octets)))))))

(defun fn-hc-decode (octets)
  (declare (xargs :guard t))
  (fn-hc-decode-at *fn-hc-version* octets))

(defun fn-hc-field-encode-at (version principal keys signatures)
  (declare (xargs :guard t))
  (let ((binary (fn-hc-encode-at version principal keys signatures)))
    (if (not binary) nil
      (let ((field (fn-stx-b64-encode binary)))
        (if (fn-cbor-at-mostp field *fn-hc-max-field-octets*)
            field nil)))))

(defun fn-hc-field-encode (principal keys signatures)
  (declare (xargs :guard t))
  (fn-hc-field-encode-at *fn-hc-version* principal keys signatures))

(defun fn-hc-field-decode-at (version value)
  (declare (xargs :guard t))
  (if (not (fn-cbor-at-mostp value *fn-hc-max-field-octets*))
      (fn-hc-error :field-limit value)
    (let ((decoded (fn-stx-b64-decode-exact (fn-stx-strip-wsp value))))
      (if (not (fn-stx-okp decoded))
          (fn-hc-error :base64 value)
        (fn-hc-decode-at version (fn-stx-val decoded))))))

(defun fn-hc-field-decode (value)
  (declare (xargs :guard t))
  (fn-hc-field-decode-at *fn-hc-version* value))

(defun fn-hc-reserved-namep (name)
  (declare (xargs :guard t))
  (or (equal name *fn-hc-name*)
      (equal name *fn-hc-path-name*)
      (equal name *fn-hc-xref-name*)
      (equal name *fn-hc-injection-date-name*)
      (equal name *fn-hc-injection-info-name*)
      (equal name *fn-hc-statement-name*)
      (equal name *fn-hc-policy-name*)))

(defun fn-hc-fields-nativep (fields)
  (declare (xargs :guard t))
  (if (consp fields)
      (and (true-listp (car fields))
           (not (fn-hc-reserved-namep (fn-article-field-name (car fields))))
           (fn-hc-fields-nativep (cdr fields)))
    (null fields)))

; Portable native v1 is already an injected article: all required identity and
; presentation fields, including Date, are signed source.  This carrier
; requires Date presence and never inserts or normalizes it after signing;
; complete Date syntax validation is an article-boundary obligation.
(defun fn-hc-required-sourcep (article)
  (declare (xargs :guard t))
  (and (fn-article-syntax-p article)
       (fn-inj-single-fieldp article *fn-inj-from-name*)
       (fn-inj-single-fieldp article *fn-inj-subject-name*)
       (fn-inj-single-fieldp article *fn-inj-date-name*)
       (equal (fn-af-status-kind (fn-af-message-id-status article)) :single)
       (equal (fn-af-status-kind (fn-af-newsgroups-status article)) :single)))

; The next lane consumes this plan.  No host or durable record changes here.
; (:ok (source field-value)) or (:unverified reason original-source).
(defun fn-hc-native-plan (source principal keys signatures)
  (declare (xargs :guard t))
  (let ((parsed (fn-article-parse source)))
    (if (not (and (fn-article-result-okp parsed)
                  (true-listp parsed)))
        (fn-hc-error :article source)
      (let ((article (fn-article-result-article parsed)))
        (if (not (fn-hc-required-sourcep article))
            (fn-hc-error :source-profile source)
          (if (not (fn-hc-fields-nativep (fn-article-fields article)))
            (fn-hc-error :reserved-field source)
          (let ((field (fn-hc-field-encode-at (fn-hsig-source-version source)
                                              principal keys signatures)))
            (if (or (null field)
                    (< *fn-hc-max-field-octets* (len field)))
                (fn-hc-error :carrier source)
              (fn-hc-ok (list source field))))))))))

; Projection over a successfully parsed received article.  It removes only
; the generated/mutable profile fields.  Callers must first establish exactly
; one valid FN-Authorship field; malformed/ambiguous input is retained by the
; plan below and never passed here as an inferred authored source.
(defun fn-hc-source-header (fields)
  (declare (xargs :guard t))
  (if (consp fields)
      (if (or (not (true-listp (car fields)))
              (fn-hc-reserved-namep (fn-article-field-name (car fields))))
          (fn-hc-source-header (cdr fields))
        (append (fn-stx-field-octets (fn-article-field-raw-lines (car fields)))
                (fn-hc-source-header (cdr fields))))
    nil))

(defun fn-hc-authored-source (article)
  (declare (xargs :guard t))
  (if (not (true-listp article)) nil
    (append (fn-hc-source-header (fn-article-fields article))
            '(13 10)
            (if (true-listp (fn-article-body article))
                (fn-article-body article) nil))))

(defun fn-hc-count-name (name fields)
  (declare (xargs :guard t))
  (if (consp fields)
      (+ (if (and (true-listp (car fields))
                  (equal name (fn-article-field-name (car fields)))) 1 0)
         (fn-hc-count-name name (cdr fields)))
    0))

(defun fn-hc-no-other-reservedp (fields)
  (declare (xargs :guard t))
  (if (consp fields)
      (and (true-listp (car fields))
           (or (equal (fn-article-field-name (car fields)) *fn-hc-name*)
               (equal (fn-article-field-name (car fields)) *fn-hc-path-name*)
               (equal (fn-article-field-name (car fields)) *fn-hc-xref-name*)
               (equal (fn-article-field-name (car fields)) *fn-hc-injection-date-name*)
               (equal (fn-article-field-name (car fields)) *fn-hc-injection-info-name*)
               (not (fn-hc-reserved-namep
                     (fn-article-field-name (car fields)))))
           (fn-hc-no-other-reservedp (cdr fields)))
    (null fields)))

(defun fn-hc-find-name (name fields)
  (declare (xargs :guard t))
  (if (consp fields)
      (if (and (true-listp (car fields))
               (equal name (fn-article-field-name (car fields))))
          (car fields)
        (fn-hc-find-name name (cdr fields)))
    nil))

; (:ok (authored-source carrier-value)) only for one valid carrier.  Every
; refusal echoes ORIGINAL as its third element, making preservation explicit.
(defun fn-hc-received-plan (original)
  (declare (xargs :guard t))
  (let ((parsed (fn-article-parse original)))
    (if (not (and (fn-article-result-okp parsed)
                  (true-listp parsed)))
        (fn-hc-error :article original)
      (let* ((article (fn-article-result-article parsed))
             (fields (if (true-listp article)
                         (fn-article-fields article) nil))
             (source (fn-hc-authored-source article)))
        (if (not (and (true-listp article)
                      (equal (fn-hc-count-name *fn-hc-name* fields) 1)
                      (fn-hc-no-other-reservedp fields)))
            (fn-hc-error :carrier-count original)
          (let ((field (fn-hc-find-name *fn-hc-name* fields)))
            (if (not (true-listp field))
                (fn-hc-error :carrier original)
              (let ((carrier (fn-hc-field-decode-at
                              (fn-hsig-source-version source)
                              (fn-article-field-unfolded-value field))))
                (if (not (fn-hc-okp carrier))
                    (fn-hc-error :carrier original)
                  (let* ((source-parsed (fn-article-parse source)))
                    (if (not (and (fn-article-result-okp source-parsed)
                                  (true-listp source-parsed)
                                  (true-listp
                                   (fn-article-result-article source-parsed))
                                  (fn-hc-required-sourcep
                                   (fn-article-result-article source-parsed))
                                  (fn-hc-fields-nativep
                                   (fn-article-fields
                                    (fn-article-result-article source-parsed)))))
                        (fn-hc-error :source-profile original)
                      (fn-hc-ok (list source (fn-hc-value carrier))))))))))))))

(defun fn-hc-take (n xs)
  (declare (xargs :guard (natp n)))
  (if (or (zp n) (atom xs)) nil
    (cons (car xs) (fn-hc-take (1- n) (cdr xs)))))

(defun fn-hc-drop (n xs)
  (declare (xargs :guard (natp n)))
  (if (or (zp n) (atom xs)) xs
    (fn-hc-drop (1- n) (cdr xs))))

(defthm fn-hc-drop-shortens-nonempty-list
  (implies (and (posp n) (consp xs))
           (< (len (fn-hc-drop n xs)) (len xs)))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-hc-drop n xs)
           :in-theory (enable fn-hc-drop))))

(defun fn-hc-fold-rest (value)
  (declare (xargs :measure (len value) :guard t))
  (if (atom value) nil
    (append (list 9) (fn-hc-take 72 value) '(13 10)
            (fn-hc-fold-rest (fn-hc-drop 72 value)))))

(defun fn-hc-field-lines (value)
  (declare (xargs :guard t))
  (if (atom value) nil
    (append '(70 78 45 65 117 116 104 111 114 115 104 105 112 58 32)
            (fn-hc-take 72 value) '(13 10)
            (fn-hc-fold-rest (fn-hc-drop 72 value)))))

(defthm fn-hc-field-lines-is-true-list
  (true-listp (fn-hc-field-lines value))
  :hints (("Goal" :in-theory (enable fn-hc-field-lines))))

(defun fn-hc-render (source principal keys signatures)
  (declare (xargs :guard t
                  :guard-hints
                  (("Goal" :in-theory (disable fn-hc-native-plan
                                               fn-hc-field-lines)))))
  (let ((plan (fn-hc-native-plan source principal keys signatures)))
    (let ((value (fn-hc-value plan)))
      (if (and (fn-hc-okp plan) (consp value) (consp (cdr value)))
          (append (fn-hc-field-lines (cadr value)) source)
        nil))))

; Rendering can add more than seven thousand carrier octets to a source near
; the article limit.  Bound the complete received article before a caller
; writes it or offers it to the bounded received-article parser.
(defun fn-hc-render-at-most (max-octets source principal keys signatures)
  (declare (xargs :guard t))
  (let ((received (fn-hc-render source principal keys signatures)))
    (if (and (natp max-octets)
             (fn-cbor-octet-listp received)
             (consp received)
             (fn-cbor-at-mostp received max-octets)) received nil)))

(defthm fn-hc-render-at-most-emitted-bound-by-definition
  (implies (fn-hc-render-at-most max-octets source principal keys signatures)
           (fn-cbor-at-mostp
            (fn-hc-render-at-most max-octets source principal keys signatures)
            max-octets))
  :hints (("Goal" :in-theory
           (e/d (fn-hc-render-at-most)
                (fn-hc-render fn-cbor-at-mostp fn-cbor-octet-listp)))))

(defthm fn-hc-error-preserves-original
  (equal (nth 2 (fn-hc-error reason original)) original))

(defthm fn-hc-native-plan-preserves-source
  (implies (fn-hc-okp (fn-hc-native-plan source principal keys signatures))
           (equal (car (fn-hc-value
                        (fn-hc-native-plan source principal keys signatures)))
                  source))
  :hints (("Goal" :in-theory
           (e/d (fn-hc-native-plan fn-hc-ok fn-hc-error
                                  fn-hc-okp fn-hc-value)
                (fn-article-parse fn-hc-required-sourcep
                 fn-hc-fields-nativep fn-hc-field-encode-at
                 fn-hsig-source-version fn-cbor-at-mostp)))))

(defthm fn-hc-binary-limit-refuses-by-definition
  (implies (not (fn-cbor-at-mostp octets *fn-hc-max-binary-octets*))
           (equal (fn-hc-decode octets)
                  (fn-hc-error :binary-limit octets)))
  :hints (("Goal" :in-theory (enable fn-hc-decode fn-hc-decode-at))))

(defthm fn-hc-encode-is-bounded-when-emitted
  (implies (fn-hc-encode principal keys signatures)
           (fn-cbor-at-mostp (fn-hc-encode principal keys signatures)
                             *fn-hc-max-binary-octets*))
  :hints (("Goal" :in-theory (enable fn-hc-encode fn-hc-encode-at))))

(defthm fn-hc-encode-at-is-bounded-when-emitted
  (implies (fn-hc-encode-at version principal keys signatures)
           (fn-cbor-at-mostp (fn-hc-encode-at version principal keys signatures)
                             *fn-hc-max-binary-octets*))
  :hints (("Goal" :in-theory (enable fn-hc-encode-at))))

(defthm fn-hc-field-encode-is-bounded-when-emitted
  (implies (fn-hc-field-encode principal keys signatures)
           (fn-cbor-at-mostp
            (fn-hc-field-encode principal keys signatures)
            *fn-hc-max-field-octets*))
  :hints (("Goal" :in-theory (enable fn-hc-field-encode fn-hc-field-encode-at))))

(defthm fn-hc-field-encode-at-is-bounded-when-emitted
  (implies (fn-hc-field-encode-at version principal keys signatures)
           (fn-cbor-at-mostp
            (fn-hc-field-encode-at version principal keys signatures)
            *fn-hc-max-field-octets*))
  :hints (("Goal" :in-theory (enable fn-hc-field-encode-at))))

(defthm fn-hc-field-limit-refuses-by-definition
  (implies (not (fn-cbor-at-mostp value *fn-hc-max-field-octets*))
           (equal (fn-hc-field-decode value)
                  (fn-hc-error :field-limit value)))
  :hints (("Goal" :in-theory (enable fn-hc-field-decode fn-hc-field-decode-at))))

;; The emitted binary is the item encoding of `fn-hc-items-at', whose nine
;; items are well formed and whose encoding fits the one-item decoder.
(local
 (defthm fn-hci-at-mostp-len
   (implies (and (fn-cbor-at-mostp xs n) (natp n))
            (<= (len xs) n))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable fn-cbor-at-mostp)))))

(local
 (defthm fn-hci-items-at-shape
   (implies (fn-hc-items-at version principal keys signatures)
            (and (fn-stmt-item-listp
                  (fn-hc-items-at version principal keys signatures))
                 (equal (len (fn-hc-items-at version principal keys signatures))
                        *fn-hc-item-count*)))
   :hints (("Goal" :in-theory (enable fn-hc-items-at fn-hc-versionp
                                      fn-hsig-exact-octets-p fn-hsig-keyset-p
                                      fn-hsig-signatures-p fn-stmt-item-listp
                                      fn-cbor-valuep fn-cbor-valuep-bounded)))))

(local
 (defthm fn-hci-decode-items-of-encode-at
   (implies (fn-hc-encode-at version principal keys signatures)
            (equal (fn-stmt-decode-items
                    *fn-hc-item-count*
                    (fn-hc-encode-at version principal keys signatures))
                   (fn-stmt-ok (fn-hc-items-at version principal keys
                                               signatures))))
   :hints (("Goal"
            :use ((:instance fn-stmt-decode-items-of-encode-items
                             (fuel *fn-hc-item-count*)
                             (items (fn-hc-items-at version principal keys
                                                    signatures)))
                  (:instance fn-hci-at-mostp-len
                             (xs (fn-stmt-encode-items
                                  (fn-hc-items-at version principal keys
                                                  signatures)))
                             (n *fn-hc-max-binary-octets*)))
            :in-theory (e/d (fn-hc-encode-at)
                            (fn-stmt-decode-items-of-encode-items
                             fn-hci-at-mostp-len fn-stmt-decode-items
                             fn-hc-items-at fn-cbor-at-mostp))))))

(local
 (defthm fn-hci-two-tagged-pairs
   (implies (and (true-listp x) (equal (len x) 2)
                 (equal (car (car x)) a) a
                 (equal (car (cadr x)) b) b)
            (equal (list (cons a (cdr (car x))) (cons b (cdr (cadr x))))
                   x))
   :hints (("Goal" :expand ((len x) (len (cdr x)) (len (cddr x)))))))

(local
 (defthm fn-hci-encode-at-has-items
   (implies (fn-hc-encode-at version principal keys signatures)
            (fn-hc-items-at version principal keys signatures))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-hc-encode-at) (fn-hc-items-at))))))

; Round trip at either version: an emitted carrier decodes, at the version
; it was emitted under, to exactly the principal, key set and signatures.
(defthm fn-hc-decode-at-of-encode-at
  (implies (fn-hc-encode-at version principal keys signatures)
           (equal (fn-hc-decode-at version
                                   (fn-hc-encode-at version principal keys
                                                    signatures))
                  (fn-hc-ok (list principal keys signatures))))
  :hints (("Goal"
           :use ((:instance fn-hci-encode-at-has-items)
                 (:instance fn-hc-encode-at-is-bounded-when-emitted))
           :in-theory (e/d (fn-hc-decode-at fn-hc-items-at
                            fn-hc-items-value-at fn-hc-versionp
                            fn-hsig-exact-octets-p fn-hsig-keyset-p
                            fn-hsig-signatures-p
                            fn-stmt-ok fn-stmt-okp fn-stmt-value
                            fn-stmt-bytes-item-p fn-stmt-uint-item-p)
                           (fn-hc-encode-at fn-hc-encode-at-is-bounded-when-emitted
                            fn-stmt-decode-items fn-cbor-at-mostp)))))

; The version item binds: an emitted carrier never decodes at another
; version, so a v1 carrier is not a v2 carrier and a flipped item 1 refuses.
(defthm fn-hc-decode-at-refuses-another-version
  (implies (and (fn-hc-encode-at version principal keys signatures)
                (not (equal other version)))
           (not (fn-hc-okp (fn-hc-decode-at other
                                            (fn-hc-encode-at version principal
                                                             keys signatures)))))
  :hints (("Goal"
           :use ((:instance fn-hci-encode-at-has-items)
                 (:instance fn-hc-encode-at-is-bounded-when-emitted))
           :in-theory (e/d (fn-hc-decode-at fn-hc-items-at
                            fn-hc-items-value-at fn-hc-versionp
                            fn-stmt-ok fn-stmt-okp fn-stmt-value
                            fn-hc-okp fn-hc-error)
                           (fn-hc-encode-at fn-hc-encode-at-is-bounded-when-emitted
                            fn-stmt-decode-items fn-cbor-at-mostp)))))

(in-theory (disable (:d fn-hc-ok) (:d fn-hc-error) (:d fn-hc-okp)
                    (:d fn-hc-value) (:d fn-hc-items) (:d fn-hc-encode)
                    (:d fn-hc-items-value) (:d fn-hc-decode)
                    (:d fn-hc-field-encode) (:d fn-hc-field-decode)
                    (:d fn-hc-reserved-namep) (:d fn-hc-fields-nativep)
                    (:d fn-hc-required-sourcep)
                    (:d fn-hc-native-plan) (:d fn-hc-source-header)
                    (:d fn-hc-authored-source) (:d fn-hc-count-name)
                    (:d fn-hc-no-other-reservedp) (:d fn-hc-find-name)
                    (:d fn-hc-received-plan) (:d fn-hc-take) (:d fn-hc-drop)
                    (:d fn-hc-fold-rest) (:d fn-hc-field-lines)
                    (:d fn-hc-render) (:d fn-hc-render-at-most)
                    (:d fn-hc-versionp) (:d fn-hc-items-at)
                    (:d fn-hc-encode-at) (:d fn-hc-items-value-at)
                    (:d fn-hc-decode-at) (:d fn-hc-field-encode-at)
                    (:d fn-hc-field-decode-at)))

(deftheory fn-hybrid-carrier-vocabulary
  '(fn-hc-ok fn-hc-error fn-hc-okp fn-hc-value fn-hc-items fn-hc-encode
    fn-hc-items-value fn-hc-decode fn-hc-field-encode fn-hc-field-decode
    fn-hc-reserved-namep fn-hc-fields-nativep fn-hc-native-plan
    fn-hc-required-sourcep
    fn-hc-source-header fn-hc-authored-source fn-hc-count-name
    fn-hc-no-other-reservedp fn-hc-find-name fn-hc-received-plan
    fn-hc-take fn-hc-drop fn-hc-fold-rest fn-hc-field-lines fn-hc-render
    fn-hc-render-at-most fn-hc-versionp fn-hc-items-at fn-hc-encode-at
    fn-hc-items-value-at fn-hc-decode-at fn-hc-field-encode-at
    fn-hc-field-decode-at))
