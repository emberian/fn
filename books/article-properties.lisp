; fn: recognizer and finite-output properties of successful article parsing.
;
; This book closes the parser's output-shape assurance debt.  Its theorems have
; no caller-provided well-formedness hypothesis: a successful fn-article-parse
; itself yields a syntax view with bounded components.  RFC-level required
; fields and semantics remain outside the bounded syntax parser.

(in-package "ACL2")
(include-book "article")
(include-book "article-invariants")

; -----------------------------------------------------------------------------
; Field construction preserves the article view recognizers.

(defthm fn-ap-header-bytes-append
  (implies (true-listp left)
           (equal (fn-article-header-bytes-p (append left right))
                  (and (fn-article-header-bytes-p left)
                       (fn-article-header-bytes-p right))))
  :hints (("Goal" :induct (fn-article-header-bytes-p left))))

(defthm fn-ap-header-bytes-are-proper-list
  (implies (fn-article-header-bytes-p bytes)
           (true-listp bytes))
  :hints (("Goal" :induct (fn-article-header-bytes-p bytes))))

; Line and final parse results use the same tagged success convention.  Keep
; that convention abstract during parse-lines induction so scanner theorems
; continue to match instead of degrading into CAR/CADR terms.
(defthm fn-ap-result-okp-is-line-okp
  (implies (fn-article-result-okp result)
           (fn-article-line-okp result))
  :hints (("Goal" :in-theory (enable fn-article-result-okp
                                      fn-article-line-okp)))
  :rule-classes :forward-chaining)

(defthm fn-ap-error-is-not-line-ok
  (not (fn-article-line-okp (fn-article-error code)))
  :hints (("Goal" :in-theory (enable fn-article-error
                                      fn-article-line-okp))))

(defthm fn-ap-article-ok-is-ok
  (fn-article-result-okp (fn-article-ok article))
  :hints (("Goal" :in-theory (enable fn-article-ok
                                      fn-article-result-okp))))

(defthm fn-ap-ascii-downcase-idempotent
  (equal (fn-article-ascii-downcase (fn-article-ascii-downcase bytes))
         (fn-article-ascii-downcase bytes))
  :hints (("Goal" :induct (fn-article-ascii-downcase bytes))))

(defthm fn-ap-ascii-downcase-preserves-ftext
  (implies (fn-article-ftext-listp bytes)
           (fn-article-ftext-listp (fn-article-ascii-downcase bytes)))
  :hints (("Goal" :induct (fn-article-ftext-listp bytes))))

(defthm fn-ap-ascii-downcase-preserves-consp
  (implies (consp bytes)
           (consp (fn-article-ascii-downcase bytes))))

(defthm fn-ap-add-fold-fieldp
  (implies (and (fn-article-fieldp field)
                (fn-article-fold-linep line))
           (fn-article-fieldp (fn-article-add-fold field line)))
  :hints (("Goal" :in-theory (enable fn-article-fieldp fn-article-add-fold
                                      fn-article-fold-linep))))

(defthm fn-ap-new-field-ok-fieldp
  (implies (fn-article-line-okp (fn-article-new-field line))
           (fn-article-fieldp
            (fn-article-line-value (fn-article-new-field line))))
  :hints (("Goal" :in-theory (enable fn-article-new-field
                                      fn-article-line-okp
                                      fn-article-line-value
                                      fn-article-fieldp))))

(defthm fn-ap-new-field-ok-value-consp
  (implies (fn-article-line-okp (fn-article-new-field line))
           (consp
            (fn-article-line-value (fn-article-new-field line))))
  :hints (("Goal"
           :use fn-ap-new-field-ok-fieldp
           :in-theory (enable fn-article-fieldp)))
  :rule-classes :forward-chaining)

(defthm fn-ap-field-list-append
  (implies (true-listp left)
           (equal (fn-article-field-listp (append left right))
                  (and (fn-article-field-listp left)
                       (fn-article-field-listp right))))
  :hints (("Goal" :induct (fn-article-field-listp left))))

(defthm fn-ap-field-list-reverse
  (implies (fn-article-field-listp fields)
           (fn-article-field-listp (rev fields)))
  :hints (("Goal" :induct (fn-article-field-listp fields)
           :in-theory (enable rev))))

(defthm fn-ap-finish-fields-field-listp
  (implies (and (fn-article-field-listp fields-rev)
                (or (null current) (fn-article-fieldp current)))
           (fn-article-field-listp
            (fn-article-finish-fields fields-rev current)))
  :hints (("Goal" :in-theory (enable fn-article-finish-fields
                                      fn-article-field-listp))))

(defthm fn-ap-parse-lines-fields-wellformed
  (implies
   (and (fn-article-field-listp fields-rev)
        (or (null current) (fn-article-fieldp current))
        (fn-article-result-okp
         (fn-article-parse-lines octets lines-left header-bytes fields-rev
                                 current header-rev)))
   (fn-article-field-listp
    (fn-article-fields
     (fn-article-result-article
      (fn-article-parse-lines octets lines-left header-bytes fields-rev
                              current header-rev)))))
  :hints
  (("Goal"
    :induct (fn-article-parse-lines octets lines-left header-bytes fields-rev
                                    current header-rev)
    :in-theory (disable fn-article-next-line fn-article-next-line-aux
                        fn-article-new-field fn-article-add-fold
                        fn-article-finish-fields fn-article-body-crlfp
                        fn-article-header-rev-add-line
                        fn-article-line-value fn-article-line-rest
                        fn-article-line-okp fn-article-result-okp))))

(defthm fn-article-successful-parse-is-parse-lines
  (implies (fn-article-result-okp (fn-article-parse octets))
           (equal (fn-article-parse octets)
                  (fn-article-parse-lines octets
                                          (1+ *fn-article-max-header-lines*)
                                          0 nil nil nil)))
  :hints (("Goal" :in-theory (enable fn-article-parse))))

(defthm fn-article-successful-parse-lines-okp
  (implies (fn-article-result-okp (fn-article-parse octets))
           (fn-article-result-okp
            (fn-article-parse-lines octets
                                    (1+ *fn-article-max-header-lines*)
                                    0 nil nil nil)))
  :hints (("Goal" :use fn-article-successful-parse-is-parse-lines)))

(defthm fn-article-successful-parse-fields-wellformed
  (implies (fn-article-result-okp (fn-article-parse octets))
           (fn-article-field-listp
            (fn-article-fields
             (fn-article-result-article (fn-article-parse octets)))))
  :hints
  (("Goal"
    :use (fn-article-successful-parse-is-parse-lines
          fn-article-successful-parse-lines-okp
          (:instance fn-ap-parse-lines-fields-wellformed
           (lines-left (1+ *fn-article-max-header-lines*))
           (header-bytes 0) (fields-rev nil) (current nil) (header-rev nil)))
    :in-theory (disable fn-article-parse fn-article-parse-lines))))

; -----------------------------------------------------------------------------
; The line scanner partitions an octet input.  Carrying this directly through
; parse-lines avoids an expensive reverse inference from source preservation.

(defthm fn-ap-octet-list-append
  (implies (true-listp left)
           (equal (fn-cbor-octet-listp (append left right))
                  (and (fn-cbor-octet-listp left)
                       (fn-cbor-octet-listp right))))
  :hints (("Goal" :induct (fn-cbor-octet-listp left))))

(defthm fn-ap-octet-list-reverse
  (implies (fn-cbor-octet-listp bytes)
           (fn-cbor-octet-listp (rev bytes)))
  :hints (("Goal" :induct (fn-cbor-octet-listp bytes)
           :in-theory (enable rev))))

(defthm fn-ap-next-line-aux-success-components-are-octets
  (implies (and (fn-cbor-octet-listp octets)
                (fn-cbor-octet-listp line-rev)
                (fn-article-line-okp
                 (fn-article-next-line-aux octets line-rev left)))
           (and (fn-cbor-octet-listp
                 (fn-article-line-value
                  (fn-article-next-line-aux octets line-rev left)))
                (fn-cbor-octet-listp
                 (fn-article-line-rest
                  (fn-article-next-line-aux octets line-rev left)))))
  :hints (("Goal" :induct (fn-article-next-line-aux octets line-rev left))))

(defthm fn-ap-next-line-success-components-are-octets
  (implies (and (fn-cbor-octet-listp octets)
                (fn-article-line-okp (fn-article-next-line octets)))
           (and (fn-cbor-octet-listp
                 (fn-article-line-value (fn-article-next-line octets)))
                (fn-cbor-octet-listp
                 (fn-article-line-rest (fn-article-next-line octets)))))
  :hints (("Goal"
           :use ((:instance fn-ap-next-line-aux-success-components-are-octets
                  (line-rev nil) (left *fn-article-max-line-octets*)))
           :in-theory (e/d (fn-article-next-line)
                           (fn-article-next-line-aux))))
  :rule-classes :forward-chaining)

(defthm fn-ap-header-rev-add-line-octets
  (implies (and (fn-cbor-octet-listp header-rev)
                (fn-cbor-octet-listp line))
           (fn-cbor-octet-listp
            (fn-article-header-rev-add-line header-rev line)))
  :hints (("Goal" :in-theory (enable fn-article-header-rev-add-line)))
  :rule-classes :forward-chaining)

(defthm fn-article-successful-parse-input-octets
  (implies (fn-article-result-okp (fn-article-parse octets))
           (fn-cbor-octet-listp octets))
  :hints (("Goal" :in-theory (enable fn-article-parse))))

(defthm fn-ap-parse-lines-components-are-octets
  (implies
   (and (fn-cbor-octet-listp octets)
        (fn-cbor-octet-listp header-rev)
        (fn-article-result-okp
         (fn-article-parse-lines octets lines-left header-bytes fields-rev
                                 current header-rev)))
   (and
    (fn-cbor-octet-listp
     (fn-article-header
      (fn-article-result-article
       (fn-article-parse-lines octets lines-left header-bytes fields-rev
                               current header-rev))))
    (fn-cbor-octet-listp
     (fn-article-body
      (fn-article-result-article
       (fn-article-parse-lines octets lines-left header-bytes fields-rev
                               current header-rev))))))
  :hints
  (("Goal"
    :induct (fn-article-parse-lines octets lines-left header-bytes fields-rev
                                    current header-rev)
    :in-theory (disable fn-article-next-line fn-article-next-line-aux
                        fn-article-new-field fn-article-add-fold
                        fn-article-finish-fields fn-article-body-crlfp
                        fn-article-header-rev-add-line
                        fn-article-line-value fn-article-line-rest
                        fn-article-line-okp fn-article-result-okp))))

(defthm fn-article-successful-parse-components-are-octets
  (implies (fn-article-result-okp (fn-article-parse octets))
           (and
            (fn-cbor-octet-listp
             (fn-article-header
              (fn-article-result-article (fn-article-parse octets))))
            (fn-cbor-octet-listp
             (fn-article-body
              (fn-article-result-article (fn-article-parse octets))))))
  :hints
  (("Goal"
    :use (fn-article-successful-parse-is-parse-lines
          fn-article-successful-parse-lines-okp
          (:instance fn-ap-parse-lines-components-are-octets
           (lines-left (1+ *fn-article-max-header-lines*))
           (header-bytes 0) (fields-rev nil) (current nil) (header-rev nil))))))

(defthm fn-ap-parse-lines-article-shape
  (implies
   (fn-article-result-okp
    (fn-article-parse-lines octets lines-left header-bytes fields-rev
                            current header-rev))
   (and
    (true-listp
     (fn-article-result-article
      (fn-article-parse-lines octets lines-left header-bytes fields-rev
                              current header-rev)))
    (equal
     (len
      (fn-article-result-article
       (fn-article-parse-lines octets lines-left header-bytes fields-rev
                               current header-rev)))
     3)))
  :hints
  (("Goal"
    :induct (fn-article-parse-lines octets lines-left header-bytes fields-rev
                                    current header-rev)
    :in-theory (disable fn-article-next-line fn-article-next-line-aux
                        fn-article-new-field fn-article-add-fold
                        fn-article-finish-fields fn-article-body-crlfp
                        fn-article-header-rev-add-line
                        fn-article-line-value fn-article-line-rest
                        fn-article-line-okp fn-article-result-okp))))

(defthm fn-article-successful-parse-article-shape
  (implies
   (fn-article-result-okp (fn-article-parse octets))
   (and
    (true-listp
     (fn-article-result-article (fn-article-parse octets)))
    (equal (len (fn-article-result-article (fn-article-parse octets))) 3)))
  :hints
  (("Goal"
    :use (fn-article-successful-parse-is-parse-lines
          fn-article-successful-parse-lines-okp
          (:instance fn-ap-parse-lines-article-shape
           (lines-left (1+ *fn-article-max-header-lines*))
           (header-bytes 0) (fields-rev nil) (current nil) (header-rev nil)))
    :in-theory (disable fn-article-parse fn-article-parse-lines))))

(defthm fn-article-successful-parse-syntax-p
  (implies (fn-article-result-okp (fn-article-parse octets))
           (fn-article-syntax-p
            (fn-article-result-article (fn-article-parse octets))))
  :hints
  (("Goal"
    :use (fn-article-successful-parse-article-shape
           fn-article-successful-parse-fields-wellformed
           fn-article-successful-parse-components-are-octets)
    :in-theory (enable fn-article-syntax-p))))

; -----------------------------------------------------------------------------
; Numeric component bounds established by successful parsing.

(defthm fn-ap-at-most-is-length-bound
  (implies (natp bound)
           (equal (fn-cbor-at-mostp xs bound)
                  (<= (len xs) bound)))
  :hints (("Goal" :induct (fn-cbor-at-mostp xs bound))))

(defthm fn-article-successful-parse-input-bound
  (implies (fn-article-result-okp (fn-article-parse octets))
           (<= (len octets) *fn-article-max-octets*))
  :hints (("Goal" :in-theory (enable fn-article-parse)))
  :rule-classes :linear)

(defthm fn-article-successful-parse-source-bound
  (implies
   (fn-article-result-okp (fn-article-parse octets))
   (<= (len (fn-article-source
             (fn-article-result-article (fn-article-parse octets))))
       *fn-article-max-octets*))
  :hints (("Goal"
           :use (fn-article-successful-parse-preserves-source
                 fn-article-successful-parse-input-bound)))
  :rule-classes :linear)

(defthm fn-ap-length-append
  (equal (len (append left right))
         (+ (len left) (len right)))
  :hints (("Goal" :induct (len left))))

(defthm fn-ap-header-rev-add-line-length
  (implies (and (true-listp header-rev)
                (true-listp line))
           (equal (len (fn-article-header-rev-add-line header-rev line))
                  (+ 2 (len line) (len header-rev))))
  :hints (("Goal"
           :use ((:instance len-of-rev (x line)))
           :in-theory (enable fn-article-header-rev-add-line))))

(defthm fn-ap-parse-lines-header-bound
  (implies
   (and (natp header-bytes)
        (true-listp header-rev)
        (equal (len header-rev) header-bytes)
        (<= header-bytes *fn-article-max-header-octets*)
        (fn-article-result-okp
         (fn-article-parse-lines octets lines-left header-bytes fields-rev
                                 current header-rev)))
   (<=
    (len
     (fn-article-header
      (fn-article-result-article
       (fn-article-parse-lines octets lines-left header-bytes fields-rev
                               current header-rev))))
    *fn-article-max-header-octets*))
  :hints
  (("Goal"
    :induct (fn-article-parse-lines octets lines-left header-bytes fields-rev
                                    current header-rev)
    :in-theory (disable fn-article-next-line fn-article-next-line-aux
                        fn-article-new-field fn-article-add-fold
                        fn-article-finish-fields fn-article-body-crlfp
                        fn-article-header-rev-add-line
                        fn-article-line-value fn-article-line-rest
                        fn-article-line-okp fn-article-result-okp))))

(defthm fn-article-successful-parse-header-bound
  (implies
   (fn-article-result-okp (fn-article-parse octets))
   (<=
    (len
     (fn-article-header
      (fn-article-result-article (fn-article-parse octets))))
    *fn-article-max-header-octets*))
  :hints
  (("Goal"
    :use (fn-article-successful-parse-is-parse-lines
          fn-article-successful-parse-lines-okp
          (:instance fn-ap-parse-lines-header-bound
           (lines-left (1+ *fn-article-max-header-lines*))
           (header-bytes 0) (fields-rev nil) (current nil) (header-rev nil)))
    :in-theory (disable fn-article-parse fn-article-parse-lines)))
  :rule-classes :linear)

(defthm fn-ap-body-no-longer-than-source
  (<= (len (fn-article-body article))
      (len (fn-article-source article)))
  :hints (("Goal" :in-theory (enable fn-article-source)))
  :rule-classes :linear)

(defthm fn-article-successful-parse-body-bound
  (implies
   (fn-article-result-okp (fn-article-parse octets))
   (<=
    (len
     (fn-article-body
      (fn-article-result-article (fn-article-parse octets))))
    *fn-article-max-octets*))
  :hints (("Goal"
           :use (fn-article-successful-parse-source-bound
                 (:instance fn-ap-body-no-longer-than-source
                  (article
                   (fn-article-result-article
                    (fn-article-parse octets)))))))
  :rule-classes :linear)

(defthm fn-ap-finish-fields-length
  (equal (len (fn-article-finish-fields fields-rev current))
         (+ (len fields-rev) (if current 1 0)))
  :hints (("Goal" :in-theory (enable fn-article-finish-fields))))

(defthm fn-ap-parse-lines-field-count-bound
  (implies
   (and (true-listp fields-rev)
        (or current (null fields-rev))
        (<= (+ (len fields-rev) (if current 1 0))
            *fn-article-max-fields*)
        (fn-article-result-okp
         (fn-article-parse-lines octets lines-left header-bytes fields-rev
                                 current header-rev)))
   (<=
    (len
     (fn-article-fields
      (fn-article-result-article
       (fn-article-parse-lines octets lines-left header-bytes fields-rev
                               current header-rev))))
    *fn-article-max-fields*))
  :hints
  (("Goal"
    :induct (fn-article-parse-lines octets lines-left header-bytes fields-rev
                                    current header-rev)
    :in-theory (disable fn-article-next-line fn-article-next-line-aux
                        fn-article-new-field fn-article-add-fold
                        fn-article-finish-fields fn-article-body-crlfp
                        fn-article-header-rev-add-line
                        fn-article-line-value fn-article-line-rest
                        fn-article-line-okp fn-article-result-okp))))

(defthm fn-article-successful-parse-field-count-bound
  (implies
   (fn-article-result-okp (fn-article-parse octets))
   (<=
    (len
     (fn-article-fields
      (fn-article-result-article (fn-article-parse octets))))
    *fn-article-max-fields*))
  :hints
  (("Goal"
    :use (fn-article-successful-parse-is-parse-lines
          fn-article-successful-parse-lines-okp
          (:instance fn-ap-parse-lines-field-count-bound
           (lines-left (1+ *fn-article-max-header-lines*))
           (header-bytes 0) (fields-rev nil) (current nil) (header-rev nil)))
    :in-theory (disable fn-article-parse fn-article-parse-lines)))
  :rule-classes :linear)

(defthm fn-article-successful-parse-component-bounds
  (implies
   (fn-article-result-okp (fn-article-parse octets))
   (let ((article
          (fn-article-result-article (fn-article-parse octets))))
     (and (<= (len (fn-article-source article))
              *fn-article-max-octets*)
          (<= (len (fn-article-header article))
              *fn-article-max-header-octets*)
          (<= (len (fn-article-body article))
              *fn-article-max-octets*)
          (<= (len (fn-article-fields article))
              *fn-article-max-fields*))))
  :hints
  (("Goal"
    :use (fn-article-successful-parse-source-bound
          fn-article-successful-parse-header-bound
          fn-article-successful-parse-body-bound
          fn-article-successful-parse-field-count-bound))))
