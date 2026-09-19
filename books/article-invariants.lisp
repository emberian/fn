; Exact-source preservation for successful bounded article parsing.
; This is syntax-level preservation, not RFC-required-field validation.
(in-package "ACL2")
(include-book "article")

(defthm fn-article-append-associative
  (equal (append (append a b) c) (append a (append b c))))

(defthm fn-article-line-scan-partitions-input
  (implies (and (true-listp line-rev)
                (fn-article-line-okp
                 (fn-article-next-line-aux octets line-rev left)))
           (equal (append
                   (fn-article-line-value
                    (fn-article-next-line-aux octets line-rev left))
                   '(13 10)
                   (fn-article-line-rest
                    (fn-article-next-line-aux octets line-rev left)))
                  (append (rev line-rev) octets)))
  :hints (("Goal" :induct (fn-article-next-line-aux octets line-rev left))))

(defthm fn-article-line-scan-value-is-list
  (implies (and (true-listp line-rev)
                (fn-article-line-okp
                 (fn-article-next-line-aux octets line-rev left)))
           (true-listp
            (fn-article-line-value
             (fn-article-next-line-aux octets line-rev left))))
  :hints (("Goal" :induct (fn-article-next-line-aux octets line-rev left))))

(defthm fn-article-line-scan-rest-is-list
  (implies (and (true-listp octets)
                (fn-article-line-okp
                 (fn-article-next-line-aux octets line-rev left)))
           (true-listp
            (fn-article-line-rest
             (fn-article-next-line-aux octets line-rev left))))
  :hints (("Goal" :induct (fn-article-next-line-aux octets line-rev left))))

(defthm fn-article-next-line-partitions-input
  (implies (and (true-listp octets)
                (fn-article-line-okp (fn-article-next-line octets)))
           (equal (append (fn-article-line-value (fn-article-next-line octets))
                          '(13 10)
                          (fn-article-line-rest (fn-article-next-line octets)))
                  octets))
  :hints (("Goal" :use ((:instance fn-article-line-scan-partitions-input
                        (line-rev nil) (left *fn-article-max-line-octets*))))))

(defthm fn-article-next-line-value-is-list
  (implies (fn-article-line-okp (fn-article-next-line octets))
           (true-listp (fn-article-line-value (fn-article-next-line octets))))
  :hints (("Goal"
           :use ((:instance fn-article-line-scan-value-is-list
                  (line-rev nil) (left *fn-article-max-line-octets*)))
           :in-theory (disable fn-article-next-line-aux))))

(defthm fn-article-next-line-rest-is-list
  (implies (and (true-listp octets)
                (fn-article-line-okp (fn-article-next-line octets)))
           (true-listp (fn-article-line-rest (fn-article-next-line octets))))
  :hints (("Goal"
           :use ((:instance fn-article-line-scan-rest-is-list
                  (line-rev nil) (left *fn-article-max-line-octets*)))
           :in-theory (disable fn-article-next-line-aux))))

(defthm fn-article-extended-header-is-list
  (implies (true-listp header-rev)
           (true-listp (fn-article-header-rev-add-line header-rev line))))

(defthm fn-article-next-line-partition-normalized
  (implies (and (true-listp octets)
                (fn-article-line-okp (fn-article-next-line octets)))
           (equal (append (fn-article-line-value (fn-article-next-line octets))
                          (cons 13 (cons 10
                           (fn-article-line-rest (fn-article-next-line octets)))))
                  octets))
  :hints (("Goal" :use fn-article-next-line-partitions-input
           :in-theory (disable fn-article-next-line fn-article-line-value
                               fn-article-line-rest))))

(defthm fn-article-blank-line-partitions-input
  (implies (and (true-listp octets)
                (fn-article-line-okp (fn-article-next-line octets))
                (null (fn-article-line-value (fn-article-next-line octets))))
           (equal (cons 13 (cons 10
                    (fn-article-line-rest (fn-article-next-line octets))))
                  octets))
  :hints (("Goal" :use fn-article-next-line-partition-normalized
           :in-theory (disable fn-article-next-line fn-article-line-value
                               fn-article-line-rest))))

(defthm fn-article-parse-lines-preserves-source
  (implies (and (true-listp octets)
                (true-listp header-rev)
                (fn-article-result-okp
                 (fn-article-parse-lines octets lines-left header-bytes
                                         fields-rev current header-rev)))
           (equal
            (fn-article-source
             (fn-article-result-article
              (fn-article-parse-lines octets lines-left header-bytes
                                      fields-rev current header-rev)))
            (append (rev header-rev) octets)))
  :hints (("Goal"
           :induct (fn-article-parse-lines octets lines-left header-bytes
                                           fields-rev current header-rev)
           :in-theory (disable fn-article-next-line fn-article-next-line-aux
                               fn-article-new-field fn-article-add-fold
                               fn-article-finish-fields fn-article-body-crlfp
                               fn-article-header-rev-add-line
                               fn-article-line-value fn-article-line-rest))))

(defthm fn-article-octets-are-proper-list
  (implies (fn-cbor-octet-listp octets) (true-listp octets)))

(defthm fn-article-successful-parse-preserves-source
  (implies (fn-article-result-okp (fn-article-parse octets))
           (equal (fn-article-source
                   (fn-article-result-article (fn-article-parse octets)))
                  octets))
  :hints (("Goal"
           :use ((:instance fn-article-parse-lines-preserves-source
                  (lines-left (1+ *fn-article-max-header-lines*))
                  (header-bytes 0) (fields-rev nil) (current nil) (header-rev nil)))
           :in-theory (disable fn-article-parse-lines fn-cbor-at-mostp))))

; -----------------------------------------------------------------------------
; Field correspondence for a successful parse.
;
; Exact-source preservation above covers `header` and `body`.  The `fields`
; view is what books/bp-ingress.lisp:131,204 and host/bp-ingress-host.lisp:45
; consume, through fn-af-message-id-status and fn-af-newsgroups-status, so it
; needs its own correspondence with the header octets:
;
;   * the raw lines of the fields, in field order, each followed by CRLF, are
;     exactly the header octets;
;   * each field's lower-name is the ASCII-lowercasing of the octets before the
;     first colon of its first raw line;
;   * each field's unfolded-value is the RFC 5322 2.2.3 unfolding of its raw
;     lines, with the field name and colon removed.
;
; RFC 5322 is not in this repository.  The unfolding rule transcribed here is
; Section 2.2.3's "unfolding is accomplished by simply removing any CRLF that
; is immediately followed by WSP", cited from memory; Section 3.5 is cited the
; same way in specs/article-parser.md for the header/body separator.
; fn-article-unfold-octets is an independent octet-level definition of that
; rule: it does not follow the parser's incremental construction, and the
; correspondence theorem below is what ties the two together.

; These are logical reference functions for the correspondence theorems, not
; executable kernel code: the ones that concatenate line lists are admitted
; with guards unverified, because `append` is applied to lists whose
; properness is a theorem rather than a guard.
(defun fn-article-crlf-freep (octets)
  (declare (xargs :guard t))
  (if (consp octets)
      (and (not (equal (car octets) 13))
           (not (equal (car octets) 10))
           (fn-article-crlf-freep (cdr octets)))
    t))

(defun fn-article-plain-linesp (lines)
  (declare (xargs :guard t))
  (if (consp lines)
      (and (true-listp (car lines))
           (fn-article-crlf-freep (car lines))
           (fn-article-plain-linesp (cdr lines)))
    t))

(defun fn-article-wsp-startsp (lines)
  (declare (xargs :guard t))
  (if (consp lines)
      (and (consp (car lines))
           (fn-article-wspp (car (car lines)))
           (fn-article-wsp-startsp (cdr lines)))
    t))

(defun fn-article-has-colonp (line)
  (declare (xargs :guard t))
  (if (consp line)
      (or (equal (car line) 58)
          (fn-article-has-colonp (cdr line)))
    nil))

(defun fn-article-name-before-colon (line)
  (declare (xargs :guard t))
  (if (consp line)
      (if (equal (car line) 58)
          nil
        (cons (car line) (fn-article-name-before-colon (cdr line))))
    nil))

(defun fn-article-value-after-colon (line)
  (declare (xargs :guard t))
  (if (consp line)
      (if (equal (car line) 58)
          (cdr line)
        (fn-article-value-after-colon (cdr line)))
    nil))

; RFC 5322 2.2.3: remove each CRLF immediately followed by WSP.
(defun fn-article-unfold-octets (octets)
  (declare (xargs :guard t :measure (acl2-count octets)))
  (if (consp octets)
      (if (and (equal (car octets) 13)
               (consp (cdr octets))
               (equal (car (cdr octets)) 10)
               (consp (cdr (cdr octets)))
               (fn-article-wspp (car (cdr (cdr octets)))))
          (fn-article-unfold-octets (cdr (cdr octets)))
        (cons (car octets) (fn-article-unfold-octets (cdr octets))))
    nil))

; The folded octets of one field: its physical lines joined by CRLF.
(defun fn-article-join-crlf (lines)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp lines)
      (if (consp (cdr lines))
          (append (car lines)
                  (cons 13 (cons 10 (fn-article-join-crlf (cdr lines)))))
        (car lines))
    nil))

(defun fn-article-concat-lines (lines)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp lines)
      (append (car lines) (fn-article-concat-lines (cdr lines)))
    nil))

; Each physical line followed by its CRLF: the header-section octets of a run
; of physical lines.
(defun fn-article-lines-octets (lines)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp lines)
      (append (car lines)
              (cons 13 (cons 10 (fn-article-lines-octets (cdr lines)))))
    nil))

(defun fn-article-fields-octets (fields)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp fields)
      (append (fn-article-lines-octets
               (fn-article-field-raw-lines (car fields)))
              (fn-article-fields-octets (cdr fields)))
    nil))

(defun fn-article-unfold-reference (lines)
  (declare (xargs :guard t :verify-guards nil))
  (fn-article-value-after-colon
   (fn-article-unfold-octets (fn-article-join-crlf lines))))

(defun fn-article-field-correspondsp (field)
  (declare (xargs :guard t :verify-guards nil))
  (and (consp (fn-article-field-raw-lines field))
       (fn-article-plain-linesp (fn-article-field-raw-lines field))
       (fn-article-wsp-startsp (cdr (fn-article-field-raw-lines field)))
       (fn-article-has-colonp (car (fn-article-field-raw-lines field)))
       (equal (fn-article-field-name field)
              (fn-article-ascii-downcase
               (fn-article-name-before-colon
                (car (fn-article-field-raw-lines field)))))
       (equal (fn-article-field-unfolded-value field)
              (fn-article-unfold-reference
               (fn-article-field-raw-lines field)))))

(defun fn-article-fields-correspondp (fields)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp fields)
      (and (fn-article-field-correspondsp (car fields))
           (fn-article-fields-correspondp (cdr fields)))
    t))

; --- octet algebra ------------------------------------------------------------

(defthm fn-article-crlf-freep-append
  (equal (fn-article-crlf-freep (append left right))
         (and (fn-article-crlf-freep left)
              (fn-article-crlf-freep right)))
  :hints (("Goal" :induct (fn-article-crlf-freep left))))

(defthm fn-article-crlf-freep-rev
  (equal (fn-article-crlf-freep (rev x))
         (fn-article-crlf-freep x))
  :hints (("Goal" :induct (fn-article-crlf-freep x))))

(defthm fn-article-unfold-octets-crlf-free-prefix
  (implies (fn-article-crlf-freep left)
           (equal (fn-article-unfold-octets (append left right))
                  (append left (fn-article-unfold-octets right))))
  :hints (("Goal" :induct (fn-article-crlf-freep left))))

(defthm fn-article-unfold-octets-of-crlf-free
  (implies (and (fn-article-crlf-freep octets)
                (true-listp octets))
           (equal (fn-article-unfold-octets octets) octets))
  :hints (("Goal" :induct (fn-article-crlf-freep octets))))

(defthm fn-article-unfold-join-is-concat
  (implies (and (fn-article-plain-linesp lines)
                (fn-article-wsp-startsp (cdr lines)))
           (equal (fn-article-unfold-octets (fn-article-join-crlf lines))
                  (fn-article-concat-lines lines)))
  :hints (("Goal" :induct (fn-article-join-crlf lines)
           :in-theory (enable fn-article-join-crlf
                              fn-article-concat-lines
                              fn-article-plain-linesp
                              fn-article-wsp-startsp))))

(defthm fn-article-value-after-colon-append
  (implies (fn-article-has-colonp left)
           (equal (fn-article-value-after-colon (append left right))
                  (append (fn-article-value-after-colon left) right)))
  :hints (("Goal" :induct (fn-article-has-colonp left))))

(defthm fn-article-concat-lines-append-one
  (implies (true-listp line)
           (equal (fn-article-concat-lines (append lines (list line)))
                  (append (fn-article-concat-lines lines) line)))
  :hints (("Goal" :induct (fn-article-concat-lines lines))))

(defthm fn-article-plain-linesp-append-one
  (equal (fn-article-plain-linesp (append lines (list line)))
         (and (fn-article-plain-linesp lines)
              (true-listp line)
              (fn-article-crlf-freep line)))
  :hints (("Goal" :induct (fn-article-plain-linesp lines))))

(defthm fn-article-wsp-startsp-append-one
  (equal (fn-article-wsp-startsp (append lines (list line)))
         (and (fn-article-wsp-startsp lines)
              (consp line)
              (fn-article-wspp (car line))))
  :hints (("Goal" :induct (fn-article-wsp-startsp lines))))

(defthm fn-article-cdr-append-one
  (implies (consp lines)
           (equal (cdr (append lines (list line)))
                  (append (cdr lines) (list line)))))

(defthm fn-article-car-append-one
  (implies (consp lines)
           (equal (car (append lines (list line)))
                  (car lines))))

(defthm fn-article-lines-octets-append-one
  (implies (true-listp line)
           (equal (fn-article-lines-octets (append lines (list line)))
                  (append (fn-article-lines-octets lines)
                          (append line (list 13 10)))))
  :hints (("Goal" :induct (fn-article-lines-octets lines))))

(defthm fn-article-fields-octets-append
  (equal (fn-article-fields-octets (append left right))
         (append (fn-article-fields-octets left)
                 (fn-article-fields-octets right)))
  :hints (("Goal" :induct (fn-article-fields-octets left))))

(defthm fn-article-fields-correspondp-append
  (equal (fn-article-fields-correspondp (append left right))
         (and (fn-article-fields-correspondp left)
              (fn-article-fields-correspondp right)))
  :hints (("Goal" :induct (fn-article-fields-correspondp left))))

(defthm fn-article-finish-fields-is-append
  (implies (true-listp fields-rev)
           (equal (fn-article-finish-fields fields-rev current)
                  (if current
                      (append (rev fields-rev) (list current))
                    (rev fields-rev))))
  :hints (("Goal" :in-theory (enable fn-article-finish-fields))))

; --- what the scanners guarantee about one physical line ----------------------

(defthm fn-article-line-scan-value-crlf-free
  (implies (and (true-listp line-rev)
                (fn-article-crlf-freep line-rev)
                (fn-article-line-okp
                 (fn-article-next-line-aux octets line-rev left)))
           (fn-article-crlf-freep
            (fn-article-line-value
             (fn-article-next-line-aux octets line-rev left))))
  :hints (("Goal" :induct (fn-article-next-line-aux octets line-rev left))))

(defthm fn-article-next-line-value-crlf-free
  (implies (fn-article-line-okp (fn-article-next-line octets))
           (fn-article-crlf-freep
            (fn-article-line-value (fn-article-next-line octets))))
  :hints (("Goal"
           :use ((:instance fn-article-line-scan-value-crlf-free
                  (line-rev nil) (left *fn-article-max-line-octets*)))
           :in-theory (e/d (fn-article-next-line)
                           (fn-article-next-line-aux)))))

(defthm fn-article-split-colon-ok-implies-has-colon
  (implies (fn-article-line-okp (fn-article-split-colon-aux line name-rev))
           (fn-article-has-colonp line))
  :hints (("Goal" :induct (fn-article-split-colon-aux line name-rev))))

(defthm fn-article-split-colon-value-is-name-before-colon
  (implies (and (true-listp name-rev)
                (fn-article-line-okp (fn-article-split-colon-aux line name-rev)))
           (equal (fn-article-line-value
                   (fn-article-split-colon-aux line name-rev))
                  (append (rev name-rev)
                          (fn-article-name-before-colon line))))
  :hints (("Goal" :induct (fn-article-split-colon-aux line name-rev))))

(defthm fn-article-split-colon-rest-is-value-after-colon
  (implies (fn-article-line-okp (fn-article-split-colon-aux line name-rev))
           (equal (fn-article-line-rest
                   (fn-article-split-colon-aux line name-rev))
                  (fn-article-value-after-colon line)))
  :hints (("Goal" :induct (fn-article-split-colon-aux line name-rev))))

(defthm fn-article-has-colonp-append
  (implies (fn-article-has-colonp left)
           (fn-article-has-colonp (append left right)))
  :hints (("Goal" :induct (fn-article-has-colonp left))))

(defthm fn-article-concat-lines-has-colon-head
  (implies (and (consp lines)
                (fn-article-has-colonp (car lines)))
           (fn-article-has-colonp (fn-article-concat-lines lines)))
  :hints (("Goal"
           :expand ((fn-article-concat-lines lines))
           :use ((:instance fn-article-has-colonp-append
                            (left (car lines))
                            (right (fn-article-concat-lines (cdr lines))))))))

; --- the two field constructors -----------------------------------------------

(defthm fn-article-new-field-corresponds
  (implies (and (true-listp line)
                (fn-article-crlf-freep line)
                (fn-article-line-okp (fn-article-new-field line)))
           (fn-article-field-correspondsp
            (fn-article-line-value (fn-article-new-field line))))
  :hints (("Goal"
           :use ((:instance fn-article-split-colon-value-is-name-before-colon
                            (name-rev nil))
                 (:instance fn-article-split-colon-rest-is-value-after-colon
                            (name-rev nil))
                 (:instance fn-article-split-colon-ok-implies-has-colon
                            (name-rev nil)))
           :in-theory (e/d (fn-article-new-field
                            fn-article-field-correspondsp
                            fn-article-unfold-reference
                            fn-article-join-crlf
                            fn-article-plain-linesp
                            fn-article-wsp-startsp
                            fn-article-make-field
                            fn-article-field-raw-lines
                            fn-article-field-name
                            fn-article-field-unfolded-value
                            fn-article-line-okp
                            fn-article-line-value
                            fn-article-line-rest)
                           (fn-article-split-colon-aux
                            fn-article-unfold-octets)))))

(defthm fn-article-add-fold-corresponds
  (implies (and (fn-article-field-correspondsp field)
                (true-listp line)
                (fn-article-crlf-freep line)
                (fn-article-fold-linep line))
           (fn-article-field-correspondsp (fn-article-add-fold field line)))
  :hints (("Goal"
           :use ((:instance fn-article-unfold-join-is-concat
                            (lines (fn-article-field-raw-lines field)))
                 (:instance fn-article-unfold-join-is-concat
                            (lines (append (fn-article-field-raw-lines field)
                                           (list line))))
                 (:instance fn-article-concat-lines-append-one
                            (lines (fn-article-field-raw-lines field)))
                 (:instance fn-article-value-after-colon-append
                            (left (fn-article-concat-lines
                                   (fn-article-field-raw-lines field)))
                            (right line)))
           :in-theory (e/d (fn-article-field-correspondsp
                            fn-article-unfold-reference
                            fn-article-add-fold
                            fn-article-fold-linep
                            fn-article-make-field
                            fn-article-field-raw-lines
                            fn-article-field-name
                            fn-article-field-unfolded-value)
                           (fn-article-unfold-octets
                            fn-article-join-crlf
                            fn-article-concat-lines
                            fn-article-unfold-join-is-concat
                            fn-article-concat-lines-append-one
                            fn-article-value-after-colon-append)))))

; Shape facts the parse induction needs while the two field constructors stay
; closed: a successful new field is a real field view whose raw lines are the
; one line it was built from, and a fold appends its line to the raw lines.
(defthm fn-article-new-field-value-is-not-nil
  (implies (fn-article-line-okp (fn-article-new-field line))
           (fn-article-line-value (fn-article-new-field line)))
  :hints (("Goal" :in-theory (enable fn-article-new-field
                                      fn-article-line-okp
                                      fn-article-line-value
                                      fn-article-make-field))))

(defthm fn-article-lines-octets-of-new-field
  (implies (fn-article-line-okp (fn-article-new-field line))
           (equal (fn-article-lines-octets
                   (car (fn-article-line-value (fn-article-new-field line))))
                  (append line '(13 10))))
  :hints (("Goal" :in-theory (enable fn-article-new-field
                                      fn-article-line-okp
                                      fn-article-line-value
                                      fn-article-make-field
                                      fn-article-lines-octets))))

(defthm fn-article-add-fold-raw-lines
  (equal (car (fn-article-add-fold field line))
         (append (car field) (list line)))
  :hints (("Goal" :in-theory (enable fn-article-add-fold
                                      fn-article-make-field
                                      fn-article-field-raw-lines))))

; --- the parse induction ------------------------------------------------------

(defthm fn-article-parse-lines-fields-correspond
  (implies (and (true-listp octets)
                (true-listp fields-rev)
                (fn-article-fields-correspondp
                 (fn-article-finish-fields fields-rev current))
                (fn-article-result-okp
                 (fn-article-parse-lines octets lines-left header-bytes
                                         fields-rev current header-rev)))
           (fn-article-fields-correspondp
            (fn-article-fields
             (fn-article-result-article
              (fn-article-parse-lines octets lines-left header-bytes
                                      fields-rev current header-rev)))))
  :hints (("Goal"
           :induct (fn-article-parse-lines octets lines-left header-bytes
                                           fields-rev current header-rev)
           :in-theory (e/d (fn-article-parse-lines
                            fn-article-ok
                            fn-article-make
                            fn-article-fields
                            fn-article-result-okp
                            fn-article-result-article)
                           (fn-article-next-line
                            fn-article-next-line-aux
                            fn-article-new-field
                            fn-article-add-fold
                            fn-article-finish-fields
                            fn-article-body-crlfp
                            fn-article-header-rev-add-line
                            fn-article-field-correspondsp
                            fn-article-line-value
                            fn-article-line-rest)))))

(defthm fn-article-parse-lines-fields-recompose-header
  (implies (and (true-listp octets)
                (true-listp fields-rev)
                (true-listp header-rev)
                (equal (fn-article-fields-octets
                        (fn-article-finish-fields fields-rev current))
                       (rev header-rev))
                (fn-article-result-okp
                 (fn-article-parse-lines octets lines-left header-bytes
                                         fields-rev current header-rev)))
           (equal (fn-article-fields-octets
                   (fn-article-fields
                    (fn-article-result-article
                     (fn-article-parse-lines octets lines-left header-bytes
                                             fields-rev current header-rev))))
                  (fn-article-header
                   (fn-article-result-article
                    (fn-article-parse-lines octets lines-left header-bytes
                                            fields-rev current header-rev)))))
  :hints (("Goal"
           :induct (fn-article-parse-lines octets lines-left header-bytes
                                           fields-rev current header-rev)
           :in-theory (e/d (fn-article-parse-lines
                            fn-article-ok
                            fn-article-make
                            fn-article-fields
                            fn-article-header
                            fn-article-header-rev-add-line
                            fn-article-result-okp
                            fn-article-result-article)
                           (fn-article-next-line
                            fn-article-next-line-aux
                            fn-article-new-field
                            fn-article-add-fold
                            fn-article-finish-fields
                            fn-article-body-crlfp
                            fn-article-field-correspondsp
                            fn-article-line-value
                            fn-article-line-rest)))))

; Every field of a successful parse is the field its raw lines say it is: the
; name is the lowercased octets before the first colon of the first raw line,
; and the unfolded value is the RFC 5322 2.2.3 unfolding of the raw lines with
; that name and colon removed.
(defthm fn-article-successful-parse-fields-correspond
  (implies (fn-article-result-okp (fn-article-parse octets))
           (fn-article-fields-correspondp
            (fn-article-fields
             (fn-article-result-article (fn-article-parse octets)))))
  :hints (("Goal"
           :use ((:instance fn-article-parse-lines-fields-correspond
                  (lines-left (1+ *fn-article-max-header-lines*))
                  (header-bytes 0) (fields-rev nil) (current nil)
                  (header-rev nil)))
           :in-theory (e/d (fn-article-parse)
                           (fn-article-parse-lines fn-cbor-at-mostp
                            fn-article-fields-correspondp)))))

; The retained raw lines of the fields, in field order and each with its CRLF,
; are exactly the preserved header octets.  With exact-source preservation this
; makes the fields view a partition of the received header, not a summary of it.
(defthm fn-article-successful-parse-fields-recompose-header
  (implies (fn-article-result-okp (fn-article-parse octets))
           (equal (fn-article-fields-octets
                   (fn-article-fields
                    (fn-article-result-article (fn-article-parse octets))))
                  (fn-article-header
                   (fn-article-result-article (fn-article-parse octets)))))
  :hints (("Goal"
           :use ((:instance fn-article-parse-lines-fields-recompose-header
                  (lines-left (1+ *fn-article-max-header-lines*))
                  (header-bytes 0) (fields-rev nil) (current nil)
                  (header-rev nil)))
           :in-theory (e/d (fn-article-parse)
                           (fn-article-parse-lines fn-cbor-at-mostp
                            fn-article-fields-octets)))))
