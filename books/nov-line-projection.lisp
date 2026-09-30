; Logical line projection for the productive legacy NOV byte cursor.
; This reference is not served code: the cursor refines it without retaining
; whole fields, rescanning the suffix, or materializing the output at a tick.
(in-package "ACL2")
(include-book "nov-fields")

(defun fn-nlp-first (fields name)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp fields)
      (if (fn-article-field-name-equalp (car fields) name)
          (list (fn-article-field-unfolded-value (car fields)))
        (fn-nlp-first (cdr fields) name)) nil))

(defun fn-nlp-columns (fields names)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp names)
      (cons (fn-nlp-first fields (car names))
            (fn-nlp-columns fields (cdr names))) nil))

(defun fn-nlp-add-field (columns field names)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp names)
      (cons (or (car columns)
                (and field (fn-article-field-name-equalp field (car names))
                     (list (fn-article-field-unfolded-value field))))
            (fn-nlp-add-field (cdr columns) field (cdr names))) nil))

(defun fn-nlp-normalize (columns)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp columns)
      (cons (fn-nov-scrub (fn-nov-value-content (car (car columns))))
            (fn-nlp-normalize (cdr columns))) nil))

(defun fn-nlp-result (parsed names)
  (declare (xargs :guard t :verify-guards nil))
  (if (fn-article-result-okp parsed)
      (list :ok (fn-nlp-normalize
                 (fn-nlp-columns
                  (fn-article-fields (fn-article-result-article parsed)) names)))
    parsed))

(defun fn-nlp-parse-lines (octets limits lines-left header-bytes nfields
                                columns current names)
  (declare (xargs :measure (nfix lines-left) :guard t :verify-guards nil))
  (if (zp lines-left)
      (fn-article-error :header-lines-limit)
    (let ((next (fn-article-next-line octets)))
      (if (not (fn-article-line-okp next)) next
        (let ((line (fn-article-line-value next))
              (rest (fn-article-line-rest next)))
          (if (null line)
              (if (or (not (fn-article-body-crlfp rest))
                      (not (fn-article-field-closedp current)))
                  (fn-article-error :invalid-header)
                (list :ok (fn-nlp-normalize (fn-nlp-add-field columns current names))))
            (if (< (fn-article-limit-octets limits) (+ header-bytes (len line) 2))
                (fn-article-error :header-octets-limit)
              (if (fn-article-wspp (car line))
                  (if (not current) (fn-article-error :invalid-header)
                    (if (not (fn-article-fold-linep line))
                        (fn-article-error :invalid-header)
                      (fn-nlp-parse-lines
                       rest limits (1- lines-left) (+ header-bytes (len line) 2)
                       nfields columns (fn-article-add-fold current line) names)))
                (let ((field-result (fn-article-new-field line)))
                  (if (not (fn-article-line-okp field-result)) field-result
                    (if (not (fn-article-field-closedp current))
                        (fn-article-error :invalid-header)
                      (if (<= (fn-article-limit-fields limits)
                              (+ (if current 1 0) (nfix nfields)))
                          (fn-article-error :header-fields-limit)
                        (fn-nlp-parse-lines
                         rest limits (1- lines-left) (+ header-bytes (len line) 2)
                         (if current (+ 1 (nfix nfields)) nfields)
                         (fn-nlp-add-field columns current names)
                         (fn-article-line-value field-result) names)))))))))))))

(local (defthm fn-nlp-first-append
  (equal (fn-nlp-first (append a b) name)
         (or (fn-nlp-first a name) (fn-nlp-first b name)))
  :hints (("Goal" :induct (fn-nlp-first a name)
           :in-theory (enable fn-nlp-first)))))

(local (defthm fn-nlp-columns-close
  (equal (fn-nlp-columns (append fields (if field (list field) nil)) names)
         (fn-nlp-add-field (fn-nlp-columns fields names) field names))
  :hints (("Goal" :induct (fn-nlp-columns fields names)
           :in-theory (enable fn-nlp-columns fn-nlp-add-field fn-nlp-first)))))

(local (defthm fn-nlp-columns-of-string
  (implies (stringp fields)
           (equal (fn-nlp-columns fields names) (fn-nlp-columns nil names)))
  :hints (("Goal" :induct (fn-nlp-columns fields names)
           :in-theory (enable fn-nlp-columns fn-nlp-first)))))
(local (defthm fn-nlp-columns-reverse-is-rev
  (equal (fn-nlp-columns (reverse fields) names)
         (fn-nlp-columns (rev fields) names))
  :hints (("Goal" :in-theory (e/d (reverse revappend rev) (fn-nlp-columns))))))
(local (defthm fn-nlp-columns-finish
  (equal (fn-nlp-columns (fn-article-finish-fields fields-rev current) names)
                  (fn-nlp-add-field (fn-nlp-columns (reverse fields-rev) names)
                                    current names))
  :hints (("Goal" :use ((:instance fn-nlp-columns-close (fields (rev fields-rev)) (field current))) :in-theory (e/d (fn-article-finish-fields reverse revappend) (fn-nlp-columns fn-nlp-add-field fn-nlp-columns-close))))))

(local (defthm fn-nlp-add-nil
  (equal (fn-nlp-add-field (fn-nlp-columns fields names) nil names)
         (fn-nlp-columns fields names))
  :hints (("Goal" :induct (fn-nlp-columns fields names)
           :in-theory (enable fn-nlp-add-field fn-nlp-columns)))))

(local (defthm fn-nlp-columns-reverse-cons
  (implies current
           (equal (fn-nlp-columns (reverse (cons current fields-rev)) names)
                  (fn-nlp-add-field (fn-nlp-columns (reverse fields-rev) names)
                                    current names)))
  :hints (("Goal" :use fn-nlp-columns-finish
           :in-theory (e/d (fn-article-finish-fields)
                            (fn-nlp-columns fn-nlp-add-field reverse reverse-removal))))))

(defthm fn-nlp-parse-lines-is-parser-projection
  (equal
            (fn-nlp-parse-lines octets limits lines-left header-bytes nfields
                                (fn-nlp-columns (reverse fields-rev) names) current names)
            (fn-nlp-result
             (fn-article-parse-lines octets limits lines-left header-bytes nfields
                                     fields-rev current header-rev) names))
  :rule-classes nil
  :hints (("Goal"
           :expand ((fn-nlp-parse-lines octets limits lines-left header-bytes nfields
                    (fn-nlp-columns (reverse fields-rev) names) current names))
           :induct (fn-article-parse-lines octets limits lines-left header-bytes nfields
                                           fields-rev current header-rev)
           :in-theory
           (e/d (fn-nlp-parse-lines fn-nlp-result fn-article-parse-lines
                 fn-article-result-okp fn-article-line-okp fn-article-result-article fn-article-fields
                 fn-article-ok fn-article-make fn-article-error)
                (fn-article-next-line fn-article-line-value
                 fn-article-line-rest fn-article-body-crlfp fn-article-field-closedp
                 fn-article-limit-octets fn-article-wspp fn-article-fold-linep
                 fn-article-add-fold fn-article-new-field fn-article-limit-fields
                 fn-article-header-rev-add-line fn-nlp-columns fn-nlp-normalize
                 fn-nlp-add-field fn-article-finish-fields reverse reverse-removal fn-nlp-columns-reverse-is-rev)))))

(defconst *fn-nlp-names*
  (list *fn-nov-subject-name* *fn-nov-from-name* *fn-nov-date-name*
        *fn-nov-message-id-name* *fn-nov-references-name*))

(defun fn-nlp-parse-under (octets limits names)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (fn-cbor-at-mostp octets *fn-article-max-octets*))
      (fn-article-error :limit)
    (if (not (fn-cbor-octet-listp octets))
        (fn-article-error :invalid-header)
      (fn-nlp-parse-lines octets limits (1+ (fn-article-limit-lines limits))
                          0 0 (fn-nlp-columns nil names) nil names))))

(defthm fn-nlp-parse-under-is-parser-projection
  (equal (fn-nlp-parse-under octets limits names)
         (fn-nlp-result (fn-article-parse-under octets limits) names))
  :hints (("Goal"
           :use ((:instance fn-nlp-parse-lines-is-parser-projection
                    (lines-left (1+ (fn-article-limit-lines limits)))
                    (header-bytes 0) (nfields 0) (fields-rev nil)
                    (current nil) (header-rev nil)))
           :in-theory (e/d (fn-nlp-parse-under fn-article-parse-under
                             fn-nlp-result fn-article-error fn-article-result-okp)
                            (fn-nlp-parse-lines fn-article-parse-lines
                             fn-nlp-columns fn-cbor-at-mostp fn-cbor-octet-listp)))))

(defun fn-nlp-parse (octets)
  (declare (xargs :guard t :verify-guards nil))
  (fn-nlp-parse-under octets *fn-article-ceiling-limits* *fn-nlp-names*))

(defthm fn-nlp-parse-is-parser-projection
  (equal (fn-nlp-parse octets)
         (fn-nlp-result (fn-article-parse octets) *fn-nlp-names*))
  :hints (("Goal" :in-theory (e/d (fn-nlp-parse fn-article-parse)
                                  (fn-nlp-parse-under fn-article-parse-under fn-nlp-result)))))

(local (defthm fn-nlp-first-is-header-lookup
  (equal (fn-nlp-first fields name)
         (let ((matches (fn-article-get-headers-aux fields name)))
           (if (consp matches)
               (list (fn-article-field-unfolded-value (car matches))) nil)))
  :hints (("Goal" :induct (fn-nlp-first fields name)
           :in-theory (enable fn-nlp-first fn-article-get-headers-aux)))))

(defthm fn-nlp-normalized-first-is-overview-content
  (equal (fn-nov-scrub
          (fn-nov-value-content (car (fn-nlp-first (fn-article-fields view) name))))
         (fn-nov-header-content view name))
  :hints (("Goal" :in-theory
           (e/d (fn-nov-header-content fn-article-get-headers)
                (fn-nlp-first fn-article-fields fn-article-get-headers-aux
                 fn-article-field-unfolded-value fn-nov-scrub fn-nov-value-content)))))

(defthm fn-nlp-five-columns-are-overview-content
  (equal (fn-nlp-normalize (fn-nlp-columns (fn-article-fields view) *fn-nlp-names*))
         (list (fn-nov-header-content view *fn-nov-subject-name*)
               (fn-nov-header-content view *fn-nov-from-name*)
               (fn-nov-header-content view *fn-nov-date-name*)
               (fn-nov-header-content view *fn-nov-message-id-name*)
               (fn-nov-header-content view *fn-nov-references-name*)))
  :hints (("Goal" :in-theory
           (e/d (fn-nlp-normalize fn-nlp-columns)
                (fn-nlp-first fn-nlp-first-is-header-lookup fn-article-fields fn-nov-header-content
                 fn-nov-scrub fn-nov-value-content)))))
