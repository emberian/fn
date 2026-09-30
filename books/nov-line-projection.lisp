; Logical line projection for the productive legacy NOV byte cursor.
; This reference is not served code: the cursor refines it without retaining
; whole fields, rescanning the suffix, or materializing the output at a tick.
(in-package "ACL2")
(include-book "nov-fields")

(defun fn-novlp-first (fields name)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp fields)
      (if (fn-article-field-name-equalp (car fields) name)
          (list (fn-article-field-unfolded-value (car fields)))
        (fn-novlp-first (cdr fields) name)) nil))

(defun fn-novlp-columns (fields names)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp names)
      (cons (fn-novlp-first fields (car names))
            (fn-novlp-columns fields (cdr names))) nil))

(defun fn-novlp-add-field (columns field names)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp names)
      (cons (or (car columns)
                (and field (fn-article-field-name-equalp field (car names))
                     (list (fn-article-field-unfolded-value field))))
            (fn-novlp-add-field (cdr columns) field (cdr names))) nil))

(defun fn-novlp-normalize (columns)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp columns)
      (cons (fn-nov-scrub (fn-nov-value-content (car (car columns))))
            (fn-novlp-normalize (cdr columns))) nil))

(defun fn-novlp-result (parsed names)
  (declare (xargs :guard t :verify-guards nil))
  (if (fn-article-result-okp parsed)
      (list :ok (fn-novlp-normalize
                 (fn-novlp-columns
                  (fn-article-fields (fn-article-result-article parsed)) names)))
    parsed))

(defun fn-novlp-parse-lines (octets limits lines-left header-bytes nfields
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
                (list :ok (fn-novlp-normalize (fn-novlp-add-field columns current names))))
            (if (< (fn-article-limit-octets limits) (+ header-bytes (len line) 2))
                (fn-article-error :header-octets-limit)
              (if (fn-article-wspp (car line))
                  (if (not current) (fn-article-error :invalid-header)
                    (if (not (fn-article-fold-linep line))
                        (fn-article-error :invalid-header)
                      (fn-novlp-parse-lines
                       rest limits (1- lines-left) (+ header-bytes (len line) 2)
                       nfields columns (fn-article-add-fold current line) names)))
                (let ((field-result (fn-article-new-field line)))
                  (if (not (fn-article-line-okp field-result)) field-result
                    (if (not (fn-article-field-closedp current))
                        (fn-article-error :invalid-header)
                      (if (<= (fn-article-limit-fields limits)
                              (+ (if current 1 0) (nfix nfields)))
                          (fn-article-error :header-fields-limit)
                        (fn-novlp-parse-lines
                         rest limits (1- lines-left) (+ header-bytes (len line) 2)
                         (if current (+ 1 (nfix nfields)) nfields)
                         (fn-novlp-add-field columns current names)
                         (fn-article-line-value field-result) names)))))))))))))

(local (defthm fn-novlp-first-append
  (equal (fn-novlp-first (append a b) name)
         (or (fn-novlp-first a name) (fn-novlp-first b name)))
  :hints (("Goal" :induct (fn-novlp-first a name)
           :in-theory (enable fn-novlp-first)))))

(local (defthm fn-novlp-columns-close
  (equal (fn-novlp-columns (append fields (if field (list field) nil)) names)
         (fn-novlp-add-field (fn-novlp-columns fields names) field names))
  :hints (("Goal" :induct (fn-novlp-columns fields names)
           :in-theory (enable fn-novlp-columns fn-novlp-add-field fn-novlp-first)))))

(local (defthm fn-novlp-columns-of-string
  (implies (stringp fields)
           (equal (fn-novlp-columns fields names) (fn-novlp-columns nil names)))
  :hints (("Goal" :induct (fn-novlp-columns fields names)
           :in-theory (enable fn-novlp-columns fn-novlp-first)))))
(local (defthm fn-novlp-columns-reverse-is-rev
  (equal (fn-novlp-columns (reverse fields) names)
         (fn-novlp-columns (rev fields) names))
  :hints (("Goal" :in-theory (e/d (reverse revappend rev) (fn-novlp-columns))))))
(local (defthm fn-novlp-columns-finish
  (equal (fn-novlp-columns (fn-article-finish-fields fields-rev current) names)
                  (fn-novlp-add-field (fn-novlp-columns (reverse fields-rev) names)
                                    current names))
  :hints (("Goal" :use ((:instance fn-novlp-columns-close (fields (rev fields-rev)) (field current))) :in-theory (e/d (fn-article-finish-fields reverse revappend) (fn-novlp-columns fn-novlp-add-field fn-novlp-columns-close))))))

(local (defthm fn-novlp-add-nil
  (equal (fn-novlp-add-field (fn-novlp-columns fields names) nil names)
         (fn-novlp-columns fields names))
  :hints (("Goal" :induct (fn-novlp-columns fields names)
           :in-theory (enable fn-novlp-add-field fn-novlp-columns)))))

(local (defthm fn-novlp-columns-reverse-cons
  (implies current
           (equal (fn-novlp-columns (reverse (cons current fields-rev)) names)
                  (fn-novlp-add-field (fn-novlp-columns (reverse fields-rev) names)
                                    current names)))
  :hints (("Goal" :use fn-novlp-columns-finish
           :in-theory (e/d (fn-article-finish-fields)
                            (fn-novlp-columns fn-novlp-add-field reverse reverse-removal))))))

(defthm fn-novlp-parse-lines-is-parser-projection
  (equal
            (fn-novlp-parse-lines octets limits lines-left header-bytes nfields
                                (fn-novlp-columns (reverse fields-rev) names) current names)
            (fn-novlp-result
             (fn-article-parse-lines octets limits lines-left header-bytes nfields
                                     fields-rev current header-rev) names))
  :rule-classes nil
  :hints (("Goal"
           :expand ((fn-novlp-parse-lines octets limits lines-left header-bytes nfields
                    (fn-novlp-columns (reverse fields-rev) names) current names))
           :induct (fn-article-parse-lines octets limits lines-left header-bytes nfields
                                           fields-rev current header-rev)
           :in-theory
           (e/d (fn-novlp-parse-lines fn-novlp-result fn-article-parse-lines
                 fn-article-result-okp fn-article-line-okp fn-article-result-article fn-article-fields
                 fn-article-ok fn-article-make fn-article-error)
                (fn-article-next-line fn-article-line-value
                 fn-article-line-rest fn-article-body-crlfp fn-article-field-closedp
                 fn-article-limit-octets fn-article-wspp fn-article-fold-linep
                 fn-article-add-fold fn-article-new-field fn-article-limit-fields
                 fn-article-header-rev-add-line fn-novlp-columns fn-novlp-normalize
                 fn-novlp-add-field fn-article-finish-fields reverse reverse-removal fn-novlp-columns-reverse-is-rev)))))

(defconst *fn-novlp-names*
  (list *fn-nov-subject-name* *fn-nov-from-name* *fn-nov-date-name*
        *fn-nov-message-id-name* *fn-nov-references-name*))

(defun fn-novlp-parse-under (octets limits names)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (fn-cbor-at-mostp octets *fn-article-max-octets*))
      (fn-article-error :limit)
    (if (not (fn-cbor-octet-listp octets))
        (fn-article-error :invalid-header)
      (fn-novlp-parse-lines octets limits (1+ (fn-article-limit-lines limits))
                          0 0 (fn-novlp-columns nil names) nil names))))

(defthm fn-novlp-parse-under-is-parser-projection
  (equal (fn-novlp-parse-under octets limits names)
         (fn-novlp-result (fn-article-parse-under octets limits) names))
  :hints (("Goal"
           :use ((:instance fn-novlp-parse-lines-is-parser-projection
                    (lines-left (1+ (fn-article-limit-lines limits)))
                    (header-bytes 0) (nfields 0) (fields-rev nil)
                    (current nil) (header-rev nil)))
           :in-theory (e/d (fn-novlp-parse-under fn-article-parse-under
                             fn-novlp-result fn-article-error fn-article-result-okp)
                            (fn-novlp-parse-lines fn-article-parse-lines
                             fn-novlp-columns fn-cbor-at-mostp fn-cbor-octet-listp)))))

(defun fn-novlp-parse (octets)
  (declare (xargs :guard t :verify-guards nil))
  (fn-novlp-parse-under octets *fn-article-ceiling-limits* *fn-novlp-names*))

(defthm fn-novlp-parse-is-parser-projection
  (equal (fn-novlp-parse octets)
         (fn-novlp-result (fn-article-parse octets) *fn-novlp-names*))
  :hints (("Goal" :in-theory (e/d (fn-novlp-parse fn-article-parse)
                                  (fn-novlp-parse-under fn-article-parse-under fn-novlp-result)))))

(local (defthm fn-novlp-first-is-header-lookup
  (equal (fn-novlp-first fields name)
         (let ((matches (fn-article-get-headers-aux fields name)))
           (if (consp matches)
               (list (fn-article-field-unfolded-value (car matches))) nil)))
  :hints (("Goal" :induct (fn-novlp-first fields name)
           :in-theory (enable fn-novlp-first fn-article-get-headers-aux)))))

(defthm fn-novlp-normalized-first-is-overview-content
  (equal (fn-nov-scrub
          (fn-nov-value-content (car (fn-novlp-first (fn-article-fields view) name))))
         (fn-nov-header-content view name))
  :hints (("Goal" :in-theory
           (e/d (fn-nov-header-content fn-article-get-headers)
                (fn-novlp-first fn-article-fields fn-article-get-headers-aux
                 fn-article-field-unfolded-value fn-nov-scrub fn-nov-value-content)))))

(defthm fn-novlp-five-columns-are-overview-content
  (equal (fn-novlp-normalize (fn-novlp-columns (fn-article-fields view) *fn-novlp-names*))
         (list (fn-nov-header-content view *fn-nov-subject-name*)
               (fn-nov-header-content view *fn-nov-from-name*)
               (fn-nov-header-content view *fn-nov-date-name*)
               (fn-nov-header-content view *fn-nov-message-id-name*)
               (fn-nov-header-content view *fn-nov-references-name*)))
  :hints (("Goal" :in-theory
           (e/d (fn-novlp-normalize fn-novlp-columns)
                (fn-novlp-first fn-novlp-first-is-header-lookup fn-article-fields fn-nov-header-content
                 fn-nov-scrub fn-nov-value-content)))))
