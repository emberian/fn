; fn: the header census an admission compares with the profile's header
; limits (lane header-limits-profile, 2026-09-27; PRF-230).  Split from
; books/article-header-limits so that an admission (books/injection) takes
; the definitions without the parser's proof library: including
; article-properties' rewrite rules into injection's world cost
; injection-invariants and nntp-post over 150 s each
; (run-20260927T014513Z-7a03).  The theorems about the census are
; books/article-header-limits'.

(in-package "ACL2")
(include-book "article")
(local (include-book "article-properties"))

(local
(defthm fn-ahl-next-line-shortens
  (implies (fn-article-line-okp (fn-article-next-line octets))
           (< (len (fn-article-line-rest (fn-article-next-line octets)))
              (len octets)))
  :hints (("Goal"
           :use ((:instance fn-article-line-scan-partitions-input
                  (line-rev nil) (left *fn-article-max-line-octets*))
                 (:instance fn-ap-length-append
                  (left (fn-article-line-value
                      (fn-article-next-line-aux
                       octets nil *fn-article-max-line-octets*)))
                  (right (append '(13 10)
                             (fn-article-line-rest
                              (fn-article-next-line-aux
                               octets nil *fn-article-max-line-octets*))))))
           :in-theory (e/d (fn-article-next-line)
                           (fn-article-next-line-aux fn-ap-length-append))))
  :rule-classes :linear))

;; The input's header census, read by `fn-article-next-line' over the lines
;; before the first empty one: its fields (lines not starting with WSP),
;; its physical lines, and its octets (each line and its CRLF).
(defmacro fn-ahl-census-step (name each)
  `(defun ,name (octets)
     (declare (xargs :measure (len octets) :guard t :verify-guards nil
                     :hints (("Goal" :use ((:instance fn-ahl-next-line-shortens))
                              :in-theory (disable fn-article-next-line
                                                  fn-ahl-next-line-shortens)))))
     (let ((next (fn-article-next-line octets)))
       (if (or (not (fn-article-line-okp next))
               (null (fn-article-line-value next)))
           0
         (+ (let ((line (fn-article-line-value next))) (declare (ignorable line)) ,each)
            (,name (fn-article-line-rest next)))))))

(fn-ahl-census-step fn-article-header-field-count
                    (if (fn-article-wspp (car line)) 0 1))
(fn-ahl-census-step fn-article-header-line-count 1)
(fn-ahl-census-step fn-article-header-octet-count (+ 2 (len line)))

(defun fn-article-header-census (octets)
  (declare (xargs :guard t :verify-guards nil))
  (list (fn-article-header-field-count octets)
        (fn-article-header-line-count octets)
        (fn-article-header-octet-count octets)))

(defthm fn-ahl-no-lines-no-fields-no-octets
  (implies (equal (fn-article-header-line-count octets) 0)
           (and (equal (fn-article-header-field-count octets) 0)
                (equal (fn-article-header-octet-count octets) 0)))
  :hints (("Goal" :expand ((fn-article-header-line-count octets)
                           (fn-article-header-field-count octets)
                           (fn-article-header-octet-count octets))
           :in-theory (disable fn-article-next-line))))

(defun fn-article-census-fields (c) (declare (xargs :guard t))
  (nfix (if (consp c) (car c) 0)))
(defun fn-article-census-lines (c) (declare (xargs :guard t))
  (nfix (if (and (consp c) (consp (cdr c))) (cadr c) 0)))
(defun fn-article-census-octets (c) (declare (xargs :guard t))
  (nfix (if (and (consp c) (consp (cdr c)) (consp (cddr c))) (caddr c) 0)))

(defun fn-article-census-within (c limits)
  (declare (xargs :guard t))
  (and (<= (fn-article-census-fields c) (fn-article-limit-fields limits))
       (<= (fn-article-census-lines c) (fn-article-limit-lines limits))
       (<= (fn-article-census-octets c) (fn-article-limit-octets limits))))

(verify-guards fn-article-header-field-count
  :hints (("Goal" :use ((:instance fn-article-next-line-value-listp))
           :in-theory (e/d (fn-article-line-okp)
                           (fn-article-next-line fn-article-next-line-value-listp)))))
(verify-guards fn-article-header-line-count
  :hints (("Goal" :use ((:instance fn-article-next-line-value-listp))
           :in-theory (e/d (fn-article-line-okp)
                           (fn-article-next-line fn-article-next-line-value-listp)))))
(verify-guards fn-article-header-octet-count
  :hints (("Goal" :use ((:instance fn-article-next-line-value-listp))
           :in-theory (e/d (fn-article-line-okp)
                           (fn-article-next-line fn-article-next-line-value-listp)))))
(verify-guards fn-article-header-census)

;; The admission's refusal by the census: the first limit the census
;; passes, by name, in the order fields, lines, octets; NIL within.
(defun fn-article-census-refusal (c limits)
  (declare (xargs :guard t))
  (cond ((< (fn-article-limit-fields limits) (fn-article-census-fields c))
         :header-fields-limit)
        ((< (fn-article-limit-lines limits) (fn-article-census-lines c))
         :header-lines-limit)
        ((< (fn-article-limit-octets limits) (fn-article-census-octets c))
         :header-octets-limit)
        (t nil)))

(defthm fn-article-census-refusal-is-a-limit-reason
  (implies (fn-article-census-refusal c limits)
           (fn-article-limit-reasonp (fn-article-census-refusal c limits))))

; Exported opaque: an admission that refuses by the census case-splits on
; its value, never on its arithmetic.
(in-theory (disable fn-article-census-refusal fn-article-header-census
                    fn-article-census-within))
