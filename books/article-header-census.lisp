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
; The census walks execute by loops (lane depth-debt, PRF-919): one frame
; per header line, and nothing caps an article's header lines below its
; octets.  fn-ahl-census-loop-step writes the accumulator loop; the census
; function executes it by mbe, its :logic the recursion, unchanged; the
; equality is <name>-loop-is-plus and the guard proof below.
(defmacro fn-ahl-census-loop-step (name each)
  `(defun ,name (octets acc)
     (declare (xargs :measure (len octets) :guard (acl2-numberp acc) :verify-guards nil
                     :hints (("Goal" :use ((:instance fn-ahl-next-line-shortens))
                              :in-theory (disable fn-article-next-line
                                                  fn-ahl-next-line-shortens)))))
     (let ((next (fn-article-next-line octets)))
       (if (or (not (fn-article-line-okp next))
               (null (fn-article-line-value next)))
           acc
         (,name (fn-article-line-rest next)
                (+ acc (let ((line (fn-article-line-value next))) (declare (ignorable line)) ,each)))))))

(defmacro fn-ahl-census-step (name loop each)
  `(defun ,name (octets)
     (declare (xargs :measure (len octets) :guard t :verify-guards nil
                     :hints (("Goal" :use ((:instance fn-ahl-next-line-shortens))
                              :in-theory (disable fn-article-next-line
                                                  fn-ahl-next-line-shortens)))))
     (mbe :logic
          (let ((next (fn-article-next-line octets)))
            (if (or (not (fn-article-line-okp next))
                    (null (fn-article-line-value next)))
                0
              (+ (let ((line (fn-article-line-value next))) (declare (ignorable line)) ,each)
                 (,name (fn-article-line-rest next)))))
          :exec (,loop octets 0))))

(defmacro fn-ahl-census-loop-lemma (name loop)
  `(defthm ,(intern-in-package-of-symbol
             (concatenate 'string (symbol-name loop) "-IS-PLUS") loop)
     (implies (acl2-numberp acc)
              (equal (,loop octets acc) (+ acc (,name octets))))
     :hints (("Goal" :induct (,loop octets acc)
                     :in-theory (disable fn-article-next-line)))))

(fn-ahl-census-loop-step fn-article-header-field-count-loop
                         (if (fn-article-wspp (car line)) 0 1))
(fn-ahl-census-loop-step fn-article-header-line-count-loop 1)
(fn-ahl-census-loop-step fn-article-header-octet-count-loop (+ 2 (len line)))

(fn-ahl-census-step fn-article-header-field-count fn-article-header-field-count-loop
                    (if (fn-article-wspp (car line)) 0 1))
(fn-ahl-census-step fn-article-header-line-count fn-article-header-line-count-loop 1)
(fn-ahl-census-step fn-article-header-octet-count fn-article-header-octet-count-loop
                    (+ 2 (len line)))

(fn-ahl-census-loop-lemma fn-article-header-field-count fn-article-header-field-count-loop)
(fn-ahl-census-loop-lemma fn-article-header-line-count fn-article-header-line-count-loop)
(fn-ahl-census-loop-lemma fn-article-header-octet-count fn-article-header-octet-count-loop)

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

(verify-guards fn-article-header-field-count-loop
  :hints (("Goal" :use ((:instance fn-article-next-line-value-listp))
           :in-theory (e/d (fn-article-line-okp)
                           (fn-article-next-line fn-article-next-line-value-listp)))))
(verify-guards fn-article-header-field-count
  :hints (("Goal" :use ((:instance fn-article-next-line-value-listp)
                        (:instance fn-article-header-field-count-loop-is-plus (acc 0)))
           :expand ((fn-article-header-field-count octets))
           :in-theory (e/d (fn-article-line-okp)
                           ((:definition fn-article-header-field-count)
                            (:definition fn-article-header-field-count-loop)
                            fn-article-header-field-count-loop-is-plus
                            fn-article-next-line fn-article-next-line-value-listp)))))
(verify-guards fn-article-header-line-count-loop
  :hints (("Goal" :use ((:instance fn-article-next-line-value-listp))
           :in-theory (e/d (fn-article-line-okp)
                           (fn-article-next-line fn-article-next-line-value-listp)))))
(verify-guards fn-article-header-line-count
  :hints (("Goal" :use ((:instance fn-article-next-line-value-listp)
                        (:instance fn-article-header-line-count-loop-is-plus (acc 0)))
           :expand ((fn-article-header-line-count octets))
           :in-theory (e/d (fn-article-line-okp)
                           ((:definition fn-article-header-line-count)
                            (:definition fn-article-header-line-count-loop)
                            fn-article-header-line-count-loop-is-plus
                            fn-article-next-line fn-article-next-line-value-listp)))))
(verify-guards fn-article-header-octet-count-loop
  :hints (("Goal" :use ((:instance fn-article-next-line-value-listp))
           :in-theory (e/d (fn-article-line-okp)
                           (fn-article-next-line fn-article-next-line-value-listp)))))
(verify-guards fn-article-header-octet-count
  :hints (("Goal" :use ((:instance fn-article-next-line-value-listp)
                        (:instance fn-article-header-octet-count-loop-is-plus (acc 0)))
           :expand ((fn-article-header-octet-count octets))
           :in-theory (e/d (fn-article-line-okp)
                           ((:definition fn-article-header-octet-count)
                            (:definition fn-article-header-octet-count-loop)
                            fn-article-header-octet-count-loop-is-plus
                            fn-article-next-line fn-article-next-line-value-listp)))))
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
