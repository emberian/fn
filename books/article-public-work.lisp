; Public ARTICLE parser work correspondence and profile bound.
(in-package "ACL2")
(include-book "article-work")
(include-book "article-work-budget")
(local (include-book "arithmetic/top" :dir :system))

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:definition fn-article-new-field)
                          (:definition fn-article-parse-lines)
                          (:rewrite fn-ap-at-most-is-length-bound)
                          (:rewrite fn-aw-reverse-value))))

(local (in-theory (disable fn-aw-r fn-aw-v fn-aw-c)))
(defun fn-aw-current-size (current)
  (+ (len (fn-article-field-raw-lines current))
     (len (fn-article-field-unfolded-value current))))
(defun fn-aw-state-size (fields-rev current header-rev)
  (+ (len fields-rev) (len header-rev) (fn-aw-current-size current)))
(defthm fn-aw-current-size-natural
  (natp (fn-aw-current-size current)) :rule-classes :type-prescription)
(defthm fn-aw-state-size-natural
  (natp (fn-aw-state-size fields-rev current header-rev)) :rule-classes :type-prescription)
(defthm fn-aw-add-fold-size
  (equal (fn-aw-current-size (fn-article-add-fold current line))
         (+ 1 (fn-aw-current-size current) (len line))))
(defthm fn-aw-new-field-size
  (implies (fn-article-line-okp (fn-article-new-field line))
           (<= (fn-aw-current-size (fn-article-line-value (fn-article-new-field line)))
               (1+ (len line))))
  :hints (("Goal"
    :use ((:instance fn-aw-split-colon-rest-bound (name-rev nil)))
    :in-theory (disable fn-article-split-colon-aux fn-article-namep
                       fn-article-header-bytes-p fn-article-has-vcharp
                       fn-article-ascii-downcase fn-aw-split-colon-rest-bound))))
(defthm fn-aw-fold-state-growth
  (implies (and (true-listp line) (true-listp header-rev))
   (<= (fn-aw-state-size fields-rev (fn-article-add-fold current line)
                        (fn-article-header-rev-add-line header-rev line))
       (+ (fn-aw-state-size fields-rev current header-rev) (* 2 (len line)) 4)))
  :hints (("Goal" :in-theory (disable fn-article-add-fold fn-aw-current-size
                                      fn-article-header-rev-add-line))))
(defthm fn-aw-new-state-growth
  (implies (and (true-listp line) (true-listp header-rev)
                (fn-article-line-okp (fn-article-new-field line)))
   (<= (fn-aw-state-size (if current (cons current fields-rev) fields-rev)
                        (fn-article-line-value (fn-article-new-field line))
                        (fn-article-header-rev-add-line header-rev line))
       (+ (fn-aw-state-size fields-rev current header-rev) (* 2 (len line)) 4)))
  :hints (("Goal" :use fn-aw-new-field-size
           :in-theory (disable fn-article-new-field fn-aw-current-size
                               fn-aw-new-field-size fn-article-header-rev-add-line))))

; ---------------------------------------------------------------------------
; The costed parser follows the original short-circuit branches.  CHARGE is
; bookkeeping only: it sums work already performed, without charging itself.
(defun fn-aw-charge (answer extra)
  (fn-aw-r (fn-aw-v answer) (+ extra (fn-aw-c answer))))
(defthm fn-aw-charge-value (equal (fn-aw-v (fn-aw-charge answer extra)) (fn-aw-v answer)))
(defthm fn-aw-charge-cost (equal (fn-aw-c (fn-aw-charge answer extra)) (+ extra (fn-aw-c answer))))
(local (in-theory (disable fn-aw-charge)))

; A conservative logical reference close charge is paid on every active
; line, including early returns. Executed accumulators instead read a flag.
(defun fn-aw-close-charge (current)
  (if current (1+ (len (fn-article-field-unfolded-value current))) 0))
(defthm fn-aw-close-charge-natural
  (natp (fn-aw-close-charge current)) :rule-classes :type-prescription)
(defthm fn-aw-close-charge-at-most-current-size
  (<= (fn-aw-close-charge current) (1+ (fn-aw-current-size current)))
  :rule-classes :linear)

(defun fn-aw-parse-lines (octets limits lines-left header-bytes nfields fields-rev current header-rev)
  (declare (xargs :measure (nfix lines-left)))
  (if (zp lines-left)
      (fn-aw-r (fn-article-error :header-lines-limit) 1)
    (let ((next (fn-aw-next-line octets)))
      (if (not (fn-article-line-okp (fn-aw-v next)))
          (fn-aw-charge next (+ 1 (fn-aw-close-charge current)))
        (let ((line (fn-article-line-value (fn-aw-v next)))
              (rest (fn-article-line-rest (fn-aw-v next))))
          (if (null line)
              (let ((body (fn-aw-body rest)))
                (if (or (not (fn-aw-v body))
                        (not (fn-article-field-closedp current)))
                    (fn-aw-r (fn-article-error :invalid-header)
                             (+ 1 (fn-aw-close-charge current) (fn-aw-c next) (fn-aw-c body)))
                  (let ((header (fn-aw-reverse header-rev))
                        (fields (fn-aw-finish-fields fields-rev current)))
                    (fn-aw-r (fn-article-ok (fn-article-make
                                             (fn-aw-v header) rest (fn-aw-v fields)))
                             (+ 1 (fn-aw-close-charge current) (fn-aw-c next) (fn-aw-c body)
                                (fn-aw-c header) (fn-aw-c fields))))))
            (let ((length1 (fn-aw-len line)))
              (if (< (fn-article-limit-octets limits)
                     (+ header-bytes (fn-aw-v length1) 2))
                  (fn-aw-r (fn-article-error :header-octets-limit)
                           (+ 1 (fn-aw-close-charge current) (fn-aw-c next) (fn-aw-c length1)))
                (if (fn-article-wspp (car line))
                    (if (not current)
                        (fn-aw-r (fn-article-error :invalid-header)
                                 (+ 1 (fn-aw-close-charge current) (fn-aw-c next) (fn-aw-c length1)))
                      (let ((fold (fn-aw-fold-line line)))
                        (if (not (fn-aw-v fold))
                            (fn-aw-r (fn-article-error :invalid-header)
                                     (+ 1 (fn-aw-close-charge current) (fn-aw-c next) (fn-aw-c length1) (fn-aw-c fold)))
                          (let ((length2 (fn-aw-len line))
                                (field (fn-aw-add-fold current line))
                                (header (fn-aw-header-add header-rev line)))
                            (fn-aw-charge
                             (fn-aw-parse-lines
                              rest limits (1- lines-left) (+ header-bytes (fn-aw-v length2) 2)
                              nfields fields-rev (fn-aw-v field) (fn-aw-v header))
                             (+ 1 (fn-aw-close-charge current) (fn-aw-c next) (fn-aw-c length1) (fn-aw-c fold)
                                (fn-aw-c length2) (fn-aw-c field) (fn-aw-c header)))))))
                  (let ((field-result (fn-aw-new-field line)))
                    (if (not (fn-article-line-okp (fn-aw-v field-result)))
                        (fn-aw-charge field-result
                                      (+ 1 (fn-aw-close-charge current) (fn-aw-c next) (fn-aw-c length1)))
                     ; Logical visible-value scan, conservatively charged in this branch.
                     (if (not (fn-article-field-closedp current))
                         (fn-aw-r (fn-article-error :invalid-header)
                                  (+ 1 (fn-aw-close-charge current) (fn-aw-c next) (fn-aw-c length1)
                                     (fn-aw-c field-result)))
                      ; The field count is carried: one comparison, no walk.
                      (if (<= (fn-article-limit-fields limits)
                              (+ (if current 1 0) (nfix nfields)))
                          (fn-aw-r (fn-article-error :header-fields-limit)
                                   (+ 1 (fn-aw-close-charge current) (fn-aw-c next) (fn-aw-c length1)
                                      (fn-aw-c field-result)))
                        (let ((length2 (fn-aw-len line))
                              (header (fn-aw-header-add header-rev line)))
                          (fn-aw-charge
                           (fn-aw-parse-lines
                            rest limits (1- lines-left) (+ header-bytes (fn-aw-v length2) 2)
                            (if current (+ 1 (nfix nfields)) nfields)
                            (if current (cons current fields-rev) fields-rev)
                            (fn-article-line-value (fn-aw-v field-result))
                            (fn-aw-v header))
                           (+ 1 (fn-aw-close-charge current) (fn-aw-c next) (fn-aw-c length1)
                              (fn-aw-c field-result)
                              (fn-aw-c length2) (fn-aw-c header))))))))))))))))
)
(defthm fn-aw-parse-lines-value
  (equal (fn-aw-v (fn-aw-parse-lines octets limits lines-left header-bytes nfields fields-rev current header-rev))
         (fn-article-parse-lines octets limits lines-left header-bytes nfields fields-rev current header-rev))
  :hints (("Goal"
    :expand ((fn-aw-parse-lines octets limits lines-left header-bytes nfields fields-rev current header-rev))
    :induct (fn-article-parse-lines octets limits lines-left header-bytes nfields fields-rev current header-rev)
    :in-theory (e/d (fn-aw-parse-lines fn-article-parse-lines)
                    (fn-aw-next-line fn-article-next-line
                     fn-aw-body fn-article-body-crlfp fn-aw-reverse
                     fn-aw-finish-fields fn-article-finish-fields fn-aw-len
                     fn-aw-fold-line fn-article-fold-linep
                     fn-aw-add-fold fn-article-add-fold
                     fn-aw-header-add fn-article-header-rev-add-line
                     fn-aw-new-field fn-article-new-field fn-article-field-closedp
                     fn-article-line-okp fn-article-line-value fn-article-line-rest)))))

(defun fn-aw-parse-under (octets limits)
  (let ((preflight (fn-aw-at-most octets *fn-article-max-octets*)))
    (if (not (fn-aw-v preflight))
        (fn-aw-r (fn-article-error :limit) (1+ (fn-aw-c preflight)))
      (let ((validation (fn-aw-octets octets)))
        (if (not (fn-aw-v validation))
            (fn-aw-r (fn-article-error :invalid-header)
                     (+ 1 (fn-aw-c preflight) (fn-aw-c validation)))
          (fn-aw-charge
           (fn-aw-parse-lines octets limits (1+ (fn-article-limit-lines limits))
                              0 0 nil nil nil)
           (+ 1 (fn-aw-c preflight) (fn-aw-c validation))))))))

(defun fn-aw-parse (octets)
  (fn-aw-parse-under octets *fn-article-ceiling-limits*))

(defthm fn-article-parse-under-work-value
  (equal (fn-aw-v (fn-aw-parse-under octets limits))
         (fn-article-parse-under octets limits))
  :hints (("Goal" :in-theory (disable fn-aw-at-most fn-cbor-at-mostp
             fn-aw-octets fn-cbor-octet-listp fn-aw-parse-lines fn-article-parse-lines))))

(defthm fn-article-parse-work-value
  (equal (fn-aw-v (fn-aw-parse octets)) (fn-article-parse octets))
  :hints (("Goal" :in-theory (disable fn-aw-parse-under fn-article-parse-under))))
