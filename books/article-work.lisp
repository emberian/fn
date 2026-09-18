; Whole public article parser work, including all repeated list traversals.
(in-package "ACL2")
(include-book "article-work-scanners")
(local (include-book "arithmetic/top" :dir :system))
(local (in-theory (disable fn-aw-r fn-aw-v fn-aw-c)))

(defthm fn-aw-at-most-cost-natural
  (natp (fn-aw-c (fn-aw-at-most xs bound)))
  :hints (("Goal" :induct (fn-aw-at-most xs bound)))
  :rule-classes :type-prescription)
(defthm fn-aw-octets-cost-natural
  (natp (fn-aw-c (fn-aw-octets xs)))
  :hints (("Goal" :induct (fn-aw-octets xs)))
  :rule-classes :type-prescription)
(defthm fn-aw-header-bytes-cost-natural
  (natp (fn-aw-c (fn-aw-header-bytes xs)))
  :hints (("Goal" :induct (fn-aw-header-bytes xs)))
  :rule-classes :type-prescription)
(defthm fn-aw-ftext-cost-natural
  (natp (fn-aw-c (fn-aw-ftext xs)))
  :hints (("Goal" :induct (fn-aw-ftext xs)))
  :rule-classes :type-prescription)
(defthm fn-aw-has-vchar-cost-natural
  (natp (fn-aw-c (fn-aw-has-vchar xs)))
  :hints (("Goal" :induct (fn-aw-has-vchar xs)))
  :rule-classes :type-prescription)
(defthm fn-aw-body-cost-natural
  (natp (fn-aw-c (fn-aw-body xs)))
  :hints (("Goal" :induct (fn-aw-body xs)))
  :rule-classes :type-prescription)
(defthm fn-aw-reverse-cost-natural
  (natp (fn-aw-c (fn-aw-reverse xs)))
  :hints (("Goal" :in-theory (disable fn-aw-revappend)))
  :rule-classes :type-prescription)
(defthm fn-aw-split-colon-cost-natural
  (natp (fn-aw-c (fn-aw-split-colon line name-rev)))
  :hints (("Goal" :induct (fn-aw-split-colon line name-rev)
           :in-theory (disable fn-aw-reverse fn-article-split-colon-aux)))
  :rule-classes :type-prescription)
(defthm fn-aw-next-line-aux-cost-natural
  (natp (fn-aw-c (fn-aw-next-line-aux octets line-rev left)))
  :hints (("Goal" :induct (fn-aw-next-line-aux octets line-rev left)
           :in-theory (disable fn-aw-reverse fn-article-next-line-aux)))
  :rule-classes :type-prescription)
(defthm fn-aw-next-line-cost-natural
  (natp (fn-aw-c (fn-aw-next-line octets)))
  :hints (("Goal" :in-theory (disable fn-aw-next-line-aux)))
  :rule-classes :type-prescription)
; ---------------------------------------------------------------------------
; Repeated field scans and folded-prefix copies are explicit work calls.
(defun fn-aw-name (name)
  (if (consp name)
      (let ((answer (fn-aw-ftext name)))
        (fn-aw-r (fn-aw-v answer) (1+ (fn-aw-c answer))))
    (fn-aw-r nil 1)))
(defthm fn-aw-name-value
  (equal (fn-aw-v (fn-aw-name name)) (fn-article-namep name))
  :hints (("Goal" :in-theory (disable fn-aw-ftext fn-article-ftext-listp))))
(defthm fn-aw-name-cost-natural
  (natp (fn-aw-c (fn-aw-name name)))
  :hints (("Goal" :in-theory (disable fn-aw-ftext)))
  :rule-classes :type-prescription)
(defthm fn-aw-name-cost-bound
  (<= (fn-aw-c (fn-aw-name name)) (+ 2 (len name)))
  :hints (("Goal" :use ((:instance fn-aw-ftext-cost-bound (xs name)))
           :in-theory (disable fn-aw-ftext fn-aw-ftext-cost-bound))))

(defun fn-aw-new-field (line)
  (let* ((split (fn-aw-split-colon line nil))
         (sv (fn-aw-v split)))
    (if (not (fn-article-line-okp sv))
        (fn-aw-r sv (1+ (fn-aw-c split)))
      (let* ((name (fn-article-line-value sv))
             (value (fn-article-line-rest sv))
             (name-check (fn-aw-name name)))
        (if (not (and (fn-aw-v name-check) (consp value)
                       (fn-article-wspp (car value))))
            (fn-aw-r (fn-article-error :invalid-header)
                     (+ 1 (fn-aw-c split) (fn-aw-c name-check)))
          (let ((header-check (fn-aw-header-bytes value)))
            (if (not (fn-aw-v header-check))
                (fn-aw-r (fn-article-error :invalid-header)
                         (+ 1 (fn-aw-c split) (fn-aw-c name-check)
                            (fn-aw-c header-check)))
              (let ((visible-check (fn-aw-has-vchar value)))
                (if (not (fn-aw-v visible-check))
                    (fn-aw-r (fn-article-error :invalid-header)
                             (+ 1 (fn-aw-c split) (fn-aw-c name-check)
                                (fn-aw-c header-check) (fn-aw-c visible-check)))
                  (let ((lower (fn-aw-downcase name)))
                    (fn-aw-r
                     (list :ok (fn-article-make-field (list line) (fn-aw-v lower) value))
                     (+ 1 (fn-aw-c split) (fn-aw-c name-check)
                        (fn-aw-c header-check) (fn-aw-c visible-check)
                        (fn-aw-c lower)))))))))))))

(defthm fn-aw-new-field-value
  (equal (fn-aw-v (fn-aw-new-field line)) (fn-article-new-field line))
  :hints (("Goal" :in-theory
           (disable fn-aw-split-colon fn-article-split-colon-aux
                    fn-aw-name fn-article-namep fn-aw-header-bytes
                    fn-article-header-bytes-p fn-aw-has-vchar
                    fn-article-has-vcharp fn-aw-downcase
                    fn-article-ascii-downcase))))
(defthm fn-aw-new-field-cost-bound
  (<= (fn-aw-c (fn-aw-new-field line)) (+ 8 (* 6 (len line))))
  :hints (("Goal"
    :use ((:instance fn-aw-split-colon-cost-bound (name-rev nil))
          (:instance fn-aw-split-colon-name-bound (name-rev nil))
          (:instance fn-aw-split-colon-rest-bound (name-rev nil))
          (:instance fn-aw-name-cost-bound
                     (name (fn-article-line-value (fn-article-split-colon-aux line nil))))
          (:instance fn-aw-header-bytes-cost-bound
                     (xs (fn-article-line-rest (fn-article-split-colon-aux line nil))))
          (:instance fn-aw-has-vchar-cost-bound
                     (xs (fn-article-line-rest (fn-article-split-colon-aux line nil))))
          (:instance fn-aw-downcase-cost
                     (xs (fn-article-line-value (fn-article-split-colon-aux line nil)))))
    :in-theory (disable fn-aw-split-colon fn-article-split-colon-aux
                        fn-aw-name fn-article-namep fn-aw-header-bytes
                        fn-article-header-bytes-p fn-aw-has-vchar
                        fn-article-has-vcharp fn-aw-downcase
                        fn-article-ascii-downcase fn-article-line-value
                        fn-article-line-rest fn-article-line-okp
                        fn-aw-split-colon-cost-bound fn-aw-split-colon-name-bound
                        fn-aw-split-colon-rest-bound fn-aw-name-cost-bound
                        fn-aw-header-bytes-cost-bound fn-aw-has-vchar-cost-bound))))

(defun fn-aw-fold-line (line)
  (if (and (consp line) (fn-article-wspp (car line)))
      (let ((header (fn-aw-header-bytes line)))
        (if (fn-aw-v header)
            (let ((visible (fn-aw-has-vchar line)))
              (fn-aw-r (fn-aw-v visible)
                       (+ 1 (fn-aw-c header) (fn-aw-c visible))))
          (fn-aw-r nil (1+ (fn-aw-c header)))))
    (fn-aw-r nil 1)))
(defthm fn-aw-fold-line-value
  (equal (fn-aw-v (fn-aw-fold-line line)) (fn-article-fold-linep line))
  :hints (("Goal" :in-theory (disable fn-aw-header-bytes fn-aw-has-vchar
             fn-article-header-bytes-p fn-article-has-vcharp))))
(defthm fn-aw-fold-line-cost-bound
  (<= (fn-aw-c (fn-aw-fold-line line)) (+ 3 (* 2 (len line))))
  :hints (("Goal" :use ((:instance fn-aw-header-bytes-cost-bound (xs line))
                         (:instance fn-aw-has-vchar-cost-bound (xs line)))
           :in-theory (disable fn-aw-header-bytes fn-aw-has-vchar fn-aw-header-bytes-cost-bound fn-aw-has-vchar-cost-bound))))

(defun fn-aw-add-fold (field line)
  (let ((raw (fn-aw-append (fn-article-field-raw-lines field) (list line)))
        (value (fn-aw-append (fn-article-field-unfolded-value field) line)))
    (fn-aw-r (fn-article-make-field (fn-aw-v raw) (fn-article-field-name field)
                                    (fn-aw-v value))
             (+ 1 (fn-aw-c raw) (fn-aw-c value)))))
(defthm fn-aw-add-fold-value
  (equal (fn-aw-v (fn-aw-add-fold field line)) (fn-article-add-fold field line))
  :hints (("Goal" :in-theory (disable fn-aw-append))))
(defthm fn-aw-add-fold-cost
  (equal (fn-aw-c (fn-aw-add-fold field line))
         (+ 3 (len (fn-article-field-raw-lines field))
            (len (fn-article-field-unfolded-value field))))
  :hints (("Goal" :in-theory (disable fn-aw-append))))

(defun fn-aw-header-add (header-rev line)
  (let* ((back (fn-aw-reverse line))
         (content (fn-aw-append (fn-aw-v back) header-rev))
         (framed (fn-aw-append '(10 13) (fn-aw-v content))))
    (fn-aw-r (fn-aw-v framed)
             (+ 1 (fn-aw-c back) (fn-aw-c content) (fn-aw-c framed)))))
(defthm fn-aw-header-add-value
  (equal (fn-aw-v (fn-aw-header-add header-rev line))
         (fn-article-header-rev-add-line header-rev line))
  :hints (("Goal" :in-theory (disable fn-aw-reverse fn-aw-append))))
(defthm fn-aw-header-add-cost
  (implies (true-listp line)
           (equal (fn-aw-c (fn-aw-header-add header-rev line))
                  (+ 6 (* 2 (len line)))))
  :hints (("Goal" :in-theory (disable fn-aw-reverse fn-aw-append))))

(defun fn-aw-finish-fields (fields-rev current)
  (let ((back (fn-aw-reverse (if current (cons current fields-rev) fields-rev))))
    (fn-aw-r (fn-aw-v back) (1+ (fn-aw-c back)))))
(defthm fn-aw-finish-fields-value
  (equal (fn-aw-v (fn-aw-finish-fields fields-rev current))
         (fn-article-finish-fields fields-rev current))
  :hints (("Goal" :in-theory (disable fn-aw-reverse))))
(defthm fn-aw-finish-fields-cost
  (implies (true-listp fields-rev)
           (equal (fn-aw-c (fn-aw-finish-fields fields-rev current))
                  (+ 2 (len fields-rev) (if current 1 0))))
  :hints (("Goal" :in-theory (disable fn-aw-reverse))))
