; Logical work accounting for the complete received-article parser.
(in-package "ACL2")
(include-book "article-properties")
(local (include-book "arithmetic/top" :dir :system))

; Cost units count list-walk visits and fixed-size scalar/control blocks.
; Fixed-tag comparisons never compare two arbitrary trees in this call graph.
; Big-integer bit costs, compiler/runtime bookkeeping and GC are not counted.
(defun fn-aw-r (value cost) (list value cost))
(defun fn-aw-v (result) (car result))
(defun fn-aw-c (result) (cadr result))
(defthm fn-aw-v-r (equal (fn-aw-v (fn-aw-r value cost)) value))
(defthm fn-aw-c-r (equal (fn-aw-c (fn-aw-r value cost)) cost))
(local (in-theory (disable fn-aw-r fn-aw-v fn-aw-c)))

(defun fn-aw-len (xs)
  (if (consp xs)
      (let ((tail (fn-aw-len (cdr xs))))
        (fn-aw-r (1+ (fn-aw-v tail)) (1+ (fn-aw-c tail))))
    (fn-aw-r 0 1)))
(defthm fn-aw-len-value (equal (fn-aw-v (fn-aw-len xs)) (len xs)))
(defthm fn-aw-len-cost (equal (fn-aw-c (fn-aw-len xs)) (1+ (len xs))))

(defun fn-aw-append (xs ys)
  (if (consp xs)
      (let ((tail (fn-aw-append (cdr xs) ys)))
        (fn-aw-r (cons (car xs) (fn-aw-v tail)) (1+ (fn-aw-c tail))))
    (fn-aw-r ys 1)))
(defthm fn-aw-append-value
  (equal (fn-aw-v (fn-aw-append xs ys)) (append xs ys)))
(defthm fn-aw-append-cost
  (equal (fn-aw-c (fn-aw-append xs ys)) (1+ (len xs))))

(defun fn-aw-revappend (xs acc)
  (if (consp xs)
      (let ((tail (fn-aw-revappend (cdr xs) (cons (car xs) acc))))
        (fn-aw-r (fn-aw-v tail) (1+ (fn-aw-c tail))))
    (fn-aw-r acc 1)))
(defthm fn-aw-revappend-value
  (equal (fn-aw-v (fn-aw-revappend xs acc)) (revappend xs acc)))
(defthm fn-aw-revappend-cost
  (equal (fn-aw-c (fn-aw-revappend xs acc)) (1+ (len xs))))
(defun fn-aw-reverse (xs)
  ; The string branch maintains helper totality, but is unreachable from the
  ; public parser: every reversed accumulator and line is a proper list.
  (if (stringp xs)
      (fn-aw-r (reverse xs) (+ 1 (* 3 (length xs))))
    (fn-aw-revappend xs nil)))
(defthm fn-aw-reverse-value
  (equal (fn-aw-v (fn-aw-reverse xs)) (reverse xs)))
(defthm fn-aw-reverse-list-cost
  (implies (true-listp xs)
           (equal (fn-aw-c (fn-aw-reverse xs)) (1+ (len xs)))))

(defun fn-aw-at-most (xs bound)
  (if (consp xs)
      (if (zp bound)
          (fn-aw-r nil 1)
        (let ((tail (fn-aw-at-most (cdr xs) (1- bound))))
          (fn-aw-r (fn-aw-v tail) (1+ (fn-aw-c tail)))))
    (fn-aw-r t 1)))
(defthm fn-aw-at-most-value
  (equal (fn-aw-v (fn-aw-at-most xs bound)) (fn-cbor-at-mostp xs bound)))
(defthm fn-aw-at-most-cost-bound
  (<= (fn-aw-c (fn-aw-at-most xs bound)) (1+ (nfix bound)))
  :hints (("Goal" :induct (fn-aw-at-most xs bound))))
(defthm fn-aw-at-most-cost-input-bound
  (<= (fn-aw-c (fn-aw-at-most xs bound)) (1+ (len xs)))
  :hints (("Goal" :induct (fn-aw-at-most xs bound))))

(defun fn-aw-octets (xs)
  (if (consp xs)
      (if (fn-cbor-octetp (car xs))
          (let ((tail (fn-aw-octets (cdr xs))))
            (fn-aw-r (fn-aw-v tail) (1+ (fn-aw-c tail))))
        (fn-aw-r nil 1))
    (fn-aw-r (null xs) 1)))
(defthm fn-aw-octets-value
  (equal (fn-aw-v (fn-aw-octets xs)) (fn-cbor-octet-listp xs)))
(defthm fn-aw-octets-cost-bound
  (<= (fn-aw-c (fn-aw-octets xs)) (1+ (len xs)))
  :hints (("Goal" :induct (fn-aw-octets xs))))

(defun fn-aw-header-bytes (xs)
  (if (consp xs)
      (if (fn-article-header-bytep (car xs))
          (let ((tail (fn-aw-header-bytes (cdr xs))))
            (fn-aw-r (fn-aw-v tail) (1+ (fn-aw-c tail))))
        (fn-aw-r nil 1))
    (fn-aw-r (null xs) 1)))
(defthm fn-aw-header-bytes-value
  (equal (fn-aw-v (fn-aw-header-bytes xs)) (fn-article-header-bytes-p xs)))
(defthm fn-aw-header-bytes-cost-bound
  (<= (fn-aw-c (fn-aw-header-bytes xs)) (1+ (len xs)))
  :hints (("Goal" :induct (fn-aw-header-bytes xs))))

(defun fn-aw-ftext (xs)
  (if (consp xs)
      (if (fn-article-ftextp (car xs))
          (let ((tail (fn-aw-ftext (cdr xs))))
            (fn-aw-r (fn-aw-v tail) (1+ (fn-aw-c tail))))
        (fn-aw-r nil 1))
    (fn-aw-r (null xs) 1)))
(defthm fn-aw-ftext-value
  (equal (fn-aw-v (fn-aw-ftext xs)) (fn-article-ftext-listp xs)))
(defthm fn-aw-ftext-cost-bound
  (<= (fn-aw-c (fn-aw-ftext xs)) (1+ (len xs)))
  :hints (("Goal" :induct (fn-aw-ftext xs))))

(defun fn-aw-has-vchar (xs)
  (if (consp xs)
      (if (fn-article-vcharp (car xs))
          (fn-aw-r t 1)
        (let ((tail (fn-aw-has-vchar (cdr xs))))
          (fn-aw-r (fn-aw-v tail) (1+ (fn-aw-c tail)))))
    (fn-aw-r nil 1)))
(defthm fn-aw-has-vchar-value
  (equal (fn-aw-v (fn-aw-has-vchar xs)) (fn-article-has-vcharp xs)))
(defthm fn-aw-has-vchar-cost-bound
  (<= (fn-aw-c (fn-aw-has-vchar xs)) (1+ (len xs)))
  :hints (("Goal" :induct (fn-aw-has-vchar xs))))

(defun fn-aw-downcase (xs)
  (if (consp xs)
      (let ((tail (fn-aw-downcase (cdr xs))))
        (fn-aw-r (cons (fn-article-ascii-downcase-byte (car xs)) (fn-aw-v tail))
                 (1+ (fn-aw-c tail))))
    (fn-aw-r nil 1)))
(defthm fn-aw-downcase-value
  (equal (fn-aw-v (fn-aw-downcase xs)) (fn-article-ascii-downcase xs)))
(defthm fn-aw-downcase-cost
  (equal (fn-aw-c (fn-aw-downcase xs)) (1+ (len xs))))

(defun fn-aw-body (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (if (equal (car xs) 13)
          (if (and (consp (cdr xs)) (equal (cadr xs) 10))
              (let ((tail (fn-aw-body (cddr xs))))
                (fn-aw-r (fn-aw-v tail) (1+ (fn-aw-c tail))))
            (fn-aw-r nil 1))
        (if (equal (car xs) 10)
            (fn-aw-r nil 1)
          (let ((tail (fn-aw-body (cdr xs))))
            (fn-aw-r (fn-aw-v tail) (1+ (fn-aw-c tail))))))
    (fn-aw-r t 1)))
(defthm fn-aw-body-value
  (equal (fn-aw-v (fn-aw-body xs)) (fn-article-body-crlfp xs))
  :hints (("Goal" :induct (fn-aw-body xs))))
(defthm fn-aw-body-cost-bound
  (<= (fn-aw-c (fn-aw-body xs)) (1+ (len xs)))
  :hints (("Goal" :induct (fn-aw-body xs))))
