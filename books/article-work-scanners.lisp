; Whole public article parser work, including all repeated list traversals.
(in-package "ACL2")
(include-book "article-work-primitives")
(local (include-book "arithmetic/top" :dir :system))
(local (in-theory (disable fn-aw-r fn-aw-v fn-aw-c)))

; ---------------------------------------------------------------------------
; Costed scanners, including the reversal of each accumulated prefix.
(defun fn-aw-next-line-aux (octets line-rev left)
  (declare (xargs :measure (acl2-count octets)))
  (if (consp octets)
      (if (equal (car octets) 13)
          (if (and (consp (cdr octets)) (equal (cadr octets) 10))
              (let ((back (fn-aw-reverse line-rev)))
                (fn-aw-r (list :ok (fn-aw-v back) (cddr octets))
                         (1+ (fn-aw-c back))))
            (fn-aw-r (fn-article-error :invalid-header) 1))
        (if (equal (car octets) 10)
            (fn-aw-r (fn-article-error :invalid-header) 1)
          (if (zp left)
              (fn-aw-r (fn-article-error :limit) 1)
            (let ((tail (fn-aw-next-line-aux
                         (cdr octets) (cons (car octets) line-rev) (1- left))))
              (fn-aw-r (fn-aw-v tail) (1+ (fn-aw-c tail)))))))
    (fn-aw-r (fn-article-error :missing-separator) 1)))
(defthm fn-aw-next-line-aux-value
  (equal (fn-aw-v (fn-aw-next-line-aux octets line-rev left))
         (fn-article-next-line-aux octets line-rev left))
  :hints (("Goal" :induct (fn-aw-next-line-aux octets line-rev left)
           :in-theory (disable fn-aw-reverse))))
(defthm fn-aw-next-line-aux-cost-bound
  (implies (true-listp line-rev)
           (<= (fn-aw-c (fn-aw-next-line-aux octets line-rev left))
               (+ 2 (* 2 (len octets)) (len line-rev))))
  :hints (("Goal" :induct (fn-aw-next-line-aux octets line-rev left)
           :in-theory (disable fn-aw-reverse))))
(defun fn-aw-next-line (octets)
  (let ((answer (fn-aw-next-line-aux octets nil *fn-article-max-line-octets*)))
    (fn-aw-r (fn-aw-v answer) (1+ (fn-aw-c answer)))))
(defthm fn-aw-next-line-value
  (equal (fn-aw-v (fn-aw-next-line octets)) (fn-article-next-line octets))
  :hints (("Goal" :in-theory (disable fn-aw-next-line-aux
                                      fn-article-next-line-aux))))
(defthm fn-aw-next-line-cost-bound
  (<= (fn-aw-c (fn-aw-next-line octets)) (+ 3 (* 2 (len octets))))
  :hints (("Goal" :use ((:instance fn-aw-next-line-aux-cost-bound
                            (line-rev nil) (left *fn-article-max-line-octets*)))
           :in-theory (disable fn-aw-next-line-aux))))

(defun fn-aw-split-colon (line name-rev)
  (if (consp line)
      (if (equal (car line) 58)
          (let ((back (fn-aw-reverse name-rev)))
            (fn-aw-r (list :ok (fn-aw-v back) (cdr line)) (1+ (fn-aw-c back))))
        (let ((tail (fn-aw-split-colon (cdr line) (cons (car line) name-rev))))
          (fn-aw-r (fn-aw-v tail) (1+ (fn-aw-c tail)))))
    (fn-aw-r (fn-article-error :invalid-header) 1)))
(defthm fn-aw-split-colon-value
  (equal (fn-aw-v (fn-aw-split-colon line name-rev))
         (fn-article-split-colon-aux line name-rev))
  :hints (("Goal" :induct (fn-aw-split-colon line name-rev)
           :in-theory (disable fn-aw-reverse))))
(defthm fn-aw-split-colon-cost-bound
  (implies (true-listp name-rev)
           (<= (fn-aw-c (fn-aw-split-colon line name-rev))
               (+ 2 (* 2 (len line)) (len name-rev))))
  :hints (("Goal" :induct (fn-aw-split-colon line name-rev)
           :in-theory (disable fn-aw-reverse))))

; Scanner result-size facts are about the actual parser, not a cost predicate.
(defthm fn-aw-next-line-aux-line-bound
  (implies (true-listp line-rev)
           (<= (len (fn-article-line-value
                     (fn-article-next-line-aux octets line-rev left)))
               (+ (len octets) (len line-rev))))
  :hints (("Goal" :induct (fn-article-next-line-aux octets line-rev left))))
(defthm fn-aw-next-line-aux-rest-bound
  (<= (len (fn-article-line-rest
            (fn-article-next-line-aux octets line-rev left)))
      (len octets))
  :hints (("Goal" :induct (fn-article-next-line-aux octets line-rev left))))
(defthm fn-aw-next-line-line-bound
  (<= (len (fn-article-line-value (fn-article-next-line octets))) (len octets))
  :hints (("Goal" :use ((:instance fn-aw-next-line-aux-line-bound
                             (line-rev nil) (left *fn-article-max-line-octets*)))
           :in-theory (disable fn-article-next-line-aux))))
(defthm fn-aw-next-line-rest-bound
  (<= (len (fn-article-line-rest (fn-article-next-line octets))) (len octets))
  :hints (("Goal" :use ((:instance fn-aw-next-line-aux-rest-bound
                             (line-rev nil) (left *fn-article-max-line-octets*)))
           :in-theory (disable fn-article-next-line-aux))))
(defthm fn-aw-split-colon-name-bound
  (implies (true-listp name-rev)
           (<= (len (fn-article-line-value
                     (fn-article-split-colon-aux line name-rev)))
               (+ (len line) (len name-rev))))
  :hints (("Goal" :induct (fn-article-split-colon-aux line name-rev))))
(defthm fn-aw-split-colon-rest-bound
  (<= (len (fn-article-line-rest (fn-article-split-colon-aux line name-rev)))
      (len line))
  :hints (("Goal" :induct (fn-article-split-colon-aux line name-rev))))
