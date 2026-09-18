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
