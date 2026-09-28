; Proofs for the native FN-Topic candidate subject and bounded constructor.
(in-package "ACL2")
(include-book "topic-history-metadata")
(local (include-book "arithmetic/top" :dir :system))

(local (defthm fn-th-encoded-32-length
  (implies (fn-th-exact-octets-p xs 32)
           (equal (len (fn-cbor-encode (cons :bytes xs))) 34))
  :hints (("Goal" :in-theory (enable fn-th-exact-octets-p
                                      fn-cbor-encode fn-cbor-encode-bounded
                                      fn-cbor-valuep-bounded
                                      fn-cbor-encode-argument)))))
(local (defthm fn-th-encoded-48-length
  (implies (fn-th-exact-octets-p xs 48)
           (equal (len (fn-cbor-encode (cons :bytes xs))) 50))
  :hints (("Goal" :in-theory (enable fn-th-exact-octets-p
                                      fn-cbor-encode fn-cbor-encode-bounded
                                      fn-cbor-valuep-bounded
                                      fn-cbor-encode-argument)))))
(local (defthm fn-th-encoded-64-length
  (implies (and (fn-cbor-octet-listp xs) (<= (len xs) 64))
           (<= (len (fn-cbor-encode (cons :bytes xs))) 66))
  :hints (("Goal" :in-theory (enable fn-cbor-encode fn-cbor-encode-bounded
                                      fn-cbor-valuep-bounded
                                      fn-cbor-encode-argument)))))
(local (defthm fn-th-encoded-small-uint-length
  (implies (and (natp n) (<= n 16))
           (equal (len (fn-cbor-encode (cons :uint n))) 1))
  :hints (("Goal" :in-theory (enable fn-cbor-encode fn-cbor-encode-bounded
                                      fn-cbor-valuep-bounded
                                      fn-cbor-encode-argument)))))

(defun fn-th-author-list-p (authors)
  (declare (xargs :guard t))
  (if (consp authors)
      (and (fn-th-author-p (car authors))
           (fn-th-author-list-p (cdr authors)))
    (null authors)))
(local (defthm fn-th-author-p-consp
  (implies (fn-th-author-p author) (consp author))
  :hints (("Goal" :in-theory (enable fn-th-author-p)))))
(local (defthm fn-th-author-encoded48-length
  (implies (fn-th-author-p author)
           (equal (len (fn-cbor-encode
                        (cons :bytes (fn-th-at 1 author)))) 50))
  :hints (("Goal" :in-theory
           (e/d (fn-th-author-p fn-th-source-id-p)
                (fn-th-exact-octets-p fn-cbor-encode))))))
(local (defthm fn-th-author-car-encoded32-length
  (implies (fn-th-author-p author)
           (equal (len (fn-cbor-encode (cons :bytes (car author)))) 34))
  :hints (("Goal" :in-theory
           (e/d (fn-th-author-p)
                (fn-th-exact-octets-p fn-cbor-encode))))))
(local (defthm fn-th-len-append
  (equal (len (append a b)) (+ (len a) (len b)))
  :hints (("Goal" :induct (len a)))))
(local (defthm fn-th-author-items-encoded-length
  (implies (fn-th-author-list-p authors)
           (equal (len (fn-stmt-encode-items (fn-th-author-items authors)))
                  (* 84 (len authors))))
  :hints (("Goal" :induct (fn-th-author-list-p authors)
           :in-theory (e/d (fn-th-author-list-p fn-th-author-items)
                           (fn-th-author-p fn-th-exact-octets-p
                            fn-th-source-id-p fn-cbor-encode))))))

(defun fn-th-parent-list-p (parents)
  (declare (xargs :guard t))
  (if (consp parents)
      (and (fn-th-source-id-p (car parents))
           (fn-th-parent-list-p (cdr parents)))
    (null parents)))
(local (defthm fn-th-parent-items-encoded-length
  (implies (fn-th-parent-list-p parents)
           (equal (len (fn-stmt-encode-items (fn-th-parent-items parents)))
                  (* 50 (len parents))))
  :hints (("Goal" :induct (fn-th-parent-list-p parents)
           :in-theory (e/d (fn-th-parent-list-p fn-th-parent-items
                            fn-th-source-id-p)
                           (fn-th-exact-octets-p fn-cbor-encode))))))
(local (defthm fn-th-authors-imply-author-list
  (implies (fn-th-authors-p authors previous)
           (fn-th-author-list-p authors))
  :rule-classes nil
  :hints (("Goal" :induct (fn-th-authors-p authors previous)
           :in-theory (e/d (fn-th-authors-p fn-th-author-list-p)
                           (fn-th-author-less-p fn-th-author-p))))))
(local (defthm fn-th-parents-imply-parent-list
  (implies (fn-th-parents-p parents previous)
           (fn-th-parent-list-p parents))
  :rule-classes nil
  :hints (("Goal" :induct (fn-th-parents-p parents previous)
           :in-theory (e/d (fn-th-parents-p fn-th-parent-list-p)
                           (fn-th-octets-less-p fn-th-source-id-p))))))

(defthm fn-th-root-encoding-bound
  (implies (and (fn-th-value-p x) (equal (car x) :root))
           (<= (len (fn-stmt-encode-items (fn-th-items x))) 1531))
  :hints (("Goal" :use ((:instance fn-th-authors-imply-author-list
                                   (authors (fn-th-at 5 x)) (previous nil))
                         (:instance fn-th-encoded-64-length
                                   (xs (fn-th-at 4 x))))
           :in-theory (e/d (fn-th-value-p fn-th-items fn-th-source-id-p)
                           (fn-th-author-items fn-cbor-encode fn-th-authors-p
                            fn-th-author-p fn-th-parents-p)))))
(defthm fn-th-control-encoding-bound
  (implies (and (fn-th-value-p x) (equal (car x) :control))
           (<= (len (fn-stmt-encode-items (fn-th-items x))) 1447))
  :hints (("Goal" :use ((:instance fn-th-authors-imply-author-list
                                   (authors (fn-th-at 3 x)) (previous nil)))
           :in-theory (e/d (fn-th-value-p fn-th-items fn-th-source-id-p)
                           (fn-th-author-items fn-cbor-encode fn-th-authors-p
                            fn-th-author-p fn-th-parents-p)))))
(defthm fn-th-report-encoding-bound
  (implies (and (fn-th-value-p x) (equal (car x) :report))
           (<= (len (fn-stmt-encode-items (fn-th-items x))) 503))
  :hints (("Goal" :use ((:instance fn-th-parents-imply-parent-list
                                   (parents (fn-th-at 3 x)) (previous nil)))
           :in-theory (e/d (fn-th-value-p fn-th-items fn-th-source-id-p)
                           (fn-th-author-items fn-cbor-encode fn-th-authors-p
                            fn-th-author-p fn-th-parents-p)))))
(defthm fn-th-constructor-encoding-bound
  (implies (fn-th-value-p x)
           (<= (len (fn-stmt-encode-items (fn-th-items x))) 1531))
  :hints (("Goal" :use (fn-th-root-encoding-bound
                          fn-th-control-encoding-bound
                          fn-th-report-encoding-bound)
           :in-theory (e/d (fn-th-value-p)
                           (fn-th-items fn-th-root-encoding-bound
                            fn-th-control-encoding-bound
                            fn-th-report-encoding-bound)))))

(local (defthm fn-th-author-items-length
  (equal (len (fn-th-author-items authors)) (* 2 (len authors)))
  :hints (("Goal" :induct (fn-th-author-items authors)
           :in-theory (enable fn-th-author-items)))))
(local (defthm fn-th-parent-items-length
  (equal (len (fn-th-parent-items parents)) (len parents))
  :hints (("Goal" :induct (fn-th-parent-items parents)
           :in-theory (enable fn-th-parent-items)))))
(defthm fn-th-items-count-bound
  (implies (fn-th-value-p x) (<= (len (fn-th-items x)) 39))
  :hints (("Goal" :in-theory
           (e/d (fn-th-value-p fn-th-items)
                (fn-th-author-items fn-th-parent-items
                 fn-th-authors-p fn-th-parents-p)))))
(defthm fn-th-encode-returns-constructor
  (implies (fn-th-value-p x)
           (equal (fn-th-encode x)
                  (fn-stmt-encode-items (fn-th-items x))))
  :hints (("Goal" :use ((:instance fn-cbor-at-mostp-from-length
                                   (xs (fn-stmt-encode-items (fn-th-items x)))
                                   (bound 1536))
                         (:instance fn-th-constructor-encoding-bound))
           :in-theory (e/d (fn-th-encode)
                           (fn-th-items fn-th-value-p
                            fn-cbor-at-mostp-from-length
                            fn-th-constructor-encoding-bound)))))

(local (defthm fn-th-read-authors-of-items
  (implies (fn-th-author-list-p authors)
           (equal (fn-th-read-authors (len authors)
                                      (fn-th-author-items authors))
                  (fn-stmt-ok2 authors nil)))
  :hints (("Goal" :induct (fn-th-author-list-p authors)
           :in-theory (enable fn-th-author-list-p fn-th-author-p
                              fn-th-source-id-p fn-th-exact-octets-p
                              fn-th-author-items fn-th-read-authors
                              fn-stmt-bytes-item-p fn-stmt-ok2
                              fn-stmt-okp fn-stmt-value fn-stmt-rest)))))
(local (defthm fn-th-read-parents-of-items
  (implies (fn-th-parent-list-p parents)
           (equal (fn-th-read-parents (len parents)
                                      (fn-th-parent-items parents))
                  (fn-stmt-ok2 parents nil)))
  :hints (("Goal" :induct (fn-th-parent-list-p parents)
           :in-theory (enable fn-th-parent-list-p fn-th-source-id-p
                              fn-th-exact-octets-p fn-th-parent-items
                              fn-th-read-parents fn-stmt-bytes-item-p
                              fn-stmt-ok2 fn-stmt-okp fn-stmt-value
                              fn-stmt-rest)))))
(local (defthm fn-th-four-reconstruct
  (implies (and (true-listp x) (equal (len x) 4))
           (equal (list (fn-th-at 0 x) (fn-th-at 1 x)
                        (fn-th-at 2 x) (fn-th-at 3 x)) x))
  :hints (("Goal" :in-theory (enable fn-th-at)))))
(local (defthm fn-th-six-reconstruct
  (implies (and (true-listp x) (equal (len x) 6))
           (equal (list (fn-th-at 0 x) (fn-th-at 1 x)
                        (fn-th-at 2 x) (fn-th-at 3 x)
                        (fn-th-at 4 x) (fn-th-at 5 x)) x))
  :hints (("Goal" :in-theory (enable fn-th-at)))))
(defthm fn-th-items-value-of-items
  (implies (fn-th-value-p x)
           (equal (fn-th-items-value (fn-th-items x)) (fn-stmt-ok x)))
  :hints (("Goal" :use ((:instance fn-th-authors-imply-author-list
                                   (authors (fn-th-at 5 x)) (previous nil))
                         (:instance fn-th-authors-imply-author-list
                                   (authors (fn-th-at 3 x)) (previous nil))
                         (:instance fn-th-parents-imply-parent-list
                                   (parents (fn-th-at 3 x)) (previous nil))
                         (:instance fn-th-four-reconstruct)
                         (:instance fn-th-six-reconstruct))
           :in-theory
           (e/d (fn-th-items-value fn-th-items fn-th-value-p
                  fn-stmt-uint-item-p fn-stmt-ok2 fn-stmt-okp
                  fn-stmt-value fn-stmt-rest)
                (fn-th-author-items fn-th-parent-items fn-th-read-authors
                 fn-th-read-parents fn-th-authors-p fn-th-parents-p
                 fn-th-four-reconstruct fn-th-six-reconstruct)))))
(defthm fn-th-constructor-roundtrip
  (implies (fn-th-value-p x)
           (equal (fn-th-decode (fn-th-encode x)) (fn-stmt-ok x)))
  :hints (("Goal" :use ((:instance fn-stmt-decode-items-of-encode-items
                                   (items (fn-th-items x)) (fuel 39))
                         (:instance fn-th-constructor-encoding-bound)
                         (:instance fn-cbor-at-mostp-from-length
                                   (xs (fn-stmt-encode-items (fn-th-items x)))
                                   (bound 1536)))
           :in-theory (e/d (fn-th-decode fn-stmt-okp fn-stmt-value
                            fn-stmt-rest fn-stmt-ok)
                           (fn-th-value-p fn-th-items fn-th-encode
                            fn-th-items-value
                            fn-stmt-decode-items-of-encode-items
                            fn-th-constructor-encoding-bound
                            fn-cbor-at-mostp-from-length)))))

; `host/native/signature-command.lisp` invokes this exact subject only on
; source octets returned by carrier verification. A successful candidate is
; tied to the unique authored field in those octets, not a received header.
(local (defthm fn-th-find-name-preserves-fieldp
  (implies (and (fn-article-field-listp fields)
                (fn-hc-find-name name fields))
           (fn-article-fieldp (fn-hc-find-name name fields)))
  :hints (("Goal" :induct (fn-hc-find-name name fields)
           :in-theory (enable fn-article-field-listp fn-hc-find-name)))))
(local (defthm fn-th-project-field-success-fieldp
  (implies (fn-stmt-okp (fn-th-project-field field))
           (fn-article-fieldp field))
  :hints (("Goal" :in-theory
           (e/d (fn-th-project-field)
                (fn-th-field-decode fn-th-field-lines))))))
(local (defthm fn-th-project-field-success-leading-sp
  (implies (fn-stmt-okp (fn-th-project-field field))
           (equal (fn-th-at 0 (fn-article-field-unfolded-value field)) 32))
  :hints (("Goal" :in-theory
           (e/d (fn-th-project-field)
                (fn-th-field-decode fn-th-field-lines))))))
(defthm fn-th-host-inspect-source-binds-authored-field
  (implies
   (fn-stmt-okp (fn-th-host-inspect-source source))
   (let* ((parsed (fn-article-parse source))
          (fields (fn-article-fields (fn-article-result-article parsed)))
          (field (fn-hc-find-name *fn-th-name* fields))
          (value (fn-article-field-unfolded-value field)))
     (and (fn-article-result-okp parsed)
          (fn-article-syntax-p (fn-article-result-article parsed))
          (equal (fn-hc-count-name *fn-th-name* fields) 1)
          (fn-article-fieldp field)
          (equal (fn-th-at 0 value) 32)
          (equal (fn-th-host-inspect-source source)
                 (fn-th-project-field field)))))
  :hints (("Goal" :use
           ((:instance fn-th-project-field-success-fieldp
                       (field (fn-hc-find-name
                               *fn-th-name*
                               (fn-article-fields
                                (fn-article-result-article
                                 (fn-article-parse source))))))
            (:instance fn-th-project-field-success-leading-sp
                       (field (fn-hc-find-name
                               *fn-th-name*
                               (fn-article-fields
                                (fn-article-result-article
                                 (fn-article-parse source)))))))
           :in-theory
           (e/d (fn-th-host-inspect-source fn-th-project-source
                  fn-th-project-fields)
                (fn-article-parse fn-th-project-field fn-th-field-decode fn-th-decode
                 fn-th-encode fn-th-items-value
                 fn-th-project-field-success-fieldp
                 fn-th-project-field-success-leading-sp)))))

(defun fn-th-lines-at-most-p (lines bound)
  (declare (xargs :guard t))
  (if (consp lines)
      (and (<= (len (car lines)) (nfix bound))
           (fn-th-lines-at-most-p (cdr lines) bound))
    (null lines)))
(local (defthm fn-th-take-length-bound
  (implies (natp n) (<= (len (fn-hc-take n xs)) n))
  :hints (("Goal" :induct (fn-hc-take n xs)
           :in-theory (enable fn-hc-take)))))
(local (defthm fn-th-take72-bound
  (<= (len (fn-hc-take 72 xs)) 72)
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn-th-take-length-bound (n 72)))
           :in-theory (disable fn-th-take-length-bound)))))
(local (defthm fn-th-continuation-lines-fit-85
  (fn-th-lines-at-most-p (fn-th-field-continuation-lines base64) 85)
  :hints (("Goal" :induct (fn-th-field-continuation-lines base64)
           :in-theory (enable fn-th-field-continuation-lines
                              fn-th-lines-at-most-p)))))
(defthm fn-th-field-lines-fit-85
  (fn-th-lines-at-most-p (fn-th-field-lines x) 85)
  :hints (("Goal" :in-theory
           (e/d (fn-th-field-lines fn-th-lines-at-most-p)
                (fn-th-field-encode fn-th-field-continuation-lines)))))
