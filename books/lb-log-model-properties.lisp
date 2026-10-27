; LB-LOG-MODEL byte refinements: owner C, retire with LA1/LA6 (owner P).
(in-package "ACL2")
(include-book "lb-log-model")
(include-book "consumer-position")
(local (include-book "def-representation-pages"))
(local (include-book "arithmetic-5/top" :dir :system))

(local (defthm fn-lbp-range-in-entries-contained
 (implies (and (fn-lb-log-model-range-in-entries off length entries)
               (natp off) (natp length) (natp inner) (natp count)
               (<= off inner) (<= (+ inner count) (+ off length)))
  (fn-lb-log-model-range-in-entries inner count entries))
 :hints (("Goal" :induct (fn-lb-log-model-range-in-entries off length entries)
          :in-theory (e/d (fn-lb-log-model-range-in-entries)
                          (fn-lb-log-model-entryp nth true-listp))))))

(local (defthm fn-lbp-read-range-contained-valid
 (implies (and (not (equal (fn-lb-log-model-read-range seg off length log) :bad))
               (natp off) (natp length) (natp inner) (natp count)
               (<= off inner) (<= (+ inner count) (+ off length)))
  (not (equal (fn-lb-log-model-read-range seg inner count log) :bad)))
 :hints (("Goal" :in-theory (e/d (fn-lb-log-model-read-range)
   (fn-lb-log-model-range-in-entries fn-lb-log-model-segment take nthcdr))))))

(local (defun fn-lbp-two-count-induction (n m xs)
 (declare (xargs :measure (nfix n) :verify-guards nil))
 (if (zp n) (cons m xs)
  (fn-lbp-two-count-induction (- n 1) (- m 1) (cdr xs)))))

(local (defthm fn-lbp-take-of-take-contained
 (implies (and (natp n) (natp m) (<= n m))
  (equal (take n (take m xs)) (take n xs)))
 :hints (("Goal" :induct (fn-lbp-two-count-induction n m xs)
 :in-theory (enable take)))))

(local (defthm fn-lbp-nthcdr-of-take-contained
 (implies (and (natp n) (natp m) (<= n m))
  (equal (nthcdr n (take m xs)) (take (- m n) (nthcdr n xs))))
 :hints (("Goal" :induct (fn-lbp-two-count-induction n m xs)
 :in-theory (enable take nthcdr)))))

(local (defthm fn-lbp-nthcdr-add
 (implies (and (natp n) (natp m))
  (equal (nthcdr m (nthcdr n xs)) (nthcdr (+ n m) xs)))
 :hints (("Goal" :induct (nthcdr n xs) :in-theory (enable nthcdr)))))

(defthm fn-lb-log-model-read-range-contained-value
 (implies (and (not (equal (fn-lb-log-model-read-range seg off length log) :bad))
               (natp off) (natp length) (natp inner) (natp count)
               (<= off inner) (<= (+ inner count) (+ off length)))
  (equal (fn-lb-log-model-read-range seg inner count log)
         (take count (nthcdr (- inner off) (fn-lb-log-model-read-range seg off length log)))))
 :hints (("Goal" :use ((:instance fn-lbp-read-range-contained-valid))
 :in-theory (e/d (fn-lb-log-model-read-range)
   (fn-lb-log-model-range-in-entries fn-lb-log-model-segment take nthcdr)))))

(defthm fn-lb-log-model-read-range-length
 (implies (not (equal (fn-lb-log-model-read-range seg off count log) :bad))
          (equal (len (fn-lb-log-model-read-range seg off count log)) count))
 :hints (("Goal" :in-theory (e/d (fn-lb-log-model-read-range)
  (take nthcdr fn-lb-log-model-segment fn-lb-log-model-range-in-entries)))))

(local (defthm fn-lbp-valid-block-rev-is-wire
 (implies (not (equal (fn-nntp-block-rev bytes startp acc) :error))
  (equal (fn-nntp-block-rev bytes startp acc)
         (revappend (fn-lb-log-model-wire bytes startp) acc)))
 :hints (("Goal" :induct (fn-nntp-block-rev bytes startp acc)
          :in-theory (enable fn-nntp-block-rev fn-lb-log-model-wire revappend)))))

(local (defun fn-lbp-both-list-induction (a b)
 (declare (xargs :verify-guards nil))
 (if (and (consp a) (consp b)) (fn-lbp-both-list-induction (cdr a) (cdr b)) (cons a b))))

(local (defthm fn-lbp-append-equality-gives-equal-prefix-length
 (implies (equal (append a suffix) (append b suffix))
          (equal (len a) (len b)))
 :hints (("Goal" :use ((:instance
  (:theorem (implies (equal x y) (equal (len x) (len y))))
  (x (append a suffix)) (y (append b suffix))))
 :in-theory (disable binary-append)))))

(local (defthm fn-lbp-append-fixedpoint-empty
 (implies (equal suffix (append b suffix)) (not (consp b)))
 :hints (("Goal" :use ((:instance fn-lbp-append-equality-gives-equal-prefix-length (a nil)))
          :in-theory (disable fn-lbp-append-equality-gives-equal-prefix-length binary-append)))))

(local (defthm fn-lbp-append-right-cancel
 (implies (and (true-listp a) (true-listp b)
               (equal (append a suffix) (append b suffix)))
          (equal a b))
 :rule-classes nil
 :hints (("Goal" :induct (fn-lbp-both-list-induction a b)
 :in-theory (enable binary-append true-listp len)))))

(local (defthm fn-lbp-wire-true-listp
 (true-listp (fn-lb-log-model-wire bytes startp))
 :rule-classes :type-prescription
 :hints (("Goal" :induct (fn-lb-log-model-wire bytes startp)
          :in-theory (enable fn-lb-log-model-wire)))))

(local (defthm fn-lbp-stuffed-lines-true-listp
 (true-listp (fn-nntp-stuff-lines lines))
 :rule-classes :type-prescription
 :hints (("Goal" :induct (fn-nntp-stuff-lines lines)
          :in-theory (enable fn-nntp-stuff-lines fn-nntp-crlf)))))

(local (defthm fn-lbp-wire-of-valid-crlf-lines
 (implies (and (fn-octet-listp bytes) (equal (car (fn-nntp-crlf-lines bytes)) :ok))
  (equal (fn-la-payload-wire bytes)
         (fn-nntp-stuff-lines (cadr (fn-nntp-crlf-lines bytes)))))
 :hints (("Goal" :use ((:instance fn-nntp-block-rev-is-the-block)
  (:instance fn-lbp-valid-block-rev-is-wire (startp t) (acc nil))
  (:instance fn-lbp-append-right-cancel (a (fn-lb-log-model-wire bytes t))
   (b (fn-nntp-stuff-lines (cadr (fn-nntp-crlf-lines bytes)))) (suffix '(46 13 10))))
 :in-theory (e/d (fn-la-payload-wire)
 (fn-nntp-block-rev fn-lb-log-model-wire fn-nntp-crlf-lines fn-nntp-stuff-lines
  fn-octet-listp fn-nntp-block-rev-is-the-block fn-lbp-valid-block-rev-is-wire))))))

(local (defthm fn-lbp-wire-crlf-append
 (equal (fn-lb-log-model-wire (append prefix (cons 13 (cons 10 rest))) startp)
        (append (fn-lb-log-model-wire prefix startp) (cons 13 (cons 10 (fn-lb-log-model-wire rest t)))))
 :hints (("Goal" :induct (fn-lb-log-model-wire prefix startp)
          :in-theory (enable fn-lb-log-model-wire)))))

(local (defthm fn-lbp-split-aux-reassembles
 (implies (and (true-listp bytes) (true-listp prefix-rev)
               (fn-nntp-split-okp (fn-nntp-split-article-aux bytes prefix-rev)))
  (equal (append (reverse prefix-rev) bytes)
         (append (fn-nntp-split-head (fn-nntp-split-article-aux bytes prefix-rev))
                 '(13 10)
                 (fn-nntp-split-body (fn-nntp-split-article-aux bytes prefix-rev)))))
 :hints (("Goal" :induct (fn-nntp-split-article-aux bytes prefix-rev)
 :in-theory (enable fn-nntp-split-article-aux fn-nntp-split-okp
                    fn-nntp-split-head fn-nntp-split-body)))))

(local (defthm fn-lbp-octets-true-listp
 (implies (fn-octet-listp bytes) (true-listp bytes))
 :hints (("Goal" :induct (fn-octet-listp bytes) :in-theory (enable fn-octet-listp)))))

(local (defthm fn-lbp-split-payload-reassembles
 (implies (fn-nntp-split-okp (fn-nntp-split-article bytes))
  (equal (append (fn-nntp-split-head (fn-nntp-split-article bytes)) '(13 10)
                 (fn-nntp-split-body (fn-nntp-split-article bytes))) bytes))
 :hints (("Goal" :use ((:instance fn-lbp-split-aux-reassembles (prefix-rev nil)))
 :in-theory (e/d (fn-nntp-split-article)
  (fn-nntp-split-okp fn-nntp-split-head fn-nntp-split-body fn-nntp-split-article-aux))))))

(local (defthm fn-lbp-wire-of-successful-lines
 (implies (equal (car (fn-nntp-crlf-lines bytes)) :ok)
  (equal (fn-la-payload-wire bytes)
         (fn-nntp-stuff-lines (cadr (fn-nntp-crlf-lines bytes)))))
 :hints (("Goal" :use fn-lbp-wire-of-valid-crlf-lines
 :in-theory (e/d (fn-nntp-crlf-lines)
  (fn-nntp-crlf-lines-aux fn-la-payload-wire fn-nntp-stuff-lines fn-octet-listp
   fn-lbp-wire-of-valid-crlf-lines))))))

(defthm fn-lb-log-model-stuffed-article-is-wire
 (implies (equal (car (fn-nntp-section-of-bytes payload :article)) :ok)
  (equal (fn-nntp-stuffed-section :article payload) (fn-la-payload-wire payload)))
 :hints (("Goal" :in-theory (e/d (fn-nntp-stuffed-section fn-nntp-section-of-bytes)
  (fn-la-payload-wire fn-nntp-crlf-lines fn-nntp-stuff-lines)))))

(defthm fn-lb-log-model-stuffed-head-is-wire
 (implies (equal (car (fn-nntp-section-of-bytes payload :head)) :ok)
  (equal (fn-nntp-stuffed-section :head payload)
         (fn-la-payload-wire (fn-nntp-split-head (fn-nntp-split-article payload)))))
 :hints (("Goal" :in-theory (e/d (fn-nntp-stuffed-section fn-nntp-section-of-bytes)
  (fn-la-payload-wire fn-nntp-crlf-lines fn-nntp-stuff-lines fn-nntp-split-head
   fn-nntp-split-article fn-nntp-split-okp)))))

(defthm fn-lb-log-model-stuffed-body-is-wire
 (implies (equal (car (fn-nntp-section-of-bytes payload :body)) :ok)
  (equal (fn-nntp-stuffed-section :body payload)
         (fn-la-payload-wire (fn-nntp-split-body (fn-nntp-split-article payload)))))
 :hints (("Goal" :in-theory (e/d (fn-nntp-stuffed-section fn-nntp-section-of-bytes)
  (fn-la-payload-wire fn-nntp-crlf-lines fn-nntp-stuff-lines fn-nntp-split-body
   fn-nntp-split-article fn-nntp-split-okp)))))

(defthm fn-lb-log-model-wire-split-decomposition
 (implies (fn-nntp-split-okp (fn-nntp-split-article payload))
  (equal (fn-la-payload-wire payload)
   (append (fn-la-payload-wire (fn-nntp-split-head (fn-nntp-split-article payload)))
           '(13 10) (fn-la-payload-wire (fn-nntp-split-body (fn-nntp-split-article payload))))))
 :hints (("Goal" :use ((:instance fn-lbp-wire-crlf-append
   (prefix (fn-nntp-split-head (fn-nntp-split-article payload)))
   (rest (fn-nntp-split-body (fn-nntp-split-article payload))) (startp t))
  (:instance fn-lbp-split-payload-reassembles (bytes payload)))
 :in-theory (e/d (fn-la-payload-wire)
 (fn-lb-log-model-wire fn-lbp-split-payload-reassembles fn-lbp-wire-crlf-append
  fn-nntp-split-okp fn-nntp-split-article fn-nntp-split-head fn-nntp-split-body)))))

(defthm fn-lb-log-model-wire-head-take
 (implies (fn-nntp-split-okp (fn-nntp-split-article payload))
  (equal (take (len (fn-la-payload-wire (fn-nntp-split-head (fn-nntp-split-article payload))))
               (fn-la-payload-wire payload))
         (fn-la-payload-wire (fn-nntp-split-head (fn-nntp-split-article payload)))))
 :hints (("Goal" :use fn-lb-log-model-wire-split-decomposition
 :in-theory (e/d (fn-la-payload-wire)
  (fn-lb-log-model-wire fn-lb-log-model-wire-split-decomposition fn-nntp-split-okp
   fn-nntp-split-article fn-nntp-split-head fn-nntp-split-body take)))))

(local (defthm fn-lbp-nthcdr-append-prefix-plus
 (implies (and (true-listp prefix) (natp n))
  (equal (nthcdr (+ (len prefix) n) (append prefix tail)) (nthcdr n tail)))
 :hints (("Goal" :use ((:instance fn-lbp-nthcdr-add
  (n (len prefix)) (m n) (xs (append prefix tail))))
 :in-theory (disable fn-lbp-nthcdr-add nthcdr binary-append)))))

(defthm fn-lb-log-model-wire-split-length
 (implies (fn-nntp-split-okp (fn-nntp-split-article payload))
  (equal (len (fn-la-payload-wire payload))
   (+ (len (fn-la-payload-wire (fn-nntp-split-head (fn-nntp-split-article payload)))) 2
      (len (fn-la-payload-wire (fn-nntp-split-body (fn-nntp-split-article payload)))))))
 :hints (("Goal" :use fn-lb-log-model-wire-split-decomposition
 :in-theory (disable fn-lb-log-model-wire-split-decomposition fn-la-payload-wire
  fn-nntp-split-okp fn-nntp-split-article fn-nntp-split-head fn-nntp-split-body))))

(defthm fn-lb-log-model-payload-wire-true-listp
 (true-listp (fn-la-payload-wire payload))
 :rule-classes :type-prescription
 :hints (("Goal" :in-theory (enable fn-la-payload-wire))))

(local (defthm fn-lbp-nthcdr-append-prefix-plus-canonical
 (implies (and (true-listp prefix) (natp n))
  (equal (nthcdr (+ n (len prefix)) (append prefix tail)) (nthcdr n tail)))
 :hints (("Goal" :use fn-lbp-nthcdr-append-prefix-plus
 :in-theory (disable fn-lbp-nthcdr-append-prefix-plus nthcdr binary-append)))))

(local (defthm fn-lbp-take-length-proper
 (implies (true-listp xs) (equal (take (len xs) xs) xs))
 :hints (("Goal" :induct (len xs) :in-theory (enable take)))))

(defthm fn-lb-log-model-wire-body-take
 (implies (fn-nntp-split-okp (fn-nntp-split-article payload))
  (equal
   (take (nfix (- (- (len (fn-la-payload-wire payload))
                    (len (fn-la-payload-wire (fn-nntp-split-head (fn-nntp-split-article payload)))) ) 2))
    (nthcdr (+ (len (fn-la-payload-wire (fn-nntp-split-head (fn-nntp-split-article payload)))) 2)
            (fn-la-payload-wire payload)))
   (fn-la-payload-wire (fn-nntp-split-body (fn-nntp-split-article payload)))))
 :hints (("Goal" :use fn-lb-log-model-wire-split-decomposition
 :in-theory (e/d (nthcdr)
  (fn-la-payload-wire fn-lb-log-model-wire fn-nntp-split-okp
   fn-nntp-split-article fn-nntp-split-head fn-nntp-split-body take)))))

(defthm fn-lb-log-model-stuffed-section-bad-is-empty
 (implies (not (equal (car (fn-nntp-section-of-bytes payload kind)) :ok))
          (equal (fn-nntp-stuffed-section kind payload) nil))
 :hints (("Goal" :in-theory (e/d (fn-nntp-stuffed-section)
  (fn-nntp-section-of-bytes fn-nntp-stuff-lines)))))

(defthm fn-lb-log-model-successful-head-body-have-split
 (implies (and (not (equal kind :article))
               (equal (car (fn-nntp-section-of-bytes payload kind)) :ok))
          (fn-nntp-split-okp (fn-nntp-split-article payload)))
 :hints (("Goal" :in-theory (e/d (fn-nntp-section-of-bytes)
 (fn-nntp-split-okp fn-nntp-split-article fn-nntp-crlf-lines fn-nntp-split-head fn-nntp-split-body)))))
