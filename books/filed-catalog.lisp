; fn: every served catalog row is filed within its own stored bytes (O1,
; packet 3).  The catalog numbers each committed row's groups in order
; (FN-O1-ASSIGN-IS-POSITIONAL), so every catalog the updaters build has
; positional memberships (FN-O1-COMMIT-, -WITHDRAW-, -REDECIDE-KEEPS-THE-
; CATALOG-POSITIONAL, FN-O1-CLEAR-MAKES-THE-CATALOG-POSITIONAL); under the
; catalog's history relation (books/catalog-relation.lisp), a history whose
; article records are filed within their own payloads (FN-O1-RECORDS-FILEDP)
; gives every row, at any index, FN-O1-ARTICLE-WITHIN-HEADERP over the bytes
; its handle denotes (FN-O1-CATALOG-ROWS-WITHIN-HEADER), the hypothesis
; books/filed-groups' FN-O1-XREF-WITHIN-THE-HEADER asks of a served article.

(in-package "ACL2")

(include-book "filed-groups")
(include-book "catalog-view")

; Rows I..N-1 positional: groups against held numbers.
(defun fn-o1-cat-rows-positionalp (i n fn-cat)
  (declare (xargs :stobjs fn-cat :guard (and (natp i) (natp n)) :verify-guards nil
                  :measure (nfix (- (nfix n) (nfix i)))))
  (if (and (natp i) (natp n) (< i n) (< i (fn-cat-count fn-cat)))
      (and (fn-membership-listp (fn-record-groups (fn-cat-at i fn-cat))
                                (fn-held-numbers (fn-cat-at i fn-cat)))
           (fn-o1-cat-rows-positionalp (+ 1 i) n fn-cat))
    t))

(defun fn-o1-cat-positionalp (fn-cat)
  (declare (xargs :stobjs fn-cat :verify-guards nil))
  (fn-o1-cat-rows-positionalp 0 (fn-cat-count fn-cat) fn-cat))

; The history invariant: every article record's groups are filed within its
; own payload octets.
(defun fn-o1-records-filedp (records)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp records)
      (and (or (not (fn-record-p (car records)))
               (fn-o1-filed-within-sourcep (fn-record-groups (car records))
                                           (fn-record-payload (car records))))
           (fn-o1-records-filedp (cdr records)))
    t))


(local
 (defthm o1c-assign-numbers-positional
  (fn-membership-listp groups (fn-cat-assign-numbers groups c))
  :hints (("Goal" :induct (len groups) :in-theory (enable fn-membership-listp)))))
(defthm fn-o1-assign-is-positional
  (fn-membership-listp (fn-record-groups (fn-cat-assign h c))
                       (fn-held-numbers (fn-cat-assign h c)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-cat-assign fn-held-with-numbers))))
(local
 (defun o1c-rowp (h)
  (fn-membership-listp (fn-record-groups h) (fn-held-numbers h))))
(local
 (defun o1c-rowsp (c)
  (if (consp c) (and (o1c-rowp (car c)) (o1c-rowsp (cdr c))) t)))
(local
 (defthm o1c-consp-nthcdr
  (implies (natp i) (iff (consp (nthcdr i c)) (< i (len c))))
  :hints (("Goal" :induct (nthcdr i c) :in-theory (enable nthcdr len (:t len))))))
(local
 (defthm o1c-car-nthcdr (equal (car (nthcdr i c)) (nth i c))
  :hints (("Goal" :induct (nthcdr i c) :in-theory (enable nthcdr nth)))))
(local
 (defthm o1c-cdr-nthcdr (implies (natp i) (equal (cdr (nthcdr i c)) (nthcdr (+ 1 i) c)))
  :hints (("Goal" :induct (nthcdr i c) :in-theory (enable nthcdr)))))
(local
 (defthm o1c-rows-positional-is-rowsp
  (implies (and (natp i) (equal n (len c)))
           (iff (fn-o1-cat-rows-positionalp i n c) (o1c-rowsp (nthcdr i c))))
  :hints (("Goal" :induct (fn-o1-cat-rows-positionalp i n c)
           :in-theory (e/d (fn-o1-cat-rows-positionalp) (nthcdr nth))
           :expand ((o1c-rowsp (nthcdr i c)))))))
(local
 (defthm o1c-positionalp-is-rowsp
  (iff (fn-o1-cat-positionalp c) (o1c-rowsp c))
  :hints (("Goal" :in-theory (enable fn-o1-cat-positionalp)))))
(local
 (defthm o1c-rowsp-append
  (iff (o1c-rowsp (append a b)) (and (o1c-rowsp a) (o1c-rowsp b)))))
(local
 (defthm o1c-rowsp-update-nth
  (implies (and (o1c-rowsp c) (o1c-rowp x) (natp k) (< k (len c)))
           (o1c-rowsp (update-nth k x c)))))
(local
 (defthm o1c-rowsp-nth
  (implies (and (o1c-rowsp c) (< (nfix k) (len c))) (o1c-rowp (nth k c)))))
(local
 (defthm o1c-with-withdrawn-rowp
  (iff (o1c-rowp (fn-held-with-withdrawn h w)) (o1c-rowp h))
  :hints (("Goal" :in-theory (enable fn-held-with-withdrawn)))))
(local
 (defthm o1c-with-context-rowp
  (iff (o1c-rowp (fn-held-with-context h x)) (o1c-rowp h))
  :hints (("Goal" :in-theory (enable fn-held-with-context)))))
(local
 (in-theory (disable o1c-rowp)))
(local
 (defthm o1c-assign-rowp
  (o1c-rowp (fn-cat-assign h c))
  :hints (("Goal" :in-theory (enable o1c-rowp) :use fn-o1-assign-is-positional))))
(defthm fn-o1-commit-keeps-the-catalog-positional
  (implies (fn-o1-cat-positionalp fn-cat)
           (let ((fn-cat (fn-cat-commit h fn-cat))) (fn-o1-cat-positionalp fn-cat)))
  :rule-classes nil)
(defthm fn-o1-withdraw-keeps-the-catalog-positional
  (implies (fn-o1-cat-positionalp fn-cat)
           (let ((fn-cat (fn-cat-withdraw target by fn-cat))) (fn-o1-cat-positionalp fn-cat)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-cat-mark-withdrawn))))
(defthm fn-o1-redecide-keeps-the-catalog-positional
  (implies (fn-o1-cat-positionalp fn-cat)
           (let ((fn-cat (fn-cat-redecide seq context fn-cat))) (fn-o1-cat-positionalp fn-cat)))
  :rule-classes nil)
(defthm fn-o1-clear-makes-the-catalog-positional
  (and (let ((fn-cat (fn-cat-clear fn-cat))) (fn-o1-cat-positionalp fn-cat))
       (let ((fn-cat (fn-cat-clear-keyed key fn-cat))) (fn-o1-cat-positionalp fn-cat)))
  :rule-classes nil)
(local
 (defun o1c-jk-ind (j k)
  (declare (xargs :measure (nfix k)))
  (if (zp k) (list j) (o1c-jk-ind (+ 1 j) (- k 1)))))
(local
 (defthm o1c-nth-wire-list
  (implies (and (natp j) (natp k) (< (+ j k) (fn-cat-count fn-cat)))
           (equal (nth k (fn-cat-wire-list j fn-arena fn-cat))
                  (fn-held-wire-of (fn-cat-at (+ j k) fn-cat) fn-arena)))
  :hints (("Goal" :induct (o1c-jk-ind j k)
           :in-theory (e/d (nth) (fn-held-wire-of fn-cat-at-is-nth fn-cat-count-is-len))
           :expand ((fn-cat-wire-list j fn-arena fn-cat))))))
(local
 (defun o1c-all-filedp (l)
  (if (consp l)
      (and (fn-o1-filed-within-sourcep (fn-record-groups (car l)) (fn-record-payload (car l)))
           (o1c-all-filedp (cdr l)))
    t)))
(local
 (defthm o1c-filedp-article-records
  (implies (fn-o1-records-filedp records) (o1c-all-filedp (fn-sf-article-records records)))
  :hints (("Goal" :in-theory (e/d (fn-o1-records-filedp) (fn-o1-filed-within-sourcep))))))
(local
 (defthm o1c-all-filedp-nth
  (implies (and (o1c-all-filedp l) (< (nfix k) (len l)))
           (fn-o1-filed-within-sourcep (fn-record-groups (nth k l)) (fn-record-payload (nth k l))))
  :hints (("Goal" :in-theory (e/d (nth) (fn-o1-filed-within-sourcep))))))
(local
 (defthm o1c-len-wire-list
  (implies (natp j)
           (equal (len (fn-cat-wire-list j fn-arena fn-cat)) (nfix (- (fn-cat-count fn-cat) j))))
  :hints (("Goal" :induct (fn-cat-wire-list j fn-arena fn-cat)
           :in-theory (e/d (fn-cat-wire-list) (fn-held-wire-of fn-cat-at-is-nth fn-cat-count-is-len))))))
(local
 (defthm o1c-filed-nil
  (fn-o1-filed-within-sourcep nil p)
  :hints (("Goal" :in-theory (enable fn-o1-filed-within-sourcep fn-o1-subseqp fn-o1-groups-octets)))))
(local
 (defthm o1c-wire-filed
  (implies (and (o1c-all-filedp (fn-cat-wire-list 0 fn-arena fn-cat))
                (natp i) (< i (fn-cat-count fn-cat)))
           (fn-o1-filed-within-sourcep (fn-record-groups (fn-cat-at i fn-cat))
                                       (fn-arena-payload (fn-record-payload (fn-cat-at i fn-cat)) fn-arena)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-held-wire-of fn-held-wire)
                           (fn-o1-filed-within-sourcep fn-cat-wire-list o1c-nth-wire-list o1c-all-filedp-nth
                            o1c-len-wire-list fn-cat-at-is-nth fn-cat-count-is-len fn-arena-payload))
           :use ((:instance o1c-nth-wire-list (j 0) (k i))
                 (:instance o1c-len-wire-list (j 0))
                 (:instance o1c-all-filedp-nth (k i) (l (fn-cat-wire-list 0 fn-arena fn-cat))))))))
(local
 (defthm o1c-row-within-below-the-count
  (implies (and (fn-cat-history-relation records fn-arena fn-cat)
                (fn-o1-records-filedp records)
                (fn-o1-cat-positionalp fn-cat)
                (natp i) (< i (fn-cat-count fn-cat)))
           (let ((article (fn-cat-row-article i fn-arena fn-cat)))
             (fn-o1-article-within-headerp
              article (fn-nntp-article-bytes article fn-arena))))
  :rule-classes nil
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-cat-history-relation fn-o1-article-within-headerp fn-cat-row-article
                            fn-nntp-article-bytes fn-nntp-payload-bytes o1c-rowp)
                           (fn-o1-filed-within-sourcep fn-membership-listp fn-cat-wire-list
                            fn-cat-at-is-nth fn-cat-count-is-len fn-arena-payload-is-nth fn-arena-count-is-len
                            fn-arena-payload fn-arena-count
                            fn-cat-handles-inp fn-cat-handles-inp-at o1c-rowsp-nth
                            o1c-positionalp-is-rowsp fn-o1-records-filedp o1c-filedp-article-records
                            fn-cat-row-payload-natp))
           :use ((:instance o1c-wire-filed)
                 (:instance o1c-filedp-article-records)
                 (:instance o1c-positionalp-is-rowsp (c fn-cat))
                 (:instance fn-cat-row-payload-natp (seq i))
                 (:instance fn-cat-handles-inp-at (n (fn-cat-count fn-cat)) (seq i))
                 (:instance o1c-rowsp-nth (c fn-cat) (k i))
                 (:instance fn-cat-at-is-nth (seq i))
                 (:instance fn-cat-count-is-len))))))
(local
 (defthm o1c-nth-past (implies (and (natp i) (<= (len c) i)) (equal (nth i c) nil))
  :hints (("Goal" :in-theory (enable nth)))))
(local
 (defthm o1c-nth-non-natp (implies (not (natp i)) (equal (nth i c) (nth 0 c)))
  :hints (("Goal" :in-theory (enable nth)))))
(local
 (defthm o1c-row-within-past-the-count
  (implies (and (natp i) (<= (fn-cat-count fn-cat) i))
           (let ((article (fn-cat-row-article i fn-arena fn-cat)))
             (fn-o1-article-within-headerp article p)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-o1-article-within-headerp fn-cat-row-article)
                           (fn-o1-filed-within-sourcep))))))
(local
 (defthm o1c-row-article-non-natp
  (implies (not (natp i))
           (equal (fn-cat-row-article i fn-arena fn-cat) (fn-cat-row-article 0 fn-arena fn-cat)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-cat-row-article)))))
(defthm fn-o1-catalog-rows-within-header
  (implies (and (fn-cat-history-relation records fn-arena fn-cat)
                (fn-o1-records-filedp records)
                (fn-o1-cat-positionalp fn-cat))
           (let ((article (fn-cat-row-article i fn-arena fn-cat)))
             (fn-o1-article-within-headerp
              article (fn-nntp-article-bytes article fn-arena))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :cases ((and (natp i) (< i (fn-cat-count fn-cat)))
                   (natp i)
                   (< 0 (fn-cat-count fn-cat)))
           :in-theory (disable fn-cat-row-article fn-o1-article-within-headerp fn-nntp-article-bytes
                               fn-cat-history-relation fn-o1-records-filedp fn-o1-cat-positionalp)
           :use (o1c-row-within-below-the-count
                 (:instance o1c-row-within-below-the-count (i 0))
                 o1c-row-article-non-natp
                 (:instance o1c-row-within-past-the-count
                            (p (fn-nntp-article-bytes (fn-cat-row-article i fn-arena fn-cat) fn-arena)))
                 (:instance o1c-row-within-past-the-count (i 0)
                            (p (fn-nntp-article-bytes (fn-cat-row-article 0 fn-arena fn-cat) fn-arena)))))))
