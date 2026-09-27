; served-catalog.lisp -- the served retrieval arms read the committed event
; catalog at the connection's pinned view (catalog slice, step 7b, first
; increment: the Message-ID and article-number arms).
;
; The served machine (books/served.lisp) dispatches an archive command line
; through fn-nntp-archive-command-pinned (books/nntp.lisp): its Message-ID
; arms find the article in the connection's pinned Message-ID trie and its
; by-number arms fall through to fn-nntp-retrieval, which WALKS the pinned
; archive (fn-nntp-find-group-number: one pass over every article per
; request; planning/performance-2026-09-26.md row 7).  The catalog
; (books/catalog.lisp) holds every committed record once, in commit order,
; and a view is a count: the rows below it that no later withdrawal hides
; (fn-cat-visible-at).  A Message-ID names its rows through the catalog's
; Message-ID column (fn-cat-msgid-seqs) and a (group, number) pair names its
; row through the number column (fn-cat-group-number, index-stobjs'
; fn-cnx-view-seq: one probe, one visibility test).  This book defines the
; two finders over the catalog and the two retrieval arms over them, and
; proves each equal to the served arm over the ARTICLES OF THE VIEW: the
; boundary theorem is fn-nntp-archive-command-cat-is-pinned, the whole
; pinned case split with the two retrieval arms reading the catalog.
;
; 7b rest (catalog-slice-7): the range arms read the catalog too.  OVER/XOVER
; of a range, LISTGROUP, GROUP, LIST COUNTS, HDR/XHDR and XPAT answer from
; index-stobjs' fn-cnx-view-range (one probe per number of the range clamped
; to the group's next number) and the number table (fn-scat-number-article),
; never a walk of the view's articles: KEYSTONE N
; (fn-scat-range-numbers-is-group-range-numbers) and KEYSTONE P
; (fn-scat-available-article-is-available) equate the two reads with the
; served folds over the view's articles, and each arm's -is-archive theorem
; is one unfolding over them.  The boundary theorem
; fn-nntp-archive-command-cat-is-pinned now covers the whole pinned case
; split with every retrieval and range arm reading the catalog.
;
; What is NOT here (the record names it): the lift through
; fn-nntp-command-pinned up to fn-served-dispatch-core; the host switch
; (step 8: the owner loads the catalog and hands the served connection its
; view as a count).  Until the host switch the archive stays the input of
; the configuration reads (groups, next numbers, the pinned withdrawal and
; verdict arms), so the -cat dispatcher takes it too and the equation is
; stated under archive = the view's articles.
(in-package "ACL2")
(include-book "catalog-number-index")
(include-book "nntp")
(include-book "nntp-range-indexed-invariants")
(include-book "nntp-list-counts")

;;; The finders.

;; The newest visible row carrying MSGID at view V, as an article; nil when
;; no visible row carries it.  fn-cat-view-last-visible reads the column
;; newest first (catalog-view.lisp keystone 4).
(defun fn-scat-msgid-article (msgid v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (natp v)
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))
                  :verify-guards nil))
  (let ((seq (fn-cat-view-last-visible (fn-cat-msgid-seqs msgid fn-cat) v fn-cat)))
    (if seq (fn-cat-row-article seq fn-arena fn-cat) nil)))

;; The row bound to number N in GROUP when it is visible at view V, as an
;; article; nil otherwise (books/catalog-number-index.lisp fn-cnx-view-seq).
(defun fn-scat-number-article (group n v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (natp v)
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))
                  :verify-guards nil))
  (let ((seq (fn-cnx-view-seq group n v fn-cat)))
    (if seq (fn-cat-row-article seq fn-arena fn-cat) nil)))

;; Both finders return nil or a row below the count: the guards of
;; fn-cat-row-article hold, and the finders run as written.
(defthm fn-scat-last-visible-in-range
  (implies (fn-cat-view-last-visible seqs v fn-cat)
           (and (natp (fn-cat-view-last-visible seqs v fn-cat))
                (< (fn-cat-view-last-visible seqs v fn-cat) (fn-cat-count fn-cat))))
  :hints (("Goal" :in-theory (enable fn-cat-view-last-visible))))

(defthm fn-scat-cnx-view-seq-in-range
  (implies (fn-cnx-view-seq group n v fn-cat)
           (and (natp (fn-cnx-view-seq group n v fn-cat))
                (< (fn-cnx-view-seq group n v fn-cat) (fn-cat-count fn-cat))))
  :hints (("Goal" :in-theory (enable fn-cnx-view-seq))))

(verify-guards fn-scat-msgid-article
  :hints (("Goal" :in-theory (disable fn-cat-handles-inp fn-cat-view-last-visible
                                      fn-cat-msgid-seqs fn-cat-p-is-held-listp
                                      fn-cat-count-is-len fn-cat-at-is-nth))))
(verify-guards fn-scat-number-article)

;;; KEYSTONE A: the Message-ID finder is the archive scan over the view.

(defthm fn-scat-msgid-article-is-find-article
  (equal (fn-scat-msgid-article msgid v fn-arena fn-cat)
         (fn-find-article msgid (fn-cat-view-articles v fn-arena fn-cat)))
  :hints (("Goal"
           :in-theory (e/d (fn-scat-msgid-article fn-cat-view-articles)
                           (fn-cat-row-article fn-cat-view-last-visible
                            fn-cat-view-find fn-cat-msgid-seqs fn-find-article
                            fn-cat-view-below))
           :use ((:instance fn-cat-view-find-article-is-walk (i (fn-cat-count fn-cat)))
                 (:instance fn-cat-view-find-is-msgid-column)))))

;;; KEYSTONE B: the number finder is the archive walk over the view.

;; Per row: the served walk reads a membership number (0 when the group is
;; absent), the catalog a bound number (nil when absent); for a positive N
;; and a named group they agree.
(defthm fn-scat-membership-number-is-number-in
  (implies (and group (posp n))
           (iff (equal (fn-nntp-membership-number group xs) n)
                (equal n (let ((pair (fn-cat-assoc group xs)))
                           (if (consp pair) (cdr pair) nil)))))
  :hints (("Goal" :in-theory (enable fn-nntp-membership-number fn-cat-assoc))))

(defthm fn-scat-find-group-number-is-number-find
  (implies (and group (posp n))
           (equal (fn-nntp-find-group-number
                   group n (fn-cat-view-below i v fn-arena fn-cat))
                  (let ((seq (fn-cat-view-number-find group n i v fn-cat)))
                    (if seq (fn-cat-row-article seq fn-arena fn-cat) nil))))
  :hints (("Goal" :induct (fn-cat-view-below i v fn-arena fn-cat)
           :in-theory (e/d (fn-nntp-find-group-number fn-held-number-in
                            fn-cat-view-number-find fn-cat-view-below)
                           (fn-cat-row-article fn-cat-visible-at
                            fn-nntp-membership-number fn-cat-assoc)))))

(defthm fn-scat-number-article-is-find-group-number
  (implies (and (fn-cnx-freshp fn-cat) group (posp n))
           (equal (fn-scat-number-article group n v fn-arena fn-cat)
                  (fn-nntp-find-group-number
                   group n (fn-cat-view-articles v fn-arena fn-cat))))
  :hints (("Goal"
           :in-theory (e/d (fn-scat-number-article fn-cat-view-articles)
                           (fn-cat-row-article fn-cnx-view-seq
                            fn-cat-view-number-find fn-nntp-find-group-number
                            fn-cat-view-below))
           :use ((:instance fn-cnx-view-seq-is-walk)
                 (:instance fn-scat-find-group-number-is-number-find
                            (i (fn-cat-count fn-cat)))))))

;;; The retrieval arms over the finders (books/nntp-responses.lisp
;;; fn-nntp-msgid-retrieval and fn-nntp-number-retrieval with the finder
;;; replaced; the renderer fn-nntp-article-response is shared).

(defun fn-nntp-msgid-retrieval-cat (session v kind token fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (natp v)
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))
                  :verify-guards nil))
  (if (not (fn-nntp-message-id-tokenp token))
      (fn-nntp-single session "501 syntax error")
    (let ((article (fn-scat-msgid-article (fn-nntp-token-string token)
                                          v fn-arena fn-cat)))
      (if (consp article)
          (fn-nntp-article-response
           session article (fn-nntp-msgid-local-number session article)
           kind nil nil fn-arena)
        (fn-nntp-single session "430 no article with that message-id")))))

(defun fn-nntp-number-retrieval-cat (session v kind token fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (natp v)
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))
                  :verify-guards nil))
  (if (not (fn-nntp-number-tokenp token))
      (fn-nntp-single session "501 syntax error")
    (let ((group (fn-nntp-session-group session))
          (number (fn-nntp-decimal-value token)))
      (if (null group)
          (fn-nntp-single session "412 no newsgroup selected")
        (let ((article (fn-scat-number-article group number v fn-arena fn-cat)))
          (if (consp article)
              (fn-nntp-article-response session article number kind t group fn-arena)
            (fn-nntp-single session "423 no article with that number")))))))

(verify-guards fn-nntp-msgid-retrieval-cat)
(verify-guards fn-nntp-number-retrieval-cat)

(defthm fn-nntp-msgid-retrieval-cat-is-scan
  (implies (equal (fn-state-articles archive)
                  (fn-cat-view-articles v fn-arena fn-cat))
           (equal (fn-nntp-msgid-retrieval-cat session v kind token fn-arena fn-cat)
                  (fn-nntp-msgid-retrieval session archive kind token fn-arena)))
  :hints (("Goal"
           :in-theory (e/d (fn-nntp-msgid-retrieval-cat fn-nntp-msgid-retrieval)
                           (fn-scat-msgid-article fn-find-article
                            fn-nntp-article-response fn-nntp-single
                            fn-nntp-msgid-local-number fn-cat-view-articles
                            fn-nntp-message-id-tokenp fn-nntp-token-string)))))

(local
 (defthm fn-scat-number-token-is-positive
   (implies (fn-nntp-number-tokenp token)
            (posp (fn-nntp-decimal-value token)))
   :hints (("Goal" :in-theory (e/d (fn-nntp-number-tokenp)
                                   (fn-nntp-decimal-tokenp fn-nntp-decimal-value))))))

(defthm fn-nntp-number-retrieval-cat-is-walk
  (implies (and (equal (fn-state-articles archive)
                       (fn-cat-view-articles v fn-arena fn-cat))
                (fn-cnx-freshp fn-cat))
           (equal (fn-nntp-number-retrieval-cat session v kind token fn-arena fn-cat)
                  (fn-nntp-number-retrieval session archive kind token fn-arena)))
  :hints (("Goal"
           :in-theory (e/d (fn-nntp-number-retrieval-cat fn-nntp-number-retrieval)
                           (fn-scat-number-article fn-nntp-find-group-number
                            fn-nntp-article-response fn-nntp-single
                            fn-cat-view-articles fn-nntp-number-tokenp
                            fn-nntp-decimal-value fn-nntp-session-group)))))

;;; ----------------------------------------------------------------------------
;;; 7b rest: the range arms (OVER/XOVER, LISTGROUP, GROUP, LIST COUNTS,
;;; HDR/XHDR, XPAT) read the catalog.  The served folds over the archive
;;; read two things per request: the numbers of a group in a range
;;; (fn-nntp-group-range-numbers: every article visited, then an insertion
;;; sort) and the article AT a number (fn-nntp-available-article: a walk per
;;; number).  Over the catalog the first is index-stobjs' fn-cnx-view-range
;;; (one probe per number of the clamped range) and the second one probe of
;;; the number table (fn-scat-number-article).  KEYSTONE N and KEYSTONE P
;;; below equate the two with the folds over the view's articles; every arm
;;; after them is the archive arm with those two reads replaced, and its
;;; keystone is one unfolding.
;;;
;;; Uniqueness: under fn-cnx-freshp a (group, number) pair is bound by one
;;; row, so the view's articles carry each number once (fn-scat-uniq).

(defun fn-scat-uniq (group articles)
  (declare (xargs :guard t))
  (if (consp articles)
      (and (let ((m (fn-nntp-membership-number
                     group (fn-article-memberships (car articles)))))
             (or (not (posp m))
                 (not (fn-nntp-find-group-number group m (cdr articles)))))
           (fn-scat-uniq group (cdr articles)))
    t))

(defun fn-scat-all-consp (l)
  (declare (xargs :guard t))
  (if (consp l) (and (consp (car l)) (fn-scat-all-consp (cdr l))) t))

(defthm fn-scat-available-without-found
  (implies (and (fn-scat-all-consp articles)
                (not (fn-nntp-find-group-number group n articles)))
           (not (fn-nntp-available-article group n articles)))
  :hints (("Goal" :induct (fn-nntp-available-article group n articles)
           :in-theory (enable fn-nntp-article-number fn-nntp-find-group-number
                              fn-nntp-available-article fn-nntp-membership-number))))

;; KEYSTONE P, archive half: over articles carrying each number once, the
;; available article at N is the one the number walk finds, when N is a
;; served number and its Message-ID is renderable.
(defthm fn-scat-available-is-found
  (implies (and (fn-scat-uniq group articles) (fn-scat-all-consp articles))
           (equal (fn-nntp-available-article group n articles)
                  (let ((a (fn-nntp-find-group-number group n articles)))
                    (if (and a (posp n) (<= n *fn-nntp-max-article-number*)
                             (fn-nntp-article-idp a))
                        a
                      nil))))
  :hints (("Goal" :induct (fn-scat-uniq group articles)
           :in-theory (enable fn-nntp-article-number fn-nntp-find-group-number
                              fn-nntp-available-article fn-nntp-membership-number))))

(defthm fn-scat-number-find-props
  (implies (and (fn-cat-view-number-find group n i v fn-cat) (natp i))
           (and (natp (fn-cat-view-number-find group n i v fn-cat))
                (< (fn-cat-view-number-find group n i v fn-cat) i)
                (equal (fn-held-number-in group (nth (fn-cat-view-number-find group n i v fn-cat) fn-cat))
                       n)))
  :hints (("Goal" :induct (fn-cat-view-number-find group n i v fn-cat)
           :in-theory (disable fn-cat-visible-at))))

;; No row below the one binding (GROUP . N) binds it (fn-cnx-number-seq-unique).
(defthm fn-scat-number-find-below-binder
  (implies (and (fn-cnx-freshp fn-cat) (natp j) (< j (len fn-cat)) n
                (equal (fn-held-number-in group (nth j fn-cat)) n))
           (not (fn-cat-view-number-find group n j v fn-cat)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-cat-view-number-find fn-cnx-freshp fn-scat-number-find-props
                               fn-held-number-in fn-cnx-number-seq-unique)
           :use ((:instance fn-scat-number-find-props (i j))
                 (:instance fn-cnx-number-seq-unique (g group) (j j) (c fn-cat))
                 (:instance fn-cnx-number-seq-unique (g group) (c fn-cat)
                            (j (fn-cat-view-number-find group n j v fn-cat)))))))

(defthm fn-scat-all-consp-of-view-below
  (fn-scat-all-consp (fn-cat-view-below i v fn-arena fn-cat))
  :hints (("Goal" :induct (fn-cat-view-below i v fn-arena fn-cat)
           :in-theory (e/d (fn-cat-row-article) (fn-cat-visible-at)))))

(defthm fn-scat-number-in-is-membership
  (implies (and group (posp (fn-nntp-membership-number group (fn-held-numbers h))))
           (equal (fn-held-number-in group h)
                  (fn-nntp-membership-number group (fn-held-numbers h))))
  :hints (("Goal" :use ((:instance fn-scat-membership-number-is-number-in
                                   (n (fn-nntp-membership-number group (fn-held-numbers h)))
                                   (xs (fn-held-numbers h))))
           :in-theory (e/d (fn-held-number-in) (fn-scat-membership-number-is-number-in)))))

(defthm fn-scat-uniq-step
  (implies (and (fn-cnx-freshp fn-cat) (posp i) (<= i (len fn-cat)) group
                (posp (fn-nntp-membership-number group (fn-held-numbers (nth (+ -1 i) fn-cat)))))
           (not (fn-nntp-find-group-number
                 group (fn-nntp-membership-number group (fn-held-numbers (nth (+ -1 i) fn-cat)))
                 (fn-cat-view-below (+ -1 i) v fn-arena fn-cat))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-cat-row-article fn-cat-visible-at fn-cnx-freshp
                               fn-held-number-in fn-nntp-find-group-number
                               fn-scat-find-group-number-is-number-find
                               fn-scat-number-find-below-binder
                               fn-cat-view-number-find fn-cat-view-below)
           :use ((:instance fn-scat-find-group-number-is-number-find
                            (n (fn-nntp-membership-number
                                group (fn-held-numbers (nth (+ -1 i) fn-cat))))
                            (i (+ -1 i)))
                 (:instance fn-scat-number-in-is-membership (h (nth (+ -1 i) fn-cat)))
                 (:instance fn-scat-number-find-below-binder
                            (j (+ -1 i))
                            (n (fn-nntp-membership-number
                                group (fn-held-numbers (nth (+ -1 i) fn-cat)))))))))

(defthm fn-scat-uniq-of-view-below
  (implies (and (fn-cnx-freshp fn-cat) (natp i) (<= i (len fn-cat)) group)
           (fn-scat-uniq group (fn-cat-view-below i v fn-arena fn-cat)))
  :hints (("Goal" :induct (fn-cat-view-below i v fn-arena fn-cat)
           :in-theory (disable fn-cat-visible-at fn-cnx-freshp
                               fn-held-number-in fn-nntp-find-group-number
                               fn-scat-find-group-number-is-number-find
                               fn-cat-view-number-find))))

(defun fn-scat-available-article (group n v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (natp v)
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))))
  (if (and (posp n) (<= n *fn-nntp-max-article-number*))
      (let ((article (fn-scat-number-article group n v fn-arena fn-cat)))
        (if (and article (fn-nntp-article-idp article)) article nil))
    nil))

(defthm fn-scat-available-article-is-available
  (implies (and (fn-cnx-freshp fn-cat) group)
           (equal (fn-scat-available-article group n v fn-arena fn-cat)
                  (fn-nntp-available-article group n (fn-cat-view-articles v fn-arena fn-cat))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-cat-view-articles)
                           (fn-scat-number-article fn-nntp-available-article
                            fn-nntp-find-group-number fn-cat-view-below fn-cnx-freshp
                            fn-scat-number-article-is-find-group-number
                            fn-nntp-article-idp))
           :cases ((posp n))
           :use ((:instance fn-scat-number-article-is-find-group-number)))))

;; Two strictly increasing lists with the same members are equal; the
;; witness is the first place they differ (fn-scat-diff).

(defun fn-scat-strictp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (rationalp (car xs))
           (if (consp (cdr xs))
               (and (rationalp (car (cdr xs)))
                    (< (car xs) (car (cdr xs)))
                    (fn-scat-strictp (cdr xs)))
             (null (cdr xs))))
    (null xs)))

(defthm fn-scat-strict-car-below-members
  (implies (and (fn-scat-strictp xs) (member-equal x (cdr xs)))
           (< (car xs) x))
  :rule-classes nil
  :hints (("Goal" :induct (fn-scat-strictp xs))))

(defun fn-scat-diff (xs ys)
  (declare (xargs :guard t))
  (if (and (consp xs) (consp ys))
      (if (equal (car xs) (car ys))
          (fn-scat-diff (cdr xs) (cdr ys))
        (if (and (rationalp (car xs)) (rationalp (car ys)) (< (car xs) (car ys)))
            (car xs)
          (car ys)))
    (if (consp xs) (car xs) (if (consp ys) (car ys) nil))))

(defthm fn-scat-diff-member
  (implies (and (fn-scat-strictp xs) (fn-scat-strictp ys) (not (equal xs ys)))
           (or (member-equal (fn-scat-diff xs ys) xs)
               (member-equal (fn-scat-diff xs ys) ys)))
  :rule-classes nil
  :hints (("Goal" :induct (fn-scat-diff xs ys))))

(defthm fn-scat-strict-lists-equal
  (implies (and (fn-scat-strictp xs) (fn-scat-strictp ys)
                (iff (member-equal (fn-scat-diff xs ys) xs)
                     (member-equal (fn-scat-diff xs ys) ys)))
           (equal xs ys))
  :rule-classes nil
  :hints (("Goal" :induct (fn-scat-diff xs ys))
          ("Subgoal *1/1" :use ((:instance fn-scat-diff-member (xs (cdr xs)) (ys (cdr ys)))
                                (:instance fn-scat-strict-car-below-members
                                           (x (fn-scat-diff (cdr xs) (cdr ys))))
                                (:instance fn-scat-strict-car-below-members
                                           (xs ys) (x (fn-scat-diff (cdr xs) (cdr ys))))))
          ("Subgoal *1/2" :use ((:instance fn-scat-strict-car-below-members (x (car ys)))
                                (:instance fn-scat-strict-car-below-members (xs ys) (x (car xs)))))))

;; The ascending filter k = low .. high of the numbers with an available
;; article: what both sides are shown equal to.

(defun fn-scat-kf (group k top articles)
  (declare (xargs :measure (nfix (- (+ 1 (nfix top)) (nfix k)))))
  (if (and (natp k) (natp top) (<= k top))
      (if (fn-nntp-available-article group k articles)
          (cons k (fn-scat-kf group (+ 1 k) top articles))
        (fn-scat-kf group (+ 1 k) top articles))
    nil))

(defthm fn-scat-available-posp
  (implies (fn-nntp-available-article group n articles) (posp n))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-nntp-available-article))))

(defthm fn-scat-member-kf
  (iff (member-equal x (fn-scat-kf group k top articles))
       (and (natp x) (natp k) (natp top) (<= k x) (<= x top)
            (fn-nntp-available-article group x articles)))
  :hints (("Goal" :induct (fn-scat-kf group k top articles)
           :in-theory (disable fn-nntp-available-article))))

(defthm fn-scat-kf-car-bound
  (implies (consp (fn-scat-kf group k top articles))
           (<= k (car (fn-scat-kf group k top articles))))
  :rule-classes (:linear :rewrite)
  :hints (("Goal" :use ((:instance fn-scat-member-kf (x (car (fn-scat-kf group k top articles)))))
           :in-theory (disable fn-scat-member-kf fn-scat-kf))))

(defthm fn-scat-strictp-kf
  (fn-scat-strictp (fn-scat-kf group k top articles))
  :hints (("Goal" :induct (fn-scat-kf group k top articles)
           :in-theory (disable fn-nntp-available-article))
          ("Subgoal *1/1" :use ((:instance fn-scat-kf-car-bound (k (+ 1 k)))))))

(defthm fn-scat-all-consp-car
  (implies (and (fn-scat-all-consp l) (consp l))
           (and (consp (car l)) (fn-scat-all-consp (cdr l))))
  :rule-classes :forward-chaining)

(defthm fn-scat-article-number-of-nil
  (equal (fn-nntp-article-number group nil) 0)
  :hints (("Goal" :in-theory (enable fn-nntp-article-number fn-nntp-membership-number
                                     fn-article-memberships))))

(defthm fn-scat-member-gr
  (implies (fn-scat-all-consp articles)
           (iff (member-equal x (fn-nntp-group-range-numbers group low high articles))
                (and (posp x) (<= low x) (<= x high)
                     (fn-nntp-available-article group x articles))))
  :hints (("Goal" :induct (fn-nntp-group-range-numbers group low high articles)
           :expand ((fn-scat-all-consp articles))
           :in-theory (e/d (fn-nntp-group-range-numbers fn-nntp-available-article)
                           (fn-scat-available-is-found fn-nntp-article-number)))))

(defthm fn-scat-no-dups-insert
  (implies (and (no-duplicatesp-equal l) (not (member-equal n l)))
           (no-duplicatesp-equal (fn-nntp-insert-number n l)))
  :hints (("Goal" :in-theory (enable fn-nntp-insert-number))))

(defthm fn-scat-gr-no-dups
  (implies (and (fn-scat-uniq group articles) (fn-scat-all-consp articles))
           (no-duplicatesp-equal (fn-nntp-group-range-numbers group low high articles)))
  :hints (("Goal" :induct (fn-nntp-group-range-numbers group low high articles)
           :in-theory (e/d (fn-nntp-group-range-numbers fn-nntp-article-number)
                           (fn-nntp-available-article fn-nntp-find-group-number
                            fn-nntp-insert-number)))
          ("Subgoal *1/2" :expand ((fn-scat-all-consp articles) (fn-scat-uniq group articles))
                          :use ((:instance fn-scat-available-without-found
                                           (n (fn-nntp-article-number group (car articles)))
                                           (articles (cdr articles)))))))

(defthm fn-scat-strictp-of-ordered
  (implies (and (fn-nntp-orderedp xs) (no-duplicatesp-equal xs)
                (rational-listp xs))
           (fn-scat-strictp xs))
  :hints (("Goal" :induct (fn-nntp-orderedp xs)
           :in-theory (enable fn-nntp-orderedp))))

(defthm fn-scat-gr-rational-listp
  (rational-listp (fn-nntp-group-range-numbers group low high articles))
  :hints (("Goal" :in-theory (enable fn-nntp-group-range-numbers fn-nntp-insert-number))))

(defthm fn-scat-gr-is-kf
  (implies (and (fn-scat-uniq group articles) (fn-scat-all-consp articles)
                (natp low) (natp high))
           (equal (fn-nntp-group-range-numbers group low high articles)
                  (fn-scat-kf group low high articles)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-scat-strict-lists-equal
                            (xs (fn-nntp-group-range-numbers group low high articles))
                            (ys (fn-scat-kf group low high articles))))
           :in-theory (disable fn-nntp-group-range-numbers fn-scat-kf
                               fn-nntp-available-article fn-scat-available-is-found))))

;; The catalog side: the numbers the clamped range probe names, each kept
;; when the served fold would keep it (a positive number within RFC 3977's
;; bound, a renderable Message-ID: fn-nntp-article-number's three tests, the
;; last read from the row's Message-ID without materializing its payload).

(defun fn-scat-msgid-idp (text)
  (declare (xargs :guard t))
  (and (stringp text)
       (<= (length text) *fn-nntp-max-message-id-octets*)
       (fn-nntp-message-id-tokenp (fn-nntp-string-octets text))))

(defthm fn-scat-article-idp-is-msgid-idp
  (equal (fn-nntp-article-idp article)
         (fn-scat-msgid-idp (fn-article-msgid article)))
  :hints (("Goal" :in-theory (enable fn-nntp-article-idp))))

(defun fn-scat-range-keep (group seqs fn-cat)
  (declare (xargs :stobjs fn-cat :guard t
                  :guard-hints (("Goal" :in-theory (disable fn-cat-p-is-held-listp fn-cat-count-is-len
                                                            fn-cat-at-is-nth)))))
  (if (consp seqs)
      (let ((s (car seqs)))
        (if (and (natp s) (< s (fn-cat-count fn-cat)))
            (let* ((h (fn-cat-at s fn-cat))
                   (n (fn-held-number-in group h)))
              (if (and (posp n) (<= n *fn-nntp-max-article-number*)
                       (fn-scat-msgid-idp (fn-record-msgid h)))
                  (cons n (fn-scat-range-keep group (cdr seqs) fn-cat))
                (fn-scat-range-keep group (cdr seqs) fn-cat)))
          (fn-scat-range-keep group (cdr seqs) fn-cat)))
    nil))

(defun fn-scat-range-numbers (group low high v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (and (natp low) (natp high) (natp v))))
  (fn-scat-range-keep group (fn-cnx-view-range group low high v fn-cat) fn-cat))

(defthm fn-scat-keep-step
  (implies (and (fn-cnx-freshp fn-cat) group (natp k))
           (iff (fn-nntp-available-article group k (fn-cat-view-articles v fn-arena fn-cat))
                (let ((s (fn-cat-view-number-find group k (len fn-cat) v fn-cat)))
                  (and s (posp k) (<= k *fn-nntp-max-article-number*)
                       (fn-scat-msgid-idp (fn-record-msgid (nth s fn-cat)))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-scat-available-article fn-scat-number-article)
                           (fn-cat-view-articles fn-cnx-freshp fn-cat-view-number-find
                            fn-cnx-view-seq fn-held-number-in fn-scat-msgid-idp
                            fn-nntp-available-article fn-scat-available-article-is-available
                            fn-scat-number-article-is-find-group-number))
           :use ((:instance fn-scat-available-article-is-available (n k))
                 (:instance fn-cnx-view-seq-is-walk (n k))))))

(defthm fn-scat-range-keep-of-walk
  (implies (and (fn-cnx-freshp fn-cat) group)
           (equal (fn-scat-range-keep group (fn-cnx-walk-range group k top v fn-cat) fn-cat)
                  (fn-scat-kf group k top (fn-cat-view-articles v fn-arena fn-cat))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-cnx-walk-range group k top v fn-cat)
           :in-theory (disable fn-cat-view-articles fn-cnx-freshp fn-cat-view-number-find
                               fn-held-number-in fn-scat-msgid-idp
                               fn-nntp-available-article))))

(defthm fn-scat-range-numbers-is-group-range-numbers
  (implies (and (fn-cnx-freshp fn-cat) group (natp low) (natp high))
           (equal (fn-scat-range-numbers group low high v fn-cat)
                  (fn-nntp-group-range-numbers group low high
                                               (fn-cat-view-articles v fn-arena fn-cat))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-cat-view-articles)
                           (fn-cnx-view-range fn-cnx-walk-range fn-cnx-freshp
                            fn-nntp-group-range-numbers fn-scat-range-keep
                            fn-cat-view-below))
           :use ((:instance fn-cnx-view-range-is-walk)
                 (:instance fn-scat-range-keep-of-walk (k low) (top high))
                 (:instance fn-scat-gr-is-kf
                            (articles (fn-cat-view-below (len fn-cat) v fn-arena fn-cat)))))))

(in-theory (disable fn-scat-gr-is-kf))

;;; OVER/XOVER of a range.

(defmacro fn-scat-guard ()
  '(and (natp v) (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat)))

(defun fn-nov-lines-for-numbers-cat (group numbers v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard (fn-scat-guard)))
  (if (consp numbers)
      (let* ((number (car numbers))
             (article (fn-scat-available-article group number v fn-arena fn-cat))
             (over (if (and (consp article)
                            (not (fn-rcl-tombstonep (fn-article-payload article))))
                       (fn-nov-overview article fn-arena)
                     (list :error))))
        (if (fn-nov-okp over)
            (cons (fn-nov-line number over)
                  (fn-nov-lines-for-numbers-cat group (cdr numbers) v fn-arena fn-cat))
          (fn-nov-lines-for-numbers-cat group (cdr numbers) v fn-arena fn-cat)))
    nil))

(defthm fn-nov-lines-for-numbers-cat-is-archive
  (implies (and (fn-cnx-freshp fn-cat) group)
           (equal (fn-nov-lines-for-numbers-cat group numbers v fn-arena fn-cat)
                  (fn-nov-lines-for-numbers group numbers
                                            (fn-cat-view-articles v fn-arena fn-cat) fn-arena)))
  :hints (("Goal" :induct (fn-nov-lines-for-numbers-cat group numbers v fn-arena fn-cat)
           :in-theory (e/d (fn-nov-lines-for-numbers)
                           (fn-scat-available-article fn-cat-view-articles
                            fn-nntp-available-article fn-nov-overview fn-nov-okp
                            fn-nov-line fn-rcl-tombstonep fn-cnx-freshp)))))

(defun fn-nntp-over-range-cat (session v token legacyp fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard (fn-scat-guard)))
  (let ((group (fn-nntp-session-group session))
        (range (fn-nntp-parse-range token)))
    (if (null group)
        (fn-nntp-single session "412 no newsgroup selected")
      (let* ((numbers (fn-scat-range-numbers
                       group (nfix (fn-nntp-range-low range))
                       (nfix (fn-nntp-range-high range)) v fn-cat))
             (lines (fn-nov-lines-for-numbers-cat group numbers v fn-arena fn-cat)))
        (if (consp lines)
            (fn-nntp-multi session "224 overview information follows" lines)
          (fn-nntp-single
           session (if legacyp "420 no article(s) selected"
                     "423 no articles in that range")))))))

(defthm fn-nntp-over-range-cat-is-archive
  (implies (and (fn-cnx-freshp fn-cat)
                (equal (fn-state-articles archive) (fn-cat-view-articles v fn-arena fn-cat))
                (natp (fn-nntp-range-low (fn-nntp-parse-range token)))
                (natp (fn-nntp-range-high (fn-nntp-parse-range token))))
           (equal (fn-nntp-over-range-cat session v token legacyp fn-arena fn-cat)
                  (if legacyp
                      (fn-nntp-xover-range session archive token fn-arena)
                    (fn-nntp-over-range session archive token fn-arena))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nntp-over-range fn-nntp-xover-range)
                           (fn-scat-range-numbers fn-nov-lines-for-numbers-cat
                            fn-nov-lines-for-numbers fn-nntp-group-range-numbers
                            fn-cat-view-articles fn-cnx-freshp fn-nntp-parse-range
                            fn-nntp-multi fn-nntp-single)))))

;;; GROUP / LISTGROUP / LIST COUNTS: count, low and high are the length,
;;; first and last of the group's numbers (the served fold's
;;; fn-nntp-group-count / -low / -high, one pass each over every article).

(defun fn-scat-last-number (l)
  (declare (xargs :guard t))
  (if (consp l) (if (consp (cdr l)) (fn-scat-last-number (cdr l)) (car l)) 0))

(defthm fn-scat-len-insert
  (equal (len (fn-nntp-insert-number n l)) (+ 1 (len l)))
  :hints (("Goal" :in-theory (enable fn-nntp-insert-number))))

(defthm fn-scat-car-insert
  (implies (and (rationalp n) (or (not (consp l)) (rationalp (car l))))
           (equal (car (fn-nntp-insert-number n l))
                  (if (and (consp l) (<= (car l) n)) (car l) n)))
  :hints (("Goal" :in-theory (enable fn-nntp-insert-number))))

(defthm fn-scat-consp-insert
  (consp (fn-nntp-insert-number n l))
  :hints (("Goal" :in-theory (enable fn-nntp-insert-number))))

(defthm fn-scat-gr-members-posp
  (implies (member-equal x (fn-nntp-group-range-numbers group low high articles))
           (posp x))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-nntp-group-range-numbers))))

(defthm fn-scat-gr-car-posp
  (implies (consp (fn-nntp-group-range-numbers group low high articles))
           (posp (car (fn-nntp-group-range-numbers group low high articles))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :use ((:instance fn-scat-gr-members-posp
                                   (x (car (fn-nntp-group-range-numbers group low high articles)))))
           :in-theory (disable fn-nntp-group-range-numbers))))

(defthm fn-scat-group-low-is-car
  (equal (fn-nntp-group-low group articles)
         (let ((l (fn-nntp-group-range-numbers group 1 *fn-nntp-max-article-number* articles)))
           (if (consp l) (car l) 0)))
  :hints (("Goal" :induct (fn-nntp-group-low group articles)
           :in-theory (enable fn-nntp-group-low fn-nntp-group-range-numbers))))

(defthm fn-scat-car-le-last
  (implies (and (fn-nntp-orderedp l) (rational-listp l) (consp l))
           (<= (car l) (fn-scat-last-number l)))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-nntp-orderedp l)
           :in-theory (enable fn-nntp-orderedp))))

(defthm fn-scat-last-insert
  (implies (and (fn-nntp-orderedp l) (rational-listp l) (rationalp n))
           (equal (fn-scat-last-number (fn-nntp-insert-number n l))
                  (if (and (consp l) (< n (fn-scat-last-number l))) (fn-scat-last-number l) n)))
  :hints (("Goal" :induct (fn-nntp-insert-number n l)
           :in-theory (enable fn-nntp-insert-number fn-nntp-orderedp))))

(defthm fn-scat-group-high-is-last
  (equal (fn-nntp-group-high group articles)
         (fn-scat-last-number
          (fn-nntp-group-range-numbers group 1 *fn-nntp-max-article-number* articles)))
  :hints (("Goal" :induct (fn-nntp-group-high group articles)
           :in-theory (enable fn-nntp-group-high fn-nntp-group-range-numbers))))

(defun fn-scat-group-summary (archive group v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v)))
  (let ((l (fn-scat-range-numbers group 1 *fn-nntp-max-article-number* v fn-cat)))
    (if (consp l)
        (list (len l) (car l) (fn-scat-last-number l))
      (let ((watermark (fn-next-number group (fn-state-nexts archive))))
        (list 0 watermark (if (posp watermark) (- watermark 1) 0))))))

(defthm fn-scat-group-summary-is-archive
  (implies (and (fn-cnx-freshp fn-cat) group
                (equal (fn-state-articles archive) (fn-cat-view-articles v fn-arena fn-cat)))
           (equal (fn-scat-group-summary archive group v fn-cat)
                  (fn-nntp-group-summary archive group)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nntp-group-summary)
                           (fn-scat-range-numbers fn-nntp-group-range-numbers
                            fn-cat-view-articles fn-cnx-freshp fn-next-number)))))

(defun fn-scat-group-initial (archive group v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v)))
  (let ((summary (fn-scat-group-summary archive group v fn-cat)))
    (fn-nntp-append-pieces
     (list (fn-nntp-string-octets "211 ")
           (fn-nntp-decimal-field (fn-nntp-summary-count summary)) '(32)
           (fn-nntp-decimal-field (fn-nntp-summary-low summary)) '(32)
           (fn-nntp-decimal-field (fn-nntp-summary-high summary)) '(32)
           (fn-nntp-string-octets group)))))

(defthm fn-scat-group-initial-is-archive
  (implies (and (fn-cnx-freshp fn-cat) group
                (equal (fn-state-articles archive) (fn-cat-view-articles v fn-arena fn-cat)))
           (equal (fn-scat-group-initial archive group v fn-cat)
                  (fn-nntp-group-initial archive group)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nntp-group-initial)
                           (fn-scat-group-summary fn-nntp-group-summary
                            fn-cat-view-articles fn-cnx-freshp)))))

(defun fn-scat-group-low (group v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v)))
  (let ((l (fn-scat-range-numbers group 1 *fn-nntp-max-article-number* v fn-cat)))
    (if (consp l) (car l) 0)))

(defthm fn-scat-group-low-is-archive
  (implies (and (fn-cnx-freshp fn-cat) group)
           (equal (fn-scat-group-low group v fn-cat)
                  (fn-nntp-group-low group (fn-cat-view-articles v fn-arena fn-cat))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-scat-range-numbers fn-nntp-group-range-numbers
                               fn-cat-view-articles fn-cnx-freshp))))

(defun fn-nntp-group-result-cat (session archive group v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v)))
  (if (mbe :logic (member-equal group (fn-state-groups archive))
           :exec (fn-ag-member group (fn-state-groups archive)))
      (let* ((low (fn-scat-group-low group v fn-cat))
             (current (if (posp low) low nil))
             (next-session (fn-nntp-set-cursor session group current)))
        (fn-nntp-make-result
         next-session
         (list (fn-nntp-reply-effect
                (fn-nntp-crlf (fn-scat-group-initial archive group v fn-cat))))))
    (fn-nntp-single session "411 no such newsgroup")))

(defthm fn-nntp-group-result-cat-is-archive
  (implies (and (fn-cnx-freshp fn-cat) group
                (equal (fn-state-articles archive) (fn-cat-view-articles v fn-arena fn-cat)))
           (equal (fn-nntp-group-result-cat session archive group v fn-cat)
                  (fn-nntp-group-result session archive group)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nntp-group-result)
                           (fn-scat-group-low fn-scat-group-initial fn-nntp-group-initial
                            fn-nntp-group-low fn-cat-view-articles fn-cnx-freshp
                            fn-nntp-set-cursor fn-nntp-make-result fn-nntp-reply-effect
                            fn-nntp-crlf fn-nntp-single)))))

(defun fn-nntp-listgroup-result-cat (session archive group range v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v)))
  (if (mbe :logic (member-equal group (fn-state-groups archive))
           :exec (fn-ag-member group (fn-state-groups archive)))
      (let* ((low (fn-scat-group-low group v fn-cat))
             (current (if (posp low) low nil))
             (next-session (fn-nntp-set-cursor session group current))
             (shown (fn-scat-range-numbers group (nfix (fn-nntp-range-low range))
                                           (nfix (fn-nntp-range-high range)) v fn-cat)))
        (fn-nntp-multi-octets next-session
                              (append (fn-scat-group-initial archive group v fn-cat)
                                      (fn-nntp-string-octets " list follows"))
                              (fn-nntp-number-lines shown)))
    (fn-nntp-single session "411 no such newsgroup")))

(defthm fn-nntp-listgroup-result-cat-is-archive
  (implies (and (fn-cnx-freshp fn-cat) group
                (natp (fn-nntp-range-low range)) (natp (fn-nntp-range-high range))
                (equal (fn-state-articles archive) (fn-cat-view-articles v fn-arena fn-cat)))
           (equal (fn-nntp-listgroup-result-cat session archive group range v fn-cat)
                  (fn-nntp-listgroup-result session archive group range)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nntp-listgroup-result fn-nntp-listgroup-initial)
                           (fn-scat-group-low fn-scat-group-initial fn-nntp-group-initial
                            fn-nntp-group-low fn-cat-view-articles fn-cnx-freshp
                            fn-scat-range-numbers fn-nntp-group-range-numbers
                            fn-nntp-set-cursor fn-nntp-multi-octets fn-nntp-number-lines
                            fn-nntp-single)))))

(defun fn-nntp-listgroup-command-cat (session archive args v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v)))
  (let ((all-range (list :ok 1 2147483647)))
    (if (null args)
        (let ((group (fn-nntp-session-group session)))
          (if (null group)
              (fn-nntp-single session "412 no newsgroup selected")
            (if (mbe :logic (member-equal group (fn-state-groups archive))
                     :exec (fn-ag-member group (fn-state-groups archive)))
                (fn-nntp-listgroup-result-cat session archive group all-range v fn-cat)
              (fn-nntp-single session "412 no newsgroup selected"))))
      (if (and (consp args) (null (cdr args))
               (fn-nntp-printable-tokenp (car args)))
          (fn-nntp-listgroup-result-cat session archive
                                        (fn-nntp-token-string (car args)) all-range v fn-cat)
        (if (and (consp args) (consp (cdr args)) (null (cdr (cdr args)))
                 (fn-nntp-printable-tokenp (car args)))
            (let ((range (fn-nntp-parse-range (car (cdr args)))))
              (if (fn-nntp-range-okp range)
                  (fn-nntp-listgroup-result-cat session archive
                                                (fn-nntp-token-string (car args)) range v fn-cat)
                (fn-nntp-single session "501 syntax error")))
          (fn-nntp-single session "501 syntax error"))))))

(defthm fn-nntp-listgroup-command-cat-is-archive
  (implies (and (fn-cnx-freshp fn-cat)
                (equal (fn-state-articles archive) (fn-cat-view-articles v fn-arena fn-cat)))
           (equal (fn-nntp-listgroup-command-cat session archive args v fn-cat)
                  (fn-nntp-listgroup-command session archive args)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nntp-listgroup-command)
                           (fn-nntp-listgroup-result-cat fn-nntp-listgroup-result
                            fn-cat-view-articles fn-cnx-freshp fn-nntp-parse-range
                            fn-nntp-single fn-nntp-printable-tokenp)))))

(defun fn-scat-counts-lines (archive groups v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v)))
  (if (consp groups)
      (cons (fn-nntp-counts-summary-line
             (car groups) (fn-scat-group-summary archive (car groups) v fn-cat))
            (fn-scat-counts-lines archive (cdr groups) v fn-cat))
    nil))

(defthm fn-scat-counts-lines-is-archive
  (implies (and (fn-cnx-freshp fn-cat) (not (member-equal nil groups))
                (equal (fn-state-articles archive) (fn-cat-view-articles v fn-arena fn-cat)))
           (equal (fn-scat-counts-lines archive groups v fn-cat)
                  (fn-nntp-counts-lines archive groups)))
  :hints (("Goal" :induct (fn-scat-counts-lines archive groups v fn-cat)
           :in-theory (e/d (fn-nntp-counts-lines fn-nntp-counts-line)
                           (fn-scat-group-summary fn-nntp-group-summary
                            fn-cat-view-articles fn-cnx-freshp
                            fn-nntp-counts-summary-line)))))

(defun fn-nntp-list-counts-command-cat (session archive args v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v)))
  (if (null args)
      (fn-nntp-multi session "215 list of newsgroups follows"
                     (fn-scat-counts-lines archive (fn-state-groups archive) v fn-cat))
    (if (and (consp args) (null (cdr args)))
        (let ((parsed (fn-wildmat-parse (car args))))
          (if (fn-wildmat-result-okp parsed)
              (fn-nntp-multi session "215 list of newsgroups follows"
                             (fn-scat-counts-lines
                              archive
                              (fn-nntp-filter-groups-by-wildmat
                               (fn-wildmat-result-value parsed) (fn-state-groups archive))
                              v fn-cat))
            (fn-nntp-single session "501 syntax error")))
      (fn-nntp-single session "501 syntax error"))))

(defthm fn-scat-safe-group-list-has-no-nil
  (implies (fn-nntp-safe-group-listp groups)
           (not (member-equal nil groups)))
  :hints (("Goal" :in-theory (enable fn-nntp-safe-group-listp fn-nntp-safe-group-namep))))

(defthm fn-scat-filter-keeps-safe
  (implies (fn-nntp-safe-group-listp groups)
           (fn-nntp-safe-group-listp
            (fn-nntp-filter-groups-by-wildmat patterns groups)))
  :hints (("Goal" :induct (fn-nntp-filter-groups-by-wildmat patterns groups)
           :in-theory (e/d (fn-nntp-filter-groups-by-wildmat
                            fn-nntp-safe-group-listp)
                           (fn-nntp-group-matches-parsed-wildmatp
                            fn-nntp-safe-group-namep)))))

(defthm fn-nntp-list-counts-command-cat-is-archive
  (implies (and (fn-cnx-freshp fn-cat) (fn-nntp-projectionp archive)
                (equal (fn-state-articles archive) (fn-cat-view-articles v fn-arena fn-cat)))
           (equal (fn-nntp-list-counts-command-cat session archive args v fn-cat)
                  (fn-nntp-list-counts-command session archive args)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nntp-list-counts-command fn-nntp-list-counts fn-nntp-projectionp)
                           (fn-scat-counts-lines fn-nntp-counts-lines
                            fn-cat-view-articles fn-cnx-freshp fn-statep
                            fn-wildmat-parse fn-nntp-filter-groups-by-wildmat
                            fn-nntp-multi fn-nntp-single)))))

;;; HDR/XHDR (RFC 3977 section 8.5, RFC 2980 section 2.6): the three forms,
;;; the current article and the range through the number table, the
;;; Message-ID form through keystone A's finder.

(defun fn-nntp-hdr-lines-for-numbers-cat (field group numbers v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard (fn-scat-guard) :verify-guards nil))
  (if (consp numbers)
      (let* ((number (car numbers))
             (article (fn-scat-available-article group number v fn-arena fn-cat))
             (content (if (consp article)
                          (fn-nntp-hdr-content field article fn-arena)
                        (list :error))))
        (if (fn-nntp-hdr-okp content)
            (cons (fn-nntp-hdr-line (fn-nntp-decimal-field number)
                                    (fn-nntp-hdr-octets content))
                  (fn-nntp-hdr-lines-for-numbers-cat field group (cdr numbers) v fn-arena fn-cat))
          (fn-nntp-hdr-lines-for-numbers-cat field group (cdr numbers) v fn-arena fn-cat)))
    nil))

(defthm fn-nntp-hdr-lines-for-numbers-cat-is-archive
  (implies (and (fn-cnx-freshp fn-cat) group)
           (equal (fn-nntp-hdr-lines-for-numbers-cat field group numbers v fn-arena fn-cat)
                  (fn-nntp-hdr-lines-for-numbers field group numbers
                                                 (fn-cat-view-articles v fn-arena fn-cat) fn-arena)))
  :hints (("Goal" :induct (fn-nntp-hdr-lines-for-numbers-cat field group numbers v fn-arena fn-cat)
           :in-theory (e/d (fn-nntp-hdr-lines-for-numbers)
                           (fn-scat-available-article fn-cat-view-articles
                            fn-nntp-available-article fn-nntp-hdr-content fn-nntp-hdr-okp
                            fn-nntp-hdr-line fn-nntp-hdr-octets fn-nntp-decimal-field
                            fn-cnx-freshp)))))

(defun fn-nntp-hdr-command-cat (session args v legacyp fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard (fn-scat-guard) :verify-guards nil))
  (if (not (and (consp args) (fn-nntp-hdr-fieldp (car args))))
        (fn-nntp-single session "501 syntax error")
      (let ((field (car args)) (rest (cdr args))
            (group (fn-nntp-session-group session)))
        (if (null rest)
            (let ((current (fn-nntp-session-current session)))
              (if (null group)
                  (fn-nntp-single session "412 no newsgroup selected")
                (if (null current)
                    (fn-nntp-single session "420 no current article")
                  (let ((article (fn-scat-available-article group current v fn-arena fn-cat)))
                    (if (not (consp article))
                        (fn-nntp-single session "420 no current article")
                      (let ((content (fn-nntp-hdr-content field article fn-arena)))
                        (if (fn-nntp-hdr-okp content)
                            (fn-nntp-multi
                             session (fn-nntp-hdr-initial legacyp)
                             (list (fn-nntp-hdr-line (fn-nntp-decimal-field current)
                                                     (fn-nntp-hdr-octets content))))
                          (fn-nntp-single
                           session "503 stored article framing unavailable"))))))))
          (if (and (consp rest) (null (cdr rest)))
              (let ((token (car rest)))
                (if (fn-nntp-range-okp (fn-nntp-parse-range token))
                    (if (null group)
                        (fn-nntp-single session "412 no newsgroup selected")
                      (let* ((range (fn-nntp-parse-range token))
                             (numbers (fn-scat-range-numbers
                                       group (nfix (fn-nntp-range-low range))
                                       (nfix (fn-nntp-range-high range)) v fn-cat))
                             (lines (fn-nntp-hdr-lines-for-numbers-cat
                                     field group numbers v fn-arena fn-cat)))
                        (if (consp lines)
                            (fn-nntp-multi session (fn-nntp-hdr-initial legacyp) lines)
                          (if legacyp
                              (fn-nntp-single session "420 no article(s) selected")
                            (fn-nntp-single session "423 no articles in that range")))))
                  (if (fn-nntp-message-id-tokenp token)
                      (let ((article (fn-scat-msgid-article (fn-nntp-token-string token)
                                                            v fn-arena fn-cat)))
                        (if (not (consp article))
                            (fn-nntp-single session "430 no article with that message-id")
                          (let ((content (fn-nntp-hdr-content field article fn-arena)))
                            (if (fn-nntp-hdr-okp content)
                                (fn-nntp-multi
                                 session (fn-nntp-hdr-initial legacyp)
                                 (list (fn-nntp-hdr-line (if legacyp
                                                             (fn-nov-scrub token)
                                                           (fn-nntp-decimal-field 0))
                                                         (fn-nntp-hdr-octets content))))
                              (fn-nntp-single session "503 stored article framing unavailable")))))
                    (fn-nntp-single session "501 syntax error"))))
            (fn-nntp-single session "501 syntax error"))))))

(defthm fn-nntp-hdr-command-cat-is-archive
  (implies (and (fn-cnx-freshp fn-cat)
                (equal (fn-state-articles archive) (fn-cat-view-articles v fn-arena fn-cat)))
           (equal (fn-nntp-hdr-command-cat session args v legacyp fn-arena fn-cat)
                  (fn-nntp-hdr-command session archive args legacyp fn-arena)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-nntp-parse-range-ok-has-natural-bounds (token (cadr args))))
           :in-theory (e/d (fn-nntp-hdr-command fn-nntp-hdr-current fn-nntp-hdr-range
                            fn-nntp-hdr-msgid)
                           (fn-scat-available-article fn-scat-range-numbers
                            fn-nntp-hdr-lines-for-numbers-cat fn-nntp-hdr-lines-for-numbers
                            fn-scat-msgid-article fn-find-article
                            fn-nntp-group-range-numbers fn-nntp-available-article
                            fn-cat-view-articles fn-cnx-freshp fn-nntp-parse-range
                            fn-nntp-hdr-content fn-nntp-hdr-okp fn-nntp-hdr-line
                            fn-nntp-hdr-octets fn-nntp-multi fn-nntp-single
                            fn-nntp-hdr-fieldp fn-nntp-message-id-tokenp
                            fn-nntp-range-okp fn-nntp-parse-range-ok-has-natural-bounds)))))

;;; XPAT (RFC 2980 section 2.9).

(verify-guards fn-nntp-hdr-lines-for-numbers-cat)
(verify-guards fn-nntp-hdr-command-cat)

(defun fn-nntp-xpat-lines-for-numbers-cat (field patterns group numbers v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard (fn-scat-guard) :verify-guards nil))
  (if (consp numbers)
      (let* ((number (car numbers))
             (article (fn-scat-available-article group number v fn-arena fn-cat))
             (content (if (consp article)
                          (fn-nntp-hdr-content field article fn-arena)
                        (list :error))))
        (if (and (fn-nntp-hdr-okp content)
                 (fn-nntp-xpat-matchesp patterns (fn-nntp-hdr-octets content)))
            (cons (fn-nntp-hdr-line (fn-nntp-decimal-field number)
                                    (fn-nntp-hdr-octets content))
                  (fn-nntp-xpat-lines-for-numbers-cat field patterns group
                                                      (cdr numbers) v fn-arena fn-cat))
          (fn-nntp-xpat-lines-for-numbers-cat field patterns group (cdr numbers)
                                              v fn-arena fn-cat)))
    nil))

(defthm fn-nntp-xpat-lines-for-numbers-cat-is-archive
  (implies (and (fn-cnx-freshp fn-cat) group)
           (equal (fn-nntp-xpat-lines-for-numbers-cat field patterns group numbers v fn-arena fn-cat)
                  (fn-nntp-xpat-lines-for-numbers field patterns group numbers
                                                  (fn-cat-view-articles v fn-arena fn-cat) fn-arena)))
  :hints (("Goal" :induct (fn-nntp-xpat-lines-for-numbers-cat field patterns group numbers v fn-arena fn-cat)
           :in-theory (e/d (fn-nntp-xpat-lines-for-numbers)
                           (fn-scat-available-article fn-cat-view-articles
                            fn-nntp-available-article fn-nntp-hdr-content fn-nntp-hdr-okp
                            fn-nntp-hdr-line fn-nntp-hdr-octets fn-nntp-decimal-field
                            fn-nntp-xpat-matchesp fn-cnx-freshp
                            fn-nntp-xpat-with-a-total-filter-is-the-hdr-block)))))

(defun fn-nntp-xpat-response-cat (session args v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard (fn-scat-guard) :verify-guards nil))
  (if (not (and (consp args) (fn-nntp-hdr-fieldp (car args))
                (consp (cdr args))
                (consp (cdr (cdr args)))))
      (fn-nntp-single session "501 syntax error")
    (let* ((field (car args))
           (token (car (cdr args)))
           (joined (fn-nntp-xpat-join (cdr (cdr args))))
           (parsed (fn-wildmat-parse-text joined)))
      (if (not (fn-wildmat-result-okp parsed))
          (fn-nntp-single session "501 syntax error")
        (let ((patterns (fn-wildmat-result-value parsed))
              (group (fn-nntp-session-group session)))
          (if (fn-nntp-range-okp (fn-nntp-parse-range token))
              (if (null group)
                  (fn-nntp-single session "412 no newsgroup selected")
                (fn-nntp-multi
                 session (fn-nntp-hdr-initial t)
                 (fn-nntp-xpat-lines-for-numbers-cat
                  field patterns group
                  (fn-scat-range-numbers
                   group (nfix (fn-nntp-range-low (fn-nntp-parse-range token)))
                   (nfix (fn-nntp-range-high (fn-nntp-parse-range token))) v fn-cat)
                  v fn-arena fn-cat)))
            (if (fn-nntp-message-id-tokenp token)
                (let ((article (fn-scat-msgid-article (fn-nntp-token-string token)
                                                      v fn-arena fn-cat)))
                  (if (not (consp article))
                      (fn-nntp-single session "430 no article with that message-id")
                    (if (not (fn-nntp-hdr-okp (fn-nntp-hdr-content field article fn-arena)))
                        (fn-nntp-single session "503 stored article framing unavailable")
                      (fn-nntp-multi session (fn-nntp-hdr-initial t)
                                     (fn-nntp-xpat-msgid-lines field patterns token
                                                               article fn-arena)))))
              (fn-nntp-single session "501 syntax error"))))))))

(defthm fn-nntp-xpat-response-cat-is-archive
  (implies (and (fn-cnx-freshp fn-cat)
                (equal (fn-state-articles archive) (fn-cat-view-articles v fn-arena fn-cat)))
           (equal (fn-nntp-xpat-response-cat session args v fn-arena fn-cat)
                  (fn-nntp-xpat-response session archive args fn-arena)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-nntp-parse-range-ok-has-natural-bounds (token (cadr args))))
           :in-theory (e/d (fn-nntp-xpat-response fn-nntp-xpat-range fn-nntp-xpat-msgid)
                           (fn-scat-available-article fn-scat-range-numbers
                            fn-nntp-xpat-lines-for-numbers-cat fn-nntp-xpat-lines-for-numbers
                            fn-scat-msgid-article fn-find-article fn-nntp-xpat-msgid-lines
                            fn-nntp-group-range-numbers fn-nntp-available-article
                            fn-cat-view-articles fn-cnx-freshp fn-nntp-parse-range
                            fn-nntp-hdr-content fn-nntp-hdr-okp fn-nntp-multi fn-nntp-single
                            fn-nntp-hdr-fieldp fn-nntp-message-id-tokenp fn-nntp-xpat-join
                            fn-wildmat-parse-text fn-nntp-range-okp
                            fn-nntp-parse-range-ok-has-natural-bounds
                            fn-nntp-xpat-with-a-total-filter-is-the-hdr-block)))))

(in-theory (disable fn-scat-group-low-is-car fn-scat-group-high-is-last))

;;; The dispatcher: fn-nntp-archive-command-pinned's case split with the two
;;; retrieval arms reading the catalog.  Every other arm is the pinned arm
;;; (it reads the archive and the pinned index until step 8).  Its guards are
;;; verified with the lift (fn-nntp-command-pinned and above call it then);
;;; the host calls nothing in this book yet.

(defun fn-nntp-archive-command-cat
    (session archive index verdicts env keyword args v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (natp v)
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))
                  :verify-guards nil))
  (let ((xref (fn-nntp-xref-reply session archive index env keyword args fn-arena)))
    (if xref xref
      (cond
       ((and (fn-nntp-keywordp keyword "LIST")
             (fn-gidx-pinp index)
             (consp args)
             (fn-nntp-keyword-tokenp (car args))
             (fn-nntp-keywordp (car args) "COUNTS"))
        (fn-nntp-list-counts-command-cat session archive (cdr args) v fn-cat))
       ((and (or (fn-nntp-keywordp keyword "ARTICLE")
                 (fn-nntp-keywordp keyword "HEAD")
                 (fn-nntp-keywordp keyword "BODY")
                 (fn-nntp-keywordp keyword "STAT"))
             (consp args) (null (cdr args))
             (fn-nntp-number-withdrawn-p session archive index (car args)))
        (fn-nntp-withdrawn-reply session nil))
       ((and (or (fn-nntp-keywordp keyword "ARTICLE")
                 (fn-nntp-keywordp keyword "HEAD")
                 (fn-nntp-keywordp keyword "BODY")
                 (fn-nntp-keywordp keyword "STAT"))
             (consp args) (null (cdr args))
             (fn-nntp-message-id-tokenp (car args))
             (fn-nntp-msgid-withdrawn-p index (car args)))
        (fn-nntp-withdrawn-reply session t))
       ;; PRF-243: the served compatibility arms, where the pinned dispatcher
       ;; has them (books/nntp.lisp fn-nntp-archive-command-pinned).
       ((fn-rcompat-reply session archive index env keyword args fn-arena)
        (fn-rcompat-reply session archive index env keyword args fn-arena))
       ((and (or (fn-nntp-keywordp keyword "ARTICLE")
                 (fn-nntp-keywordp keyword "HEAD")
                 (fn-nntp-keywordp keyword "BODY")
                 (fn-nntp-keywordp keyword "STAT"))
             (consp args) (null (cdr args))
             (fn-nntp-message-id-tokenp (car args)))
        (fn-nntp-msgid-retrieval-cat
         session v
         (cond ((fn-nntp-keywordp keyword "ARTICLE") :article)
               ((fn-nntp-keywordp keyword "HEAD") :head)
               ((fn-nntp-keywordp keyword "BODY") :body)
               (t :stat))
         (car args) fn-arena fn-cat))
       ((and (or (fn-nntp-keywordp keyword "ARTICLE")
                 (fn-nntp-keywordp keyword "HEAD")
                 (fn-nntp-keywordp keyword "BODY")
                 (fn-nntp-keywordp keyword "STAT"))
             (consp args) (null (cdr args))
             (fn-nntp-number-tokenp (car args)))
        (fn-nntp-number-retrieval-cat
         session v
         (cond ((fn-nntp-keywordp keyword "ARTICLE") :article)
               ((fn-nntp-keywordp keyword "HEAD") :head)
               ((fn-nntp-keywordp keyword "BODY") :body)
               (t :stat))
         (car args) fn-arena fn-cat))
       ((and (fn-nntp-keywordp keyword "LISTGROUP")
             (fn-gidx-pinp index))
        (fn-nntp-listgroup-command-cat session archive args v fn-cat))
       ((and (or (fn-nntp-keywordp keyword "OVER")
                 (fn-nntp-keywordp keyword "XOVER"))
             (fn-gidx-pinp index)
             (consp args) (null (cdr args))
             (fn-nntp-range-okp (fn-nntp-parse-range (car args))))
        (fn-nntp-over-range-cat session v (car args) (fn-nntp-keywordp keyword "XOVER")
                                fn-arena fn-cat))
       ((and (fn-nntp-keywordp keyword "HDR")
             (consp args)
             (fn-nntp-keywordp (car args) ":FN-VERIFIED"))
        (fn-nntp-verdict-hdr-response session archive verdicts args))
       ((and (fn-nntp-keywordp keyword "HDR")
             (consp args)
             (fn-nntp-keywordp (car args) ":FN-CONTROL"))
        (fn-nntp-control-hdr-response session archive index verdicts args))
       ((and (fn-nntp-keywordp keyword "HDR")
             (consp args)
             (fn-nntp-keywordp (car args) ":FN-ENROLLMENT"))
        (fn-nntp-enrollment-hdr-response session archive index verdicts args))
       ((fn-nntp-keywordp keyword "GROUP")
        (if (and (consp args) (null (cdr args)) (fn-nntp-printable-tokenp (car args)))
            (fn-nntp-group-result-cat session archive (fn-nntp-token-string (car args)) v fn-cat)
          (fn-nntp-single session "501 syntax error")))
       ((fn-nntp-keywordp keyword "HDR")
        (fn-nntp-hdr-command-cat session args v nil fn-arena fn-cat))
       ((fn-nntp-keywordp keyword "XHDR")
        (fn-nntp-hdr-command-cat session args v t fn-arena fn-cat))
       ((fn-nntp-keywordp keyword "XPAT")
        (fn-nntp-xpat-response-cat session args v fn-arena fn-cat))
       (t (fn-nntp-archive-command session archive env keyword args fn-arena))))))

;;; KEYSTONE (the boundary theorem of this increment): under archive = the
;;; view's articles, trie = its Message-ID index and a fresh number column,
;;; the -cat dispatcher IS the pinned dispatcher.

;; The by-number line of the pinned dispatcher reaches fn-nntp-number-retrieval
;; through the fallthrough (fn-nntp-archive-command, fn-nntp-retrieval).
(local
 (defthm fn-scat-pinned-number-line-is-number-retrieval
   (implies (and (or (fn-nntp-keywordp keyword "ARTICLE")
                     (fn-nntp-keywordp keyword "HEAD")
                     (fn-nntp-keywordp keyword "BODY")
                     (fn-nntp-keywordp keyword "STAT"))
                 (consp args) (null (cdr args))
                 (fn-nntp-number-tokenp (car args)))
            (equal (fn-nntp-archive-command session archive env keyword args fn-arena)
                   (fn-nntp-number-retrieval
                    session archive
                    (cond ((fn-nntp-keywordp keyword "ARTICLE") :article)
                          ((fn-nntp-keywordp keyword "HEAD") :head)
                          ((fn-nntp-keywordp keyword "BODY") :body)
                          (t :stat))
                    (car args) fn-arena)))
   :hints (("Goal" :in-theory (e/d (fn-nntp-archive-command fn-nntp-retrieval)
                                   (fn-nntp-number-retrieval fn-nntp-msgid-retrieval
                                    fn-nntp-current-retrieval fn-nntp-number-tokenp
                                    fn-nntp-message-id-tokenp fn-nntp-upcase-keyword))))))

;; The three pinned bucket arms are the archive folds under the pin's
;; correspondence (books/nntp-list-counts.lisp, group-bucket-invariants.lisp,
;; nntp-range-indexed-invariants.lisp).
(local
 (defthm fn-scat-pin-buckets-are-built
   (implies (and (fn-gidx-pin-correspondencep index archive) (fn-gidx-pinp index))
            (equal (fn-gidx-pin-buckets index)
                   (fn-gidx-build (fn-state-articles archive))))
   :hints (("Goal" :in-theory (enable fn-gidx-pin-correspondencep)))))

(local
 (defthm fn-scat-pin-trie-is-built
   (implies (fn-midx-correspondencep (fn-gidx-pin-trie index) (fn-state-articles archive))
            (equal (fn-gidx-pin-trie index)
                   (fn-midx-build (fn-state-articles archive))))
   :hints (("Goal" :in-theory (enable fn-midx-correspondencep)))))

(local
 (defthm fn-scat-built-trie-corresponds
   (fn-midx-correspondencep (fn-midx-build articles) articles)
   :hints (("Goal" :in-theory (enable fn-midx-correspondencep)))))

(local
 (defthm fn-scat-projection-is-state
   (implies (fn-nntp-projectionp archive) (fn-statep archive))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-nntp-projectionp)))))

(local
 (defthm fn-scat-built-listgroup-is-fold
   (implies (fn-nntp-projectionp archive)
            (equal (fn-gidx-listgroup-command
                    session archive (fn-gidx-build (fn-state-articles archive)) args)
                   (fn-nntp-listgroup-command session archive args)))
   :hints (("Goal" :use ((:instance fn-gidx-listgroup-command-of-build))
            :in-theory (disable fn-gidx-listgroup-command fn-nntp-listgroup-command
                                fn-gidx-build fn-nntp-projectionp)))))

(defthm fn-nntp-archive-command-cat-is-pinned
  (implies (and (equal (fn-state-articles archive)
                       (fn-cat-view-articles v fn-arena fn-cat))
                (fn-nntp-projectionp archive)
                (fn-gidx-pin-correspondencep index archive)
                (fn-midx-correspondencep (fn-gidx-pin-trie index)
                                         (fn-state-articles archive))
                (fn-cnx-freshp fn-cat))
           (equal (fn-nntp-archive-command-cat
                   session archive index verdicts env keyword args v fn-arena fn-cat)
                  (fn-nntp-archive-command-pinned
                   session archive index verdicts env keyword args fn-arena)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nntp-archive-command-cat fn-nntp-archive-command-pinned
                            fn-nntp-archive-command fn-nntp-list-command
                            fn-nntp-hdr-response fn-nntp-xhdr-response
                            fn-nntp-over-response fn-nntp-xover-response
                            fn-nntp-retrieval)
                           (fn-rcompat-reply fn-nntp-xref-reply fn-gidx-list-counts-command
                            fn-nntp-number-withdrawn-p fn-nntp-msgid-withdrawn-p
                            fn-nntp-withdrawn-reply fn-gidx-listgroup-command
                            fn-nntp-over-range-indexed fn-nntp-verdict-hdr-response
                            fn-nntp-control-hdr-response
                            fn-nntp-enrollment-hdr-response
                            fn-nntp-upcase-keyword
                            fn-nntp-keyword-tokenp fn-gidx-pinp fn-gidx-pin-trie
                            fn-gidx-pin-buckets fn-nntp-message-id-tokenp
                            fn-nntp-number-tokenp fn-nntp-range-okp
                            fn-nntp-parse-range fn-nntp-msgid-retrieval-cat
                            fn-nntp-number-retrieval-cat
                            fn-nntp-msgid-retrieval-indexed
                            fn-nntp-msgid-retrieval fn-nntp-number-retrieval
                            fn-cat-view-articles fn-midx-correspondencep
                            fn-nntp-projectionp fn-gidx-pin-correspondencep
                            fn-nntp-list-counts-command-cat fn-nntp-list-counts-command
                            fn-nntp-listgroup-command-cat fn-nntp-listgroup-command
                            fn-nntp-over-range-cat fn-nntp-over-range fn-nntp-xover-range
                            fn-nntp-group-result-cat fn-nntp-group-result
                            fn-nntp-hdr-command-cat fn-nntp-hdr-command
                            fn-nntp-xpat-response-cat fn-nntp-xpat-response
                            fn-nntp-current-retrieval fn-nntp-over-current fn-nntp-over-msgid
                            fn-nntp-list-response fn-nntp-list-active-times
                            fn-nntp-list-newsgroups-described fn-nntp-list-motd
                            fn-nntp-printable-tokenp fn-nntp-token-string
                            fn-nntp-single fn-gidx-build fn-midx-build fn-statep
                            fn-nntp-over-range-indexed-is-walk)))))
