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
; A group's summary at a view below the count (lane scale-latency, PKT-870).
(include-book "served-catalog-view")
(include-book "newnews-stream-cursor")
(include-book "protocol-table") ; reply texts: (fn-proto-text ROW KEY)
(include-book "nntp")
(include-book "nntp-range-indexed-invariants")
(include-book "nntp-list-counts")
(include-book "served-columns")   ; the overview column: OVER/HDR/XPAT without the bytes

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:definition fn-nntp-article-idp)
                          (:definition fn-scat-msgid-idp)
                          (:rewrite fn-nntp-available-number-article-is-projectable)
                          (:rewrite fn-nntp-message-id-token-is-response-text)
                          (:rewrite fn-nntp-response-text-is-octets))))

; Included rules these proofs try on every string, length and group-number
; goal and never use (accumulated-persistence over the whole book,
; 2026-09-28, lane d26-books).  None is cited below.
(local (in-theory (disable fn-nntp-index-msgid-okp-stringp
                           fn-nntp-find-group-number-of-fresh-member)))

; The tau system is off here: it is time no prover step counts (tau is not
; rewriting), and on this book's goals it was half the proof time (7.7 ->
; 3.7 s ACL2 time over the book's own forms, persvati REPL 2026-09-28).
; One guard proof below is shorter with it (7,565 against 447,668 steps)
; and turns it back on.  `fn-nntp-article-idp-is-consp' is not enabled:
; 230k frames tried, 144 useful, none needed (lane d26-books-2).
(local (in-theory (disable (tau-system))))

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
                  :guard (natp v)
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
                                      fn-cat-msgid-seqs fn-cat-p-is-rowsp
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
      (fn-nntp-single session (fn-proto-text * :syntax))
    (let ((article (fn-scat-msgid-article (fn-nntp-token-string token)
                                          v fn-arena fn-cat)))
      (if (consp article)
          (fn-nntp-article-response
           session article (fn-nntp-msgid-local-number session article)
           kind nil nil fn-arena)
        (fn-nntp-single session (fn-proto-text * :no-msgid))))))

(defun fn-nntp-number-retrieval-cat (session v kind token fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (natp v)
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))
                  :verify-guards nil))
  (if (not (fn-nntp-number-tokenp token))
      (fn-nntp-single session (fn-proto-text * :syntax))
    (let ((group (fn-nntp-session-group session))
          (number (fn-nntp-decimal-value token)))
      (if (null group)
          (fn-nntp-single session (fn-proto-text * :no-group-selected))
        (let ((article (fn-scat-number-article group number v fn-arena fn-cat)))
          (if (consp article)
              (fn-nntp-article-response session article number kind t group fn-arena)
            (fn-nntp-single session (fn-proto-text * :no-number))))))))

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
                  :guard (natp v)))
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

; fn-scat-msgid-idp is books/catalog.lisp's (moved down for the catalog's
; live summary, lane sca-join-5).

(defthm fn-scat-article-idp-is-msgid-idp
  (equal (fn-nntp-article-idp article)
         (fn-scat-msgid-idp (fn-article-msgid article)))
  :hints (("Goal" :in-theory (enable fn-nntp-article-idp))))

; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-scat-range-keep-loop (group seqs fn-cat acc)
  (declare (xargs :stobjs fn-cat :guard (true-listp acc) :verify-guards nil))
  (if (consp seqs)
      (let ((s (car seqs)))
        (if (and (natp s) (< s (fn-cat-count fn-cat)))
            (let* ((h (fn-cat-at s fn-cat))
                   (n (fn-held-number-in group h)))
              (if (and (posp n)
                       (<= n *fn-nntp-max-article-number*)
                       (fn-scat-msgid-idp (fn-record-msgid h)))
                  (fn-scat-range-keep-loop group (cdr seqs) fn-cat (cons n acc))
                (fn-scat-range-keep-loop group (cdr seqs) fn-cat acc)))
          (fn-scat-range-keep-loop group (cdr seqs) fn-cat acc)))
    (revappend acc nil)))

(defun fn-scat-range-keep (group seqs fn-cat)
  (declare (xargs :verify-guards nil :stobjs fn-cat :guard t
                  :guard-hints (("Goal" :in-theory (disable fn-cat-p-is-rowsp fn-cat-count-is-len
                                                            fn-cat-at-is-nth)))))
  (mbe :logic
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
         nil)
       :exec (fn-scat-range-keep-loop group seqs fn-cat nil)))

(local
 (defthm fn-scat-range-keep-loop-is-revappend
   (equal (fn-scat-range-keep-loop group seqs fn-cat acc)
          (revappend acc (fn-scat-range-keep group seqs fn-cat)))
   :hints (("Goal" :induct (fn-scat-range-keep-loop group seqs fn-cat acc)
                   :in-theory (union-theories '(fn-scat-range-keep-loop fn-scat-range-keep revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-scat-range-keep-loop
  :hints (("Goal"
           :in-theory
           (disable fn-cat-p-is-rowsp fn-cat-count-is-len fn-cat-at-is-nth))))

(verify-guards fn-scat-range-keep
  :hints (("Goal" :in-theory (union-theories '(revappend fn-scat-range-keep)
                                                  (union-theories (theory 'minimal-theory)
                                                                  (executable-counterpart-theory :here)))
                  :use ((:instance fn-scat-range-keep-loop-is-revappend (acc nil))))))


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

; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
; The OVER line builders ask (natp v) and nothing of the whole catalog: a
; window reads the rows of its own numbers, each through a reader that
; checks its handle (see fn-cat-row-article).  They are what a cursor
; quantum runs (fn-ovw-lines), so their guard is checked once per quantum.
(defun fn-nov-lines-for-numbers-cat-loop (group numbers v fn-arena fn-cat acc)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard (and (natp v) (true-listp acc)) :verify-guards nil))
  (if (consp numbers)
      (let* ((number (car numbers))
             (article (fn-scat-available-article group number v fn-arena fn-cat))
             (over (if (and (consp article)
                            (not (fn-nntp-article-tombstonep article fn-arena)))
                       (fn-nov-overview article fn-arena)
                     (list :error))))
        (if (fn-nov-okp over)
            (fn-nov-lines-for-numbers-cat-loop group
                                               (cdr numbers)
                                               v
                                               fn-arena
                                               fn-cat
                                               (cons (fn-nov-line number over) acc))
          (fn-nov-lines-for-numbers-cat-loop group (cdr numbers) v fn-arena fn-cat acc)))
    (revappend acc nil)))

(defun fn-nov-lines-for-numbers-cat (group numbers v fn-arena fn-cat)
  (declare (xargs :verify-guards nil :stobjs (fn-arena fn-cat) :guard (natp v)))
  (mbe :logic
       (if (consp numbers)
           (let* ((number (car numbers))
                  (article (fn-scat-available-article group number v fn-arena fn-cat))
                  (over (if (and (consp article)
                                 (not (fn-nntp-article-tombstonep article fn-arena)))
                            (fn-nov-overview article fn-arena)
                          (list :error))))
             (if (fn-nov-okp over)
                 (cons (fn-nov-line number over)
                       (fn-nov-lines-for-numbers-cat group (cdr numbers) v fn-arena fn-cat))
               (fn-nov-lines-for-numbers-cat group (cdr numbers) v fn-arena fn-cat)))
         nil)
       :exec (fn-nov-lines-for-numbers-cat-loop group numbers v fn-arena fn-cat nil)))

(local
 (defthm fn-nov-lines-for-numbers-cat-loop-is-revappend
   (equal (fn-nov-lines-for-numbers-cat-loop group numbers v fn-arena fn-cat acc)
          (revappend acc (fn-nov-lines-for-numbers-cat group numbers v fn-arena fn-cat)))
   :hints (("Goal" :induct (fn-nov-lines-for-numbers-cat-loop group numbers v fn-arena fn-cat acc)
                   :in-theory (union-theories '(fn-nov-lines-for-numbers-cat-loop fn-nov-lines-for-numbers-cat revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-nov-lines-for-numbers-cat-loop)

(verify-guards fn-nov-lines-for-numbers-cat
  :hints (("Goal" :in-theory (union-theories '(revappend fn-nov-lines-for-numbers-cat)
                                                  (union-theories (theory 'minimal-theory)
                                                                  (executable-counterpart-theory :here)))
                  :use ((:instance fn-nov-lines-for-numbers-cat-loop-is-revappend (acc nil))))))


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
        (fn-nntp-single session (fn-proto-text * :no-group-selected))
      (let* ((numbers (fn-scat-range-numbers
                       group (nfix (fn-nntp-range-low range))
                       (nfix (fn-nntp-range-high range)) v fn-cat))
             (lines (fn-nov-lines-for-numbers-cat group numbers v fn-arena fn-cat)))
        (if (consp lines)
            (fn-nntp-multi session (fn-proto-text * :overview) lines)
          (fn-nntp-single
           session (if legacyp (fn-proto-text * :none-selected)
                     (fn-proto-text * :empty-range))))))))

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

;;; The served lines (the Xref field of a node with a server name; the
;;; overview column, books/served-columns.lisp).  Defined here, above the
;;; windowed reader, because a cursor that carries a server name reads them
;;; (fn-ovw-lines); their equation with the column fold is with the served
;;; range arm below (fn-nov-served-lines-for-numbers-cat-is-col).
(defun fn-nov-served-lines-for-numbers-cat-loop (group numbers server v fn-arena fn-cat acc)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard (and (natp v) (true-listp acc)) :verify-guards nil))
  (if (consp numbers)
      (let* ((number (car numbers))
             (article (fn-scat-available-article group number v fn-arena fn-cat))
             (over (if (and (consp article)
                            (not (fn-scol-tombstonep article fn-arena fn-cat)))
                       (fn-scol-overview-of article fn-arena fn-cat)
                     (list :error))))
        (if (fn-nov-okp over)
            (fn-nov-served-lines-for-numbers-cat-loop
             group (cdr numbers) server v fn-arena fn-cat
             (cons (fn-nov-served-line number over server article) acc))
          (fn-nov-served-lines-for-numbers-cat-loop group (cdr numbers) server v fn-arena fn-cat acc)))
    (revappend acc nil)))

(defun fn-nov-served-lines-for-numbers-cat (group numbers server v fn-arena fn-cat)
  (declare (xargs :verify-guards nil :stobjs (fn-arena fn-cat) :guard (natp v)))
  (mbe :logic
       (if (consp numbers)
           (let* ((number (car numbers))
                  (article (fn-scat-available-article group number v fn-arena fn-cat))
                  (over (if (and (consp article)
                                 (not (fn-scol-tombstonep article fn-arena fn-cat)))
                            (fn-scol-overview-of article fn-arena fn-cat)
                          (list :error))))
             (if (fn-nov-okp over)
                 (cons (fn-nov-served-line number over server article)
                       (fn-nov-served-lines-for-numbers-cat group (cdr numbers) server v fn-arena fn-cat))
               (fn-nov-served-lines-for-numbers-cat group (cdr numbers) server v fn-arena fn-cat)))
         nil)
       :exec (fn-nov-served-lines-for-numbers-cat-loop group numbers server v fn-arena fn-cat nil)))

(local
 (defthm fn-nov-served-lines-for-numbers-cat-loop-is-revappend
   (equal (fn-nov-served-lines-for-numbers-cat-loop group numbers server v fn-arena fn-cat acc)
          (revappend acc (fn-nov-served-lines-for-numbers-cat group numbers server v fn-arena fn-cat)))
   :hints (("Goal" :induct (fn-nov-served-lines-for-numbers-cat-loop group numbers server v fn-arena fn-cat acc)
                   :in-theory (union-theories '(fn-nov-served-lines-for-numbers-cat-loop
                                                fn-nov-served-lines-for-numbers-cat revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-nov-served-lines-for-numbers-cat-loop)

(verify-guards fn-nov-served-lines-for-numbers-cat
  :hints (("Goal" :in-theory (union-theories '(revappend fn-nov-served-lines-for-numbers-cat)
                                             (union-theories (theory 'minimal-theory)
                                                             (executable-counterpart-theory :here)))
           :use ((:instance fn-nov-served-lines-for-numbers-cat-loop-is-revappend (acc nil))))))

;;; -----------------------------------------------------------------------------
;;; OVER/XOVER of a range answered in bounded windows (D27; PRF-1020; lanes
;;; join-f2-10 and join-f2-12).
;;;
;;; fn-nntp-over-range-cat above probes every number of the clamped range and
;;; builds every NOV line in one served step: the step's work grows with the
;;; range.  The served arm fn-nntp-over-range-ovw (the OVER/XOVER range arm
;;; of fn-nntp-archive-command-cat) answers the range with a CURSOR instead:
;;; fn-ovw-start parses and clamps the range once, no number probed, and the
;;; step's effects carry (:over-cursor CUR), which the host drains one window
;;; of at most W numbers per quantum (books/over-window.lisp fn-ovw-step; the
;;; owner's continuation entry is the host's).  A cursor effect MEANS the
;;; complete reply of its range (fn-ovw-cursor-octets: the lines K..TOP of
;;; GROUP in the pinned view V, the status line owed); fn-ovw-expand replaces
;;; every cursor effect of an effects list by that reply and touches nothing
;;; else.  KEYSTONE fn-nntp-over-range-ovw-expands-to-over-range-cat: the
;;; expanded arm is the unbounded reader's reply and the session is unchanged.
;;; books/over-window.lisp fn-ovw-cursor-effect-expands-to-run adds that the
;;; windowed run of the arm's cursor is that reply for every W.  From
;;; fn-nntp-archive-command-cat-is-pinned up books/served-catalog-chain.lisp
;;; every -cat = pinned equation is stated on the results' components with the
;;; effects of BOTH sides expanded: the pinned reference carries no cursor
;;; (fn-ovw-cursor-effect is built by this arm alone), so its expansion is
;;; itself; stating the equations symmetrically keeps them free of that
;;; structural fact about the whole pinned dispatcher.

(defun fn-ovw-status (text)
  (declare (xargs :guard t))
  (fn-nntp-crlf (fn-nntp-string-octets text)))

; The lines of the numbers K..HI of GROUP in view V: the unbounded reader's
; lines restricted to one window.  SERVER is the node's Xref server name, or
; NIL: with one, the lines are the served reader's (fn-nntp-over-range-
; served-cat: the Xref field, the overview column); with none, the plain
; reader's (fn-nntp-over-range-cat).
(defun fn-ovw-lines (group k hi server v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (natp k) (natp hi) (natp v))))
  (let ((numbers (fn-scat-range-keep group (fn-cnx-range-aux group k hi v fn-cat) fn-cat)))
    (if server
        (fn-nov-served-lines-for-numbers-cat group numbers server v fn-arena fn-cat)
      (fn-nov-lines-for-numbers-cat group numbers v fn-arena fn-cat))))

; (GROUP K TOP V LEGACYP OWEDP SERVER): the next number to probe, the range's
; last number (clamped once, at the start), the pinned view, XOVER or OVER,
; whether the status line is still owed (no line sent yet), and the Xref
; server name the lines carry (NIL: none).
(defun fn-ovw-cursor (group k top v legacyp owedp server)
  (declare (xargs :guard t))
  (list group k top v legacyp owedp server))

(defun fn-ovw-cursorp (cur)
  (declare (xargs :guard t))
  (and (true-listp cur) (natp (nth 3 cur))))

(defthm fn-ovw-cursor-fields
  (and (equal (nth 0 (fn-ovw-cursor group k top v legacyp owedp server)) group)
       (equal (nth 1 (fn-ovw-cursor group k top v legacyp owedp server)) k)
       (equal (nth 2 (fn-ovw-cursor group k top v legacyp owedp server)) top)
       (equal (nth 3 (fn-ovw-cursor group k top v legacyp owedp server)) v)
       (equal (nth 4 (fn-ovw-cursor group k top v legacyp owedp server)) legacyp)
       (equal (nth 5 (fn-ovw-cursor group k top v legacyp owedp server)) owedp)
       (equal (nth 6 (fn-ovw-cursor group k top v legacyp owedp server)) server)))

(defun fn-ovw-empty-text (legacyp)
  (declare (xargs :guard t))
  (if legacyp (fn-proto-text * :none-selected) (fn-proto-text * :empty-range)))

; The command's step: O(1), no number probed.
(defun fn-ovw-start (session v token legacyp server fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v)))
  (let ((group (fn-nntp-session-group session))
        (range (fn-nntp-parse-range token)))
    (if (null group)
        (mv (fn-ovw-status (fn-proto-text * :no-group-selected)) nil)
      (mv nil
          (fn-ovw-cursor group (nfix (fn-nntp-range-low range))
                         (min (nfix (fn-nntp-range-high range))
                              (nfix (- (fn-cat-group-next group fn-cat) 1)))
                         v legacyp t server)))))

(defthm fn-ovw-start-cursorp
  (implies (and (natp v)
                (mv-nth 1 (fn-ovw-start session v token legacyp server fn-cat)))
           (fn-ovw-cursorp (mv-nth 1 (fn-ovw-start session v token legacyp server fn-cat)))))

; The reply of LINES: the status line when it is owed, the stuffed lines,
; the dot -- or the empty-range status when the owed status line has no line.
(defun fn-ovw-reply (lines legacyp owedp)
  (declare (xargs :guard t :verify-guards nil))
  (if owedp
      (if (consp lines)
          (append (fn-ovw-status (fn-proto-text * :overview))
                  (fn-nntp-stuff-lines lines)
                  '(46 13 10))
        (fn-ovw-status (fn-ovw-empty-text legacyp)))
    (append (fn-nntp-stuff-lines lines) '(46 13 10))))

;;; -----------------------------------------------------------------------------
;;; HDR/XHDR/XPAT of a range on the same cursor (lane cold-line, 2026-10-04;
;;; ledger sl-cold-line-quanta).
;;;
;;; A header range was one served step: every number's field read in one run
;;; of the line.  A field that is not in the overview column (Newsgroups,
;;; Path, Organization, any non-overview header; Xref through the
;;; compatibility arm's tombstone test) is read from the article's payload,
;;; and the line runs with the extent realizer in its no-I/O mode: past
;;; fn-arx-read-cache-entries (8) payloads it evicted its own reads on every
;;; run and never finished (image set 45e05c7fd, 40 articles;
;;; books/cold-line-quanta.lisp fn-clq-nine-reads-never-finish is the
;;; mechanism).  The range now answers with the OVER cursor carrying a HEADER
;;; SOURCE in its eighth slot (fn-ovw-hdr-cursor; an OVER cursor's is NIL):
;;; books/over-window.lisp fn-ovw-step runs a header cursor's window of at
;;; most fn-clq-payload-quantum numbers when the source reads payloads, so a
;;; quantum's reads fit the cache with margin (fn-ovw-step-payloads-fit) and
;;; the line finishes in ceiling(N/Q) quanta (fn-clq-quantized-line-finishes).
;;; The status line is decided lazily, as OVER's: the 225/221 head before the
;;; first line; with no line the arm's empty reply (423 HDR, 420 XHDR, the
;;; empty 221 block for XPAT).

; (:hdr FORM FIELD PATTERNS XREF): FORM :hdr, :xhdr or :xpat; FIELD the
; header asked; PATTERNS XPAT's parsed wildmat (unused otherwise); XREF
; (:xref . SERVER) when the range is the compatibility arm's HDR Xref
; (fn-rcompat-hdr-cat, SERVER the node's Xref server name), else NIL.
(defun fn-ovw-hdr-source (form field patterns xref)
  (declare (xargs :guard t))
  (list :hdr form field patterns xref))

(defun fn-ovw-hdr-content (src article fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard t :verify-guards nil))
  (if (consp (fn-cur-at 4 src))
      (fn-rcompat-xref-content (cdr (fn-cur-at 4 src)) article fn-arena)
    (if (consp article)
        (fn-scol-hdr-content (fn-cur-at 2 src) article fn-arena fn-cat)
      (list :error))))

(defun fn-ovw-hdr-keepp (src content)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-nntp-hdr-okp content)
       (or (not (eq (fn-cur-at 1 src) :xpat))
           (fn-nntp-xpat-matchesp (fn-cur-at 3 src) (fn-nntp-hdr-octets content)))))

; The lines of NUMBERS: the -cat readers' rows (fn-nntp-hdr-lines-for-
; numbers-cat, fn-nntp-xpat-lines-for-numbers-cat, fn-rcompat-hdr-lines-cat;
; books/over-window.lisp equates them).  Only a window's numbers are run.
(defun fn-ovw-hdr-lines-for-numbers (group numbers src v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard (natp v) :verify-guards nil))
  (if (consp numbers)
      (let ((content (fn-ovw-hdr-content
                      src (fn-scat-available-article group (car numbers) v fn-arena fn-cat)
                      fn-arena fn-cat)))
        (if (fn-ovw-hdr-keepp src content)
            (cons (fn-nntp-hdr-line (fn-nntp-decimal-field (car numbers))
                                    (fn-nntp-hdr-octets content))
                  (fn-ovw-hdr-lines-for-numbers group (cdr numbers) src v fn-arena fn-cat))
          (fn-ovw-hdr-lines-for-numbers group (cdr numbers) src v fn-arena fn-cat)))
    nil))

; The lines of the numbers K..HI of GROUP in view V.
(defun fn-ovw-hdr-lines (group k hi src v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard (and (natp k) (natp hi) (natp v))
                  :verify-guards nil))
  (fn-ovw-hdr-lines-for-numbers
   group (fn-scat-range-keep group (fn-cnx-range-aux group k hi v fn-cat) fn-cat)
   src v fn-arena fn-cat))

; The arm's status line (fn-nntp-hdr-initial: HDR's 225, XHDR's and XPAT's 221).
(defun fn-ovw-hdr-status (src)
  (declare (xargs :guard t))
  (fn-ovw-status (if (eq (fn-cur-at 1 src) :hdr)
                     (fn-proto-text "HDR" :headers)
                   (fn-proto-text * :header))))

; The arm's reply when the range holds no line.
(defun fn-ovw-hdr-empty (src)
  (declare (xargs :guard t))
  (case (fn-cur-at 1 src)
    (:xpat (append (fn-ovw-hdr-status src) '(46 13 10)))
    (:xhdr (fn-ovw-status (fn-proto-text * :none-selected)))
    (otherwise (fn-ovw-status (fn-proto-text * :empty-range)))))

(defun fn-ovw-hdr-reply (lines src owedp)
  (declare (xargs :guard t :verify-guards nil))
  (if owedp
      (if (consp lines)
          (append (fn-ovw-hdr-status src) (fn-nntp-stuff-lines lines) '(46 13 10))
        (fn-ovw-hdr-empty src))
    (append (fn-nntp-stuff-lines lines) '(46 13 10))))

; (GROUP K TOP V NIL OWEDP NIL SRC): the OVER cursor's slots, its LEGACYP and
; SERVER unused, SRC the header source.
; The header cursor's window readers run under the owner mutex as the OVER
; window's do: guards verified (books/over-window.lisp fn-ovw-step).
(verify-guards fn-ovw-hdr-content)
(verify-guards fn-ovw-hdr-keepp)
(verify-guards fn-ovw-hdr-lines-for-numbers)
(verify-guards fn-ovw-hdr-lines)
(verify-guards fn-ovw-hdr-reply)

(defun fn-ovw-hdr-cursor (group k top v owedp src)
  (declare (xargs :guard t))
  (list group k top v nil owedp nil src))

(defthm fn-ovw-hdr-cursor-fields
  (and (equal (nth 0 (fn-ovw-hdr-cursor group k top v owedp src)) group)
       (equal (nth 1 (fn-ovw-hdr-cursor group k top v owedp src)) k)
       (equal (nth 2 (fn-ovw-hdr-cursor group k top v owedp src)) top)
       (equal (nth 3 (fn-ovw-hdr-cursor group k top v owedp src)) v)
       (equal (nth 5 (fn-ovw-hdr-cursor group k top v owedp src)) owedp)
       (equal (nth 7 (fn-ovw-hdr-cursor group k top v owedp src)) src)))

(defthm fn-ovw-cursor-has-no-source
  (equal (nth 7 (fn-ovw-cursor group k top v legacyp owedp server)) nil))

; The arm's step: O(1), no number probed (fn-ovw-start's clamp).
(defun fn-ovw-hdr-start (session v token src fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v)))
  (let ((group (fn-nntp-session-group session))
        (range (fn-nntp-parse-range token)))
    (if (null group)
        (mv (fn-ovw-status (fn-proto-text * :no-group-selected)) nil)
      (mv nil
          (fn-ovw-hdr-cursor group (nfix (fn-nntp-range-low range))
                             (min (nfix (fn-nntp-range-high range))
                                  (nfix (- (fn-cat-group-next group fn-cat) 1)))
                             v t src)))))

; The cursor effect.  Built here and nowhere else (tools/callers.py
; fn-ovw-cursor-effect): the pinned reference's effects never carry one.
(defun fn-ovw-cursor-effect (cur)
  (declare (xargs :guard t))
  (list :over-cursor cur))

(defun fn-ovw-cursor-effectp (effect)
  (declare (xargs :guard t))
  (and (consp effect) (equal (car effect) :over-cursor) (consp (cdr effect))))

; The served arm: the start's cursor as the step's one effect, or the 412
; reply when no group is selected.  SERVER: the node's Xref server name
; (fn-nntp-xref-server env) or NIL; the dispatcher's two OVER/XOVER range
; arms (fn-nntp-xref-reply-cat with a name, fn-nntp-archive-command-cat
; without) both answer with this cursor.
(defun fn-nntp-over-range-ovw (session v token legacyp server fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v)))
  (mv-let (octets cur)
    (fn-ovw-start session v token legacyp server fn-cat)
    (fn-nntp-make-result
     session
     (list (if cur (fn-ovw-cursor-effect cur) (fn-nntp-reply-effect octets))))))

;; The header range arms (HDR/XHDR, XPAT, the compatibility arm's HDR Xref):
;; the start's cursor as the step's one effect, or the 412 reply when no
;; group is selected.
(defun fn-nntp-hdr-range-ovw (session v token src fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v)))
  (mv-let (octets cur)
    (fn-ovw-hdr-start session v token src fn-cat)
    (fn-nntp-make-result
     session
     (list (if cur (fn-ovw-cursor-effect cur) (fn-nntp-reply-effect octets))))))

; What a cursor effect stands for: the reply of the numbers K..TOP of GROUP
; in view V with the status line owed (the cursor a served step emits is
; fn-ovw-start's, whose status line is unsent).
(defun fn-ovw-cursor-octets (cur fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (if (nth 7 cur)
      (fn-ovw-hdr-reply (fn-ovw-hdr-lines (nth 0 cur) (nfix (nth 1 cur)) (nfix (nth 2 cur))
                                          (nth 7 cur) (nth 3 cur) fn-arena fn-cat)
                        (nth 7 cur) t)
    (fn-ovw-reply (fn-ovw-lines (nth 0 cur) (nfix (nth 1 cur)) (nfix (nth 2 cur)) (nth 6 cur)
                                (nth 3 cur) fn-arena fn-cat)
                  (nth 4 cur) t)))

; The expansion: every cursor effect becomes the reply it stands for; every
; other element, and the list's final cdr, is kept.
(defun fn-ovw-expand (effects fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (if (consp effects)
      (cons (if (fn-ovw-cursor-effectp (car effects))
                (fn-nntp-reply-effect
                 (fn-ovw-cursor-octets (car (cdr (car effects))) fn-arena fn-cat))
              (if (and (fn-nnw-meta-effectp (car effects))
                       (fn-nnw-meta-initialp (car (cdr (car effects)))))
                  (fn-nntp-reply-effect
                   (fn-nnw-stream-remaining (car (cdr (car effects))) fn-arena fn-cat))
                (car effects)))
            (fn-ovw-expand (cdr effects) fn-arena fn-cat))
    effects))

(defthm fn-nntp-newnews-response-cursor-expands-to-cat
  (equal (fn-ovw-expand
          (cdr (fn-nntp-newnews-response-cursor session archive env args fn-arena fn-cat))
          fn-arena fn-cat)
         (cdr (fn-nntp-newnews-response-cat session archive env args fn-arena fn-cat)))
  :hints (("Goal" :do-not-induct t
           :use fn-nntp-newnews-response-cursor-is-cat
           :in-theory (e/d (fn-nntp-newnews-response-cursor fn-nntp-newnews-response-cat fn-ovw-expand
                             fn-ovw-cursor-effectp fn-nnw-meta-expand
                             fn-nnw-meta-effectp fn-nnw-meta-effect fn-nnw-meta-initialp
                             fn-nnw-stream-outputp fn-nnw-stream-renderp fn-nnw-stream-selectp
                             fn-nnw-configuredp fn-nnw-cursor
                             fn-cur-at fn-cur-make fn-cur-progress fn-cur-pending
                             fn-nntp-multi fn-nntp-make-result fn-nntp-single fn-nntp-reply-effect)
                            (fn-nntp-newnews-response-cursor-is-cat
                             fn-nnw-stream-remaining fn-nnw-stream-owes fn-nnw-stream-normal-owes
                             fn-nnw-meta-remaining fn-nnw-meta-owes
                             fn-nntp-newnews-scan-cat fn-wildmat-parse
                             fn-nntp-newgroups-date-parse fn-nntp-newgroups-time-parse
                             fn-nntp-civil-dtn-ms fn-nntp-string-octets fn-nntp-crlf
                             fn-nntp-filter-groups-by-wildmat)))))

(defthm fn-nntp-newnews-response-stream-expands-to-cat
  (equal (fn-ovw-expand
          (cdr (fn-nntp-newnews-response-stream session archive env args fn-arena fn-cat))
          fn-arena fn-cat)
         (cdr (fn-nntp-newnews-response-cat session archive env args fn-arena fn-cat)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nntp-newnews-response-stream fn-nntp-newnews-response-cat
                             fn-ovw-expand fn-ovw-cursor-effectp
                             fn-nnw-meta-effectp fn-nnw-meta-effect
                                                          fn-nnw-stream-renderp fn-nnw-stream-selectp fn-nnw-configuredp
                             fn-nnw-stream-scan-cursor fn-nnw-group-source
                             fn-nnw-group-source-effective fn-cur-at fn-cur-make fn-cur-progress fn-cur-pending
                             fn-nnw-meta-remaining fn-nnw-meta-owes fn-nnw-cursor fn-nnw-at
                             fn-nnw-tail fn-nnw-groups fn-nnw-threshold fn-nnw-horizon
                             fn-nntp-multi fn-nntp-make-result fn-nntp-single fn-nntp-reply-effect
                             fn-nnw-meta-initialp)
                            (fn-nnw-stream-remaining fn-nnw-stream-owes fn-nnw-stream-normal-owes
                             fn-nntp-newnews-response-cursor-expands-to-cat
                             fn-nntp-newnews-response-cursor-is-cat fn-nnw-stream-fresh-remaining
                             fn-nntp-newnews-scan-cat fn-wildmat-parse
                             fn-nntp-newgroups-date-parse fn-nntp-newgroups-time-parse
                             fn-nntp-civil-dtn-ms fn-nntp-string-octets fn-nntp-crlf
                             fn-nntp-filter-groups-by-wildmat)))))

(in-theory (disable fn-ovw-cursor fn-ovw-status fn-ovw-lines fn-ovw-reply fn-ovw-empty-text
                    fn-ovw-cursor-effect fn-ovw-cursor-effectp fn-ovw-cursor-octets fn-ovw-expand))

(defthm fn-ovw-expand-of-append
  (equal (fn-ovw-expand (append a b) fn-arena fn-cat)
         (append (fn-ovw-expand a fn-arena fn-cat) (fn-ovw-expand b fn-arena fn-cat)))
  :hints (("Goal" :induct (fn-ovw-expand a fn-arena fn-cat)
           :in-theory (enable fn-ovw-expand))))

(defthm fn-ovw-expand-of-nil
  (equal (fn-ovw-expand nil fn-arena fn-cat) nil)
  :hints (("Goal" :in-theory (enable fn-ovw-expand))))

(defthm fn-ovw-expand-of-reply-cons
  (equal (fn-ovw-expand (cons (fn-nntp-reply-effect octets) rest) fn-arena fn-cat)
         (cons (fn-nntp-reply-effect octets) (fn-ovw-expand rest fn-arena fn-cat)))
  :hints (("Goal" :in-theory (enable fn-ovw-expand fn-ovw-cursor-effectp fn-nntp-reply-effect))))

(defthm fn-ovw-expand-of-single-effects
  (equal (fn-ovw-expand (cdr (fn-nntp-single session text)) fn-arena fn-cat)
         (cdr (fn-nntp-single session text)))
  :hints (("Goal" :in-theory (enable fn-nntp-single fn-nntp-make-result))))

(defthm fn-ovw-expand-of-multi-effects
  (equal (fn-ovw-expand (cdr (fn-nntp-multi session initial lines)) fn-arena fn-cat)
         (cdr (fn-nntp-multi session initial lines)))
  :hints (("Goal" :in-theory (enable fn-nntp-multi fn-nntp-make-result))))

(defthm fn-ovw-expand-of-multi-octets-effects
  (equal (fn-ovw-expand (cdr (fn-nntp-multi-octets session initial lines)) fn-arena fn-cat)
         (cdr (fn-nntp-multi-octets session initial lines)))
  :hints (("Goal" :in-theory (enable fn-nntp-multi-octets fn-nntp-make-result))))

; The reply constructors' session, for the arms' proofs with the
; constructors closed.
(defthm fn-ovw-session-of-single
  (equal (car (fn-nntp-single session text)) session)
  :hints (("Goal" :in-theory (enable fn-nntp-single fn-nntp-make-result))))

(defthm fn-ovw-session-of-multi
  (equal (car (fn-nntp-multi session initial lines)) session)
  :hints (("Goal" :in-theory (enable fn-nntp-multi fn-nntp-make-result))))

(defthm fn-ovw-session-of-multi-octets
  (equal (car (fn-nntp-multi-octets session initial lines)) session)
  :hints (("Goal" :in-theory (enable fn-nntp-multi-octets fn-nntp-make-result))))

; The reference readers of a range (books/nntp-responses.lisp), whose
; results the pinned OVER/XOVER arm answers: session kept, no cursor.
(defthm fn-ovw-over-range-session
  (equal (car (fn-nntp-over-range session archive token fn-arena)) session)
  :hints (("Goal" :in-theory (e/d (fn-nntp-over-range)
                                  (fn-nntp-single fn-nntp-multi fn-nntp-parse-range
                                   fn-nntp-group-range-numbers fn-nov-lines-for-numbers)))))

(defthm fn-ovw-xover-range-session
  (equal (car (fn-nntp-xover-range session archive token fn-arena)) session)
  :hints (("Goal" :in-theory (e/d (fn-nntp-xover-range)
                                  (fn-nntp-single fn-nntp-multi fn-nntp-parse-range
                                   fn-nntp-group-range-numbers fn-nov-lines-for-numbers)))))

(defthm fn-ovw-expand-of-over-range-effects
  (equal (fn-ovw-expand (cdr (fn-nntp-over-range session archive token fn-arena)) fn-arena fn-cat)
         (cdr (fn-nntp-over-range session archive token fn-arena)))
  :hints (("Goal" :in-theory (e/d (fn-nntp-over-range)
                                  (fn-nntp-single fn-nntp-multi fn-nntp-parse-range
                                   fn-nntp-group-range-numbers fn-nov-lines-for-numbers)))))

(defthm fn-ovw-expand-of-xover-range-effects
  (equal (fn-ovw-expand (cdr (fn-nntp-xover-range session archive token fn-arena)) fn-arena fn-cat)
         (cdr (fn-nntp-xover-range session archive token fn-arena)))
  :hints (("Goal" :in-theory (e/d (fn-nntp-xover-range)
                                  (fn-nntp-single fn-nntp-multi fn-nntp-parse-range
                                   fn-nntp-group-range-numbers fn-nov-lines-for-numbers)))))

(defthm fn-ovw-expand-of-close-list
  (equal (fn-ovw-expand (list (fn-nntp-close-effect)) fn-arena fn-cat)
         (list (fn-nntp-close-effect)))
  :hints (("Goal" :in-theory (enable fn-ovw-expand fn-ovw-cursor-effectp fn-nntp-close-effect))))

(defthm fn-ovw-expand-of-submit-list
  (equal (fn-ovw-expand (list (fn-served-submit-effect decision login account)) fn-arena fn-cat)
         (list (fn-served-submit-effect decision login account)))
  :hints (("Goal" :in-theory (enable fn-ovw-expand fn-ovw-cursor-effectp fn-served-submit-effect))))

(defthm fn-ovw-offeredp-of-expand
  (equal (fn-post-offeredp (fn-ovw-expand effects fn-arena fn-cat))
         (fn-post-offeredp effects))
  :hints (("Goal" :induct (fn-ovw-expand effects fn-arena fn-cat)
           :in-theory (enable fn-ovw-expand fn-ovw-cursor-effectp fn-post-offeredp
                              fn-nntp-begin-article-effect fn-nntp-reply-effect))))

(defthm fn-ovw-submission-of-expand
  (equal (fn-served-submission (fn-ovw-expand effects fn-arena fn-cat))
         (fn-served-submission effects))
  :hints (("Goal" :induct (fn-ovw-expand effects fn-arena fn-cat)
           :in-theory (enable fn-ovw-expand fn-ovw-cursor-effectp fn-served-submission
                              fn-nntp-reply-effect))))

(defthm fn-ovw-submission-login-of-expand
  (equal (fn-served-submission-login (fn-ovw-expand effects fn-arena fn-cat))
         (fn-served-submission-login effects))
  :hints (("Goal" :induct (fn-ovw-expand effects fn-arena fn-cat)
           :in-theory (enable fn-ovw-expand fn-ovw-cursor-effectp fn-served-submission-login
                              fn-nntp-reply-effect))))

(defthm fn-ovw-submission-account-of-expand
  (equal (fn-served-submission-account (fn-ovw-expand effects fn-arena fn-cat))
         (fn-served-submission-account effects))
  :hints (("Goal" :induct (fn-ovw-expand effects fn-arena fn-cat)
           :in-theory (enable fn-ovw-expand fn-ovw-cursor-effectp fn-served-submission-account
                              fn-nntp-reply-effect))))

(local
 (defthm fn-ovw-hdr-reply-status-first
   (let ((octets (fn-ovw-hdr-reply lines src t)))
     (not (and (consp octets) (equal (car octets) 50)
               (consp (cdr octets)) (equal (car (cdr octets)) 49))))
   :hints (("Goal" :in-theory (e/d (fn-ovw-hdr-reply fn-ovw-hdr-status fn-ovw-hdr-empty fn-ovw-status)
                                   (fn-nntp-stuff-lines))))))

(local
 (defthm fn-ovw-cursor-octets-status-first
   (let ((octets (fn-ovw-cursor-octets cur fn-arena fn-cat)))
     (not (and (consp octets) (equal (car octets) 50)
               (consp (cdr octets)) (equal (car (cdr octets)) 49))))
   :hints (("Goal" :in-theory (e/d (fn-ovw-cursor-octets fn-ovw-reply fn-ovw-empty-text fn-ovw-status)
                                   (fn-ovw-lines fn-nntp-stuff-lines fn-ovw-hdr-lines fn-ovw-hdr-reply
                                    fn-ovw-hdr-reply-status-first))
            :use ((:instance fn-ovw-hdr-reply-status-first
                             (lines (fn-ovw-hdr-lines (nth 0 cur) (nfix (nth 1 cur)) (nfix (nth 2 cur))
                                                      (nth 7 cur) (nth 3 cur) fn-arena fn-cat))
                             (src (nth 7 cur))))))))

(defthm fn-ovw-selectedp-of-expand
  (equal (fn-served-selectedp (fn-ovw-expand effects fn-arena fn-cat))
         (fn-served-selectedp effects))
  :hints (("Goal" :do-not-induct t
           :expand ((fn-ovw-expand effects fn-arena fn-cat))
           :in-theory (e/d (fn-served-selectedp fn-ovw-cursor-effectp fn-nntp-reply-effect)
                           (fn-ovw-cursor-octets fn-nnw-meta-initialp))
           :use ((:instance fn-ovw-cursor-octets-status-first (cur (car (cdr (car effects)))))
                 (:instance fn-nnw-stream-initial-status-first (cur (car (cdr (car effects)))))))))

(defun fn-ovw-spec (session v token legacyp server fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (let ((group (fn-nntp-session-group session))
        (range (fn-nntp-parse-range token)))
    (if (null group)
        (fn-ovw-status (fn-proto-text * :no-group-selected))
      (fn-ovw-reply (fn-ovw-lines group (nfix (fn-nntp-range-low range))
                                  (min (nfix (fn-nntp-range-high range))
                                       (nfix (- (fn-cat-group-next group fn-cat) 1)))
                                  server v fn-arena fn-cat)
                    legacyp t))))

(local
 (defthm fn-ovw-status-is-crlf
   (equal (fn-nntp-crlf (fn-nntp-string-octets text)) (fn-ovw-status text))
   :hints (("Goal" :in-theory (enable fn-ovw-status)))))

(defthm fn-ovw-over-range-cat-is-spec
  (and (equal (car (fn-nntp-over-range-cat session v token legacyp fn-arena fn-cat))
              session)
       (equal (cdr (fn-nntp-over-range-cat session v token legacyp fn-arena fn-cat))
              (list (fn-nntp-reply-effect (fn-ovw-spec session v token legacyp nil fn-arena fn-cat)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nntp-over-range-cat fn-scat-range-numbers fn-cnx-view-range
                            fn-ovw-spec fn-ovw-reply fn-ovw-lines
                            fn-nntp-single fn-nntp-multi fn-nntp-make-result fn-nntp-reply-effect
                            fn-ovw-empty-text)
                           (fn-cat-group-next-is-high fn-cat-group-next fn-cnx-range-aux
                            fn-scat-range-keep fn-nov-lines-for-numbers-cat fn-nntp-stuff-lines
                            fn-nntp-parse-range fn-ovw-status fn-nntp-crlf fn-nntp-string-octets)))))

(in-theory (disable fn-ovw-spec))

; The cursor arm, expanded, is the specification's reply at its server name.
(defthm fn-nntp-over-range-ovw-expands-to-spec
  (equal (fn-ovw-expand (cdr (fn-nntp-over-range-ovw session v token legacyp server fn-cat))
                        fn-arena fn-cat)
         (list (fn-nntp-reply-effect (fn-ovw-spec session v token legacyp server fn-arena fn-cat))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nntp-over-range-ovw fn-ovw-start fn-ovw-cursor-effect
                            fn-ovw-cursor-effectp fn-ovw-cursor-octets fn-ovw-expand fn-ovw-spec
                            fn-nntp-make-result fn-nntp-reply-effect)
                           (fn-ovw-lines fn-ovw-reply fn-ovw-status fn-nntp-parse-range
                            fn-cat-group-next)))))

(in-theory (disable fn-nntp-over-range-ovw-expands-to-spec))

; The cursor arm with no server name expands to the plain unbounded reader.
; (With a name: fn-nntp-over-range-ovw-expands-to-over-range-served-cat,
; below the served reader.)
(defthm fn-nntp-over-range-ovw-expands-to-over-range-cat
  (and (equal (car (fn-nntp-over-range-ovw session v token legacyp server fn-cat))
              session)
       (equal (fn-ovw-expand (cdr (fn-nntp-over-range-ovw session v token legacyp nil fn-cat))
                             fn-arena fn-cat)
              (cdr (fn-nntp-over-range-cat session v token legacyp fn-arena fn-cat))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nntp-over-range-ovw fn-ovw-start fn-ovw-cursor-effect
                            fn-ovw-cursor-effectp fn-ovw-cursor-octets fn-ovw-expand fn-ovw-spec
                            fn-nntp-make-result fn-nntp-reply-effect fn-ovw-over-range-cat-is-spec)
                           (fn-ovw-lines fn-ovw-reply fn-ovw-status fn-nntp-parse-range
                            fn-cat-group-next fn-nntp-over-range-cat)))))

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

(defun fn-scat-group-summary-pass (archive group v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v)))
  (let ((l (fn-scat-range-numbers group 1 *fn-nntp-max-article-number* v fn-cat)))
    (if (consp l)
        (list (len l) (car l) (fn-scat-last-number l))
      (let ((watermark (fn-next-number group (fn-state-nexts archive))))
        (list 0 watermark (if (posp watermark) (- watermark 1) 0))))))

(defthm fn-scat-group-summary-pass-is-archive
  (implies (and (fn-cnx-freshp fn-cat) group
                (equal (fn-state-articles archive) (fn-cat-view-articles v fn-arena fn-cat)))
           (equal (fn-scat-group-summary-pass archive group v fn-cat)
                  (fn-nntp-group-summary archive group)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nntp-group-summary)
                           (fn-scat-range-numbers fn-nntp-group-range-numbers
                            fn-cat-view-articles fn-cnx-freshp fn-next-number)))))

; Raw compatibility readers retain visible identities even when the payload
; is reclaimed or metadata declares it unavailable. The catalog live table
; and fn-scv-* instead describe available reader rows. Never equate the two.
; Available served command adapters use catalog-available-readers directly.
(local
 (defthm fn-scat-number-seq-binds
   (implies (and (natp i) (fn-cat-number-seq g n c i))
            (and (natp (fn-cat-number-seq g n c i))
                 (<= i (fn-cat-number-seq g n c i))
                 (< (fn-cat-number-seq g n c i) (+ i (len c)))
                 (equal (fn-held-number-in g (nth (- (fn-cat-number-seq g n c i) i) c)) n)))
   :hints (("Goal" :induct (fn-cat-number-seq g n c i)
            :in-theory (e/d (fn-cat-number-seq) (fn-held-number-in))))))

(defun fn-scat-raw-keptp (group k v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v)
                  :guard-hints (("Goal" :in-theory (disable fn-cat-count-is-len fn-cat-at-is-nth
                                                            fn-cat-group-number-is-number-seq)))))
  (let ((s (fn-cat-group-number group k fn-cat)))
    (and (natp s) (< s (fn-cat-count fn-cat))
         (fn-cat-visible-at s (nfix v) fn-cat)
         (posp k) (<= k *fn-nntp-max-article-number*)
         (fn-scat-msgid-idp (fn-record-msgid (fn-cat-at s fn-cat)))
         t)))

(defun fn-scat-raw-count-p (group k top v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (and (natp k) (natp top) (natp v))
                  :measure (nfix (- (+ 1 (nfix top)) (nfix k)))))
  (if (and (natp k) (natp top) (<= k top))
      (+ (if (fn-scat-raw-keptp group k v fn-cat) 1 0)
         (fn-scat-raw-count-p group (+ 1 k) top v fn-cat))
    0))

(defun fn-scat-raw-first-p (group k top v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (and (natp k) (natp top) (natp v))
                  :measure (nfix (- (+ 1 (nfix top)) (nfix k)))))
  (if (and (natp k) (natp top) (<= k top))
      (if (fn-scat-raw-keptp group k v fn-cat)
          k
        (fn-scat-raw-first-p group (+ 1 k) top v fn-cat))
    0))

(defun fn-scat-raw-last-p (group k v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (and (natp k) (natp v))))
  (if (posp k)
      (if (fn-scat-raw-keptp group k v fn-cat)
          k
        (fn-scat-raw-last-p group (- k 1) v fn-cat))
    0))

(local (in-theory (disable fn-scat-raw-keptp)))

(defun fn-scat-view-list (group k top v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (and (natp k) (natp top) (natp v))
                  :verify-guards nil
                  :measure (nfix (- (+ 1 (nfix top)) (nfix k)))))
  (if (and (natp k) (natp top) (<= k top))
      (if (fn-scat-raw-keptp group k v fn-cat)
          (cons k (fn-scat-view-list group (+ 1 k) top v fn-cat))
        (fn-scat-view-list group (+ 1 k) top v fn-cat))
    nil))

(local
 (defthm fn-scat-range-keep-aux-is-view-list
   (implies (natp v)
            (equal (fn-scat-range-keep group (fn-cnx-range-aux group k top v fn-cat) fn-cat)
                   (fn-scat-view-list group k top v fn-cat)))
   :hints (("Goal" :induct (fn-scat-view-list group k top v fn-cat)
            :in-theory (e/d (fn-scat-raw-keptp fn-cnx-view-seq)
                            (fn-held-withdrawn fn-held-number-in fn-scat-msgid-idp)))
           ("Subgoal *1/2" :use ((:instance fn-scat-number-seq-binds (g group) (n k) (c fn-cat) (i 0))))
           ("Subgoal *1/1" :use ((:instance fn-scat-number-seq-binds (g group) (n k) (c fn-cat) (i 0)))))))

(local
 (defthm fn-scat-view-list-len
   (equal (len (fn-scat-view-list group k top v fn-cat))
          (fn-scat-raw-count-p group k top v fn-cat))))

(local
 (defthm fn-scat-view-list-car
   (equal (fn-scat-raw-first-p group k top v fn-cat)
          (let ((l (fn-scat-view-list group k top v fn-cat))) (if (consp l) (car l) 0)))
   :rule-classes nil))

(local
 (defthm fn-scat-view-list-consp
   (iff (consp (fn-scat-view-list group k top v fn-cat))
        (posp (fn-scat-raw-count-p group k top v fn-cat)))))

(local
 (defthm fn-scat-view-list-empty
   (implies (< top k)
            (equal (fn-scat-view-list group k top v fn-cat) nil))))

(local
 (defthm fn-scat-keptp-above-max
   (implies (< *fn-nntp-max-article-number* k)
            (not (fn-scat-raw-keptp group k v fn-cat)))
   :hints (("Goal" :in-theory (enable fn-scat-raw-keptp)))))

(local
 (defthm fn-scat-view-list-snoc
   (implies (and (natp k) (natp top) (<= k top))
            (equal (fn-scat-view-list group k top v fn-cat)
                   (append (fn-scat-view-list group k (- top 1) v fn-cat)
                           (if (fn-scat-raw-keptp group top v fn-cat) (list top) nil))))
   :rule-classes nil
   :hints (("Goal" :induct (fn-scat-view-list group k top v fn-cat)
            :expand ((fn-scat-view-list group k top v fn-cat)
                     (fn-scat-view-list group k (+ -1 top) v fn-cat))))))

(local
 (defthm fn-scat-last-number-of-append-one
   (equal (fn-scat-last-number (append l (list x))) x)
   :hints (("Goal" :in-theory (enable fn-scat-last-number)))))

(local
 (defthm fn-scat-view-list-last
   (implies (natp top)
            (equal (fn-scat-raw-last-p group top v fn-cat)
                   (fn-scat-last-number (fn-scat-view-list group 1 top v fn-cat))))
   :rule-classes nil
   :hints (("Goal" :induct (fn-scat-raw-last-p group top v fn-cat))
           ("Subgoal *1/2" :use ((:instance fn-scat-view-list-snoc (k 1))))
           ("Subgoal *1/1" :use ((:instance fn-scat-view-list-snoc (k 1)))))))

(local
 (defthm fn-scat-view-list-clamp
   (implies (natp top)
            (equal (fn-scat-view-list group k (min top *fn-nntp-max-article-number*) v fn-cat)
                   (fn-scat-view-list group k top v fn-cat)))
   :hints (("Goal" :induct (fn-scat-view-list group k top v fn-cat)))))

(local
 (defthm fn-scat-range-numbers-at-view
   (implies (natp v)
            (equal (fn-scat-range-numbers group 1 *fn-nntp-max-article-number* v fn-cat)
                   (fn-scat-view-list group 1 (fn-cat-group-high group fn-cat) v fn-cat)))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-cnx-view-range)
                            (fn-scat-view-list fn-cnx-range-aux fn-scat-range-keep))
            :use ((:instance fn-scat-view-list-clamp (k 1)
                             (top (fn-cat-group-high group fn-cat))))))))

;; The table answers at V: V is the count and no withdrawal is at or past it.
(defun fn-scat-top-viewp (v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v)))
  (and (equal v (fn-cat-count fn-cat))
       (<= (fn-cat-horizon fn-cat) v)))

(defthm fn-scat-top-viewp-gives
  (implies (fn-scat-top-viewp v fn-cat)
           (and (fn-cat-rowsp fn-cat) (equal v (len fn-cat))
                (<= (fn-cat-horizon-of fn-cat) v)))
  :rule-classes :forward-chaining)

(defun fn-scat-group-summary (archive group v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v)))
  (fn-scat-group-summary-pass archive group v fn-cat))

(defthm fn-scat-group-summary-by-definition
  (equal (fn-scat-group-summary archive group v fn-cat)
         (fn-scat-group-summary-pass archive group v fn-cat)))

(defthm fn-scat-group-summary-is-archive
  (implies (and (fn-cnx-freshp fn-cat) group
                (equal (fn-state-articles archive) (fn-cat-view-articles v fn-arena fn-cat)))
           (equal (fn-scat-group-summary archive group v fn-cat)
                  (fn-nntp-group-summary archive group)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-scat-group-summary fn-scat-group-summary-pass
                               fn-nntp-group-summary fn-cat-view-articles fn-cnx-freshp))))

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

(defun fn-scat-group-low-pass (group v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v)))
  (let ((l (fn-scat-range-numbers group 1 *fn-nntp-max-article-number* v fn-cat)))
    (if (consp l) (car l) 0)))

(defthm fn-scat-group-low-pass-is-archive
  (implies (and (fn-cnx-freshp fn-cat) group)
           (equal (fn-scat-group-low-pass group v fn-cat)
                  (fn-nntp-group-low group (fn-cat-view-articles v fn-arena fn-cat))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-scat-range-numbers fn-nntp-group-range-numbers
                               fn-cat-view-articles fn-cnx-freshp))))

; Raw compatibility low uses the retained-identity range pass. The actual
; availability adapter has its own maintained fn-scat-available-low.
(defun fn-scat-group-low (group v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v)))
  (fn-scat-group-low-pass group v fn-cat))

(defthm fn-scat-group-low-by-definition
  (equal (fn-scat-group-low group v fn-cat)
         (fn-scat-group-low-pass group v fn-cat)))

(defthm fn-scat-group-low-is-archive
  (implies (and (fn-cnx-freshp fn-cat) group)
           (equal (fn-scat-group-low group v fn-cat)
                  (fn-nntp-group-low group (fn-cat-view-articles v fn-arena fn-cat))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-scat-group-low fn-scat-group-low-pass
                               fn-nntp-group-low fn-cat-view-articles fn-cnx-freshp))))

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
    (fn-nntp-single session (fn-proto-text * :no-group))))

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
    (fn-nntp-single session (fn-proto-text * :no-group))))

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
              (fn-nntp-single session (fn-proto-text * :no-group-selected))
            (if (mbe :logic (member-equal group (fn-state-groups archive))
                     :exec (fn-ag-member group (fn-state-groups archive)))
                (fn-nntp-listgroup-result-cat session archive group all-range v fn-cat)
              (fn-nntp-single session (fn-proto-text * :no-group-selected)))))
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
                (fn-nntp-single session (fn-proto-text * :syntax))))
          (fn-nntp-single session (fn-proto-text * :syntax)))))))

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

; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-scat-counts-lines-loop (archive groups closed v fn-cat acc)
  (declare (xargs :stobjs fn-cat :guard (and (natp v) (true-listp acc)) :verify-guards nil))
  (if (consp groups)
      (fn-scat-counts-lines-loop archive
                                 (cdr groups)
                                 closed
                                 v
                                 fn-cat
                                 (cons (fn-nntp-counts-summary-line (car groups)
                                                                    (fn-scat-group-summary archive
                                                                                           (car groups)
                                                                                           v
                                                                                           fn-cat)
                                                                    closed)
                                       acc))
    (revappend acc nil)))

(defun fn-scat-counts-lines (archive groups closed v fn-cat)
  (declare (xargs :verify-guards nil :stobjs fn-cat :guard (natp v)))
  (mbe :logic
       (if (consp groups)
           (cons (fn-nntp-counts-summary-line
                  (car groups) (fn-scat-group-summary archive (car groups) v fn-cat)
                  closed)
                 (fn-scat-counts-lines archive (cdr groups) closed v fn-cat))
         nil)
       :exec (fn-scat-counts-lines-loop archive groups closed v fn-cat nil)))

(local
 (defthm fn-scat-counts-lines-loop-is-revappend
   (equal (fn-scat-counts-lines-loop archive groups closed v fn-cat acc)
          (revappend acc (fn-scat-counts-lines archive groups closed v fn-cat)))
   :hints (("Goal" :induct (fn-scat-counts-lines-loop archive groups closed v fn-cat acc)
                   :in-theory (union-theories '(fn-scat-counts-lines-loop fn-scat-counts-lines revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-scat-counts-lines-loop)

(verify-guards fn-scat-counts-lines
  :hints (("Goal" :in-theory (union-theories '(revappend fn-scat-counts-lines)
                                                  (union-theories (theory 'minimal-theory)
                                                                  (executable-counterpart-theory :here)))
                  :use ((:instance fn-scat-counts-lines-loop-is-revappend (acc nil))))))


(defthm fn-scat-counts-lines-is-archive
  (implies (and (fn-cnx-freshp fn-cat) (not (member-equal nil groups))
                (equal (fn-state-articles archive) (fn-cat-view-articles v fn-arena fn-cat)))
           (equal (fn-scat-counts-lines archive groups closed v fn-cat)
                  (fn-nntp-counts-lines archive groups closed)))
  :hints (("Goal" :induct (fn-scat-counts-lines archive groups closed v fn-cat)
           :in-theory (e/d (fn-nntp-counts-lines fn-nntp-counts-line)
                           (fn-scat-group-summary fn-nntp-group-summary
                            fn-cat-view-articles fn-cnx-freshp
                            fn-nntp-counts-summary-line)))))

;; KEYSTONE (PKT-703, the catalog arm the host runs: host/owner-host.lisp
;; fn-owner-chunk-span-at -> fn-scr-command (books/served-catalog-chain) ->
;; fn-nntp-archive-command-cat -> fn-nntp-list-counts-command-cat -> this):
;; line I of the served LIST COUNTS carries line I of LIST ACTIVE's status
;; (RFC 6048 section 2.2.2), for any catalog state; CLOSED is the
;; environment's (fn-nntp-env-closed).
(defthm fn-scat-counts-lines-status-is-the-active-status
  (equal (fn-nlc-status-octet (nth i (fn-scat-counts-lines archive groups closed v fn-cat)))
         (fn-nlc-status-octet (nth i (fn-nntp-active-status-lines archive groups closed))))
  :hints (("Goal" :induct (nth i groups)
           :expand ((fn-scat-counts-lines archive groups closed v fn-cat)
                    (fn-nntp-active-status-lines archive groups closed))
           :in-theory (e/d ()
                           (fn-nlc-status-octet fn-nntp-counts-summary-line
                            fn-nntp-active-status-line fn-scat-group-summary)))))

(defun fn-nntp-list-counts-command-cat (session archive closed args v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v)))
  (if (null args)
      (fn-nntp-multi session (fn-proto-text "LIST" :newsgroups)
                     (fn-scat-counts-lines archive (fn-state-groups archive) closed v fn-cat))
    (if (and (consp args) (null (cdr args)))
        (let ((parsed (fn-wildmat-parse (car args))))
          (if (fn-wildmat-result-okp parsed)
              (fn-nntp-multi session (fn-proto-text "LIST" :newsgroups)
                             (fn-scat-counts-lines
                              archive
                              (fn-nntp-filter-groups-by-wildmat
                               (fn-wildmat-result-value parsed) (fn-state-groups archive))
                              closed v fn-cat))
            (fn-nntp-single session (fn-proto-text * :syntax))))
      (fn-nntp-single session (fn-proto-text * :syntax)))))

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

;; The group names of a state are strings (fn-statep), and the wildmat filter
;; keeps a subset of them: what LIST COUNTS needs of the archive, where it
;; used to ask fn-nntp-projectionp's safe names (lane join-f2: the catalog
;; premise no longer asks the projection recognizer, whose article-count
;; conjunct no store fact gives).
(local
 (defthm fn-scat-filter-keeps-strings
   (implies (fn-string-listp groups)
            (fn-string-listp (fn-nntp-filter-groups-by-wildmat patterns groups)))
   :hints (("Goal" :induct (fn-nntp-filter-groups-by-wildmat patterns groups)
            :in-theory (e/d (fn-nntp-filter-groups-by-wildmat fn-string-listp)
                            (fn-nntp-group-matches-parsed-wildmatp))))))

(local
 (defthm fn-scat-string-list-has-no-nil
   (implies (fn-string-listp groups) (not (member-equal nil groups)))
   :hints (("Goal" :in-theory (enable fn-string-listp)))))

(local
 (defthm fn-scat-state-groups-are-strings
   (implies (fn-statep archive) (fn-string-listp (fn-state-groups archive)))
   :hints (("Goal" :in-theory (enable fn-statep)))))

(defthm fn-nntp-list-counts-command-cat-is-archive
  (implies (and (fn-cnx-freshp fn-cat) (fn-statep archive)
                (equal (fn-state-articles archive) (fn-cat-view-articles v fn-arena fn-cat)))
           (equal (fn-nntp-list-counts-command-cat session archive closed args v fn-cat)
                  (fn-nntp-list-counts-command session archive closed args)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nntp-list-counts-command fn-nntp-list-counts)
                           (fn-scat-counts-lines fn-nntp-counts-lines
                            fn-cat-view-articles fn-cnx-freshp fn-statep
                            fn-wildmat-parse fn-nntp-filter-groups-by-wildmat
                            fn-nntp-multi fn-nntp-single)))))

;;; HDR/XHDR (RFC 3977 section 8.5, RFC 2980 section 2.6): the three forms,
;;; the current article and the range through the number table, the
;;; Message-ID form through keystone A's finder.

; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-nntp-hdr-lines-for-numbers-cat-loop (field group numbers v fn-arena fn-cat acc)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard (and (fn-scat-guard) (true-listp acc)) :verify-guards nil))
  (if (consp numbers)
      (let* ((number (car numbers))
             (article (fn-scat-available-article group number v fn-arena fn-cat))
             (content (if (consp article)
                          (fn-scol-hdr-content field article fn-arena fn-cat)
                        (list :error))))
        (if (fn-nntp-hdr-okp content)
            (fn-nntp-hdr-lines-for-numbers-cat-loop field
                                                    group
                                                    (cdr numbers)
                                                    v
                                                    fn-arena
                                                    fn-cat
                                                    (cons (fn-nntp-hdr-line (fn-nntp-decimal-field number)
                                                                            (fn-nntp-hdr-octets content))
                                                          acc))
          (fn-nntp-hdr-lines-for-numbers-cat-loop field
                                                  group
                                                  (cdr numbers)
                                                  v
                                                  fn-arena
                                                  fn-cat
                                                  acc)))
    (revappend acc nil)))

(defun fn-nntp-hdr-lines-for-numbers-cat (field group numbers v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard (fn-scat-guard) :verify-guards nil))
  (mbe :logic
       (if (consp numbers)
           (let* ((number (car numbers))
                  (article (fn-scat-available-article group number v fn-arena fn-cat))
                  (content (if (consp article)
                               (fn-scol-hdr-content field article fn-arena fn-cat)
                             (list :error))))
             (if (fn-nntp-hdr-okp content)
                 (cons (fn-nntp-hdr-line (fn-nntp-decimal-field number)
                                         (fn-nntp-hdr-octets content))
                       (fn-nntp-hdr-lines-for-numbers-cat field group (cdr numbers) v fn-arena fn-cat))
               (fn-nntp-hdr-lines-for-numbers-cat field group (cdr numbers) v fn-arena fn-cat)))
         nil)
       :exec (fn-nntp-hdr-lines-for-numbers-cat-loop field group numbers v fn-arena fn-cat nil)))

(local
 (defthm fn-nntp-hdr-lines-for-numbers-cat-loop-is-revappend
   (equal (fn-nntp-hdr-lines-for-numbers-cat-loop field group numbers v fn-arena fn-cat acc)
          (revappend acc (fn-nntp-hdr-lines-for-numbers-cat field group numbers v fn-arena fn-cat)))
   :hints (("Goal" :induct (fn-nntp-hdr-lines-for-numbers-cat-loop field group numbers v fn-arena fn-cat acc)
                   :in-theory (union-theories '(fn-nntp-hdr-lines-for-numbers-cat-loop fn-nntp-hdr-lines-for-numbers-cat revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))


(defthm fn-nntp-hdr-lines-for-numbers-cat-is-archive
  (implies (and (fn-cnx-freshp fn-cat) (fn-scol-okp fn-arena fn-cat) group)
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
        (fn-nntp-single session (fn-proto-text * :syntax))
      (let ((field (car args)) (rest (cdr args))
            (group (fn-nntp-session-group session)))
        (if (null rest)
            (let ((current (fn-nntp-session-current session)))
              (if (null group)
                  (fn-nntp-single session (fn-proto-text * :no-group-selected))
                (if (null current)
                    (fn-nntp-single session (fn-proto-text * :no-current))
                  (let ((article (fn-scat-available-article group current v fn-arena fn-cat)))
                    (if (not (consp article))
                        (fn-nntp-single session (fn-proto-text * :no-current))
                      (let ((content (fn-scol-hdr-content field article fn-arena fn-cat)))
                        (if (fn-nntp-hdr-okp content)
                            (fn-nntp-multi
                             session (fn-nntp-hdr-initial legacyp)
                             (list (fn-nntp-hdr-line (fn-nntp-decimal-field current)
                                                     (fn-nntp-hdr-octets content))))
                          (fn-nntp-single
                           session (fn-proto-text * :no-framing)))))))))
          (if (and (consp rest) (null (cdr rest)))
              (let ((token (car rest)))
                (if (fn-nntp-range-okp (fn-nntp-parse-range token))
                    (fn-nntp-hdr-range-ovw
                     session v token
                     (fn-ovw-hdr-source (if legacyp :xhdr :hdr) field :all nil) fn-cat)
                  (if (fn-nntp-message-id-tokenp token)
                      (let ((article (fn-scat-msgid-article (fn-nntp-token-string token)
                                                            v fn-arena fn-cat)))
                        (if (not (consp article))
                            (fn-nntp-single session (fn-proto-text * :no-msgid))
                          (let ((content (fn-scol-hdr-content field article fn-arena fn-cat)))
                            (if (fn-nntp-hdr-okp content)
                                (fn-nntp-multi
                                 session (fn-nntp-hdr-initial legacyp)
                                 (list (fn-nntp-hdr-line (if legacyp
                                                             (fn-nov-scrub token)
                                                           (fn-nntp-decimal-field 0))
                                                         (fn-nntp-hdr-octets content))))
                              (fn-nntp-single session (fn-proto-text * :no-framing))))))
                    (fn-nntp-single session (fn-proto-text * :syntax)))))
            (fn-nntp-single session (fn-proto-text * :syntax)))))))

;;; The header range arms on the cursor, expanded (lane cold-line).  Each arm
;;; is equated with the arm it replaced (its whole-range body, kept below as
;;; a local -OLD function with its original proof against the archive), and
;;; through it with the archive reader: fn-nntp-hdr-command-cat-is-archive,
;;; fn-nntp-xpat-response-cat-is-archive and fn-rcompat-hdr-cat-is-hdr now
;;; hold modulo fn-ovw-expand, as OVER's arm does.

(defthm fn-ovw-hdr-lines-of-start
  (equal (fn-ovw-hdr-lines group (nfix low)
                           (min (nfix high) (nfix (- (fn-cat-group-next group fn-cat) 1)))
                           src v fn-arena fn-cat)
         (fn-ovw-hdr-lines-for-numbers group (fn-scat-range-numbers group (nfix low) (nfix high) v fn-cat)
                                       src v fn-arena fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-ovw-hdr-lines fn-scat-range-numbers fn-cnx-view-range)
                                  (fn-cnx-range-aux fn-scat-range-keep fn-ovw-hdr-lines-for-numbers
                                   fn-cat-group-next)))))

(defthm fn-nntp-hdr-range-ovw-expands
  (and (equal (car (fn-nntp-hdr-range-ovw session v token (fn-ovw-hdr-source form field patterns xref) fn-cat))
              session)
       (equal (fn-ovw-expand (cdr (fn-nntp-hdr-range-ovw session v token
                                                         (fn-ovw-hdr-source form field patterns xref) fn-cat))
                             fn-arena fn-cat)
              (list (fn-nntp-reply-effect
                     (if (fn-nntp-session-group session)
                         (fn-ovw-hdr-reply
                          (fn-ovw-hdr-lines-for-numbers
                           (fn-nntp-session-group session)
                           (fn-scat-range-numbers (fn-nntp-session-group session)
                                                  (nfix (fn-nntp-range-low (fn-nntp-parse-range token)))
                                                  (nfix (fn-nntp-range-high (fn-nntp-parse-range token)))
                                                  v fn-cat)
                           (fn-ovw-hdr-source form field patterns xref) v fn-arena fn-cat)
                          (fn-ovw-hdr-source form field patterns xref) t)
                       (fn-ovw-status (fn-proto-text * :no-group-selected)))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nntp-hdr-range-ovw fn-ovw-hdr-start fn-ovw-cursor-effect
                            fn-ovw-cursor-effectp fn-ovw-cursor-octets fn-ovw-expand
                            fn-nntp-make-result fn-nntp-reply-effect fn-ovw-hdr-cursor)
                           (fn-ovw-hdr-lines fn-ovw-hdr-reply fn-ovw-status fn-nntp-parse-range
                            fn-cat-group-next fn-ovw-hdr-lines-for-numbers fn-scat-range-numbers
                            fn-ovw-hdr-source))
           :use ((:instance fn-ovw-hdr-lines-of-start
                            (group (fn-nntp-session-group session))
                            (low (fn-nntp-range-low (fn-nntp-parse-range token)))
                            (high (fn-nntp-range-high (fn-nntp-parse-range token)))
                            (src (fn-ovw-hdr-source form field patterns xref)))))))

(defthm fn-ovw-hdr-lines-for-numbers-is-hdr-cat
  (implies (not (equal form :xpat))
           (equal (fn-ovw-hdr-lines-for-numbers group numbers (fn-ovw-hdr-source form field patterns nil)
                                                v fn-arena fn-cat)
                  (fn-nntp-hdr-lines-for-numbers-cat field group numbers v fn-arena fn-cat)))
  :hints (("Goal" :induct (fn-nntp-hdr-lines-for-numbers-cat field group numbers v fn-arena fn-cat)
           :in-theory (e/d (fn-ovw-hdr-content fn-ovw-hdr-keepp fn-ovw-hdr-source)
                           (fn-scat-available-article fn-scol-hdr-content fn-nntp-hdr-okp
                            fn-nntp-hdr-line fn-nntp-hdr-octets fn-nntp-decimal-field)))))

(defthm fn-ovw-hdr-reply-is-hdr-multi
  (implies (not (equal form :xpat))
           (equal (list (fn-nntp-reply-effect
                         (fn-ovw-hdr-reply lines (fn-ovw-hdr-source form field patterns xref) t)))
                  (cdr (if (consp lines)
                           (fn-nntp-multi session (fn-nntp-hdr-initial (not (equal form :hdr))) lines)
                         (if (equal form :xhdr)
                             (fn-nntp-single session (fn-proto-text * :none-selected))
                           (fn-nntp-single session (fn-proto-text * :empty-range)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-ovw-hdr-reply fn-ovw-hdr-status fn-ovw-hdr-empty fn-ovw-status
                                   fn-ovw-hdr-source fn-nntp-multi fn-nntp-single fn-nntp-make-result
                                   fn-nntp-hdr-initial)
                                  (fn-nntp-stuff-lines fn-ovw-status-is-crlf)))))

(defthm fn-ovw-hdr-reply-is-xpat-multi
  (equal (list (fn-nntp-reply-effect
                (fn-ovw-hdr-reply lines (fn-ovw-hdr-source :xpat field patterns xref) t)))
         (cdr (fn-nntp-multi session (fn-nntp-hdr-initial t) lines)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-ovw-hdr-reply fn-ovw-hdr-status fn-ovw-hdr-empty fn-ovw-status
                                   fn-ovw-hdr-source fn-nntp-multi fn-nntp-make-result
                                   fn-nntp-hdr-initial)
                                  (fn-nntp-stuff-lines fn-ovw-status-is-crlf))
           :cases ((consp lines)))
          ("Subgoal 2" :expand ((fn-nntp-stuff-lines lines)))))

;; The reply of one status line.
(local
 (defthm fn-scat-single-is-status
   (equal (cdr (fn-nntp-single session text))
          (list (fn-nntp-reply-effect (fn-ovw-status text))))
   :hints (("Goal" :in-theory (e/d (fn-nntp-single fn-nntp-make-result fn-ovw-status) (fn-ovw-status-is-crlf))))))

(local
 (defthm fn-scat-expand-of-one-reply
   (equal (fn-ovw-expand (list (list :reply x)) fn-arena fn-cat)
          (list (list :reply x)))
   :hints (("Goal" :in-theory (enable fn-ovw-expand fn-ovw-cursor-effectp fn-nnw-meta-effectp)))))

;; The arm it replaced (whole range in one step), as a proof device.
(local
 (defun fn-scat-hdr-command-old (session args v legacyp fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard (fn-scat-guard) :verify-guards nil))
  (if (not (and (consp args) (fn-nntp-hdr-fieldp (car args))))
        (fn-nntp-single session (fn-proto-text * :syntax))
      (let ((field (car args)) (rest (cdr args))
            (group (fn-nntp-session-group session)))
        (if (null rest)
            (let ((current (fn-nntp-session-current session)))
              (if (null group)
                  (fn-nntp-single session (fn-proto-text * :no-group-selected))
                (if (null current)
                    (fn-nntp-single session (fn-proto-text * :no-current))
                  (let ((article (fn-scat-available-article group current v fn-arena fn-cat)))
                    (if (not (consp article))
                        (fn-nntp-single session (fn-proto-text * :no-current))
                      (let ((content (fn-scol-hdr-content field article fn-arena fn-cat)))
                        (if (fn-nntp-hdr-okp content)
                            (fn-nntp-multi
                             session (fn-nntp-hdr-initial legacyp)
                             (list (fn-nntp-hdr-line (fn-nntp-decimal-field current)
                                                     (fn-nntp-hdr-octets content))))
                          (fn-nntp-single
                           session (fn-proto-text * :no-framing)))))))))
          (if (and (consp rest) (null (cdr rest)))
              (let ((token (car rest)))
                (if (fn-nntp-range-okp (fn-nntp-parse-range token))
                    (if (null group)
                        (fn-nntp-single session (fn-proto-text * :no-group-selected))
                      (let* ((range (fn-nntp-parse-range token))
                             (numbers (fn-scat-range-numbers
                                       group (nfix (fn-nntp-range-low range))
                                       (nfix (fn-nntp-range-high range)) v fn-cat))
                             (lines (fn-nntp-hdr-lines-for-numbers-cat
                                     field group numbers v fn-arena fn-cat)))
                        (if (consp lines)
                            (fn-nntp-multi session (fn-nntp-hdr-initial legacyp) lines)
                          (if legacyp
                              (fn-nntp-single session (fn-proto-text * :none-selected))
                            (fn-nntp-single session (fn-proto-text * :empty-range))))))
                  (if (fn-nntp-message-id-tokenp token)
                      (let ((article (fn-scat-msgid-article (fn-nntp-token-string token)
                                                            v fn-arena fn-cat)))
                        (if (not (consp article))
                            (fn-nntp-single session (fn-proto-text * :no-msgid))
                          (let ((content (fn-scol-hdr-content field article fn-arena fn-cat)))
                            (if (fn-nntp-hdr-okp content)
                                (fn-nntp-multi
                                 session (fn-nntp-hdr-initial legacyp)
                                 (list (fn-nntp-hdr-line (if legacyp
                                                             (fn-nov-scrub token)
                                                           (fn-nntp-decimal-field 0))
                                                         (fn-nntp-hdr-octets content))))
                              (fn-nntp-single session (fn-proto-text * :no-framing))))))
                    (fn-nntp-single session (fn-proto-text * :syntax)))))
            (fn-nntp-single session (fn-proto-text * :syntax))))))))

(local
 (defthm fn-scat-hdr-command-old-is-archive
  (implies (and (fn-cnx-freshp fn-cat) (fn-scol-okp fn-arena fn-cat)
                (equal (fn-state-articles archive) (fn-cat-view-articles v fn-arena fn-cat)))
           (equal (fn-scat-hdr-command-old session args v legacyp fn-arena fn-cat)
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
                            fn-nntp-range-okp fn-nntp-parse-range-ok-has-natural-bounds))))))

(local
 (defthm fn-scat-hdr-command-cat-is-old
   (and (equal (car (fn-nntp-hdr-command-cat session args v legacyp fn-arena fn-cat))
               (car (fn-scat-hdr-command-old session args v legacyp fn-arena fn-cat)))
        (equal (fn-ovw-expand (cdr (fn-nntp-hdr-command-cat session args v legacyp fn-arena fn-cat))
                              fn-arena fn-cat)
               (cdr (fn-scat-hdr-command-old session args v legacyp fn-arena fn-cat))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-nntp-hdr-command-cat fn-scat-hdr-command-old fn-nntp-hdr-initial)
                            (fn-nntp-hdr-range-ovw fn-ovw-hdr-source fn-ovw-hdr-reply
                             fn-ovw-hdr-lines-for-numbers fn-scat-range-numbers
                             fn-nntp-hdr-lines-for-numbers-cat fn-scat-available-article
                             fn-scat-msgid-article fn-scol-hdr-content fn-nntp-multi fn-nntp-single
                             fn-nntp-parse-range fn-nntp-range-okp fn-nntp-hdr-fieldp
                             fn-nntp-message-id-tokenp fn-ovw-status))
            :use ((:instance fn-ovw-hdr-reply-is-hdr-multi
                             (form (if legacyp :xhdr :hdr)) (field (car args)) (patterns :all) (xref nil)
                             (lines (fn-nntp-hdr-lines-for-numbers-cat
                                     (car args) (fn-nntp-session-group session)
                                     (fn-scat-range-numbers
                                      (fn-nntp-session-group session)
                                      (nfix (fn-nntp-range-low (fn-nntp-parse-range (cadr args))))
                                      (nfix (fn-nntp-range-high (fn-nntp-parse-range (cadr args))))
                                      v fn-cat)
                                     v fn-arena fn-cat))))))))

; Modulo the cursor: the arm, expanded, is the archive reader's reply.
(defthm fn-nntp-hdr-command-cat-is-archive
  (implies (and (fn-cnx-freshp fn-cat) (fn-scol-okp fn-arena fn-cat)
                (equal (fn-state-articles archive) (fn-cat-view-articles v fn-arena fn-cat)))
           (and (equal (car (fn-nntp-hdr-command-cat session args v legacyp fn-arena fn-cat))
                       (car (fn-nntp-hdr-command session archive args legacyp fn-arena)))
                (equal (fn-ovw-expand (cdr (fn-nntp-hdr-command-cat session args v legacyp fn-arena fn-cat))
                                      fn-arena fn-cat)
                       (cdr (fn-nntp-hdr-command session archive args legacyp fn-arena)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-nntp-hdr-command-cat fn-scat-hdr-command-old fn-nntp-hdr-command
                               fn-scat-hdr-command-cat-is-old fn-scat-hdr-command-old-is-archive)
           :use (fn-scat-hdr-command-cat-is-old fn-scat-hdr-command-old-is-archive))))

;;; XPAT (RFC 2980 section 2.9).

(verify-guards fn-nntp-hdr-lines-for-numbers-cat-loop)

(verify-guards fn-nntp-hdr-lines-for-numbers-cat
  :hints (("Goal" :in-theory (union-theories '(revappend fn-nntp-hdr-lines-for-numbers-cat)
                                                  (union-theories (theory 'minimal-theory)
                                                                  (executable-counterpart-theory :here)))
                  :use ((:instance fn-nntp-hdr-lines-for-numbers-cat-loop-is-revappend (acc nil))))))
(verify-guards fn-nntp-hdr-command-cat)

; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-nntp-xpat-lines-for-numbers-cat-loop (field patterns group numbers v fn-arena fn-cat acc)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard (and (fn-scat-guard) (true-listp acc)) :verify-guards nil))
  (if (consp numbers)
      (let* ((number (car numbers))
             (article (fn-scat-available-article group number v fn-arena fn-cat))
             (content (if (consp article)
                          (fn-scol-hdr-content field article fn-arena fn-cat)
                        (list :error))))
        (if (and (fn-nntp-hdr-okp content)
                 (fn-nntp-xpat-matchesp patterns (fn-nntp-hdr-octets content)))
            (fn-nntp-xpat-lines-for-numbers-cat-loop field
                                                     patterns
                                                     group
                                                     (cdr numbers)
                                                     v
                                                     fn-arena
                                                     fn-cat
                                                     (cons (fn-nntp-hdr-line (fn-nntp-decimal-field number)
                                                                             (fn-nntp-hdr-octets content))
                                                           acc))
          (fn-nntp-xpat-lines-for-numbers-cat-loop field
                                                   patterns
                                                   group
                                                   (cdr numbers)
                                                   v
                                                   fn-arena
                                                   fn-cat
                                                   acc)))
    (revappend acc nil)))

(defun fn-nntp-xpat-lines-for-numbers-cat (field patterns group numbers v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard (fn-scat-guard) :verify-guards nil))
  (mbe :logic
       (if (consp numbers)
           (let* ((number (car numbers))
                  (article (fn-scat-available-article group number v fn-arena fn-cat))
                  (content (if (consp article)
                               (fn-scol-hdr-content field article fn-arena fn-cat)
                             (list :error))))
             (if (and (fn-nntp-hdr-okp content)
                      (fn-nntp-xpat-matchesp patterns (fn-nntp-hdr-octets content)))
                 (cons (fn-nntp-hdr-line (fn-nntp-decimal-field number)
                                         (fn-nntp-hdr-octets content))
                       (fn-nntp-xpat-lines-for-numbers-cat field patterns group
                                                           (cdr numbers) v fn-arena fn-cat))
               (fn-nntp-xpat-lines-for-numbers-cat field patterns group (cdr numbers)
                                                   v fn-arena fn-cat)))
         nil)
       :exec (fn-nntp-xpat-lines-for-numbers-cat-loop field patterns group numbers v fn-arena fn-cat nil)))

(local
 (defthm fn-nntp-xpat-lines-for-numbers-cat-loop-is-revappend
   (equal (fn-nntp-xpat-lines-for-numbers-cat-loop field patterns group numbers v fn-arena fn-cat acc)
          (revappend acc (fn-nntp-xpat-lines-for-numbers-cat field patterns group numbers v fn-arena fn-cat)))
   :hints (("Goal" :induct (fn-nntp-xpat-lines-for-numbers-cat-loop field patterns group numbers v fn-arena fn-cat acc)
                   :in-theory (union-theories '(fn-nntp-xpat-lines-for-numbers-cat-loop fn-nntp-xpat-lines-for-numbers-cat revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))


(defthm fn-nntp-xpat-lines-for-numbers-cat-is-archive
  (implies (and (fn-cnx-freshp fn-cat) (fn-scol-okp fn-arena fn-cat) group)
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
      (fn-nntp-single session (fn-proto-text * :syntax))
    (let* ((field (car args))
           (token (car (cdr args)))
           (joined (fn-nntp-xpat-join (cdr (cdr args))))
           (parsed (fn-wildmat-parse-text joined)))
      (if (not (fn-wildmat-result-okp parsed))
          (fn-nntp-single session (fn-proto-text * :syntax))
        (let ((patterns (fn-wildmat-result-value parsed)))
          (if (fn-nntp-range-okp (fn-nntp-parse-range token))
              (fn-nntp-hdr-range-ovw
               session v token (fn-ovw-hdr-source :xpat field patterns nil) fn-cat)
            (if (fn-nntp-message-id-tokenp token)
                (let ((article (fn-scat-msgid-article (fn-nntp-token-string token)
                                                      v fn-arena fn-cat)))
                  (if (not (consp article))
                      (fn-nntp-single session (fn-proto-text * :no-msgid))
                    (if (not (fn-nntp-hdr-okp (fn-scol-hdr-content field article fn-arena fn-cat)))
                        (fn-nntp-single session (fn-proto-text * :no-framing))
                      (fn-nntp-multi session (fn-nntp-hdr-initial t)
                                     (fn-nntp-xpat-msgid-lines field patterns token
                                                               article fn-arena)))))
              (fn-nntp-single session (fn-proto-text * :syntax)))))))))

(defthm fn-ovw-hdr-lines-for-numbers-is-xpat-cat
  (equal (fn-ovw-hdr-lines-for-numbers group numbers (fn-ovw-hdr-source :xpat field patterns nil)
                                       v fn-arena fn-cat)
         (fn-nntp-xpat-lines-for-numbers-cat field patterns group numbers v fn-arena fn-cat))
  :hints (("Goal" :induct (fn-nntp-xpat-lines-for-numbers-cat field patterns group numbers v fn-arena fn-cat)
           :in-theory (e/d (fn-ovw-hdr-content fn-ovw-hdr-keepp fn-ovw-hdr-source)
                           (fn-scat-available-article fn-scol-hdr-content fn-nntp-hdr-okp
                            fn-nntp-xpat-matchesp
                            fn-nntp-hdr-line fn-nntp-hdr-octets fn-nntp-decimal-field)))))

(local
 (defun fn-scat-xpat-response-old (session args v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard (fn-scat-guard) :verify-guards nil))
  (if (not (and (consp args) (fn-nntp-hdr-fieldp (car args))
                (consp (cdr args))
                (consp (cdr (cdr args)))))
      (fn-nntp-single session (fn-proto-text * :syntax))
    (let* ((field (car args))
           (token (car (cdr args)))
           (joined (fn-nntp-xpat-join (cdr (cdr args))))
           (parsed (fn-wildmat-parse-text joined)))
      (if (not (fn-wildmat-result-okp parsed))
          (fn-nntp-single session (fn-proto-text * :syntax))
        (let ((patterns (fn-wildmat-result-value parsed))
              (group (fn-nntp-session-group session)))
          (if (fn-nntp-range-okp (fn-nntp-parse-range token))
              (if (null group)
                  (fn-nntp-single session (fn-proto-text * :no-group-selected))
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
                      (fn-nntp-single session (fn-proto-text * :no-msgid))
                    (if (not (fn-nntp-hdr-okp (fn-scol-hdr-content field article fn-arena fn-cat)))
                        (fn-nntp-single session (fn-proto-text * :no-framing))
                      (fn-nntp-multi session (fn-nntp-hdr-initial t)
                                     (fn-nntp-xpat-msgid-lines field patterns token
                                                               article fn-arena)))))
              (fn-nntp-single session (fn-proto-text * :syntax))))))))))

(local
 (defthm fn-scat-xpat-response-old-is-archive
  (implies (and (fn-cnx-freshp fn-cat) (fn-scol-okp fn-arena fn-cat)
                (equal (fn-state-articles archive) (fn-cat-view-articles v fn-arena fn-cat)))
           (equal (fn-scat-xpat-response-old session args v fn-arena fn-cat)
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
                            fn-nntp-xpat-with-a-total-filter-is-the-hdr-block))))))

(local
 (defthm fn-scat-xpat-response-cat-is-old
   (and (equal (car (fn-nntp-xpat-response-cat session args v fn-arena fn-cat))
               (car (fn-scat-xpat-response-old session args v fn-arena fn-cat)))
        (equal (fn-ovw-expand (cdr (fn-nntp-xpat-response-cat session args v fn-arena fn-cat))
                              fn-arena fn-cat)
               (cdr (fn-scat-xpat-response-old session args v fn-arena fn-cat))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-nntp-xpat-response-cat fn-scat-xpat-response-old fn-nntp-hdr-initial)
                            (fn-nntp-hdr-range-ovw fn-ovw-hdr-source fn-ovw-hdr-reply
                             fn-ovw-hdr-lines-for-numbers fn-scat-range-numbers
                             fn-nntp-xpat-lines-for-numbers-cat fn-scat-available-article
                             fn-scat-msgid-article fn-scol-hdr-content fn-nntp-multi fn-nntp-single
                             fn-nntp-parse-range fn-nntp-range-okp fn-nntp-hdr-fieldp
                             fn-nntp-message-id-tokenp fn-ovw-status fn-nntp-xpat-msgid-lines
                             fn-wildmat-parse-text fn-nntp-xpat-join))
            :use ((:instance fn-ovw-hdr-reply-is-xpat-multi
                             (field (car args))
                             (patterns (fn-wildmat-result-value
                                        (fn-wildmat-parse-text (fn-nntp-xpat-join (cddr args)))))
                             (xref nil)
                             (lines (fn-nntp-xpat-lines-for-numbers-cat
                                     (car args)
                                     (fn-wildmat-result-value
                                      (fn-wildmat-parse-text (fn-nntp-xpat-join (cddr args))))
                                     (fn-nntp-session-group session)
                                     (fn-scat-range-numbers
                                      (fn-nntp-session-group session)
                                      (nfix (fn-nntp-range-low (fn-nntp-parse-range (cadr args))))
                                      (nfix (fn-nntp-range-high (fn-nntp-parse-range (cadr args))))
                                      v fn-cat)
                                     v fn-arena fn-cat))))))))

; Modulo the cursor: the arm, expanded, is the archive reader's reply.
(defthm fn-nntp-xpat-response-cat-is-archive
  (implies (and (fn-cnx-freshp fn-cat) (fn-scol-okp fn-arena fn-cat)
                (equal (fn-state-articles archive) (fn-cat-view-articles v fn-arena fn-cat)))
           (and (equal (car (fn-nntp-xpat-response-cat session args v fn-arena fn-cat))
                       (car (fn-nntp-xpat-response session archive args fn-arena)))
                (equal (fn-ovw-expand (cdr (fn-nntp-xpat-response-cat session args v fn-arena fn-cat))
                                      fn-arena fn-cat)
                       (cdr (fn-nntp-xpat-response session archive args fn-arena)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-nntp-xpat-response-cat fn-scat-xpat-response-old fn-nntp-xpat-response
                               fn-scat-xpat-response-cat-is-old fn-scat-xpat-response-old-is-archive)
           :use (fn-scat-xpat-response-cat-is-old fn-scat-xpat-response-old-is-archive))))

(in-theory (disable fn-scat-group-low-is-car fn-scat-group-high-is-last))

;;; F2 (lane sca-join-5): the Xref arms read the catalog.  With an Xref
;;; server configured (every node), fn-rcompat-reply answers ARTICLE and HEAD
;;; before the -cat retrieval arms, and books/nntp-reader-compat.lisp
;;; fn-rcompat-retrieval finds the article by number with
;;; fn-nntp-find-group-number over the pinned archive (one walk of every
;;; article per request) and the current article with
;;; fn-nntp-available-article (another walk).  The twin below is that
;;; retrieval with the two finders replaced by the catalog's
;;; (fn-scat-number-article: one probe of the number table;
;;; fn-scat-available-article: the same probe and the served-number tests);
;;; the Xref rendering (fn-rcompat-article-reply) and the Message-ID arm (the
;;; pinned trie) are the reference's, text for text.  HDR/XHDR Xref gets
;;; the same treatment (fn-rcompat-hdr-cat).  The reply wrapper delegates
;;; every other compatibility arm to fn-rcompat-reply unchanged.
;;;
;;; Why this side and not the Xref rendering in the -cat arms: the reference
;;; the served chain is proved against (fn-nntp-archive-command-pinned) calls
;;; fn-rcompat-reply, so a twin of it is one equation over the reply
;;; (fn-rcompat-reply-cat-is-rcompat-reply) and the boundary theorem keeps its
;;; statement; moving the rendering into fn-nntp-number-retrieval-cat would
;;; change which arm answers and restate the dispatcher's case split.

(defun fn-rcompat-retrieval-cat (session archive trie kind args server v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (natp v)
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))
                  :verify-guards nil)
           (ignorable archive trie))
  (if (null args)
      (let ((group (fn-nntp-session-group session))
            (current (fn-nntp-session-current session)))
        (if (null group)
            (fn-nntp-single session (fn-proto-text * :no-group-selected))
          (if (null current)
              (fn-nntp-single session (fn-proto-text * :no-current))
            (let ((article (fn-scat-available-article group current v fn-arena fn-cat)))
              (if (consp article)
                  (fn-rcompat-article-reply session article current kind t
                                            group server fn-arena)
                (fn-nntp-single session (fn-proto-text * :no-current)))))))
    (let ((token (and (consp args) (car args))))
      (if (fn-nntp-number-tokenp token)
          (let ((group (fn-nntp-session-group session))
                (number (fn-nntp-decimal-value token)))
            (if (null group)
                (fn-nntp-single session (fn-proto-text * :no-group-selected))
              (let ((article (fn-scat-number-article group number v fn-arena fn-cat)))
                (if (consp article)
                    (fn-rcompat-article-reply session article number kind t
                                              group server fn-arena)
                  (fn-nntp-single session (fn-proto-text * :no-number))))))
        (if (not (and (fn-nntp-message-id-tokenp token) (fn-octet-listp token)))
            (fn-nntp-single session (fn-proto-text * :syntax))
          ;; The catalog's Message-ID column (join-f2: the served arms read
          ;; no Message-ID trie; KEYSTONE A, fn-scat-msgid-article-is-find-article).
          (let ((article (fn-scat-msgid-article (fn-nntp-token-string token) v fn-arena fn-cat)))
            (if (consp article)
                (fn-rcompat-article-reply
                 session article (fn-nntp-msgid-local-number session article)
                 kind nil nil server fn-arena)
              (fn-nntp-single session
                              (fn-proto-text * :no-msgid)))))))))

(local
 (defthm fn-scat-msgid-token-key
   (implies (fn-nntp-message-id-tokenp token)
            (and (stringp (fn-nntp-token-string token))
                 (consp (fn-midx-key-chars (fn-nntp-token-string token)))))
   :hints (("Goal" :use ((:instance fn-nntp-message-id-token-has-nonempty-index-key))
            :in-theory (e/d (fn-nntp-message-id-tokenp)
                            (fn-nntp-message-id-token-has-nonempty-index-key))))))

(defthm fn-rcompat-retrieval-cat-is-retrieval
  (implies (and (equal (fn-state-articles archive)
                       (fn-cat-view-articles v fn-arena fn-cat))
                (fn-midx-correspondencep trie (fn-state-articles archive))
                (fn-cnx-freshp fn-cat))
           (equal (fn-rcompat-retrieval-cat session archive trie kind args server v
                                            fn-arena fn-cat)
                  (fn-rcompat-retrieval session archive trie kind args server fn-arena)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-rcompat-retrieval-cat fn-rcompat-retrieval fn-midx-correspondencep
                            fn-scat-msgid-article-is-find-article
                            fn-midx-lookup-of-build-is-find-article-for-nonempty
                            fn-scat-msgid-token-key)
                           (fn-scat-msgid-article fn-find-article fn-midx-build fn-midx-key-chars
                            fn-scat-number-article fn-scat-available-article
                            fn-nntp-find-group-number fn-nntp-available-article
                            fn-rcompat-article-reply fn-nntp-single fn-midx-lookup
                            fn-cat-view-articles fn-nntp-number-tokenp
                            fn-nntp-decimal-value fn-nntp-session-group
                            fn-nntp-session-current fn-nntp-message-id-tokenp
                            fn-nntp-token-string fn-nntp-msgid-local-number
                            fn-cnx-freshp)))))

;; HDR/XHDR Xref, as fn-rcompat-hdr (books/nntp-reader-compat.lisp) with the
;; numbers of a range read from the catalog (fn-scat-range-numbers, KEYSTONE
;; N) and the article at each number by one probe (fn-scat-available-article),
;; where the reference folds over the archive once for the range and once per
;; number.
; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-rcompat-hdr-lines-cat-loop (group numbers server v fn-arena fn-cat acc)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard (and (and (natp v) (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat)) (true-listp acc)) :verify-guards nil))
  (if (consp numbers)
      (let ((content (fn-rcompat-xref-content server
                                              (fn-scat-available-article group
                                                                         (car numbers)
                                                                         v
                                                                         fn-arena
                                                                         fn-cat)
                                              fn-arena)))
        (if (fn-nntp-hdr-okp content)
            (fn-rcompat-hdr-lines-cat-loop group
                                           (cdr numbers)
                                           server
                                           v
                                           fn-arena
                                           fn-cat
                                           (cons (fn-nntp-hdr-line (fn-nntp-decimal-field (car numbers))
                                                                   (fn-nntp-hdr-octets content))
                                                 acc))
          (fn-rcompat-hdr-lines-cat-loop group
                                         (cdr numbers)
                                         server
                                         v
                                         fn-arena
                                         fn-cat
                                         acc)))
    (revappend acc nil)))

(defun fn-rcompat-hdr-lines-cat (group numbers server v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (natp v)
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))
                  :verify-guards nil))
  (mbe :logic
       (if (consp numbers)
           (let ((content (fn-rcompat-xref-content
                           server (fn-scat-available-article group (car numbers) v fn-arena fn-cat)
                           fn-arena)))
             (if (fn-nntp-hdr-okp content)
                 (cons (fn-nntp-hdr-line (fn-nntp-decimal-field (car numbers))
                                         (fn-nntp-hdr-octets content))
                       (fn-rcompat-hdr-lines-cat group (cdr numbers) server v fn-arena fn-cat))
               (fn-rcompat-hdr-lines-cat group (cdr numbers) server v fn-arena fn-cat)))
         nil)
       :exec (fn-rcompat-hdr-lines-cat-loop group numbers server v fn-arena fn-cat nil)))

(local
 (defthm fn-rcompat-hdr-lines-cat-loop-is-revappend
   (equal (fn-rcompat-hdr-lines-cat-loop group numbers server v fn-arena fn-cat acc)
          (revappend acc (fn-rcompat-hdr-lines-cat group numbers server v fn-arena fn-cat)))
   :hints (("Goal" :induct (fn-rcompat-hdr-lines-cat-loop group numbers server v fn-arena fn-cat acc)
                   :in-theory (union-theories '(fn-rcompat-hdr-lines-cat-loop fn-rcompat-hdr-lines-cat revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))


(defthm fn-rcompat-hdr-lines-cat-is-hdr-lines
  (implies (and (fn-cnx-freshp fn-cat) group)
           (equal (fn-rcompat-hdr-lines-cat group numbers server v fn-arena fn-cat)
                  (fn-rcompat-hdr-lines group numbers (fn-cat-view-articles v fn-arena fn-cat)
                                        server fn-arena)))
  :hints (("Goal" :induct (fn-rcompat-hdr-lines-cat group numbers server v fn-arena fn-cat)
           :in-theory (e/d (fn-rcompat-hdr-lines)
                           (fn-scat-available-article fn-nntp-available-article
                            fn-rcompat-xref-content fn-nntp-hdr-okp fn-nntp-hdr-line
                            fn-nntp-decimal-field fn-nntp-hdr-octets
                            fn-cat-view-articles fn-cnx-freshp)))))

(defun fn-rcompat-hdr-cat (session archive trie args legacyp server v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (natp v)
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))
                  :verify-guards nil)
           (ignorable archive trie))
  (let ((rest (and (consp args) (cdr args))))
    (if (null rest)
        (let ((group (fn-nntp-session-group session))
              (current (fn-nntp-session-current session)))
          (if (null group)
              (fn-nntp-single session (fn-proto-text * :no-group-selected))
            (if (null current)
                (fn-nntp-single session (fn-proto-text * :no-current))
              (let ((article (fn-scat-available-article group current v fn-arena fn-cat)))
                (if (not (consp article))
                    (fn-nntp-single session (fn-proto-text * :no-current))
                  (let ((content (fn-rcompat-xref-content server article fn-arena)))
                    (if (fn-nntp-hdr-okp content)
                        (fn-nntp-multi
                         session (fn-nntp-hdr-initial legacyp)
                         (list (fn-nntp-hdr-line
                                (fn-nntp-decimal-field current)
                                (fn-nntp-hdr-octets content))))
                      (fn-nntp-single session (fn-proto-text * :reclaimed)))))))))
      (if (not (and (consp rest) (null (cdr rest))))
          (fn-nntp-single session (fn-proto-text * :syntax))
        (let ((token (car rest)))
          (if (fn-nntp-range-okp (fn-nntp-parse-range token))
              (fn-nntp-hdr-range-ovw
               session v token
               (fn-ovw-hdr-source (if legacyp :xhdr :hdr) (car args) :all (cons :xref server)) fn-cat)
            (if (not (and (fn-nntp-message-id-tokenp token)
                          (fn-octet-listp token)))
                (fn-nntp-single session (fn-proto-text * :syntax))
              (let* ((article (fn-scat-msgid-article (fn-nntp-token-string token) v fn-arena fn-cat))
                     (content (fn-rcompat-xref-content server article fn-arena)))
                (if (not (consp article))
                    (fn-nntp-single session (fn-proto-text * :no-msgid))
                  (if (fn-nntp-hdr-okp content)
                      (fn-nntp-multi
                       session (fn-nntp-hdr-initial legacyp)
                       (list (fn-nntp-hdr-line
                              (if legacyp (fn-nov-scrub token)
                                (fn-nntp-decimal-field 0))
                              (fn-nntp-hdr-octets content))))
                    (fn-nntp-single session (fn-proto-text * :reclaimed-msgid))))))))))))

(defthm fn-ovw-hdr-lines-for-numbers-is-rcompat-cat
  (implies (not (equal form :xpat))
           (equal (fn-ovw-hdr-lines-for-numbers group numbers
                                                (fn-ovw-hdr-source form field patterns (cons :xref server))
                                                v fn-arena fn-cat)
                  (fn-rcompat-hdr-lines-cat group numbers server v fn-arena fn-cat)))
  :hints (("Goal" :induct (fn-rcompat-hdr-lines-cat group numbers server v fn-arena fn-cat)
           :in-theory (e/d (fn-ovw-hdr-content fn-ovw-hdr-keepp fn-ovw-hdr-source)
                           (fn-scat-available-article fn-rcompat-xref-content fn-nntp-hdr-okp
                            fn-nntp-hdr-line fn-nntp-hdr-octets fn-nntp-decimal-field)))))

(local
 (defun fn-scat-rcompat-hdr-old (session archive trie args legacyp server v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (natp v)
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))
                  :verify-guards nil)
           (ignorable archive trie))
  (let ((rest (and (consp args) (cdr args))))
    (if (null rest)
        (let ((group (fn-nntp-session-group session))
              (current (fn-nntp-session-current session)))
          (if (null group)
              (fn-nntp-single session (fn-proto-text * :no-group-selected))
            (if (null current)
                (fn-nntp-single session (fn-proto-text * :no-current))
              (let ((article (fn-scat-available-article group current v fn-arena fn-cat)))
                (if (not (consp article))
                    (fn-nntp-single session (fn-proto-text * :no-current))
                  (let ((content (fn-rcompat-xref-content server article fn-arena)))
                    (if (fn-nntp-hdr-okp content)
                        (fn-nntp-multi
                         session (fn-nntp-hdr-initial legacyp)
                         (list (fn-nntp-hdr-line
                                (fn-nntp-decimal-field current)
                                (fn-nntp-hdr-octets content))))
                      (fn-nntp-single session (fn-proto-text * :reclaimed)))))))))
      (if (not (and (consp rest) (null (cdr rest))))
          (fn-nntp-single session (fn-proto-text * :syntax))
        (let ((token (car rest)))
          (if (fn-nntp-range-okp (fn-nntp-parse-range token))
              (let ((group (fn-nntp-session-group session))
                    (range (fn-nntp-parse-range token)))
                (if (null group)
                    (fn-nntp-single session (fn-proto-text * :no-group-selected))
                  (let ((lines (fn-rcompat-hdr-lines-cat
                                group
                                (fn-scat-range-numbers
                                 group (nfix (fn-nntp-range-low range))
                                 (nfix (fn-nntp-range-high range)) v fn-cat)
                                server v fn-arena fn-cat)))
                    (if (consp lines)
                        (fn-nntp-multi session (fn-nntp-hdr-initial legacyp)
                                       lines)
                      (fn-nntp-single session
                                      (if legacyp (fn-proto-text * :none-selected)
                                        (fn-proto-text * :empty-range)))))))
            (if (not (and (fn-nntp-message-id-tokenp token)
                          (fn-octet-listp token)))
                (fn-nntp-single session (fn-proto-text * :syntax))
              (let* ((article (fn-scat-msgid-article (fn-nntp-token-string token) v fn-arena fn-cat))
                     (content (fn-rcompat-xref-content server article fn-arena)))
                (if (not (consp article))
                    (fn-nntp-single session (fn-proto-text * :no-msgid))
                  (if (fn-nntp-hdr-okp content)
                      (fn-nntp-multi
                       session (fn-nntp-hdr-initial legacyp)
                       (list (fn-nntp-hdr-line
                              (if legacyp (fn-nov-scrub token)
                                (fn-nntp-decimal-field 0))
                              (fn-nntp-hdr-octets content))))
                    (fn-nntp-single session (fn-proto-text * :reclaimed-msgid)))))))))))))

(local
 (defthm fn-scat-rcompat-hdr-old-is-hdr
  (implies (and (equal (fn-state-articles archive)
                       (fn-cat-view-articles v fn-arena fn-cat))
                (fn-midx-correspondencep trie (fn-state-articles archive))
                (fn-cnx-freshp fn-cat))
           (equal (fn-scat-rcompat-hdr-old session archive trie args legacyp server v fn-arena fn-cat)
                  (fn-rcompat-hdr session archive trie args legacyp server fn-arena)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-scat-rcompat-hdr-old fn-rcompat-hdr fn-midx-correspondencep
                            fn-scat-msgid-article-is-find-article
                            fn-midx-lookup-of-build-is-find-article-for-nonempty
                            fn-scat-msgid-token-key)
                           (fn-scat-msgid-article fn-find-article fn-midx-build fn-midx-key-chars
                            fn-scat-available-article fn-nntp-available-article
                            fn-rcompat-hdr-lines-cat fn-rcompat-hdr-lines
                            fn-scat-range-numbers fn-nntp-group-range-numbers
                            fn-rcompat-xref-content fn-nntp-hdr-okp fn-nntp-hdr-line
                            fn-nntp-decimal-field fn-nntp-hdr-octets fn-nntp-multi
                            fn-nntp-single fn-nntp-hdr-initial fn-midx-lookup
                            fn-nntp-parse-range fn-nntp-range-okp fn-nov-scrub
                            fn-nntp-message-id-tokenp fn-nntp-token-string
                            fn-cat-view-articles fn-cnx-freshp fn-nntp-session-group
                            fn-nntp-session-current))
           :use ((:instance fn-nntp-parse-range-ok-has-natural-bounds
                            (token (car (cdr args)))))))))

(local
 (defthm fn-scat-rcompat-hdr-cat-is-old
   (and (equal (car (fn-rcompat-hdr-cat session archive trie args legacyp server v fn-arena fn-cat))
               (car (fn-scat-rcompat-hdr-old session archive trie args legacyp server v fn-arena fn-cat)))
        (equal (fn-ovw-expand (cdr (fn-rcompat-hdr-cat session archive trie args legacyp server v fn-arena fn-cat))
                              fn-arena fn-cat)
               (cdr (fn-scat-rcompat-hdr-old session archive trie args legacyp server v fn-arena fn-cat))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-rcompat-hdr-cat fn-scat-rcompat-hdr-old fn-nntp-hdr-initial)
                            (fn-nntp-hdr-range-ovw fn-ovw-hdr-source fn-ovw-hdr-reply
                             fn-ovw-hdr-lines-for-numbers fn-scat-range-numbers
                             fn-rcompat-hdr-lines-cat fn-scat-available-article fn-rcompat-xref-content
                             fn-scat-msgid-article fn-nntp-multi fn-nntp-single
                             fn-nntp-parse-range fn-nntp-range-okp fn-nov-scrub
                             fn-nntp-message-id-tokenp fn-ovw-status))
            :use ((:instance fn-ovw-hdr-reply-is-hdr-multi
                             (form (if legacyp :xhdr :hdr)) (field (car args)) (patterns :all)
                             (xref (cons :xref server))
                             (lines (fn-rcompat-hdr-lines-cat
                                     (fn-nntp-session-group session)
                                     (fn-scat-range-numbers
                                      (fn-nntp-session-group session)
                                      (nfix (fn-nntp-range-low (fn-nntp-parse-range (cadr args))))
                                      (nfix (fn-nntp-range-high (fn-nntp-parse-range (cadr args))))
                                      v fn-cat)
                                     server v fn-arena fn-cat))))))))

; Modulo the cursor: the compatibility arm, expanded, is the reference's.
(defthm fn-rcompat-hdr-cat-is-hdr
  (implies (and (equal (fn-state-articles archive)
                       (fn-cat-view-articles v fn-arena fn-cat))
                (fn-midx-correspondencep trie (fn-state-articles archive))
                (fn-cnx-freshp fn-cat))
           (and (equal (car (fn-rcompat-hdr-cat session archive trie args legacyp server v fn-arena fn-cat))
                       (car (fn-rcompat-hdr session archive trie args legacyp server fn-arena)))
                (equal (fn-ovw-expand (cdr (fn-rcompat-hdr-cat session archive trie args legacyp server
                                                               v fn-arena fn-cat))
                                      fn-arena fn-cat)
                       (cdr (fn-rcompat-hdr session archive trie args legacyp server fn-arena)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-rcompat-hdr-cat fn-scat-rcompat-hdr-old fn-rcompat-hdr
                               fn-scat-rcompat-hdr-cat-is-old fn-scat-rcompat-hdr-old-is-hdr)
           :use (fn-scat-rcompat-hdr-cat-is-old fn-scat-rcompat-hdr-old-is-hdr))))

(defun fn-rcompat-reply-cat (session archive index env keyword args v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (natp v)
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))
                  :verify-guards nil))
  (let ((server (fn-nntp-xref-server env)))
    (if (and server
             (or (fn-nntp-keywordp keyword "ARTICLE")
                 (fn-nntp-keywordp keyword "HEAD"))
             (fn-gidx-pinp index)
             (or (null args) (and (consp args) (null (cdr args)))))
        (fn-rcompat-retrieval-cat session archive (fn-gidx-pin-trie index)
                                  (fn-rcompat-retrieval-kind keyword) args server
                                  v fn-arena fn-cat)
      (if (and server
               (or (fn-nntp-keywordp keyword "HDR")
                   (fn-nntp-keywordp keyword "XHDR"))
               (fn-gidx-pinp index)
               (consp args)
               (fn-nntp-keywordp (car args) "XREF"))
          (fn-rcompat-hdr-cat session archive (fn-gidx-pin-trie index) args
                              (fn-nntp-keywordp keyword "XHDR") server v fn-arena fn-cat)
        (fn-rcompat-reply session archive index env keyword args fn-arena)))))

(local
 (defthm fn-scat-rcompat-hdr-has-no-cursor
   (equal (fn-ovw-expand (cdr (fn-rcompat-hdr session archive trie args legacyp server fn-arena))
                         fn-arena fn-cat)
          (cdr (fn-rcompat-hdr session archive trie args legacyp server fn-arena)))
   :hints (("Goal" :in-theory (e/d (fn-rcompat-hdr)
                                   (fn-nntp-single fn-nntp-multi fn-rcompat-hdr-lines
                                    fn-nntp-available-article fn-find-article fn-midx-lookup
                                    fn-rcompat-xref-content fn-nntp-parse-range))))))

; Modulo the cursor (the HDR Xref range arm answers with one, lane
; cold-line): the sessions are equal and so are the expanded effects.
(defthm fn-rcompat-reply-cat-is-rcompat-reply
  (implies (and (equal (fn-state-articles archive)
                       (fn-cat-view-articles v fn-arena fn-cat))
                (fn-midx-correspondencep (fn-gidx-pin-trie index) (fn-state-articles archive))
                (fn-cnx-freshp fn-cat))
           (and (equal (car (fn-rcompat-reply-cat session archive index env keyword args v fn-arena fn-cat))
                       (car (fn-rcompat-reply session archive index env keyword args fn-arena)))
                (equal (fn-ovw-expand
                        (cdr (fn-rcompat-reply-cat session archive index env keyword args v fn-arena fn-cat))
                        fn-arena fn-cat)
                       (fn-ovw-expand
                        (cdr (fn-rcompat-reply session archive index env keyword args fn-arena))
                        fn-arena fn-cat))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-rcompat-reply-cat fn-rcompat-reply)
                           (fn-rcompat-retrieval-cat fn-rcompat-retrieval
                            fn-rcompat-hdr-cat fn-rcompat-hdr
                            fn-rcompat-newgroups fn-rcompat-active-times
                            fn-rcompat-subscriptions fn-rcompat-hdr
                            fn-nntp-xref-server fn-gidx-pinp fn-gidx-pin-trie
                            fn-rcompat-list-keywordp fn-cat-view-articles fn-cnx-freshp
                            fn-midx-correspondencep)))))

; The dispatcher tests the compatibility reply's truth (a one-element cond
; clause): equal to the reference's.
(defthm fn-rcompat-reply-cat-iff-rcompat-reply
  (iff (fn-rcompat-reply-cat session archive index env keyword args v fn-arena fn-cat)
       (fn-rcompat-reply session archive index env keyword args fn-arena))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-rcompat-reply-cat fn-rcompat-reply fn-rcompat-hdr-cat fn-rcompat-hdr
                            fn-nntp-hdr-range-ovw fn-nntp-make-result fn-nntp-single fn-nntp-multi
                            fn-rcompat-retrieval-cat fn-rcompat-retrieval)
                           (fn-rcompat-newgroups fn-rcompat-active-times fn-rcompat-subscriptions
                            fn-nntp-xref-server fn-gidx-pinp fn-gidx-pin-trie
                            fn-rcompat-list-keywordp fn-cat-view-articles fn-cnx-freshp
                            fn-midx-correspondencep)))))

;; The withdrawn test of a by-number line: the article's absence is read
;; from the catalog's number table (one probe), not by a walk of the pinned
;; archive; the pinned withdrawn list W is walked only when the number names
;; no visible article (the reply is then 423 either way).
(defun fn-nntp-number-withdrawn-p-cat (session index token v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (natp v)
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))
                  :verify-guards nil))
  (let ((group (fn-nntp-session-group session)))
    (and group
         (fn-nntp-number-tokenp token)
         (let ((number (fn-nntp-decimal-value token)))
           (and (not (consp (fn-scat-number-article group number v fn-arena fn-cat)))
                (consp (fn-nntp-find-group-number
                        group number
                        (fn-ctl-pin-withdrawn (fn-gidx-pin-control index)))))))))

(defthm fn-nntp-number-withdrawn-p-cat-is-archive
  (implies (and (equal (fn-state-articles archive)
                       (fn-cat-view-articles v fn-arena fn-cat))
                (fn-cnx-freshp fn-cat))
           (iff (fn-nntp-number-withdrawn-p-cat session index token v fn-arena fn-cat)
                (fn-nntp-number-withdrawn-p session archive index token)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nntp-number-withdrawn-p-cat fn-nntp-number-withdrawn-p)
                           (fn-scat-number-article fn-nntp-find-group-number
                            fn-cat-view-articles fn-nntp-number-tokenp
                            fn-nntp-decimal-value fn-nntp-session-group fn-cnx-freshp)))))

;;; HDR :fn-verified (lane scale-reads, 2026-09-28).  The pinned reference
;;; (books/nntp-verdict.lisp) finds each number's article by a walk of the
;;; view's article list and each article's verdict by a walk of the verdict
;;; list, so a whole-range request over N articles was N x (N + V): a 100k
;;; store held the owner over 30 minutes (lane serve-depth).  The twin finds
;;; the numbers and the articles in the catalog (fn-scat-range-numbers,
;;; fn-scat-available-article, fn-scat-msgid-article: a probe each) and
;;; every verdict of the reply in ONE pass over the verdict list, through a
;;; table of the reply's Message-IDs: O(R + V) hash operations for a reply of
;;; R lines, where the reference was O(R x (N + V)).
;;;
;;; The verdict is read from the recorded evidence (the view's verdict list,
;;; books/store-node.lisp fn-sn-verdicts), never from the catalog row's
;;; context: a row's context is decided under the keyring in force at its
;;; intern and a redecision replaces it (books/catalog-delta.lisp
;;; :redecide), while HDR :fn-verified answers the acceptance evidence,
;;; which a keyring change never rewrites.  Reading the row instead (O(R))
;;; needs that equation carried in the join invariant; it is not proved.
;;;
;;; KEYSTONE fn-nntp-verdict-hdr-response-cat-is-archive: the twin IS
;;; fn-nntp-verdict-hdr-response under the view's catalog (the -cat
;;; dispatcher's hypotheses).

; The table of the Message-IDs of the articles at NUMBERS, onto TBL.
(defun fn-scat-vh-want (group numbers v fn-arena fn-cat tbl)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard (fn-scat-guard)))
  (if (consp numbers)
      (let ((article (fn-scat-available-article group (car numbers) v fn-arena fn-cat)))
        (fn-scat-vh-want group (cdr numbers) v fn-arena fn-cat
                         (if (consp article)
                             (hons-acons (fn-article-msgid article) t tbl)
                           tbl)))
    tbl))

; One pass over VERDICTS: the first pair of each wanted Message-ID, onto FOUND.
(defun fn-scat-vh-fill (verdicts wanted found)
  (declare (xargs :guard t))
  (if (consp verdicts)
      (let ((e (car verdicts)))
        (fn-scat-vh-fill (cdr verdicts) wanted
                         (if (and (consp e)
                                  (hons-get (car e) wanted)
                                  (not (hons-get (car e) found)))
                             (hons-acons (car e) (cdr e) found)
                           found)))
    found))

(defthm fn-scat-vh-want-keeps
  (implies (hons-assoc-equal m tbl)
           (hons-assoc-equal m (fn-scat-vh-want group numbers v fn-arena fn-cat tbl)))
  :hints (("Goal" :induct (fn-scat-vh-want group numbers v fn-arena fn-cat tbl)
                  :in-theory (disable fn-scat-available-article))))

(defthm fn-scat-vh-want-member
  (implies (and (member-equal n numbers)
                (consp (fn-scat-available-article group n v fn-arena fn-cat)))
           (hons-assoc-equal
            (fn-article-msgid (fn-scat-available-article group n v fn-arena fn-cat))
            (fn-scat-vh-want group numbers v fn-arena fn-cat tbl)))
  :hints (("Goal" :induct (fn-scat-vh-want group numbers v fn-arena fn-cat tbl)
                  :in-theory (disable fn-scat-available-article))))

(defthm fn-scat-vh-fill-lookup
  (equal (hons-assoc-equal m (fn-scat-vh-fill verdicts wanted found))
         (or (hons-assoc-equal m found)
             (and (hons-assoc-equal m wanted)
                  (hons-assoc-equal m verdicts))))
  :hints (("Goal" :induct (fn-scat-vh-fill verdicts wanted found))))

(defthm fn-scat-stx-reader-lookup-is-hons-assoc
  (equal (fn-stx-reader-lookup m verdicts)
         (cdr (hons-assoc-equal m verdicts)))
  :hints (("Goal" :in-theory (enable fn-stx-reader-lookup))))

(in-theory (disable fn-scat-vh-want fn-scat-vh-fill))

; The lines, each verdict read from FOUND.
(defun fn-scat-vh-line (number article found)
  (declare (xargs :guard t))
  (fn-nntp-hdr-line (fn-nntp-decimal-field number)
                    (fn-stx-reader-item (cdr (hons-get (fn-article-msgid article) found)))))

(defun fn-scat-vh-lines-loop (group numbers v found fn-arena fn-cat acc)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard (and (fn-scat-guard) (true-listp acc))
                  :verify-guards nil))
  (if (consp numbers)
      (let ((article (fn-scat-available-article group (car numbers) v fn-arena fn-cat)))
        (fn-scat-vh-lines-loop group (cdr numbers) v found fn-arena fn-cat
                               (if (consp article)
                                   (cons (fn-scat-vh-line (car numbers) article found) acc)
                                 acc)))
    (revappend acc nil)))

(defun fn-scat-vh-lines (group numbers v found fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard (fn-scat-guard) :verify-guards nil))
  (mbe :logic
       (if (consp numbers)
           (let ((article (fn-scat-available-article group (car numbers) v fn-arena fn-cat)))
             (if (consp article)
                 (cons (fn-scat-vh-line (car numbers) article found)
                       (fn-scat-vh-lines group (cdr numbers) v found fn-arena fn-cat))
               (fn-scat-vh-lines group (cdr numbers) v found fn-arena fn-cat)))
         nil)
       :exec (fn-scat-vh-lines-loop group numbers v found fn-arena fn-cat nil)))

(local
 (defthm fn-scat-vh-lines-loop-is-revappend
   (equal (fn-scat-vh-lines-loop group numbers v found fn-arena fn-cat acc)
          (revappend acc (fn-scat-vh-lines group numbers v found fn-arena fn-cat)))
   :hints (("Goal" :induct (fn-scat-vh-lines-loop group numbers v found fn-arena fn-cat acc)
                   :in-theory (union-theories '(fn-scat-vh-lines-loop fn-scat-vh-lines revappend
                                                car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-scat-vh-lines-loop)

(verify-guards fn-scat-vh-lines
  :hints (("Goal" :in-theory (union-theories '(revappend fn-scat-vh-lines)
                                             (union-theories (theory 'minimal-theory)
                                                             (executable-counterpart-theory :here)))
                  :use ((:instance fn-scat-vh-lines-loop-is-revappend (acc nil))))))

; Every number of NUMBERS drawn from ALL: its verdict is in the table of ALL.
(defthm fn-scat-vh-want-member-view
  (implies (and (fn-cnx-freshp fn-cat) group
                (member-equal n numbers)
                (consp (fn-nntp-available-article group n (fn-cat-view-articles v fn-arena fn-cat))))
           (hons-assoc-equal
            (fn-article-msgid (fn-nntp-available-article group n (fn-cat-view-articles v fn-arena fn-cat)))
            (fn-scat-vh-want group numbers v fn-arena fn-cat tbl)))
  :hints (("Goal" :use ((:instance fn-scat-vh-want-member))
                  :in-theory (disable fn-scat-vh-want-member fn-scat-available-article
                                      fn-nntp-available-article fn-cat-view-articles fn-cnx-freshp))))

(defthm fn-scat-vh-lines-is-verdict-hdr-lines
  (implies (and (fn-cnx-freshp fn-cat) group (subsetp-equal numbers all))
           (equal (fn-scat-vh-lines group numbers v
                                    (fn-scat-vh-fill verdicts
                                                     (fn-scat-vh-want group all v fn-arena fn-cat nil)
                                                     nil)
                                    fn-arena fn-cat)
                  (fn-nntp-verdict-hdr-lines group numbers
                                             (fn-cat-view-articles v fn-arena fn-cat)
                                             verdicts)))
  :hints (("Goal" :induct (fn-nntp-verdict-hdr-lines group numbers
                                                     (fn-cat-view-articles v fn-arena fn-cat)
                                                     verdicts)
                  :in-theory (e/d (fn-nntp-verdict-hdr-lines fn-stx-reader-verdict)
                                  (fn-scat-available-article fn-cat-view-articles
                                   fn-nntp-available-article fn-nntp-hdr-line
                                   fn-nntp-decimal-field fn-stx-reader-item
                                   fn-cnx-freshp fn-stx-reader-lookup)))))

(local (defthm fn-scat-vh-subsetp-cons
  (implies (subsetp-equal x y) (subsetp-equal x (cons a y)))))

(defthm fn-scat-vh-subsetp-refl
  (subsetp-equal x x))

; The three arms.
(defun fn-nntp-verdict-hdr-range-cat (session verdicts token v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard (fn-scat-guard)))
  (let ((group (fn-nntp-session-group session))
        (range (fn-nntp-parse-range token)))
    (if (null group)
        (fn-nntp-single session (fn-proto-text * :no-group-selected))
      (let* ((numbers (fn-scat-range-numbers
                       group (nfix (fn-nntp-range-low range))
                       (nfix (fn-nntp-range-high range)) v fn-cat))
             (wanted (fn-scat-vh-want group numbers v fn-arena fn-cat nil))
             (found (fn-scat-vh-fill verdicts wanted nil))
             (lines (fast-alist-free-on-exit
                     wanted
                     (fast-alist-free-on-exit
                      found
                      (fn-scat-vh-lines group numbers v found fn-arena fn-cat)))))
        (if (consp lines)
            (fn-nntp-multi session (fn-nntp-hdr-initial nil) lines)
          (fn-nntp-single session (fn-proto-text * :empty-range)))))))

(defthm fn-nntp-verdict-hdr-range-cat-is-archive
  (implies (and (fn-cnx-freshp fn-cat)
                (equal (fn-state-articles archive) (fn-cat-view-articles v fn-arena fn-cat))
                (natp (fn-nntp-range-low (fn-nntp-parse-range token)))
                (natp (fn-nntp-range-high (fn-nntp-parse-range token))))
           (equal (fn-nntp-verdict-hdr-range-cat session verdicts token v fn-arena fn-cat)
                  (fn-nntp-verdict-hdr-range session archive verdicts token)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nntp-verdict-hdr-range)
                           (fn-scat-range-numbers fn-scat-vh-lines fn-nntp-verdict-hdr-lines
                            fn-nntp-group-range-numbers fn-cat-view-articles fn-cnx-freshp
                            fn-nntp-parse-range fn-nntp-multi fn-nntp-single)))))

(defun fn-nntp-verdict-hdr-current-cat (session verdicts v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard (fn-scat-guard)))
  (let ((group (fn-nntp-session-group session))
        (current (fn-nntp-session-current session)))
    (if (null group)
        (fn-nntp-single session (fn-proto-text * :no-group-selected))
      (if (null current)
          (fn-nntp-single session (fn-proto-text * :no-current))
        (let ((article (fn-scat-available-article group current v fn-arena fn-cat)))
          (if (not (consp article))
              (fn-nntp-single session (fn-proto-text * :no-current))
            (fn-nntp-multi
             session (fn-nntp-hdr-initial nil)
             (list (fn-nntp-hdr-line
                    (fn-nntp-decimal-field current)
                    (fn-stx-reader-verdict (fn-article-msgid article) verdicts))))))))))

(defthm fn-nntp-verdict-hdr-current-cat-is-archive
  (implies (and (fn-cnx-freshp fn-cat)
                (equal (fn-state-articles archive) (fn-cat-view-articles v fn-arena fn-cat)))
           (equal (fn-nntp-verdict-hdr-current-cat session verdicts v fn-arena fn-cat)
                  (fn-nntp-verdict-hdr-current session archive verdicts)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nntp-verdict-hdr-current)
                           (fn-scat-available-article fn-nntp-available-article
                            fn-cat-view-articles fn-cnx-freshp fn-stx-reader-verdict
                            fn-nntp-multi fn-nntp-single)))))

(defun fn-nntp-verdict-hdr-msgid-cat (session verdicts token v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard (fn-scat-guard)))
  (let ((article (fn-scat-msgid-article (fn-nntp-token-string token) v fn-arena fn-cat)))
    (if (not (consp article))
        (fn-nntp-single session (fn-proto-text * :no-msgid))
      (fn-nntp-multi
       session (fn-nntp-hdr-initial nil)
       (list (fn-nntp-hdr-line
              (fn-nntp-decimal-field 0)
              (fn-stx-reader-verdict (fn-article-msgid article) verdicts)))))))

(defthm fn-nntp-verdict-hdr-msgid-cat-is-archive
  (implies (equal (fn-state-articles archive) (fn-cat-view-articles v fn-arena fn-cat))
           (equal (fn-nntp-verdict-hdr-msgid-cat session verdicts token v fn-arena fn-cat)
                  (fn-nntp-verdict-hdr-msgid session archive verdicts token)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nntp-verdict-hdr-msgid)
                           (fn-scat-msgid-article fn-find-article fn-cat-view-articles
                            fn-stx-reader-verdict fn-nntp-multi fn-nntp-single)))))

(defun fn-nntp-verdict-hdr-response-cat (session verdicts args v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard (fn-scat-guard)))
  (if (not (and (consp args)
                (fn-nntp-keywordp (car args) ":FN-VERIFIED")))
      (fn-nntp-single session (fn-proto-text * :syntax))
    (let ((rest (cdr args)))
      (if (null rest)
          (fn-nntp-verdict-hdr-current-cat session verdicts v fn-arena fn-cat)
        (if (and (consp rest) (null (cdr rest)))
            (let ((token (car rest)))
              (if (fn-nntp-range-okp (fn-nntp-parse-range token))
                  (fn-nntp-verdict-hdr-range-cat session verdicts token v fn-arena fn-cat)
                (if (fn-nntp-message-id-tokenp token)
                    (fn-nntp-verdict-hdr-msgid-cat session verdicts token v fn-arena fn-cat)
                  (fn-nntp-single session (fn-proto-text * :syntax)))))
          (fn-nntp-single session (fn-proto-text * :syntax)))))))

;; KEYSTONE.  Host path: fn-scr-command (books/served-catalog-chain.lisp)
;; -> fn-nntp-archive-command-cat -> this; the reference is the pinned
;; dispatcher's arm.
(defthm fn-nntp-verdict-hdr-response-cat-is-archive
  (implies (and (fn-cnx-freshp fn-cat)
                (equal (fn-state-articles archive) (fn-cat-view-articles v fn-arena fn-cat)))
           (equal (fn-nntp-verdict-hdr-response-cat session verdicts args v fn-arena fn-cat)
                  (fn-nntp-verdict-hdr-response session archive verdicts args)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nntp-verdict-hdr-response)
                           (fn-nntp-verdict-hdr-range-cat fn-nntp-verdict-hdr-range
                            fn-nntp-verdict-hdr-current-cat fn-nntp-verdict-hdr-current
                            fn-nntp-verdict-hdr-msgid-cat fn-nntp-verdict-hdr-msgid
                            fn-nntp-range-okp fn-nntp-parse-range fn-nntp-message-id-tokenp
                            fn-nntp-keywordp fn-cat-view-articles fn-cnx-freshp
                            fn-nntp-single))
           :use ((:instance fn-nntp-parse-range-ok-has-natural-bounds (token (cadr args)))))))


;;; OVER/XOVER of a range with an Xref server, and the Message-ID withdrawn
;;; test, over the catalog (lane join-f2-midx, the fn-midx retirement): the
;;; served arm reads the catalog's number column and its rows, not the pinned
;;; group buckets and Message-ID trie.  Each is equated to the trie arm it
;;; replaces under the pin's built index (the reference dispatcher is unchanged).

(defthm fn-scat-nidx-of-build-is-available
  (implies (and (fn-article-listp configured (fn-cat-view-articles v fn-arena fn-cat))
                (fn-cnx-freshp fn-cat) group)
           (equal (fn-gidx-nidx-number-article
                   n (fn-gidx-bucket-numbers group (fn-gidx-build (fn-cat-view-articles v fn-arena fn-cat)))
                   (fn-midx-build (fn-cat-view-articles v fn-arena fn-cat)))
                  (fn-scat-available-article group n v fn-arena fn-cat)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-scat-available-article-is-available
                            fn-gidx-nidx-number-article-is-walk
                            fn-gidx-numbers-okp-of-build)
                           (fn-scat-available-article fn-gidx-nidx-number-article
                            fn-gidx-entry-number-article fn-gidx-build fn-midx-build
                            fn-cat-view-articles fn-cnx-freshp fn-gidx-bucket-numbers
                            fn-gidx-bucket fn-nntp-available-article))
           :use ((:instance fn-gidx-entry-number-article-of-built-bucket
                            (number n) (articles (fn-cat-view-articles v fn-arena fn-cat)))))))

(defthm fn-nov-served-lines-for-numbers-cat-is-col
  (implies (and (fn-article-listp configured (fn-cat-view-articles v fn-arena fn-cat))
                (fn-cnx-freshp fn-cat) group)
           (equal (fn-nov-served-lines-for-numbers-cat group numbers server v fn-arena fn-cat)
                  (fn-nov-served-lines-numbered-col
                   numbers (fn-gidx-bucket-numbers group (fn-gidx-build (fn-cat-view-articles v fn-arena fn-cat)))
                   (fn-midx-build (fn-cat-view-articles v fn-arena fn-cat))
                   server fn-arena fn-cat)))
  :hints (("Goal" :induct (fn-nov-served-lines-for-numbers-cat group numbers server v fn-arena fn-cat)
           :in-theory (e/d (fn-nov-served-lines-numbered-col fn-scat-nidx-of-build-is-available)
                           (fn-scat-available-article fn-gidx-nidx-number-article fn-gidx-build
                            fn-midx-build fn-cat-view-articles fn-cnx-freshp fn-gidx-bucket-numbers
                            fn-scol-tombstonep fn-scol-overview-of fn-nov-okp fn-nov-served-line
                            fn-article-listp)))))

(defthm fn-scat-select-nonstring
  (implies (and (fn-index-listp entries) (not (stringp group)))
           (equal (fn-gidx-select group entries) nil))
  :hints (("Goal" :induct (len entries) :in-theory (enable fn-gidx-select fn-index-listp fn-index-entryp))))
(defthm fn-scat-built-range-numbers-nonstring
  (implies (and (fn-article-listp configured articles)
                (not (stringp group)))
           (equal (fn-gidx-range-numbers (fn-gidx-build articles) group low high) nil))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-gidx-range-numbers fn-gidx-bucket-of-build fn-nntp-index-group-range-numbers fn-index-query-range fn-nntp-index-numbers fn-nntp-numbers-sort)
                           (fn-gidx-build fn-index-build))
           :use ((:instance fn-index-build-listp)
                 (:instance fn-scat-select-nonstring (entries (fn-index-build articles)))))))

(defthm fn-scat-index-range-numbers-of-nil
  (equal (fn-nntp-index-group-range-numbers nil group low high) nil)
  :hints (("Goal" :in-theory (enable fn-nntp-index-group-range-numbers fn-index-query-range
                                     fn-nntp-index-numbers fn-nntp-numbers-sort))))

(defun fn-nntp-over-range-served-cat (session v token legacyp server fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard (fn-scat-guard)))
  (let ((group (fn-nntp-session-group session))
        (range (fn-nntp-parse-range token)))
    (if (null group)
        (fn-nntp-single session (fn-proto-text * :no-group-selected))
      (let* ((numbers (fn-scat-range-numbers
                       group (nfix (fn-nntp-range-low range))
                       (nfix (fn-nntp-range-high range)) v fn-cat))
             (lines (fn-nov-served-lines-for-numbers-cat group numbers server v fn-arena fn-cat)))
        (if (consp lines)
            (fn-nntp-multi session (fn-proto-text * :overview) lines)
          (fn-nntp-single
           session (if legacyp (fn-proto-text * :none-selected)
                     (fn-proto-text * :empty-range))))))))

;; The served reader of a range is the windowed reader's specification at
;; its server name, and the cursor arm with that name expands to it: the
;; served OVER/XOVER range of a node with an Xref server name is answered by
;; a CURSOR (fn-nntp-xref-reply-cat below), in bounded quanta, as the plain
;; one is.
(defthm fn-ovw-over-range-served-cat-is-spec
  (implies server
           (and (equal (car (fn-nntp-over-range-served-cat session v token legacyp server fn-arena fn-cat))
                       session)
                (equal (cdr (fn-nntp-over-range-served-cat session v token legacyp server fn-arena fn-cat))
                       (list (fn-nntp-reply-effect
                              (fn-ovw-spec session v token legacyp server fn-arena fn-cat))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nntp-over-range-served-cat fn-scat-range-numbers fn-cnx-view-range
                            fn-ovw-spec fn-ovw-reply fn-ovw-lines
                            fn-nntp-single fn-nntp-multi fn-nntp-make-result fn-nntp-reply-effect
                            fn-ovw-empty-text)
                           (fn-cat-group-next-is-high fn-cat-group-next fn-cnx-range-aux
                            fn-scat-range-keep fn-nov-served-lines-for-numbers-cat fn-nntp-stuff-lines
                            fn-nntp-parse-range fn-ovw-status fn-nntp-crlf fn-nntp-string-octets)))))

;; KEYSTONE (the served cursor arm): with a server name the arm's one cursor
;; effect, expanded, is the served unbounded reader's reply, session kept.
(defthm fn-nntp-over-range-ovw-expands-to-over-range-served-cat
  (implies server
           (and (equal (car (fn-nntp-over-range-ovw session v token legacyp server fn-cat))
                       (car (fn-nntp-over-range-served-cat session v token legacyp server
                                                           fn-arena fn-cat)))
                (equal (fn-ovw-expand (cdr (fn-nntp-over-range-ovw session v token legacyp server fn-cat))
                                      fn-arena fn-cat)
                       (cdr (fn-nntp-over-range-served-cat session v token legacyp server
                                                           fn-arena fn-cat)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nntp-over-range-ovw fn-ovw-start fn-ovw-cursor-effect
                            fn-ovw-cursor-effectp fn-ovw-cursor-octets fn-ovw-expand fn-ovw-spec
                            fn-nntp-make-result fn-nntp-reply-effect
                            fn-ovw-over-range-served-cat-is-spec)
                           (fn-ovw-lines fn-ovw-reply fn-ovw-status fn-nntp-parse-range
                            fn-cat-group-next fn-nntp-over-range-served-cat)))))

(defthm fn-nntp-over-range-served-cat-is-col
  (implies (and (fn-article-listp configured (fn-cat-view-articles v fn-arena fn-cat))
                (fn-cnx-freshp fn-cat)
                (natp (fn-nntp-range-low (fn-nntp-parse-range token)))
                (natp (fn-nntp-range-high (fn-nntp-parse-range token))))
           (equal (fn-nntp-over-range-served-cat session v token legacyp server fn-arena fn-cat)
                  (fn-nntp-over-range-served-col
                   session (fn-gidx-build (fn-cat-view-articles v fn-arena fn-cat))
                   (fn-midx-build (fn-cat-view-articles v fn-arena fn-cat))
                   token legacyp server fn-arena fn-cat)))
  :hints (("Goal" :do-not-induct t
           :cases ((stringp (fn-nntp-session-group session)))
           :use ((:instance fn-gidx-range-of-build-equals-archive-fold
                            (articles (fn-cat-view-articles v fn-arena fn-cat))
                            (group (fn-nntp-session-group session))
                            (low (fn-nntp-range-low (fn-nntp-parse-range token)))
                            (high (fn-nntp-range-high (fn-nntp-parse-range token))))
                 (:instance fn-scat-built-range-numbers-nonstring
                            (articles (fn-cat-view-articles v fn-arena fn-cat))
                            (group (fn-nntp-session-group session))
                            (low (fn-nntp-range-low (fn-nntp-parse-range token)))
                            (high (fn-nntp-range-high (fn-nntp-parse-range token))))
                 (:instance fn-xri-archive-range-nonstring
                            (articles (fn-cat-view-articles v fn-arena fn-cat))
                            (group (fn-nntp-session-group session))
                            (low (fn-nntp-range-low (fn-nntp-parse-range token)))
                            (high (fn-nntp-range-high (fn-nntp-parse-range token))))
                 (:instance fn-scat-range-numbers-is-group-range-numbers
                            (group (fn-nntp-session-group session))
                            (low (fn-nntp-range-low (fn-nntp-parse-range token)))
                            (high (fn-nntp-range-high (fn-nntp-parse-range token)))))
           :in-theory (e/d (fn-nntp-over-range-served-cat fn-nntp-over-range-served-col
                            fn-nov-served-lines-for-numbers-cat-is-col fn-gidx-range-numbers
                            fn-scat-index-range-numbers-of-nil)
                           (fn-nntp-index-group-range-numbers fn-scat-range-numbers fn-gidx-build fn-midx-build
                            fn-cat-view-articles fn-cnx-freshp fn-nntp-group-range-numbers
                            fn-nov-served-lines-for-numbers-cat fn-nov-served-lines-numbered-col
                            fn-nntp-parse-range fn-nntp-range-okp fn-article-listp
                            fn-nntp-multi fn-nntp-single fn-gidx-bucket-numbers
                            fn-gidx-range-of-build-equals-archive-fold
                            fn-scat-range-numbers-is-group-range-numbers)))))

;;; OVER/XOVER with no argument and OVER <msgid> (audit R4, lane
;;; served-incremental-1): the current article from the number table
;;; (fn-scat-available-article, KEYSTONE P) and the Message-ID form from the
;;; catalog's Message-ID column (fn-scat-msgid-article, KEYSTONE A), never a
;;; walk of the view's articles (fn-nntp-available-article,
;;; fn-find-article: O(N) per command).
(defun fn-nntp-over-current-served-cat (session server v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard (fn-scat-guard)))
  (let ((group (fn-nntp-session-group session))
        (current (fn-nntp-session-current session)))
    (if (null group)
        (fn-nntp-single session "412 no newsgroup selected")
      (if (null current)
          (fn-nntp-single session "420 no current article")
        (let ((article (fn-scat-available-article group current v fn-arena fn-cat)))
          (if (not (consp article))
              (fn-nntp-single session "420 no current article")
            (if (fn-scol-tombstonep article fn-arena fn-cat)
                (fn-nntp-single session "423 article reclaimed")
              (let ((over (fn-scol-overview-of article fn-arena fn-cat)))
                (if (fn-nov-okp over)
                    (fn-nntp-multi session "224 overview information follows"
                                   (list (fn-nov-served-line current over
                                                             server article)))
                  (fn-nntp-single
                   session "503 stored article framing unavailable"))))))))))

(defthm fn-nntp-over-current-served-cat-is-col
  (implies (and (fn-cnx-freshp fn-cat)
                (equal (fn-state-articles archive) (fn-cat-view-articles v fn-arena fn-cat)))
           (equal (fn-nntp-over-current-served-cat session server v fn-arena fn-cat)
                  (fn-nntp-over-current-served-col session archive server fn-arena fn-cat)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nntp-over-current-served-col)
                           (fn-scat-available-article fn-nntp-available-article
                            fn-cat-view-articles fn-cnx-freshp fn-scol-tombstonep
                            fn-scol-overview-of fn-nov-okp fn-nov-served-line
                            fn-nntp-multi fn-nntp-single)))))

;; Cost (Codex r51 F1): flat in N, not O(1).  One Message-ID column probe
;; (the keyed tag consing nothing, books/msgid-tag-exec), then work per ID
;; (the Message-ID's seq list, reversed and walked to the one visible at V)
;; and per output line (the group membership walk of the overview line).
(defun fn-nntp-over-msgid-served-cat (session token server v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard (fn-scat-guard)))
  (let ((article (fn-scat-msgid-article (fn-nntp-token-string token) v fn-arena fn-cat)))
    (if (not (consp article))
        (fn-nntp-single session "430 no article with that message-id")
      (if (fn-scol-tombstonep article fn-arena fn-cat)
          (fn-nntp-single session "430 article reclaimed")
        (let ((over (fn-scol-overview-of article fn-arena fn-cat)))
          (if (fn-nov-okp over)
              (fn-nntp-multi session "224 overview information follows"
                             (list (fn-nov-served-line 0 over server article)))
            (fn-nntp-single session
                            "503 stored article framing unavailable")))))))

(defthm fn-nntp-over-msgid-served-cat-is-col
  (implies (equal (fn-state-articles archive) (fn-cat-view-articles v fn-arena fn-cat))
           (equal (fn-nntp-over-msgid-served-cat session token server v fn-arena fn-cat)
                  (fn-nntp-over-msgid-served-col session archive token server fn-arena fn-cat)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nntp-over-msgid-served-col)
                           (fn-scat-msgid-article fn-find-article
                            fn-cat-view-articles fn-scol-tombstonep
                            fn-scol-overview-of fn-nov-okp fn-nov-served-line
                            fn-nntp-multi fn-nntp-single)))))

(in-theory (disable fn-nntp-over-current-served-cat fn-nntp-over-msgid-served-cat))

(defun fn-nntp-xref-reply-cat (session archive index env keyword args v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard (fn-scat-guard))
           (ignorable archive))
  (cond
   ((and (fn-nntp-keywordp keyword "LIST")
         (fn-nntp-xref-server env)
         (consp args) (null (cdr args))
         (fn-nntp-keyword-tokenp (car args))
         (fn-nntp-keywordp (car args) "OVERVIEW.FMT"))
    (fn-nntp-list-overview-fmt-served session))
   ((and (or (fn-nntp-keywordp keyword "OVER")
             (fn-nntp-keywordp keyword "XOVER"))
         (fn-nntp-xref-server env)
         (fn-gidx-pinp index)
         (consp args) (null (cdr args))
         (fn-nntp-range-okp (fn-nntp-parse-range (car args))))
    ;; The CURSOR at the server name (fn-nntp-over-range-ovw): the range is
    ;; parsed and clamped, no number probed; the host drains it in quanta.
    ;; Expanded it is fn-nntp-over-range-served-cat's whole reply
    ;; (fn-nntp-over-range-ovw-expands-to-over-range-served-cat).
    (fn-nntp-over-range-ovw
     session v (car args) (fn-nntp-keywordp keyword "XOVER") (fn-nntp-xref-server env) fn-cat))
   ((and (or (fn-nntp-keywordp keyword "OVER")
             (fn-nntp-keywordp keyword "XOVER"))
         (fn-nntp-xref-server env)
         (null args))
    (fn-nntp-over-current-served-cat session (fn-nntp-xref-server env) v fn-arena fn-cat))
   ((and (fn-nntp-keywordp keyword "OVER")
         (fn-nntp-xref-server env)
         (consp args) (null (cdr args))
         (not (fn-nntp-range-okp (fn-nntp-parse-range (car args))))
         (fn-nntp-message-id-tokenp (car args)))
    (fn-nntp-over-msgid-served-cat session (car args)
                                   (fn-nntp-xref-server env) v fn-arena fn-cat))
   (t nil)))

; The served Xref arms are the column reference's modulo the OVER cursor:
; the same arm answers (iff), the sessions are equal, and the effects are
; equal once the cursor is expanded (fn-ovw-expand; the range arm is the one
; place the two differ).  The column reference carries no cursor.
(defthm fn-nntp-xref-reply-cat-is-col
  (implies (and (fn-article-listp configured (fn-cat-view-articles v fn-arena fn-cat))
                (equal (fn-state-articles archive) (fn-cat-view-articles v fn-arena fn-cat))
                (fn-cnx-freshp fn-cat)
                (implies (fn-gidx-pinp index)
                         (and (equal (fn-gidx-pin-buckets index)
                                     (fn-gidx-build (fn-cat-view-articles v fn-arena fn-cat)))
                              (equal (fn-gidx-pin-trie index)
                                     (fn-midx-build (fn-cat-view-articles v fn-arena fn-cat))))))
           (and (iff (fn-nntp-xref-reply-cat session archive index env keyword args v fn-arena fn-cat)
                     (fn-nntp-xref-reply-col session archive index env keyword args fn-arena fn-cat))
                (equal (car (fn-nntp-xref-reply-cat session archive index env keyword args v
                                                    fn-arena fn-cat))
                       (car (fn-nntp-xref-reply-col session archive index env keyword args
                                                    fn-arena fn-cat)))
                (equal (fn-ovw-expand
                        (cdr (fn-nntp-xref-reply-cat session archive index env keyword args v
                                                     fn-arena fn-cat))
                        fn-arena fn-cat)
                       (fn-ovw-expand
                        (cdr (fn-nntp-xref-reply-col session archive index env keyword args
                                                     fn-arena fn-cat))
                        fn-arena fn-cat))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nntp-xref-reply-cat fn-nntp-xref-reply-col
                            fn-nntp-over-range-ovw-expands-to-over-range-served-cat)
                           (fn-nntp-over-range-served-cat fn-nntp-over-range-served-col
                            fn-nntp-over-range-ovw fn-ovw-expand
                            fn-nntp-over-current-served-col fn-nntp-over-msgid-served-col
                            fn-nntp-over-current-served-cat fn-nntp-over-msgid-served-cat
                            fn-nntp-list-overview-fmt-served fn-nntp-keywordp fn-nntp-xref-server
                            fn-gidx-pinp fn-nntp-parse-range fn-nntp-range-okp fn-nntp-keyword-tokenp
                            fn-nntp-message-id-tokenp fn-gidx-build fn-midx-build fn-cat-view-articles
                            fn-cnx-freshp fn-article-listp fn-gidx-pin-buckets fn-gidx-pin-trie))
           :use ((:instance fn-nntp-over-range-served-cat-is-col
                            (token (car args)) (legacyp (fn-nntp-keywordp keyword "XOVER"))
                            (server (fn-nntp-xref-server env)))
                 (:instance fn-nntp-over-current-served-cat-is-col
                            (server (fn-nntp-xref-server env)))
                 (:instance fn-nntp-over-msgid-served-cat-is-col
                            (token (car args)) (server (fn-nntp-xref-server env)))
                 (:instance fn-nntp-parse-range-ok-has-natural-bounds (token (car args)))))))

(defun fn-nntp-msgid-withdrawn-p-cat (index token v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard (fn-scat-guard)))
  (and (fn-octet-listp token)
       (fn-ctl-msgid-withdrawn (fn-nntp-token-string token)
                               (fn-ctl-pin-withdrawn (fn-gidx-pin-control index)))
       (not (consp (fn-scat-msgid-article (fn-nntp-token-string token) v fn-arena fn-cat)))
       t))

(defthm fn-nntp-msgid-withdrawn-p-cat-is-trie
  (implies (and (fn-nntp-message-id-tokenp token)
                (equal (fn-gidx-pin-trie index) (fn-midx-build (fn-cat-view-articles v fn-arena fn-cat))))
           (equal (fn-nntp-msgid-withdrawn-p-cat index token v fn-arena fn-cat)
                  (fn-nntp-msgid-withdrawn-p index token)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nntp-msgid-withdrawn-p-cat fn-nntp-msgid-withdrawn-p
                            fn-scat-msgid-article-is-find-article
                            fn-midx-lookup-of-build-is-find-article-for-nonempty)
                           (fn-scat-msgid-article fn-midx-lookup fn-midx-build fn-find-article
                            fn-cat-view-articles fn-ctl-msgid-withdrawn fn-nntp-token-string
                            fn-nntp-message-id-tokenp fn-gidx-pin-trie fn-gidx-pin-control))
           :use ((:instance fn-nntp-message-id-token-has-nonempty-index-key)))))


;;; HDR :fn-control and HDR :fn-enrollment over the catalog (lane
;;; join-f2-midx): the article a Message-ID names is found in the catalog's
;;; Message-ID column at the pin's version, not the pinned trie; each arm is
;;; equated to the pinned arm under the pin's correspondence.

(defun fn-scat-control-held (msgid visible withdrawn v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard (fn-scat-guard)))
  (or (fn-ctl-msgid-withdrawn msgid withdrawn)
      (if (and (stringp msgid) (< 0 (length msgid)))
          (let ((hit (fn-scat-msgid-article msgid v fn-arena fn-cat)))
            (if (consp hit) hit nil))
        (fn-ctl-msgid-withdrawn msgid visible))))

(defthm fn-scat-control-held-is-find-held
  (implies (equal visible (fn-cat-view-articles v fn-arena fn-cat))
           (equal (fn-scat-control-held msgid visible withdrawn v fn-arena fn-cat)
                  (fn-ctl-find-held msgid visible withdrawn)))
  :hints (("Goal" :in-theory (e/d (fn-ctl-find-held fn-scat-msgid-article-is-find-article)
                                  (fn-scat-msgid-article fn-find-article fn-ctl-msgid-withdrawn
                                   fn-cat-view-articles fn-ctl-find-article-is-msgid-withdrawn))
           :use ((:instance fn-ctl-find-article-is-msgid-withdrawn (xs visible))))))

(defun fn-scat-control-status (c cbytes visible withdrawn ws verdicts v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard (fn-scat-guard)))
  (let* ((msgid (and (consp c) (fn-article-msgid c)))
         (target (and (consp c) (fn-ctl-target-octets cbytes)))
         (plan (fn-ctl-withdrawal-plan msgid (fn-ctl-lookup-verdict msgid verdicts)
                                       target
                                       (and (consp c)
                                            (fn-ctl-keys-octets cbytes))
                                       nil)))
    (cond ((not target) (list :none))
          ((not (fn-ctl-withdrawalp plan)) (list :declined (fn-ctl-at 1 plan)))
          (t (let ((rec (fn-ctl-cause-record ws msgid target)))
               (if (not rec)
                   (list :declined :no-record)
                 (let ((held (fn-scat-control-held target visible withdrawn v fn-arena fn-cat)))
                   (if (not held)
                       (list :owed)
                     (let ((effect (fn-ctl-withdrawal-effect
                                    rec (fn-article-groups held)
                                    (fn-ctl-lookup-verdict target verdicts)
                                    (fn-article-payload held))))
                       (if (fn-ctl-effect-withdrawsp effect)
                           (list :executed effect)
                         (list :declined (fn-ctl-at 1 effect))))))))))))

(defthm fn-scat-control-status-is-control-status
  (implies (equal visible (fn-cat-view-articles v fn-arena fn-cat))
           (equal (fn-scat-control-status c cbytes visible withdrawn ws verdicts v fn-arena fn-cat)
                  (fn-ctl-control-status c cbytes visible withdrawn ws verdicts)))
  :hints (("Goal" :in-theory (e/d (fn-ctl-control-status fn-scat-control-held-is-find-held)
                                  (fn-scat-control-held fn-ctl-find-held fn-cat-view-articles
                                   fn-ctl-withdrawal-plan fn-ctl-withdrawalp
                                   fn-ctl-withdrawal-effect fn-ctl-effect-withdrawsp
                                   fn-ctl-cause-record fn-ctl-target-octets fn-ctl-keys-octets
                                   fn-ctl-lookup-verdict)))))

(defun fn-nntp-control-hdr-response-cat (session archive index verdicts args v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard (fn-scat-guard)))
  (if (and (consp args) (consp (cdr args)) (null (cddr args))
           (fn-nntp-message-id-tokenp (cadr args))
           (fn-octet-listp (cadr args)))
      (let* ((control (fn-gidx-pin-control index))
             (visible (fn-state-articles archive))
             (withdrawn (fn-ctl-pin-withdrawn control))
             (c (fn-scat-control-held (fn-nntp-token-string (cadr args))
                                        visible withdrawn v fn-arena fn-cat)))
        (if (not (consp c))
            (fn-nntp-single session (fn-proto-text "HDR" :no-msgid))
          (let* ((cbytes (fn-nntp-article-bytes c fn-arena))
                 (item (fn-nntp-string-octets
                        (fn-ctl-control-item
                         (fn-scat-control-status c cbytes visible withdrawn
                                                   (fn-ctl-pin-ws control) verdicts v fn-arena fn-cat)
                         (fn-ctl-target-octets cbytes)))))
            (if (fn-nntp-control-cleanp item)
                (fn-nntp-multi
                 session (fn-nntp-hdr-initial nil)
                 (list (fn-nntp-hdr-line (fn-nntp-decimal-field 0) item)))
              (fn-nntp-single session (fn-proto-text "HDR" :no-control-status))))))
    (fn-nntp-single session (fn-proto-text "HDR" :syntax))))

(defthm fn-nntp-control-hdr-response-cat-is-pinned
  (implies (and (equal (fn-state-articles archive) (fn-cat-view-articles v fn-arena fn-cat))
                (fn-midx-correspondencep (fn-gidx-pin-trie index) (fn-state-articles archive)))
           (equal (fn-nntp-control-hdr-response-cat session archive index verdicts args v fn-arena fn-cat)
                  (fn-nntp-control-hdr-response session archive index verdicts args fn-arena)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nntp-control-hdr-response-cat fn-nntp-control-hdr-response
                            fn-scat-control-held-is-find-held fn-scat-control-status-is-control-status
                            fn-ctl-served-held-is-find-held fn-ctl-served-status-is-control-status)
                           (fn-scat-control-held fn-ctl-served-held fn-scat-control-status
                            fn-ctl-served-status fn-ctl-find-held fn-ctl-control-status
                            fn-cat-view-articles fn-midx-correspondencep fn-nntp-article-bytes
                            fn-ctl-control-item fn-nntp-string-octets fn-nntp-control-cleanp
                            fn-nntp-multi fn-nntp-single fn-nntp-hdr-line fn-nntp-message-id-tokenp)))))

(defun fn-nntp-enrollment-hdr-response-cat (session index verdicts args v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard (fn-scat-guard)))
  (if (and (consp args) (consp (cdr args)) (null (cddr args))
           (fn-nntp-message-id-tokenp (cadr args))
           (fn-octet-listp (cadr args)))
      (let ((msgid (fn-nntp-token-string (cadr args))))
        (if (not (consp (fn-scat-msgid-article msgid v fn-arena fn-cat)))
            (fn-nntp-single session (fn-proto-text * :no-msgid))
          (fn-nntp-multi
           session (fn-nntp-hdr-initial nil)
           (list (fn-nntp-hdr-line
                  (fn-nntp-decimal-field 0)
                  (fn-enr-item (fn-stx-reader-lookup msgid verdicts)
                               (fn-gidx-pin-control index)))))))
    (fn-nntp-single session (fn-proto-text * :syntax))))

(defthm fn-nntp-enrollment-hdr-response-cat-is-pinned
  (implies (and (equal (fn-state-articles archive) (fn-cat-view-articles v fn-arena fn-cat))
                (fn-midx-correspondencep (fn-gidx-pin-trie index) (fn-state-articles archive)))
           (equal (fn-nntp-enrollment-hdr-response-cat session index verdicts args v fn-arena fn-cat)
                  (fn-nntp-enrollment-hdr-response session archive index verdicts args)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nntp-enrollment-hdr-response-cat fn-nntp-enrollment-hdr-response
                            fn-scat-msgid-article-is-find-article fn-midx-correspondencep
                            fn-midx-lookup-of-build-is-find-article-for-nonempty)
                           (fn-scat-msgid-article fn-find-article fn-midx-lookup fn-midx-build
                            fn-cat-view-articles fn-nntp-token-string fn-nntp-message-id-tokenp
                            fn-enr-item fn-stx-reader-lookup fn-nntp-multi fn-nntp-single
                            fn-nntp-hdr-line fn-gidx-pin-trie fn-gidx-pin-control))
           :use ((:instance fn-nntp-message-id-token-has-nonempty-index-key (token (cadr args)))))))

;;; The dispatcher: fn-nntp-archive-command-pinned's case split with the two
;;; retrieval arms reading the catalog.  Every other arm is the pinned arm
;;; (it reads the archive and the pinned index until step 8).  Its guards are
;;; verified with the lift (fn-nntp-command-pinned and above call it then);
;;; the host calls nothing in this book yet.

;;; LIST / LIST ACTIVE (audit R1, lane served-incremental-1): each group's
;;; line from the raw compatibility group summary (fn-scat-group-summary
;;; enumerates retained identities), never the list model's
;;; per-group walk (fn-nntp-group-summary: three walks and three N-cons
;;; copies of the view's articles per group, O(G*N) per LIST).

(defun fn-scat-active-line (archive group v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v)))
  (let ((summary (fn-scat-group-summary archive group v fn-cat)))
    (fn-nntp-append-pieces
     (list (fn-nntp-string-octets group) '(32)
           (fn-nntp-decimal-field (fn-nntp-summary-high summary)) '(32)
           (fn-nntp-decimal-field (fn-nntp-summary-low summary))
           (fn-nntp-string-octets " y")))))

(defun fn-scat-active-status-line (archive group closed v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v)))
  (let ((summary (fn-scat-group-summary archive group v fn-cat)))
    (fn-nntp-append-pieces
     (list (fn-nntp-string-octets group) '(32)
           (fn-nntp-decimal-field (fn-nntp-summary-high summary)) '(32)
           (fn-nntp-decimal-field (fn-nntp-summary-low summary)) '(32)
           (fn-nntp-string-octets
            (fn-nntp-closed-status (fn-nntp-string-octets group) closed))))))

; GEN: def-loop (a read-only stobj formal; :map has no stobj formals yet).
(defun fn-scat-active-lines-loop (archive groups closed statusp v fn-cat acc)
  (declare (xargs :stobjs fn-cat :guard (and (natp v) (true-listp acc)) :verify-guards nil))
  (if (consp groups)
      (fn-scat-active-lines-loop
       archive (cdr groups) closed statusp v fn-cat
       (cons (if statusp
                 (fn-scat-active-status-line archive (car groups) closed v fn-cat)
               (fn-scat-active-line archive (car groups) v fn-cat))
             acc))
    (revappend acc nil)))

(defun fn-scat-active-lines (archive groups closed statusp v fn-cat)
  (declare (xargs :verify-guards nil :stobjs fn-cat :guard (natp v)))
  (mbe :logic
       (if (consp groups)
           (cons (if statusp
                     (fn-scat-active-status-line archive (car groups) closed v fn-cat)
                   (fn-scat-active-line archive (car groups) v fn-cat))
                 (fn-scat-active-lines archive (cdr groups) closed statusp v fn-cat))
         nil)
       :exec (fn-scat-active-lines-loop archive groups closed statusp v fn-cat nil)))

(local
 (defthm fn-scat-active-lines-loop-is-revappend
   (equal (fn-scat-active-lines-loop archive groups closed statusp v fn-cat acc)
          (revappend acc (fn-scat-active-lines archive groups closed statusp v fn-cat)))
   :hints (("Goal" :induct (fn-scat-active-lines-loop archive groups closed statusp v fn-cat acc)
                   :in-theory (union-theories '(fn-scat-active-lines-loop fn-scat-active-lines
                                                revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-scat-active-lines-loop)

(verify-guards fn-scat-active-lines
  :hints (("Goal" :in-theory (union-theories '(revappend fn-scat-active-lines)
                                             (union-theories (theory 'minimal-theory)
                                                             (executable-counterpart-theory :here)))
                  :use ((:instance fn-scat-active-lines-loop-is-revappend (acc nil))))))

(defthm fn-scat-active-lines-is-active-lines
  (implies (and (fn-cnx-freshp fn-cat) (not (member-equal nil groups))
                (equal (fn-state-articles archive) (fn-cat-view-articles v fn-arena fn-cat)))
           (equal (fn-scat-active-lines archive groups closed nil v fn-cat)
                  (fn-nntp-active-lines archive groups)))
  :hints (("Goal" :induct (fn-nntp-active-lines archive groups)
           :in-theory (e/d (fn-nntp-active-lines fn-nntp-active-line fn-scat-active-line)
                           (fn-scat-group-summary fn-nntp-group-summary
                            fn-cat-view-articles fn-cnx-freshp fn-nntp-append-pieces
                            fn-nntp-decimal-field fn-nntp-summary-high fn-nntp-summary-low)))))

(defthm fn-scat-active-lines-is-active-status-lines
  (implies (and (fn-cnx-freshp fn-cat) (not (member-equal nil groups))
                (equal (fn-state-articles archive) (fn-cat-view-articles v fn-arena fn-cat)))
           (equal (fn-scat-active-lines archive groups closed t v fn-cat)
                  (fn-nntp-active-status-lines archive groups closed)))
  :hints (("Goal" :induct (fn-nntp-active-status-lines archive groups closed)
           :in-theory (e/d (fn-nntp-active-status-lines fn-nntp-active-status-line
                            fn-scat-active-status-line)
                           (fn-scat-group-summary fn-nntp-group-summary
                            fn-cat-view-articles fn-cnx-freshp fn-nntp-append-pieces
                            fn-nntp-decimal-field fn-nntp-summary-high fn-nntp-summary-low
                            fn-nntp-closed-status)))))

;; Cost (Codex r51 F2): flat in N at the TOP view only (fn-scat-top-viewp:
;; the carried live summaries).  A session pinned at an older view V reads
;; Raw compatibility summary enumerates the clamped range per group.
;; (measured: 1.2 MB and 1.5 ms per LIST at D = 1,000, 10 groups).
;; The LIST forms this arm answers: LIST and LIST ACTIVE [wildmat].
(defun fn-scat-list-active-formp (args)
  (declare (xargs :guard t))
  (or (null args)
      (and (consp args)
           (fn-nntp-keyword-tokenp (car args))
           (fn-nntp-keywordp (car args) "ACTIVE"))))

(defun fn-nntp-list-active-cat (session archive closed args v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v)))
  (let ((arguments (if (consp args) (cdr args) nil))
        (statusp (consp closed)))
    (if (null arguments)
        (fn-nntp-multi session (fn-proto-text "LIST" :active)
                       (fn-scat-active-lines archive (fn-state-groups archive)
                                             closed statusp v fn-cat))
      (if (and (consp arguments) (null (cdr arguments)))
          (let ((parsed (fn-wildmat-parse (car arguments))))
            (if (fn-wildmat-result-okp parsed)
                (fn-nntp-multi session (fn-proto-text "LIST" :active)
                               (fn-scat-active-lines
                                archive
                                (fn-nntp-filter-groups-by-wildmat
                                 (fn-wildmat-result-value parsed) (fn-state-groups archive))
                                closed statusp v fn-cat))
              (fn-nntp-single session (fn-proto-text * :syntax))))
        (fn-nntp-single session (fn-proto-text * :syntax))))))

(defthm fn-nntp-list-active-cat-is-list-command
  (implies (and (fn-scat-list-active-formp args)
                (fn-cnx-freshp fn-cat) (fn-statep archive)
                (equal (fn-state-articles archive) (fn-cat-view-articles v fn-arena fn-cat)))
           (equal (fn-nntp-list-active-cat session archive (fn-nntp-env-closed env) args v fn-cat)
                  (fn-nntp-list-command session archive env args)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nntp-list-command fn-nntp-list-status-response
                            fn-nntp-list-response fn-nntp-list-active-status
                            fn-nntp-list-active fn-nntp-list-active-or-newsgroups
                            fn-nntp-list-filtered-response)
                           (fn-scat-active-lines fn-nntp-active-lines
                            fn-nntp-active-status-lines
                            fn-cat-view-articles fn-cnx-freshp fn-statep
                            fn-wildmat-parse fn-nntp-filter-groups-by-wildmat
                            fn-nntp-multi fn-nntp-single fn-nntp-list-active-times
                            fn-nntp-list-counts-command fn-nntp-list-newsgroups-described
                            fn-nntp-list-motd fn-nntp-list-unmaintained-response
                            fn-nntp-list-newsgroups)))))

(in-theory (disable fn-nntp-list-active-cat))

;;; NEXT / LAST (audit R2, lane served-incremental-1): the neighbour of the
;;; current number served at V, probed number by number up (down) from the
;;; current one through the number table (fn-scat-raw-first-p / fn-scat-raw-last-p:
;;; one probe and one visibility test a number, nothing consed), never the
;;; list model's copy of every article (fn-nntp-group-next-number's
;;; fn-ag-rev-onto) plus two walks.  The work is the gap to the neighbour.

;; The list model's neighbours are the ends of a range of available numbers.
(defthm fn-scat-group-next-number-is-car
  (implies (natp current)
           (equal (fn-nntp-group-next-number group current articles)
                  (let ((l (fn-nntp-group-range-numbers
                            group (+ 1 current) *fn-nntp-max-article-number* articles)))
                    (if (consp l) (car l) 0))))
  :hints (("Goal" :induct (fn-nntp-group-next-number group current articles)
           :in-theory (enable fn-nntp-group-next-number fn-nntp-group-range-numbers))))

(defthm fn-scat-group-last-number-is-last
  (implies (natp current)
           (equal (fn-nntp-group-last-number group current articles)
                  (fn-scat-last-number
                   (fn-nntp-group-range-numbers group 1 (- current 1) articles))))
  :hints (("Goal" :induct (fn-nntp-group-last-number group current articles)
           :in-theory (enable fn-nntp-group-last-number fn-nntp-group-range-numbers))))

(local
 (defthm fn-scat-range-numbers-from-at-view
   (implies (and (natp v) (natp k) (natp top))
            (equal (fn-scat-range-numbers group k top v fn-cat)
                   (fn-scat-view-list group k (min top (fn-cat-group-high group fn-cat))
                                      v fn-cat)))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-cnx-view-range)
                            (fn-scat-view-list fn-cnx-range-aux fn-scat-range-keep))))))

(defun fn-scat-next-number (group current v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (and (natp current) (natp v))))
  (fn-scat-raw-first-p group (+ 1 current) (nfix (- (fn-cat-group-next group fn-cat) 1)) v fn-cat))

(defun fn-scat-previous-number (group current v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (and (natp current) (natp v))))
  (if (posp current)
      (fn-scat-raw-last-p group (min (- current 1) (nfix (- (fn-cat-group-next group fn-cat) 1)))
                     v fn-cat)
    0))

(defthm fn-scat-next-number-is-next-number
  (implies (and (fn-cnx-freshp fn-cat) group (natp current) (natp v))
           (equal (fn-scat-next-number group current v fn-cat)
                  (fn-nntp-group-next-number group current
                                             (fn-cat-view-articles v fn-arena fn-cat))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-scat-next-number)
                           (fn-scat-raw-first-p fn-scat-view-list fn-scat-range-numbers
                            fn-nntp-group-range-numbers fn-cat-view-articles fn-cnx-freshp
                            fn-scat-range-numbers-is-group-range-numbers))
           :use ((:instance fn-scat-range-numbers-is-group-range-numbers
                            (low (+ 1 current)) (high *fn-nntp-max-article-number*))
                 (:instance fn-scat-range-numbers-from-at-view
                            (k (+ 1 current)) (top *fn-nntp-max-article-number*))
                 (:instance fn-scat-view-list-clamp (k (+ 1 current))
                            (top (fn-cat-group-high group fn-cat)))
                 (:instance fn-scat-view-list-car (k (+ 1 current))
                            (top (fn-cat-group-high group fn-cat)))))))

(local
 (defthm fn-scat-range-numbers-below-one
   (implies (and (rationalp high) (< high 1))
            (equal (fn-nntp-group-range-numbers group low high articles) nil))
   :hints (("Goal" :induct (fn-nntp-group-range-numbers group low high articles)
            :in-theory (enable fn-nntp-group-range-numbers)))))

(defthm fn-scat-previous-number-is-last-number
  (implies (and (fn-cnx-freshp fn-cat) group (natp current) (natp v))
           (equal (fn-scat-previous-number group current v fn-cat)
                  (fn-nntp-group-last-number group current
                                             (fn-cat-view-articles v fn-arena fn-cat))))
  :hints (("Goal" :do-not-induct t
           :cases ((posp current))
           :in-theory (e/d (fn-scat-previous-number)
                           (fn-scat-raw-last-p fn-scat-view-list fn-scat-range-numbers
                            fn-nntp-group-range-numbers fn-cat-view-articles fn-cnx-freshp
                            fn-scat-range-numbers-is-group-range-numbers))
           :use ((:instance fn-scat-range-numbers-is-group-range-numbers
                            (low 1) (high (- current 1)))
                 (:instance fn-scat-range-numbers-from-at-view
                            (k 1) (top (- current 1)))
                 (:instance fn-scat-view-list-last
                            (top (min (- current 1) (fn-cat-group-high group fn-cat))))))
))

(in-theory (disable fn-scat-next-number fn-scat-previous-number))

;; A current number that is not a natural (no session the reader machine
;; builds carries one) is answered by the list model unchanged.
(defun fn-nntp-next-or-last-cat (session archive direction v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard (fn-scat-guard) :verify-guards nil))
  (let ((group (fn-nntp-session-group session))
        (current (fn-nntp-session-current session)))
    (if (and group (natp current) (natp v))
        (let ((number (if (equal direction :next)
                          (fn-scat-next-number group current v fn-cat)
                        (fn-scat-previous-number group current v fn-cat))))
          (if (posp number)
              (fn-nntp-article-response
               session (fn-scat-available-article group number v fn-arena fn-cat)
               number :stat t group fn-arena)
            (if (equal direction :next)
                (fn-nntp-single session (fn-proto-text "NEXT" :no-next))
              (fn-nntp-single session (fn-proto-text "LAST" :no-previous)))))
      (fn-nntp-next-or-last session archive direction fn-arena))))

(defthm fn-nntp-next-or-last-cat-is-next-or-last
  (implies (and (fn-cnx-freshp fn-cat)
                (equal (fn-state-articles archive) (fn-cat-view-articles v fn-arena fn-cat)))
           (equal (fn-nntp-next-or-last-cat session archive direction v fn-arena fn-cat)
                  (fn-nntp-next-or-last session archive direction fn-arena)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nntp-next-or-last)
                           (fn-scat-available-article fn-nntp-available-article
                            fn-nntp-group-next-number fn-nntp-group-last-number
                            fn-cat-view-articles fn-cnx-freshp fn-nntp-article-response
                            fn-nntp-single)))))

;;; The current article of ARTICLE/HEAD/BODY/STAT with no argument (audit
;;; R4): the number table, as fn-rcompat-retrieval-cat reads it for the Xref
;;; form, never the walk of fn-nntp-current-retrieval.
(defun fn-nntp-current-retrieval-cat (session kind v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard (fn-scat-guard) :verify-guards nil))
  (let ((group (fn-nntp-session-group session))
        (current (fn-nntp-session-current session)))
    (if (null group)
        (fn-nntp-single session (fn-proto-text * :no-group-selected))
      (if (null current)
          (fn-nntp-single session (fn-proto-text * :no-current))
        (let ((article (fn-scat-available-article group current v fn-arena fn-cat)))
          (if (consp article)
              (fn-nntp-article-response session article current kind t group fn-arena)
            (fn-nntp-single session (fn-proto-text * :no-current))))))))

(defthm fn-nntp-current-retrieval-cat-is-current-retrieval
  (implies (and (fn-cnx-freshp fn-cat)
                (equal (fn-state-articles archive) (fn-cat-view-articles v fn-arena fn-cat)))
           (equal (fn-nntp-current-retrieval-cat session kind v fn-arena fn-cat)
                  (fn-nntp-current-retrieval session archive kind fn-arena)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nntp-current-retrieval)
                           (fn-scat-available-article fn-nntp-available-article
                            fn-cat-view-articles fn-cnx-freshp fn-nntp-article-response
                            fn-nntp-single)))))

(verify-guards fn-nntp-next-or-last-cat)
(verify-guards fn-nntp-current-retrieval-cat)
(in-theory (disable fn-nntp-next-or-last-cat fn-nntp-current-retrieval-cat))

; Guards of the arms the lift executes (books/served-catalog-chain.lisp
; fn-scr-command calls the dispatcher): the whole -cat path is guard-verified.
(verify-guards fn-nntp-xpat-lines-for-numbers-cat-loop)

(verify-guards fn-nntp-xpat-lines-for-numbers-cat
  :hints (("Goal" :in-theory (union-theories '(revappend fn-nntp-xpat-lines-for-numbers-cat)
                                                  (union-theories (theory 'minimal-theory)
                                                                  (executable-counterpart-theory :here)))
                  :use ((:instance fn-nntp-xpat-lines-for-numbers-cat-loop-is-revappend (acc nil))))))
(verify-guards fn-nntp-xpat-response-cat)
(verify-guards fn-rcompat-retrieval-cat)
(verify-guards fn-rcompat-hdr-lines-cat-loop)

(verify-guards fn-rcompat-hdr-lines-cat
  :hints (("Goal" :in-theory (union-theories '(revappend fn-rcompat-hdr-lines-cat)
                                                  (union-theories (theory 'minimal-theory)
                                                                  (executable-counterpart-theory :here)))
                  :use ((:instance fn-rcompat-hdr-lines-cat-loop-is-revappend (acc nil))))))
(verify-guards fn-rcompat-hdr-cat)
(verify-guards fn-rcompat-reply-cat)
(verify-guards fn-nntp-number-withdrawn-p-cat)
;; Withdrawn from includers (lane rule-hygiene, tools/rule_cost.py).
;; Each is tried in includers' proofs and pays for its frames in
;; almost none (planning/evidence/rule-cost-*.json has the counts;
;; docs/proof-style.md section 8).  An includer that needs one
;; enables it where it is used.
(in-theory (disable (:rewrite fn-scat-article-idp-is-msgid-idp)))
