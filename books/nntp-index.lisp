; C1-09: the proved PRF-010 index, adopted as a generation-bound cache for the
; NNTP number projection.
;
; books/nntp.lisp enumerates article numbers with single-pass folds over
; FN-STATE-ARTICLES: FN-NNTP-GROUP-COUNT, -LOW, -HIGH, -NEXT-NUMBER,
; -LAST-NUMBER and FN-NNTP-GROUP-RANGE-NUMBERS.  GROUP pays three of those
; folds and LISTGROUP a fourth, per command, over the whole archive.
;
; This book defines index-backed variants that traverse only the materialized
; FN-INDEX-BUILD entries, and proves each one equal to the fold it replaces on
; every consistent article list.  The bridge from the index to the articles is
; FN-INDEX-RANGE-QUERY-CORRECT (books/index.lisp): it equates
; FN-INDEX-QUERY-RANGE over a fresh build with the independent source
; enumeration FN-INDEX-REFERENCE-RANGE.  Nothing here re-derives what that
; theorem already establishes.
;
; The cache is generation bound.  FN-NNTP-INDEX-CACHE-QUERY answers from the
; index only when the caller's generation and configuration digest equal the
; ones the cache was built with; otherwise it returns a distinct (:STALE)
; result.  A stale answer is not one of its outcomes.
(in-package "ACL2")
(include-book "nntp")
(include-book "index")

; This book reasons about the NNTP transitions themselves, so it opens the
; vocabularies the five books of the nntp cluster withdraw at their export
; events (2026-09-19 split of books/nntp.lisp).
(local (in-theory (enable fn-nntp-syntax-vocabulary fn-nntp-session-vocabulary fn-nntp-projection-vocabulary fn-nntp-responses-vocabulary fn-nntp-vocabulary)))

; -----------------------------------------------------------------------------
; An index entry carries (group number msgid).  That is exactly the data
; FN-NNTP-ARTICLE-NUMBER needs: the per-article projectability test
; FN-NNTP-ARTICLE-IDP reads only FN-ARTICLE-MSGID.

(defun fn-nntp-index-msgid-okp (text)
  (declare (xargs :guard t :verify-guards nil))
  (and (stringp text)
       (<= (length text) *fn-nntp-max-message-id-octets*)
       (fn-nntp-message-id-tokenp (fn-nntp-string-octets text))))

(defthm fn-nntp-article-idp-is-msgid-okp
  (equal (fn-nntp-article-idp article)
         (fn-nntp-index-msgid-okp (fn-article-msgid article))))

; The available local number an entry denotes, or 0.  This is the entry-level
; twin of FN-NNTP-ARTICLE-NUMBER: same posp test, same RFC 3977 section 6
; bound, same identifier test.
(defun fn-nntp-index-entry-available (entry)
  (declare (xargs :guard t :verify-guards nil))
  (let ((number (fn-index-entry-number entry)))
    (if (and (posp number)
             (<= number *fn-nntp-max-article-number*)
             (fn-nntp-index-msgid-okp (fn-index-entry-msgid entry)))
        number
      0)))

(defun fn-nntp-index-numbers (entries)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp entries)
      (let ((number (fn-nntp-index-entry-available (fn-ag-car entries))))
        (if (posp number)
            (cons number (fn-nntp-index-numbers (fn-ag-cdr entries)))
          (fn-nntp-index-numbers (fn-ag-cdr entries))))
    nil))

; The article-side twin: the available numbers of GROUP inside [LOW,HIGH], in
; committed article order.  This is FN-NNTP-GROUP-RANGE-NUMBERS with CONS in
; place of the ordered insert, so the two differ only by the sort.
(defun fn-nntp-available-numbers (group low high articles)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp articles)
      (let ((number (fn-nntp-article-number group (fn-ag-car articles))))
        (if (and (posp number)
                 (fn-ng-less-equal low number)
                 (fn-ng-less-equal number high))
            (cons number
                  (fn-nntp-available-numbers group low high (fn-ag-cdr articles)))
          (fn-nntp-available-numbers group low high (fn-ag-cdr articles))))
    nil))

; -----------------------------------------------------------------------------
; Entry accessors of a freshly constructed entry.

(defthm fn-index-entry-group-of-entry
  (equal (fn-index-entry-group (fn-index-entry group number msgid)) group))
(defthm fn-index-entry-number-of-entry
  (equal (fn-index-entry-number (fn-index-entry group number msgid)) number))
(defthm fn-index-entry-msgid-of-entry
  (equal (fn-index-entry-msgid (fn-index-entry group number msgid)) msgid))

(in-theory (disable fn-index-entry fn-index-entry-group
                    fn-index-entry-number fn-index-entry-msgid))

; -----------------------------------------------------------------------------
; A consistent article's membership list is positional against its group list
; (FN-MEMBERSHIP-LISTP) and its group list has no duplicates
; (FN-SELECTION-VALIDP), so each group contributes exactly one membership.
; Those two facts are what make the materialized entries for one article agree
; with FN-NNTP-MEMBERSHIP-NUMBER, which reads only the first match.

(defthm fn-nntp-membership-number-of-non-member
  (implies (and (fn-membership-listp groups memberships)
                (not (member-equal group groups)))
           (equal (fn-nntp-membership-number group memberships) 0))
  :hints (("Goal" :induct (fn-membership-listp groups memberships))))

(defthm fn-index-reference-memberships-of-non-member
  (implies (and (fn-membership-listp groups memberships)
                (not (member-equal group groups)))
           (equal (fn-index-reference-memberships group low high msgid memberships)
                  nil))
  :hints (("Goal" :induct (fn-membership-listp groups memberships))))

(defthm fn-index-reference-memberships-of-member
  (implies (and (fn-membership-listp groups memberships)
                (fn-no-duplicatesp groups)
                (member-equal group groups))
           (equal (fn-index-reference-memberships group low high msgid memberships)
                  (if (and (<= low (fn-nntp-membership-number group memberships))
                           (<= (fn-nntp-membership-number group memberships) high))
                      (list (fn-index-entry
                             group
                             (fn-nntp-membership-number group memberships)
                             msgid))
                    nil)))
  :hints (("Goal" :induct (fn-membership-listp groups memberships))))

; -----------------------------------------------------------------------------
; One article's contribution: the index numbers of its reference memberships
; are exactly the one-element-or-empty contribution the fold makes.

(defthm fn-nntp-index-numbers-of-append
  (equal (fn-nntp-index-numbers (append xs ys))
         (append (fn-nntp-index-numbers xs)
                 (fn-nntp-index-numbers ys)))
  :hints (("Goal" :induct (append xs ys))))

(defthm fn-nntp-index-numbers-of-article-memberships
  (implies (fn-articlep configured article)
           (equal (fn-nntp-index-numbers
                   (fn-index-reference-memberships
                    group low high
                    (fn-article-msgid article)
                    (fn-article-memberships article)))
                  (if (and (posp (fn-nntp-article-number group article))
                           (<= low (fn-nntp-article-number group article))
                           (<= (fn-nntp-article-number group article) high))
                      (list (fn-nntp-article-number group article))
                    nil)))
  :hints (("Goal"
           :use ((:instance fn-index-reference-memberships-of-member
                            (groups (fn-article-groups article))
                            (memberships (fn-article-memberships article))
                            (msgid (fn-article-msgid article)))
                 (:instance fn-index-reference-memberships-of-non-member
                            (groups (fn-article-groups article))
                            (memberships (fn-article-memberships article))
                            (msgid (fn-article-msgid article))))
           :in-theory (e/d (fn-articlep fn-selection-validp
                            fn-nntp-article-number
                            fn-nntp-index-entry-available)
                           (fn-nntp-index-msgid-okp fn-nntp-article-idp)))))

(defthm fn-nntp-index-numbers-of-reference-range
  (implies (fn-article-listp configured articles)
           (equal (fn-nntp-index-numbers
                   (fn-index-reference-range group low high articles))
                  (fn-nntp-available-numbers group low high articles)))
  ; The accessors stay folded here on purpose: FN-ARTICLE-MSGID and
  ; FN-ARTICLE-MEMBERSHIPS normalize to CAR/CADDDR, and the lemma above is
  ; stated in accessor vocabulary, so it cannot match an unfolded goal.
  ; FN-ARTICLEP stays folded for the same reason -- it is the lemma's
  ; hypothesis, not a bag of conjuncts.
  :hints (("Goal" :induct (fn-index-reference-range group low high articles)
           :in-theory (disable fn-nntp-article-number
                               fn-nntp-index-entry-available
                               fn-articlep
                               fn-article-msgid
                               fn-article-memberships))))

; The keystone bridge: the numbers read out of a fresh index query are the
; numbers the fold would have computed.  FN-INDEX-RANGE-QUERY-CORRECT is the
; cited theorem; everything above only transports it through the projection's
; availability test.
(defthm fn-nntp-index-numbers-of-query-range
  (implies (and (fn-article-listp configured articles)
                (stringp group)
                (natp low)
                (natp high))
           (equal (fn-nntp-index-numbers
                   (fn-index-query-range (fn-index-build articles) group low high))
                  (fn-nntp-available-numbers group low high articles)))
  :hints (("Goal" :use ((:instance fn-index-range-query-correct)
                        (:instance fn-nntp-index-numbers-of-reference-range))
           :in-theory (disable fn-index-query-range fn-index-build
                               fn-nntp-index-numbers))))

; -----------------------------------------------------------------------------
; Each fold in books/nntp.lisp is the same fold over that number list.  These
; are stated with no hypothesis: they hold for every GROUP and every ARTICLES.

(defun fn-nntp-numbers-count (numbers)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp numbers)
      (+ 1 (fn-nntp-numbers-count (fn-ag-cdr numbers)))
    0))

(defun fn-nntp-numbers-min (numbers)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp numbers)
      (let ((number (fn-ag-car numbers))
            (rest (fn-nntp-numbers-min (fn-ag-cdr numbers))))
        (if (and (posp number)
                 (or (not (posp rest)) (< number rest)))
            number
          rest))
    0))

(defun fn-nntp-numbers-max (numbers)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp numbers)
      (let ((number (fn-ag-car numbers))
            (rest (fn-nntp-numbers-max (fn-ag-cdr numbers))))
        (if (and (posp number) (< rest number)) number rest))
    0))

(defthm fn-nntp-numbers-max-natp
  (natp (fn-nntp-numbers-max numbers))
  :rule-classes (:type-prescription :rewrite))

(defun fn-nntp-numbers-min-above (current numbers)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp numbers)
      (let ((number (fn-ag-car numbers))
            (rest (fn-nntp-numbers-min-above current (fn-ag-cdr numbers))))
        (if (and (posp number)
                 (fn-ag-less current number)
                 (or (not (posp rest)) (< number rest)))
            number
          rest))
    0))

(defun fn-nntp-numbers-max-below (current numbers)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp numbers)
      (let ((number (fn-ag-car numbers))
            (rest (fn-nntp-numbers-max-below current (fn-ag-cdr numbers))))
        (if (and (posp number)
                 (fn-ag-less number current)
                 (< rest number))
            number
          rest))
    0))

(defthm fn-nntp-numbers-max-below-natp
  (natp (fn-nntp-numbers-max-below current numbers))
  :rule-classes (:type-prescription :rewrite))

(defun fn-nntp-numbers-sort (numbers)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp numbers)
      (fn-nntp-insert-number (fn-ag-car numbers)
                             (fn-nntp-numbers-sort (fn-ag-cdr numbers)))
    nil))

; FN-NNTP-ARTICLE-NUMBER is positive only inside [1, *FN-NNTP-MAX-ARTICLE-NUMBER*]
; (FN-NNTP-ARTICLE-NUMBER-BOUNDED), so the whole-group folds are the
; [1, max] case of FN-NNTP-AVAILABLE-NUMBERS.
(defthm fn-nntp-group-count-is-index-shaped
  (equal (fn-nntp-group-count group articles)
         (fn-nntp-numbers-count
          (fn-nntp-available-numbers group 1 *fn-nntp-max-article-number* articles))))

(defthm fn-nntp-group-low-is-index-shaped
  (equal (fn-nntp-group-low group articles)
         (fn-nntp-numbers-min
          (fn-nntp-available-numbers group 1 *fn-nntp-max-article-number* articles))))

(defthm fn-nntp-group-high-is-index-shaped
  (equal (fn-nntp-group-high group articles)
         (fn-nntp-numbers-max
          (fn-nntp-available-numbers group 1 *fn-nntp-max-article-number* articles))))

(defthm fn-nntp-group-next-number-is-index-shaped
  (equal (fn-nntp-group-next-number group current articles)
         (fn-nntp-numbers-min-above
          current
          (fn-nntp-available-numbers group 1 *fn-nntp-max-article-number* articles))))

(defthm fn-nntp-group-last-number-is-index-shaped
  (equal (fn-nntp-group-last-number group current articles)
         (fn-nntp-numbers-max-below
          current
          (fn-nntp-available-numbers group 1 *fn-nntp-max-article-number* articles))))

(defthm fn-nntp-group-range-numbers-is-index-shaped
  (equal (fn-nntp-group-range-numbers group low high articles)
         (fn-nntp-numbers-sort
          (fn-nntp-available-numbers group low high articles))))

; -----------------------------------------------------------------------------
; The index-backed variants.  Each traverses only INDEX.

(defconst *fn-nntp-index-all-low* 1)
(defconst *fn-nntp-index-all-high* 2147483647)

(defun fn-nntp-index-group-numbers (index group)
  (declare (xargs :guard t :verify-guards nil))
  (fn-nntp-index-numbers
   (fn-index-query-range index group
                         *fn-nntp-index-all-low* *fn-nntp-index-all-high*)))

(defun fn-nntp-index-group-count (index group)
  (declare (xargs :guard t :verify-guards nil))
  (fn-nntp-numbers-count (fn-nntp-index-group-numbers index group)))

(defun fn-nntp-index-group-low (index group)
  (declare (xargs :guard t :verify-guards nil))
  (fn-nntp-numbers-min (fn-nntp-index-group-numbers index group)))

(defun fn-nntp-index-group-high (index group)
  (declare (xargs :guard t :verify-guards nil))
  (fn-nntp-numbers-max (fn-nntp-index-group-numbers index group)))

(defun fn-nntp-index-group-next-number (index group current)
  (declare (xargs :guard t :verify-guards nil))
  (fn-nntp-numbers-min-above current (fn-nntp-index-group-numbers index group)))

(defun fn-nntp-index-group-last-number (index group current)
  (declare (xargs :guard t :verify-guards nil))
  (fn-nntp-numbers-max-below current (fn-nntp-index-group-numbers index group)))

(defun fn-nntp-index-group-range-numbers (index group low high)
  (declare (xargs :guard t :verify-guards nil))
  (fn-nntp-numbers-sort
   (fn-nntp-index-numbers (fn-index-query-range index group low high))))

(defthm fn-nntp-index-group-numbers-of-build
  (implies (and (fn-article-listp configured articles)
                (stringp group))
           (equal (fn-nntp-index-group-numbers (fn-index-build articles) group)
                  (fn-nntp-available-numbers
                   group 1 *fn-nntp-max-article-number* articles)))
  :hints (("Goal" :use (:instance fn-nntp-index-numbers-of-query-range
                                  (low 1) (high *fn-nntp-max-article-number*))
           :in-theory (disable fn-nntp-index-numbers-of-query-range))))

; -----------------------------------------------------------------------------
; The equality theorems.  Subject on the left is the function the host calls;
; subject on the right is the fold books/nntp.lisp uses today.

(defthm fn-nntp-index-group-count-equals-fold
  (implies (and (fn-article-listp configured articles)
                (stringp group))
           (equal (fn-nntp-index-group-count (fn-index-build articles) group)
                  (fn-nntp-group-count group articles)))
  :hints (("Goal" :in-theory (disable fn-nntp-index-group-numbers
                                      fn-nntp-available-numbers))))

(defthm fn-nntp-index-group-low-equals-fold
  (implies (and (fn-article-listp configured articles)
                (stringp group))
           (equal (fn-nntp-index-group-low (fn-index-build articles) group)
                  (fn-nntp-group-low group articles)))
  :hints (("Goal" :in-theory (disable fn-nntp-index-group-numbers
                                      fn-nntp-available-numbers))))

(defthm fn-nntp-index-group-high-equals-fold
  (implies (and (fn-article-listp configured articles)
                (stringp group))
           (equal (fn-nntp-index-group-high (fn-index-build articles) group)
                  (fn-nntp-group-high group articles)))
  :hints (("Goal" :in-theory (disable fn-nntp-index-group-numbers
                                      fn-nntp-available-numbers))))

(defthm fn-nntp-index-group-next-number-equals-fold
  (implies (and (fn-article-listp configured articles)
                (stringp group))
           (equal (fn-nntp-index-group-next-number
                   (fn-index-build articles) group current)
                  (fn-nntp-group-next-number group current articles)))
  :hints (("Goal" :in-theory (disable fn-nntp-index-group-numbers
                                      fn-nntp-available-numbers))))

(defthm fn-nntp-index-group-last-number-equals-fold
  (implies (and (fn-article-listp configured articles)
                (stringp group))
           (equal (fn-nntp-index-group-last-number
                   (fn-index-build articles) group current)
                  (fn-nntp-group-last-number group current articles)))
  :hints (("Goal" :in-theory (disable fn-nntp-index-group-numbers
                                      fn-nntp-available-numbers))))

(defthm fn-nntp-index-group-range-numbers-equals-fold
  (implies (and (fn-article-listp configured articles)
                (stringp group)
                (natp low)
                (natp high))
           (equal (fn-nntp-index-group-range-numbers
                   (fn-index-build articles) group low high)
                  (fn-nntp-group-range-numbers group low high articles)))
  :hints (("Goal" :in-theory (disable fn-nntp-available-numbers))))

; -----------------------------------------------------------------------------
; The shape lemmas above are unconditional rewrites over FN-NNTP-GROUP-COUNT
; and its siblings.  They have done their work; leaving them enabled would
; rewrite every later goal about those folds into number-list form, so they
; are disabled for every book that includes this one.  The index accessors are
; restored to the theory books/index.lisp exports.

(in-theory (disable fn-nntp-group-count-is-index-shaped
                    fn-nntp-group-low-is-index-shaped
                    fn-nntp-group-high-is-index-shaped
                    fn-nntp-group-next-number-is-index-shaped
                    fn-nntp-group-last-number-is-index-shaped
                    fn-nntp-group-range-numbers-is-index-shaped
                    fn-nntp-article-idp-is-msgid-okp))
(in-theory (enable fn-index-entry fn-index-entry-group
                   fn-index-entry-number fn-index-entry-msgid))

; -----------------------------------------------------------------------------
; The generation-bound cache.
;
; The generation is the store's durable record count at the recovery the index
; was built from; the digest is computed here, from the archive, not by the
; host.  A query carries the generation and digest the caller observed; the
; cache answers only when both equal the ones it was built with.

(defun fn-nntp-index-config-digest (archive)
  (declare (xargs :guard t :verify-guards nil))
  (list (fn-state-groups archive)
        (fn-state-nexts archive)
        (len (fn-state-articles archive))))

(defun fn-nntp-index-cache (generation digest index)
  (declare (xargs :guard t :verify-guards nil))
  (list :fn-index-cache generation digest index))

(defun fn-nntp-index-cache-generation (cache)
  (declare (xargs :guard t :verify-guards nil))
  (fn-ag-car (fn-ag-cdr cache)))
(defun fn-nntp-index-cache-digest (cache)
  (declare (xargs :guard t :verify-guards nil))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr cache))))
(defun fn-nntp-index-cache-index (cache)
  (declare (xargs :guard t :verify-guards nil))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr cache)))))

(defun fn-nntp-index-cache-open (generation archive)
  (declare (xargs :guard t :verify-guards nil))
  (fn-nntp-index-cache generation
                       (fn-nntp-index-config-digest archive)
                       (fn-index-build (fn-state-articles archive))))

(defun fn-nntp-index-cache-freshp (cache generation digest)
  (declare (xargs :guard t :verify-guards nil))
  (and (equal (fn-ag-car cache) :fn-index-cache)
       (natp generation)
       (equal (fn-nntp-index-cache-generation cache) generation)
       (equal (fn-nntp-index-cache-digest cache) digest)))

; Three outcomes stay distinct: (:OK . answer) for a fresh cache, (:STALE) for
; a generation or configuration the cache was not built for, and (:UNKNOWN)
; for a query kind this cache does not answer.  A stale answer is not among
; them.
(defun fn-nntp-index-cache-query
  (cache generation digest kind group low high current)
  (declare (xargs :guard t :verify-guards nil))
  (if (fn-nntp-index-cache-freshp cache generation digest)
      (let ((index (fn-nntp-index-cache-index cache)))
        (cond ((equal kind :count)
               (cons :ok (fn-nntp-index-group-count index group)))
              ((equal kind :low)
               (cons :ok (fn-nntp-index-group-low index group)))
              ((equal kind :high)
               (cons :ok (fn-nntp-index-group-high index group)))
              ((equal kind :next)
               (cons :ok (fn-nntp-index-group-next-number index group current)))
              ((equal kind :last)
               (cons :ok (fn-nntp-index-group-last-number index group current)))
              ((equal kind :range)
               (cons :ok (fn-nntp-index-group-range-numbers
                          index group low high)))
              (t (list :unknown))))
    (list :stale)))

(defthm fn-nntp-index-cache-query-refuses-other-generation
  (implies (not (equal (fn-nntp-index-cache-generation cache) generation))
           (equal (fn-nntp-index-cache-query
                   cache generation digest kind group low high current)
                  (list :stale))))

(defthm fn-nntp-index-cache-query-refuses-other-configuration
  (implies (not (equal (fn-nntp-index-cache-digest cache) digest))
           (equal (fn-nntp-index-cache-query
                   cache generation digest kind group low high current)
                  (list :stale))))

(defthm fn-nntp-index-cache-open-is-fresh
  (implies (natp generation)
           (fn-nntp-index-cache-freshp
            (fn-nntp-index-cache-open generation archive)
            generation
            (fn-nntp-index-config-digest archive))))

; A cache opened at GENERATION over ARCHIVE answers each query kind with the
; value the corresponding books/nntp.lisp fold computes over that archive's
; committed articles.
(defthm fn-nntp-index-cache-open-answers-group
  (implies (and (fn-statep archive)
                (natp generation)
                (stringp group))
           (and (equal (fn-nntp-index-cache-query
                        (fn-nntp-index-cache-open generation archive)
                        generation (fn-nntp-index-config-digest archive)
                        :count group low high current)
                       (cons :ok (fn-nntp-group-count
                                  group (fn-state-articles archive))))
                (equal (fn-nntp-index-cache-query
                        (fn-nntp-index-cache-open generation archive)
                        generation (fn-nntp-index-config-digest archive)
                        :low group low high current)
                       (cons :ok (fn-nntp-group-low
                                  group (fn-state-articles archive))))
                (equal (fn-nntp-index-cache-query
                        (fn-nntp-index-cache-open generation archive)
                        generation (fn-nntp-index-config-digest archive)
                        :high group low high current)
                       (cons :ok (fn-nntp-group-high
                                  group (fn-state-articles archive))))))
  :hints (("Goal" :use ((:instance fn-nntp-index-group-count-equals-fold
                                   (configured (fn-state-groups archive))
                                   (articles (fn-state-articles archive)))
                        (:instance fn-nntp-index-group-low-equals-fold
                                   (configured (fn-state-groups archive))
                                   (articles (fn-state-articles archive)))
                        (:instance fn-nntp-index-group-high-equals-fold
                                   (configured (fn-state-groups archive))
                                   (articles (fn-state-articles archive))))
           :in-theory (disable fn-nntp-index-group-count
                               fn-nntp-index-group-low
                               fn-nntp-index-group-high
                               fn-nntp-index-group-count-equals-fold
                               fn-nntp-index-group-low-equals-fold
                               fn-nntp-index-group-high-equals-fold
                               fn-index-build))))

(defthm fn-nntp-index-cache-open-answers-cursor
  (implies (and (fn-statep archive)
                (natp generation)
                (stringp group))
           (and (equal (fn-nntp-index-cache-query
                        (fn-nntp-index-cache-open generation archive)
                        generation (fn-nntp-index-config-digest archive)
                        :next group low high current)
                       (cons :ok (fn-nntp-group-next-number
                                  group current (fn-state-articles archive))))
                (equal (fn-nntp-index-cache-query
                        (fn-nntp-index-cache-open generation archive)
                        generation (fn-nntp-index-config-digest archive)
                        :last group low high current)
                       (cons :ok (fn-nntp-group-last-number
                                  group current (fn-state-articles archive))))))
  :hints (("Goal" :use ((:instance fn-nntp-index-group-next-number-equals-fold
                                   (configured (fn-state-groups archive))
                                   (articles (fn-state-articles archive)))
                        (:instance fn-nntp-index-group-last-number-equals-fold
                                   (configured (fn-state-groups archive))
                                   (articles (fn-state-articles archive))))
           :in-theory (disable fn-nntp-index-group-next-number
                               fn-nntp-index-group-last-number
                               fn-nntp-index-group-next-number-equals-fold
                               fn-nntp-index-group-last-number-equals-fold
                               fn-index-build))))

(defthm fn-nntp-index-cache-open-answers-range
  (implies (and (fn-statep archive)
                (natp generation)
                (stringp group)
                (natp low)
                (natp high))
           (equal (fn-nntp-index-cache-query
                   (fn-nntp-index-cache-open generation archive)
                   generation (fn-nntp-index-config-digest archive)
                   :range group low high current)
                  (cons :ok (fn-nntp-group-range-numbers
                             group low high (fn-state-articles archive)))))
  :hints (("Goal" :use ((:instance fn-nntp-index-group-range-numbers-equals-fold
                                   (configured (fn-state-groups archive))
                                   (articles (fn-state-articles archive))))
           :in-theory (disable fn-nntp-index-group-range-numbers
                               fn-nntp-index-group-range-numbers-equals-fold
                               fn-index-build))))

; -----------------------------------------------------------------------------
; Guards.  Every function above is total on guard T, as in books/nntp.lisp.

(verify-guards fn-nntp-index-msgid-okp)
(verify-guards fn-nntp-index-entry-available)
(verify-guards fn-nntp-index-numbers)
(verify-guards fn-nntp-available-numbers)
(verify-guards fn-nntp-numbers-count)
(verify-guards fn-nntp-numbers-min)
(verify-guards fn-nntp-numbers-max)
(verify-guards fn-nntp-numbers-min-above)
(verify-guards fn-nntp-numbers-max-below)
(verify-guards fn-nntp-numbers-sort)
(verify-guards fn-nntp-index-group-numbers)
(verify-guards fn-nntp-index-group-count)
(verify-guards fn-nntp-index-group-low)
(verify-guards fn-nntp-index-group-high)
(verify-guards fn-nntp-index-group-next-number)
(verify-guards fn-nntp-index-group-last-number)
(verify-guards fn-nntp-index-group-range-numbers)
(verify-guards fn-nntp-index-config-digest)
(verify-guards fn-nntp-index-cache)
(verify-guards fn-nntp-index-cache-generation)
(verify-guards fn-nntp-index-cache-digest)
(verify-guards fn-nntp-index-cache-index)
(verify-guards fn-nntp-index-cache-open)
(verify-guards fn-nntp-index-cache-freshp)
(verify-guards fn-nntp-index-cache-query)
