; fn: LIST COUNTS (RFC 6048 section 2.2) and the numbered Message-ID answer
; (RFC 3977 section 6.2.1.2), stated at the pinned dispatcher the served
; path calls.
;
; The served reader reaches fn-nntp-archive-command-pinned (books/nntp.lisp)
; on every archive command; books/owner-list-counts-read.lisp carries the
; statements below up to fn-served-step, which fn-own-read runs
; (fn-own-read-is-served-step-on-pinned-prefix) and which the host reaches
; through fn-owner-chunk (host/owner-host.lisp).
;
; LIST COUNTS reads each group's pinned membership bucket, never the
; archive.  The keystones: the pinned reply is the archive fold's
; (fn-gidx-list-counts-command-is-the-archive-fold, under the bucket relation
; the owner carries for every connection), and the count field is exact: it
; is the length of the number list LISTGROUP answers for the group
; (fn-nntp-group-count-is-listgroup-length).  The work bound is
; fn-gidx-counts-work-bound.
;
; ARTICLE/HEAD/BODY/STAT <msgid> answer the article's number in the
; selected group, or 0 (fn-nntp-msgid-local-number, books/nntp-responses).
; Section 6.2.1.2 permits a number only when "use of that number in a second
; ARTICLE command immediately following this one would return the same
; article": fn-nntp-msgid-number-retrieves-the-same-article.
(in-package "ACL2")
(include-book "nntp")
(include-book "nntp-range-indexed-invariants")
(include-book "acceptance-invariants")

(local (in-theory (enable fn-nntp-responses-vocabulary
                          fn-nntp-projection-vocabulary
                          fn-nntp-session-vocabulary)))

; -----------------------------------------------------------------------------
; The count is the LISTGROUP length.

(local
 (defthm fn-nlc-len-of-insert-number
   (equal (len (fn-nntp-insert-number number numbers))
          (+ 1 (len numbers)))
   :hints (("Goal" :in-theory (enable fn-nntp-insert-number)))))

(defthm fn-nntp-group-count-is-listgroup-length
  (equal (fn-nntp-group-count group articles)
         (len (fn-nntp-group-range-numbers
               group 1 *fn-nntp-max-article-number* articles)))
  :hints (("Goal" :induct (fn-nntp-group-count group articles)
           :in-theory (enable fn-nntp-group-count fn-nntp-group-range-numbers
                              fn-ng-less-equal))))

; -----------------------------------------------------------------------------
; The pinned reply is the archive fold.

(local
 (defthm fn-nlc-safe-group-list-members-are-strings
   (implies (and (fn-nntp-safe-group-listp groups) (consp groups))
            (stringp (car groups)))
   :hints (("Goal" :in-theory (enable fn-nntp-safe-group-listp
                                      fn-nntp-safe-group-namep)))))

(defthm fn-gidx-counts-lines-of-build
  (implies (and (fn-statep archive)
                (fn-nntp-safe-group-listp groups))
           (equal (fn-gidx-counts-lines
                   archive (fn-gidx-build (fn-state-articles archive)) groups)
                  (fn-nntp-counts-lines archive groups)))
  :hints (("Goal" :induct (fn-nntp-counts-lines archive groups)
           :in-theory (e/d (fn-gidx-counts-lines fn-nntp-counts-lines
                            fn-gidx-counts-line fn-nntp-counts-line
                            fn-nntp-safe-group-listp)
                           (fn-gidx-build fn-statep fn-gidx-group-summary
                            fn-nntp-group-summary fn-nntp-counts-summary-line)))
          ("Subgoal *1/1" :use ((:instance fn-gidx-group-summary-of-build
                                 (group (car groups)))))))

(local
 (defthm fn-nlc-projection-safe-groups
   (implies (fn-nntp-projectionp archive)
            (and (fn-statep archive)
                 (fn-nntp-safe-group-listp (fn-state-groups archive))))
   :hints (("Goal" :in-theory (enable fn-nntp-projectionp)))))

(local
 (defthm fn-nlc-filter-keeps-safe
   (implies (fn-nntp-safe-group-listp groups)
            (fn-nntp-safe-group-listp
             (fn-nntp-filter-groups-by-wildmat patterns groups)))
   :hints (("Goal" :induct (fn-nntp-filter-groups-by-wildmat patterns groups)
            :in-theory (e/d (fn-nntp-filter-groups-by-wildmat
                             fn-nntp-safe-group-listp)
                            (fn-nntp-group-matches-parsed-wildmatp
                             fn-nntp-safe-group-namep))))))

(defthm fn-gidx-list-counts-command-is-the-archive-fold
  (implies (and (fn-nntp-projectionp archive)
                (equal buckets (fn-gidx-build (fn-state-articles archive))))
           (equal (fn-gidx-list-counts-command session archive buckets args)
                  (fn-nntp-list-counts-command session archive args)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-gidx-list-counts-command
                            fn-nntp-list-counts-command fn-nntp-list-counts)
                           (fn-gidx-build fn-statep fn-nntp-projectionp
                            fn-gidx-counts-lines fn-nntp-counts-lines
                            fn-nntp-filter-groups-by-wildmat
                            fn-wildmat-parse fn-nntp-multi fn-nntp-single)))))

; The dispatcher the served step calls.  With a pinned index it takes the
; bucket arm; without one, the archive arm through fn-nntp-list-command.
; Either way the reply is the archive fold's.
(defthm fn-nntp-archive-command-pinned-list-counts
  (implies (and (fn-nntp-projectionp archive)
                (fn-gidx-pin-correspondencep index archive)
                (fn-nntp-keywordp keyword "LIST")
                (consp args)
                (fn-nntp-keyword-tokenp (car args))
                (fn-nntp-keywordp (car args) "COUNTS"))
           (equal (fn-nntp-archive-command-pinned
                   session archive index verdicts env keyword args)
                  (fn-nntp-list-counts-command session archive (cdr args))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nntp-archive-command-pinned
                            fn-nntp-archive-command fn-nntp-list-command
                            fn-gidx-pin-correspondencep fn-nntp-keywordp)
                           (fn-nntp-upcase-keyword fn-nntp-keyword-tokenp
                            fn-gidx-list-counts-command
                            fn-nntp-list-counts-command
                            fn-nntp-list-active-times fn-nntp-list-response
                            fn-gidx-build fn-nntp-projectionp
                            fn-nntp-msgid-retrieval-indexed
                            fn-gidx-listgroup-command
                            fn-nntp-over-range-indexed
                            fn-nntp-verdict-hdr-response)))))

; -----------------------------------------------------------------------------
; Work: a group's line visits at most B bucket headers (B = the number of
; buckets) and its own bucket's E_g entries; fn-gidx-group-summary makes a
; constant number of passes over those entries.  Summed over G listed groups
; the reply visits at most G*B headers and the listed buckets' entries.

(defun fn-gidx-counts-work (buckets groups)
  (declare (xargs :guard t))
  (if (consp groups)
      (+ (fn-gidx-range-work buckets (car groups))
         (fn-gidx-counts-work buckets (cdr groups)))
    0))

(defun fn-gidx-listed-entries (buckets groups)
  (declare (xargs :guard t))
  (if (consp groups)
      (+ (len (fn-gidx-bucket (car groups) buckets))
         (fn-gidx-listed-entries buckets (cdr groups)))
    0))

(defthm fn-gidx-counts-work-bound
  (<= (fn-gidx-counts-work buckets groups)
      (+ (* (len groups) (len buckets))
         (fn-gidx-listed-entries buckets groups)))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-gidx-counts-work buckets groups)
           :in-theory (enable fn-gidx-range-work))))

; Over a built bucket set and distinct groups, the listed entries are at
; most the memberships of the archive, M = (len (fn-index-build articles)).
(defun fn-nlc-count-in (x xs)
  (if (consp xs)
      (+ (if (equal x (car xs)) 1 0) (fn-nlc-count-in x (cdr xs)))
    0))

(local
 (defthm fn-nlc-count-in-of-distinct
   (implies (no-duplicatesp-equal xs)
            (<= (fn-nlc-count-in x xs) 1))
   :rule-classes :linear))

(defun fn-nlc-selected-sum (groups entries)
  (if (consp groups)
      (+ (len (fn-gidx-select (car groups) entries))
         (fn-nlc-selected-sum (cdr groups) entries))
    0))

(local
 (defthm fn-nlc-selected-sum-of-cons
   (equal (fn-nlc-selected-sum groups (cons e entries))
          (+ (fn-nlc-selected-sum groups entries)
             (fn-nlc-count-in (fn-index-entry-group e) groups)))))

(local
 (defthm fn-nlc-selected-sum-at-most-entries
   (implies (no-duplicatesp-equal groups)
            (<= (fn-nlc-selected-sum groups entries) (len entries)))
   :rule-classes :linear
   :hints (("Goal" :induct (len entries)))))

(local
 (defthm fn-nlc-listed-entries-of-build
   (equal (fn-gidx-listed-entries (fn-gidx-build articles) groups)
          (fn-nlc-selected-sum groups (fn-index-build articles)))
   :hints (("Goal" :in-theory (disable fn-gidx-build)))))

(defthm fn-gidx-counts-work-of-build-bound
  (implies (no-duplicatesp-equal groups)
           (<= (fn-gidx-counts-work (fn-gidx-build articles) groups)
               (+ (* (len groups) (len (fn-gidx-build articles)))
                  (len (fn-index-build articles)))))
  :rule-classes :linear
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-gidx-counts-work-bound
                            (buckets (fn-gidx-build articles))))
           :in-theory (disable fn-gidx-build fn-gidx-counts-work-bound
                               fn-gidx-counts-work))))

; -----------------------------------------------------------------------------
; The Message-ID answer's number names the same article.

(local
 (defthm fn-nlc-membership-number-is-a-pair
   (implies (and (posp n)
                 (equal (fn-nntp-membership-number group ms) n))
            (fn-pair-memberp (cons group n) ms))
   :hints (("Goal" :in-theory (enable fn-nntp-membership-number
                                      fn-pair-memberp fn-pair-equalp)))))

(local
 (defthm fn-nlc-pair-memberp-of-append
   (equal (fn-pair-memberp p (append xs ys))
          (or (fn-pair-memberp p xs) (fn-pair-memberp p ys)))
   :hints (("Goal" :in-theory (enable fn-pair-memberp)))))

(local
 (defthm fn-nlc-pair-of-member-article
   (implies (and (member-equal a articles)
                 (fn-pair-memberp p (fn-article-memberships a)))
            (fn-pair-memberp p (fn-all-article-memberships articles)))
   :hints (("Goal" :in-theory (enable fn-all-article-memberships)))))

(local
 (defthm fn-nlc-pair-equalp-is-equal
   (implies (fn-pair-equalp p q) (equal q p))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-pair-equalp)))))

(local
 (defthm fn-nlc-pair-conflicts
   (implies (and (fn-pair-memberp p ms)
                 (fn-pair-memberp p (fn-all-article-memberships others)))
            (fn-memberships-conflictsp ms others))
   :hints (("Goal" :induct (fn-pair-memberp p ms)
            :in-theory (e/d (fn-pair-memberp fn-memberships-conflictsp)
                            (fn-all-article-memberships))))))

(local
 (defthm fn-nlc-shared-number-conflicts
   (implies (and (member-equal article others)
                 (posp n)
                 (equal (fn-nntp-membership-number group ms) n)
                 (equal (fn-nntp-membership-number
                         group (fn-article-memberships article))
                        n))
            (fn-memberships-conflictsp ms others))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-nlc-pair-conflicts (p (cons group n)))
                  (:instance fn-nlc-membership-number-is-a-pair)
                  (:instance fn-nlc-membership-number-is-a-pair
                             (ms (fn-article-memberships article)))
                  (:instance fn-nlc-pair-of-member-article
                             (a article) (articles others)
                             (p (cons group n))))
            :in-theory (disable fn-nlc-pair-conflicts
                                fn-nlc-membership-number-is-a-pair
                                fn-nlc-pair-of-member-article
                                fn-memberships-conflictsp
                                fn-all-article-memberships fn-pair-memberp
                                fn-nntp-membership-number)))))

(defthm fn-nntp-find-group-number-of-fresh-member
  (implies (and (fn-articles-freshp articles)
                (member-equal article articles)
                (posp n)
                (equal (fn-nntp-membership-number
                        group (fn-article-memberships article))
                       n))
           (equal (fn-nntp-find-group-number group n articles) article))
  :hints (("Goal" :induct (fn-articles-freshp articles)
           :in-theory (e/d (fn-articles-freshp fn-nntp-find-group-number)
                           (fn-all-article-memberships
                            fn-memberships-conflictsp
                            fn-nntp-membership-number)))
          ("Subgoal *1/1"
           :use ((:instance fn-nlc-shared-number-conflicts
                            (ms (fn-article-memberships (car articles)))
                            (others (cdr articles)))))))

(local
 (defthm fn-nlc-find-article-is-member
   (implies (consp (fn-find-article msgid articles))
            (member-equal (fn-find-article msgid articles) articles))
   :hints (("Goal" :in-theory (enable fn-find-article)))))

; RFC 3977 section 6.2.1.2: the number is 0 unless a group is selected and
; the article is available in it.  Both directions are the definition.
(defthm fn-nntp-msgid-local-number-by-definition
  (equal (fn-nntp-msgid-local-number session article)
         (if (fn-nntp-session-group session)
             (fn-nntp-article-number (fn-nntp-session-group session) article)
           0))
  :rule-classes nil)

; The keystone: a positive number answered for a Message-ID, sent back as
; any number token that reads as it, retrieves the same article, in the same
; group, as the section's "second ARTICLE command" requires.
(defthm fn-nntp-msgid-number-retrieves-the-same-article
  (let* ((article (fn-find-article (fn-nntp-token-string token)
                                   (fn-state-articles archive)))
         (n (fn-nntp-msgid-local-number session article)))
    (implies (and (fn-statep archive)
                  (posp n)
                  (fn-nntp-number-tokenp number-token)
                  (equal (fn-nntp-decimal-value number-token) n))
             (equal (fn-nntp-number-retrieval session archive kind number-token)
                    (fn-nntp-article-response
                     session article n kind t
                     (fn-nntp-session-group session)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-state-has-fresh-local-numbers (s archive))
                 (:instance fn-nntp-find-group-number-of-fresh-member
                            (articles (fn-state-articles archive))
                            (article (fn-find-article
                                      (fn-nntp-token-string token)
                                      (fn-state-articles archive)))
                            (group (fn-nntp-session-group session))
                            (n (fn-nntp-msgid-local-number
                                session
                                (fn-find-article
                                 (fn-nntp-token-string token)
                                 (fn-state-articles archive))))))
           :in-theory (e/d (fn-nntp-number-retrieval
                            fn-nntp-msgid-local-number
                            fn-nntp-article-number)
                           (fn-state-has-fresh-local-numbers
                            fn-nntp-find-group-number-of-fresh-member
                            fn-statep fn-articles-freshp
                            fn-nntp-article-response
                            fn-nntp-find-group-number
                            fn-nntp-membership-number
                            fn-find-article)))))
