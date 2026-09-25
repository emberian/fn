; The pinned OVER/XOVER range renderer equals the historical archive fold.
; Bucket/trie correspondence is established at connection open and preserved
; by the served transition; it is not checked during a reader command.
(in-package "ACL2")
(include-book "nntp-range-indexed")
(include-book "group-bucket-article-invariants")
(include-book "group-bucket-invariants")

(defthm fn-nntp-range-parse-aux-ok-has-natural-bounds
  (implies (fn-nntp-range-okp (fn-nntp-range-parse-aux token prefix-rev))
           (and (natp (fn-nntp-range-low
                       (fn-nntp-range-parse-aux token prefix-rev)))
                (natp (fn-nntp-range-high
                       (fn-nntp-range-parse-aux token prefix-rev)))))
  :hints (("Goal" :induct (fn-nntp-range-parse-aux token prefix-rev)
           :in-theory (enable fn-nntp-range-parse-aux
                              fn-nntp-range-okp fn-nntp-range-low
                              fn-nntp-range-high))))

(defthm fn-nntp-parse-range-ok-has-natural-bounds
  (implies (fn-nntp-range-okp (fn-nntp-parse-range token))
           (and (natp (fn-nntp-range-low (fn-nntp-parse-range token)))
                (natp (fn-nntp-range-high (fn-nntp-parse-range token)))))
  :hints (("Goal" :in-theory (e/d (fn-nntp-parse-range)
                                  (fn-nntp-range-parse-aux)))))

(defthm fn-nov-indexed-lines-equal-archive-lines
  (implies (fn-article-listp configured articles)
           (equal (fn-nov-lines-for-numbers-indexed
                   group numbers
                   (fn-gidx-bucket group (fn-gidx-build articles))
                   (fn-midx-build articles))
                  (fn-nov-lines-for-numbers group numbers articles)))
  :hints (("Goal" :induct (fn-nov-lines-for-numbers group numbers articles)
           :in-theory (e/d (fn-nov-lines-for-numbers-indexed
                            fn-nov-lines-for-numbers)
                           (fn-gidx-entry-number-article fn-nntp-available-article
                            fn-midx-build fn-gidx-build fn-gidx-bucket-of-build
                            fn-rcl-tombstonep)))))

; A malformed session can carry a non-text selected group.  Valid archived
; memberships all name text groups, so both projections select no numbers.
; This removes the session recognizer from the range correspondence theorem;
; the served call still supplies a well-formed session by construction.
(defthm fn-xri-membership-number-nonstring
  (implies (and (fn-string-listp groups)
                (fn-membership-listp groups memberships)
                (not (stringp group)))
           (equal (fn-nntp-membership-number group memberships) 0))
  :hints (("Goal" :induct (fn-membership-listp groups memberships)
           :in-theory (enable fn-string-listp fn-membership-listp
                              fn-nntp-membership-number))))

(defthm fn-xri-article-number-nonstring
  (implies (and (fn-articlep configured article)
                (not (stringp group)))
           (equal (fn-nntp-article-number group article) 0))
  :hints (("Goal" :use ((:instance fn-xri-membership-number-nonstring
                            (groups (fn-article-groups article))
                            (memberships (fn-article-memberships article))))
           :in-theory (e/d (fn-articlep fn-nntp-article-number)
                           (fn-xri-membership-number-nonstring)))))

(defthm fn-xri-archive-range-nonstring
  (implies (and (fn-article-listp configured articles)
                (not (stringp group)))
           (equal (fn-nntp-group-range-numbers group low high articles) nil))
  :hints (("Goal" :induct (fn-article-listp configured articles)
           :in-theory (enable fn-article-listp
                              fn-nntp-group-range-numbers))))

(defthm fn-xri-over-range-nonstring
  (implies (and (fn-statep archive)
                (not (stringp (fn-nntp-session-group session))))
           (equal (fn-nntp-over-range-indexed
                   session (fn-gidx-build (fn-state-articles archive))
                   (fn-midx-build (fn-state-articles archive))
                   token legacyp)
                  (if legacyp
                      (fn-nntp-xover-range session archive token)
                    (fn-nntp-over-range session archive token))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-xri-archive-range-nonstring
                            (configured (fn-state-groups archive))
                            (articles (fn-state-articles archive))
                            (group (fn-nntp-session-group session))
                            (low (fn-nntp-range-low (fn-nntp-parse-range token)))
                            (high (fn-nntp-range-high (fn-nntp-parse-range token)))))
           :in-theory (e/d (fn-nntp-over-range-indexed
                            fn-nntp-over-range fn-nntp-xover-range
                            fn-statep fn-gidx-range-numbers
                            fn-index-query-range
                            fn-nov-lines-for-numbers-indexed
                            fn-nov-lines-for-numbers)
                           (fn-gidx-build fn-gidx-build-entries
                            fn-nntp-group-range-numbers)))))

(defthm fn-nntp-over-range-indexed-equals-fold
  (implies (and (fn-statep archive)
                (fn-nntp-range-okp (fn-nntp-parse-range token)))
           (equal (fn-nntp-over-range-indexed
                   session (fn-gidx-build (fn-state-articles archive))
                   (fn-midx-build (fn-state-articles archive))
                   token legacyp)
                  (if legacyp
                      (fn-nntp-xover-range session archive token)
                    (fn-nntp-over-range session archive token))))
  :hints (("Goal" :do-not-induct t
           :cases ((stringp (fn-nntp-session-group session)))
           :use ((:instance fn-nntp-parse-range-ok-has-natural-bounds)
                 (:instance fn-xri-over-range-nonstring)
                 (:instance fn-gidx-range-of-build-equals-archive-fold
                            (configured (fn-state-groups archive))
                            (articles (fn-state-articles archive))
                            (group (fn-nntp-session-group session))
                            (low (fn-nntp-range-low (fn-nntp-parse-range token)))
                            (high (fn-nntp-range-high (fn-nntp-parse-range token))))
                 (:instance fn-nov-indexed-lines-equal-archive-lines
                            (configured (fn-state-groups archive))
                            (articles (fn-state-articles archive))
                            (group (fn-nntp-session-group session))
                            (numbers (fn-nntp-group-range-numbers
                                      (fn-nntp-session-group session)
                                      (fn-nntp-range-low (fn-nntp-parse-range token))
                                      (fn-nntp-range-high (fn-nntp-parse-range token))
                                      (fn-state-articles archive))))
                 (:instance fn-nntp-group-range-numbers-is-index-shaped
                            (group (fn-nntp-session-group session))
                            (low (fn-nntp-range-low (fn-nntp-parse-range token)))
                            (high (fn-nntp-range-high (fn-nntp-parse-range token)))
                            (articles (fn-state-articles archive))))
           :in-theory (e/d (fn-nntp-over-range-indexed
                            fn-nntp-over-range fn-nntp-xover-range
                            fn-statep fn-nntp-sessionp
                            fn-gidx-range-numbers)
                           (fn-gidx-build fn-gidx-build-entries
                            fn-nov-lines-for-numbers-indexed
                            fn-nov-lines-for-numbers
                            fn-nntp-group-range-numbers
                            fn-nntp-group-range-numbers-is-index-shaped)))))

(defthm fn-nntp-pinned-over-range-equals-archive-command
  (implies (and (fn-statep archive)
                (or (fn-nntp-keywordp keyword "OVER")
                    (fn-nntp-keywordp keyword "XOVER")))
           (equal
            (fn-nntp-archive-command-pinned
             session archive
             (fn-gidx-pin (fn-midx-build (fn-state-articles archive))
                          (fn-gidx-build (fn-state-articles archive)))
             verdicts env keyword (list token))
            (fn-nntp-archive-command
             session archive env keyword (list token))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-nntp-over-range-indexed-equals-fold
                            (legacyp (fn-nntp-keywordp keyword "XOVER"))))
           :in-theory (e/d (fn-nntp-archive-command-pinned
                            fn-nntp-archive-command fn-nntp-over-response
                            fn-nntp-xover-response fn-nntp-keywordp)
                           (fn-nntp-over-range-indexed
                            fn-nntp-over-range fn-nntp-xover-range
                            fn-nntp-parse-range fn-nntp-upcase-keyword)))))

(defthm fn-nntp-carried-over-range-equals-archive-command
  (implies (and (fn-statep archive)
                (fn-gidx-pin-correspondencep index archive)
                (fn-midx-correspondencep
                 (fn-gidx-pin-trie index)
                 (fn-state-articles archive))
                (or (fn-nntp-keywordp keyword "OVER")
                    (fn-nntp-keywordp keyword "XOVER")))
           (equal (fn-nntp-archive-command-pinned
                   session archive index verdicts env keyword (list token))
                  (fn-nntp-archive-command
                   session archive env keyword (list token))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-nntp-over-range-indexed-equals-fold
                            (legacyp (fn-nntp-keywordp keyword "XOVER"))))
           :in-theory (e/d (fn-gidx-pin-correspondencep
                            fn-midx-correspondencep
                            fn-nntp-archive-command-pinned
                            fn-nntp-archive-command
                            fn-nntp-over-response fn-nntp-xover-response
                            fn-nntp-keywordp)
                           (fn-nntp-over-range-indexed
                            fn-nntp-over-range fn-nntp-xover-range
                            fn-nntp-upcase-keyword fn-nntp-parse-range)))))
