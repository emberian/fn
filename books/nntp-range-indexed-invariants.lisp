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
           :in-theory (enable fn-nov-lines-for-numbers-indexed
                              fn-nov-lines-for-numbers))))

(defthm fn-nntp-over-range-indexed-equals-fold
  (implies (and (fn-statep archive)
                (fn-nntp-sessionp session)
                (fn-nntp-range-okp (fn-nntp-parse-range token))
                (natp (fn-nntp-range-low (fn-nntp-parse-range token)))
                (natp (fn-nntp-range-high (fn-nntp-parse-range token))))
           (equal (fn-nntp-over-range-indexed
                   session (fn-gidx-build (fn-state-articles archive))
                   (fn-midx-build (fn-state-articles archive))
                   token legacyp)
                  (if legacyp
                      (fn-nntp-xover-range session archive token)
                    (fn-nntp-over-range session archive token))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-gidx-range-of-build-equals-archive-fold
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
                                      (fn-state-articles archive)))))
           :in-theory (e/d (fn-nntp-over-range-indexed
                            fn-nntp-over-range fn-nntp-xover-range
                            fn-statep fn-nntp-sessionp
                            fn-gidx-range-numbers)
                           (fn-gidx-build fn-gidx-build-entries
                            fn-nov-lines-for-numbers-indexed
                            fn-nov-lines-for-numbers
                            fn-nntp-group-range-numbers)))))

(defthm fn-nntp-pinned-over-range-equals-archive-command
  (implies (and (fn-statep archive)
                (fn-nntp-sessionp session)
                (fn-nntp-range-okp (fn-nntp-parse-range token))
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
                            (legacyp (fn-nntp-keywordp keyword "XOVER")))
                 (:instance fn-nntp-parse-range-ok-has-natural-bounds))
           :in-theory (e/d (fn-nntp-archive-command-pinned
                            fn-nntp-archive-command fn-nntp-over-response
                            fn-nntp-xover-response fn-nntp-keywordp)
                           (fn-nntp-over-range-indexed
                            fn-nntp-over-range fn-nntp-xover-range
                            fn-nntp-parse-range fn-nntp-upcase-keyword)))))

(defthm fn-nntp-carried-over-range-equals-archive-command
  (implies (and (fn-statep archive)
                (fn-nntp-sessionp session)
                (fn-gidx-pinp index)
                (fn-gidx-pin-correspondencep index archive)
                (fn-midx-correspondencep
                 (fn-gidx-pin-trie index)
                 (fn-state-articles archive))
                (fn-nntp-range-okp (fn-nntp-parse-range token))
                (or (fn-nntp-keywordp keyword "OVER")
                    (fn-nntp-keywordp keyword "XOVER")))
           (equal (fn-nntp-archive-command-pinned
                   session archive index verdicts env keyword (list token))
                  (fn-nntp-archive-command
                   session archive env keyword (list token))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-nntp-over-range-indexed-equals-fold
                            (legacyp (fn-nntp-keywordp keyword "XOVER")))
                 (:instance fn-nntp-parse-range-ok-has-natural-bounds))
           :in-theory (e/d (fn-gidx-pin-correspondencep
                            fn-midx-correspondencep
                            fn-nntp-archive-command-pinned
                            fn-nntp-archive-command
                            fn-nntp-over-response fn-nntp-xover-response
                            fn-nntp-keywordp)
                           (fn-nntp-over-range-indexed
                            fn-nntp-over-range fn-nntp-xover-range
                            fn-nntp-upcase-keyword fn-nntp-parse-range)))))
