; Correspondence of grouped membership buckets to the original NNTP folds.
(in-package "ACL2")
(include-book "group-bucket-cursor-invariants")
(include-book "group-bucket-index")
(include-book "nntp-invariants")


(defthm fn-gidx-range-of-build-equals-archive-fold
  (implies (and (fn-article-listp configured articles)
                (stringp group) (natp low) (natp high))
           (equal (fn-gidx-range-numbers (fn-gidx-build articles)
                                          group low high)
                  (fn-nntp-group-range-numbers group low high articles)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-gidx-range-of-build-is-flat-index-range
                            (entries (fn-index-build articles)))
                 (:instance fn-nntp-index-group-range-numbers-equals-fold))
           :in-theory (disable fn-gidx-range-of-build-is-flat-index-range
                               fn-nntp-index-group-range-numbers-equals-fold))))


(defthm fn-gidx-group-summary-of-build
  (implies (and (fn-statep archive) (stringp group))
           (equal (fn-gidx-group-summary
                   archive (fn-gidx-build (fn-state-articles archive)) group)
                  (fn-nntp-group-summary archive group)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-index-build-listp
                            (configured (fn-state-groups archive))
                            (articles (fn-state-articles archive)))
                 (:instance fn-gidx-index-group-numbers-of-select
                            (entries (fn-index-build (fn-state-articles archive))))
                 (:instance fn-nntp-index-group-count-equals-fold
                            (configured (fn-state-groups archive))
                            (articles (fn-state-articles archive)))
                 (:instance fn-nntp-index-group-low-equals-fold
                            (configured (fn-state-groups archive))
                            (articles (fn-state-articles archive)))
                 (:instance fn-nntp-index-group-high-equals-fold
                            (configured (fn-state-groups archive))
                            (articles (fn-state-articles archive))))
           :in-theory
           (e/d (fn-statep fn-gidx-group-summary fn-nntp-group-summary
                  fn-gidx-build fn-nntp-index-group-count
                  fn-nntp-index-group-low fn-nntp-index-group-high)
                (fn-gidx-index-group-numbers-of-select
                 fn-nntp-index-group-count-equals-fold
                 fn-nntp-index-group-low-equals-fold
                 fn-nntp-index-group-high-equals-fold)))))

; The assembly lemma separates result formatting from the index relation.
; Its three hypotheses are exactly the three values the old result reads.
(defthm fn-gidx-listgroup-result-projection-unfolds
  (implies
   (and (equal (fn-gidx-group-summary archive buckets group)
               (fn-nntp-group-summary archive group))
        (equal (fn-nntp-index-group-low (fn-gidx-bucket group buckets) group)
               (fn-nntp-group-low group (fn-state-articles archive)))
        (equal (fn-gidx-range-numbers buckets group
                                      (fn-nntp-range-low range)
                                      (fn-nntp-range-high range))
               (fn-nntp-group-range-numbers
                group (fn-nntp-range-low range) (fn-nntp-range-high range)
                (fn-state-articles archive))))
   (equal (fn-gidx-listgroup-result session archive buckets group range)
          (fn-nntp-listgroup-result session archive group range)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory
           (e/d (fn-gidx-listgroup-result fn-nntp-listgroup-result
                  fn-gidx-group-initial fn-nntp-group-initial
                  fn-nntp-listgroup-initial)
                (fn-nntp-multi-octets fn-nntp-number-lines
                 fn-gidx-range-numbers)))))

(defthm fn-gidx-listgroup-result-of-build
  (implies (and (fn-statep archive) (stringp group)
                (natp (fn-nntp-range-low range))
                (natp (fn-nntp-range-high range)))
           (equal (fn-gidx-listgroup-result
                   session archive
                   (fn-gidx-build (fn-state-articles archive)) group range)
                  (fn-nntp-listgroup-result session archive group range)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-gidx-listgroup-result-projection-unfolds
                            (buckets (fn-gidx-build
                                      (fn-state-articles archive))))
                 (:instance fn-gidx-group-summary-of-build)
                 (:instance fn-gidx-group-low-of-build
                            (configured (fn-state-groups archive))
                            (articles (fn-state-articles archive)))
                 (:instance fn-gidx-range-of-build-equals-archive-fold
                            (configured (fn-state-groups archive))
                            (articles (fn-state-articles archive))
                            (low (fn-nntp-range-low range))
                            (high (fn-nntp-range-high range))))
           :in-theory
           (e/d (fn-statep)
                (fn-gidx-listgroup-result fn-nntp-listgroup-result
                 fn-gidx-group-low-of-build
                 fn-gidx-range-of-build-equals-archive-fold)))))

(defthm fn-gidx-range-parse-aux-natp
  (implies (fn-nntp-range-okp
            (fn-nntp-range-parse-aux token prefix))
           (and (natp (fn-nntp-range-low
                       (fn-nntp-range-parse-aux token prefix)))
                (natp (fn-nntp-range-high
                       (fn-nntp-range-parse-aux token prefix)))))
  :hints (("Goal" :induct (fn-nntp-range-parse-aux token prefix)
           :in-theory (enable fn-nntp-range-okp fn-nntp-range-low
                              fn-nntp-range-high fn-nntp-range-parse-aux))))

(defthm fn-gidx-parse-range-natp
  (implies (fn-nntp-range-okp (fn-nntp-parse-range token))
           (and (natp (fn-nntp-range-low (fn-nntp-parse-range token)))
                (natp (fn-nntp-range-high (fn-nntp-parse-range token)))))
  :hints (("Goal" :in-theory (enable fn-nntp-parse-range))))

(defthm fn-gidx-listgroup-command-of-build
  (implies (fn-nntp-projectionp archive)
           (equal (fn-gidx-listgroup-command
                   session archive
                   (fn-gidx-build (fn-state-articles archive)) args)
                  (fn-nntp-listgroup-command session archive args)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-gidx-listgroup-result-of-build
                            (group (fn-nntp-session-group session))
                            (range (list :ok 1 2147483647)))
                 (:instance fn-gidx-listgroup-result-of-build
                            (group (fn-nntp-token-string (car args)))
                            (range (list :ok 1 2147483647)))
                 (:instance fn-gidx-listgroup-result-of-build
                            (group (fn-nntp-token-string (car args)))
                            (range (fn-nntp-parse-range (cadr args))))
                 (:instance fn-gidx-parse-range-natp
                            (token (cadr args))))
           :in-theory
           (e/d (fn-gidx-listgroup-command fn-nntp-listgroup-command
                  fn-nntp-projectionp fn-nntp-token-string)
                (fn-gidx-listgroup-result fn-nntp-listgroup-result
                 fn-nntp-parse-range fn-nntp-printable-tokenp)))))
