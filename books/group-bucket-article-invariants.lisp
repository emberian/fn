; Proof-only relation between the pinned bucket/trie lookup and the accepted
; article selected by NNTP's historical local-number scan.
(in-package "ACL2")
(include-book "group-bucket-article")
(include-book "nntp-index")

(defthm fn-gidx-find-number-entry-of-memberships
  (implies (and (fn-membership-listp groups memberships)
                (fn-no-duplicatesp groups))
           (equal (fn-gidx-find-number-entry
                   group number
                   (fn-index-membership-entries msgid memberships))
                  (if (and (member-equal group groups)
                           (posp number)
                           (<= number *fn-nntp-max-article-number*)
                           (fn-nntp-index-msgid-okp msgid)
                           (equal number
                                  (fn-nntp-membership-number group memberships)))
                      (fn-index-entry group number msgid)
                    nil)))
  :hints (("Goal" :induct (fn-membership-listp groups memberships)
           :in-theory (enable fn-index-membership-entries
                              fn-nntp-index-entry-available
                              fn-nntp-membership-number
                              fn-membership-listp fn-no-duplicatesp))))

(defthm fn-gidx-find-number-entry-of-article
  (implies (fn-articlep configured article)
           (equal (fn-gidx-find-number-entry
                   group number (fn-index-article-entries article))
                  (if (and (posp number)
                           (equal number (fn-nntp-article-number group article)))
                      (fn-index-entry group number
                                      (fn-article-msgid article))
                    nil)))
  :hints (("Goal"
           :use ((:instance fn-gidx-find-number-entry-of-memberships
                            (groups (fn-article-groups article))
                            (memberships (fn-article-memberships article))
                            (msgid (fn-article-msgid article)))
                 (:instance fn-nntp-article-idp-is-msgid-okp))
           :in-theory (e/d (fn-articlep fn-selection-validp
                            fn-index-article-entries
                            fn-nntp-article-number)
                           (fn-gidx-find-number-entry-of-memberships)))))

(defthm fn-gidx-find-number-entry-of-build
  (implies (fn-article-listp configured articles)
           (equal (fn-gidx-find-number-entry
                   group number (fn-index-build articles))
                  (let ((article (fn-nntp-available-article
                                  group number articles)))
                    (if (consp article)
                        (fn-index-entry group number
                                        (fn-article-msgid article))
                      nil))))
  :hints (("Goal" :induct (fn-index-build articles)
           :in-theory (enable fn-index-build fn-article-listp
                              fn-nntp-available-article))
          ("Subgoal *1/1" :use ((:instance fn-gidx-find-number-entry-of-article
                                       (article (car articles)))))))

(defthm fn-nntp-available-article-is-member
  (implies (consp (fn-nntp-available-article group number articles))
           (member-equal (fn-nntp-available-article group number articles)
                         articles))
  :hints (("Goal" :induct (fn-nntp-available-article group number articles)
           :in-theory (enable fn-nntp-available-article))))

(defthm fn-article-msgid-of-member-is-in-msgids
  (implies (member-equal article articles)
           (member-equal (fn-article-msgid article)
                         (fn-article-msgids articles)))
  :hints (("Goal" :induct (member-equal article articles))))

(defthm fn-find-article-of-member-in-unique-list
  (implies (and (fn-article-listp configured articles)
                (member-equal article articles))
           (equal (fn-find-article (fn-article-msgid article) articles)
                  article))
  :hints (("Goal" :induct (fn-article-listp configured articles)
           :in-theory (enable fn-article-listp fn-find-article))))

(defthm fn-article-listp-gives-midx-string-articles
  (implies (fn-article-listp configured articles)
           (fn-midx-string-article-listp articles))
  :hints (("Goal" :induct (fn-article-listp configured articles)
           :in-theory (enable fn-article-listp fn-articlep
                              fn-midx-string-article-listp))))

(defthm fn-member-of-article-list-has-string-id
  (implies (and (fn-article-listp configured articles)
                (member-equal article articles))
           (stringp (fn-article-msgid article)))
  :hints (("Goal" :induct (fn-article-listp configured articles)
           :in-theory (enable fn-article-listp fn-articlep))))

(defthm fn-nntp-available-article-of-valid-list-is-cons-or-nil
  (implies (fn-article-listp configured articles)
           (or (consp (fn-nntp-available-article group number articles))
               (null (fn-nntp-available-article group number articles))))
  :hints (("Goal" :induct (fn-nntp-available-article group number articles)
           :in-theory (enable fn-nntp-available-article fn-article-listp
                              fn-articlep fn-article-shapep))))

(defthm fn-gidx-number-article-of-build
  (implies (fn-article-listp configured articles)
           (equal (fn-gidx-number-article
                   group number (fn-gidx-build articles)
                   (fn-midx-build articles))
                  (fn-nntp-available-article group number articles)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance fn-gidx-find-number-entry-of-build)
                 (:instance fn-gidx-find-number-entry-of-built-bucket)
                 (:instance fn-nntp-available-article-of-valid-list-is-cons-or-nil)
                 (:instance fn-nntp-available-article-is-member)
                 (:instance fn-find-article-of-member-in-unique-list
                            (article (fn-nntp-available-article
                                      group number articles)))
                 (:instance fn-midx-lookup-of-build-is-find-article
                            (msgid (fn-article-msgid
                                    (fn-nntp-available-article
                                     group number articles)))))
           :cases ((consp (fn-nntp-available-article group number articles)))
           :in-theory (e/d (fn-gidx-number-article)
                           (fn-midx-build fn-midx-lookup fn-midx-get-chars
                            fn-gidx-find-number-entry fn-gidx-build
                            fn-index-build fn-nntp-available-article)))))

(defthm fn-gidx-entry-number-article-of-built-bucket
  (implies (fn-article-listp configured articles)
           (equal (fn-gidx-entry-number-article
                   group number
                   (fn-gidx-bucket group (fn-gidx-build articles))
                   (fn-midx-build articles))
                  (fn-nntp-available-article group number articles)))
  :hints (("Goal" :use ((:instance fn-gidx-number-article-of-build))
           :in-theory (e/d (fn-gidx-number-article)
                           (fn-gidx-number-article-of-build)))))
