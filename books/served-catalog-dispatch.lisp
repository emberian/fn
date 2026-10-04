; served-catalog-dispatch.lisp -- the lemmas the served dispatcher's forms
; are proved from (split from books/served-catalog.lisp, lane served-
; incremental-1, D26: that book was 9.99 s ACL2 time before the reader arms
; it now defines).  The served archive dispatcher itself is GENERATED from the
; protocol table's served columns (books/protocol-served.lisp
; fn-proto-archive-command-cat, called by books/served-catalog-chain.lisp
; fn-scr-command); its equation with the pinned reference dispatcher
; (books/nntp.lisp fn-nntp-archive-command-pinned) is that book's keystone
; fn-proto-archive-command-cat-is-pinned.  What is here are the facts a form's
; :by names (books/protocol-served-table.lisp): the pinned references that
; carry no cursor, the pinned by-number line, and the pinned bucket arms of
; LISTGROUP and LIST COUNTS as the archive folds.  The hand dispatcher
; fn-nntp-archive-command-cat and its keystone fn-nntp-archive-command-cat-is-
; pinned were deleted with the switch (DC02); the generated keystone replaces
; them.
(in-package "ACL2")
(include-book "served-catalog")
(include-book "newnews-stream-cursor")

;; The rules books/served-catalog.lisp's proofs run under (its header).
(local (in-theory (enable (:definition fn-nntp-article-idp)
                          (:definition fn-scat-msgid-idp)
                          (:rewrite fn-nntp-available-number-article-is-projectable)
                          (:rewrite fn-nntp-message-id-token-is-response-text)
                          (:rewrite fn-nntp-response-text-is-octets))))
(local (in-theory (disable fn-nntp-index-msgid-okp-stringp
                           fn-nntp-find-group-number-of-fresh-member)))
(local (in-theory (disable (tau-system))))

(defthm fn-scat-newnews-reference-keeps-session
   (equal (car (fn-nntp-newnews-response session archive env args fn-arena))
          session)
   :hints (("Goal" :in-theory (enable fn-nntp-newnews-response
                                      fn-nntp-single fn-nntp-multi
                                      fn-nntp-make-result))))

(defthm fn-scat-newnews-reference-has-no-cursor
   (equal (fn-ovw-expand
           (cdr (fn-nntp-newnews-response session archive env args fn-arena))
           fn-arena fn-cat)
          (cdr (fn-nntp-newnews-response session archive env args fn-arena)))
   :hints (("Goal" :in-theory (enable fn-ovw-expand fn-ovw-cursor-effectp fn-nnw-meta-effectp
                                      fn-nntp-newnews-response fn-nntp-single
                                      fn-nntp-multi fn-nntp-make-result
                                      fn-nntp-reply-effect))))

;; The pinned HDR/XHDR and XPAT readers carry no cursor (lane cold-line: the
;; -cat arms answer ranges with one, so the boundary theorem reads these
;; references through the expansion).
(defthm fn-scat-hdr-reference-has-no-cursor
  (and (consp (fn-nntp-hdr-command session archive args legacyp fn-arena))
       (equal (fn-ovw-expand (cdr (fn-nntp-hdr-command session archive args legacyp fn-arena))
                             fn-arena fn-cat)
              (cdr (fn-nntp-hdr-command session archive args legacyp fn-arena))))
  :hints (("Goal" :in-theory (e/d (fn-nntp-hdr-command fn-nntp-hdr-current fn-nntp-hdr-range
                                   fn-nntp-hdr-msgid)
                                  (fn-nntp-single fn-nntp-multi fn-nntp-hdr-lines-for-numbers
                                   fn-nntp-group-range-numbers fn-nntp-available-article
                                   fn-find-article fn-nntp-hdr-content fn-nntp-parse-range)))))

(defthm fn-scat-xpat-reference-has-no-cursor
  (and (consp (fn-nntp-xpat-response session archive args fn-arena))
       (equal (fn-ovw-expand (cdr (fn-nntp-xpat-response session archive args fn-arena))
                             fn-arena fn-cat)
              (cdr (fn-nntp-xpat-response session archive args fn-arena))))
  :hints (("Goal" :in-theory (e/d (fn-nntp-xpat-response fn-nntp-xpat-range fn-nntp-xpat-msgid)
                                  (fn-nntp-single fn-nntp-multi fn-nntp-xpat-lines-for-numbers
                                   fn-nntp-group-range-numbers fn-find-article fn-nntp-xpat-msgid-lines
                                   fn-nntp-parse-range fn-wildmat-parse-text)))))

;; The by-number line of the pinned dispatcher reaches fn-nntp-number-retrieval
;; through the fallthrough (fn-nntp-archive-command, fn-nntp-retrieval).
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
                                    fn-nntp-message-id-tokenp fn-nntp-upcase-keyword)))))

;; Group names: books/served-catalog.lisp's local lemmas, restated.
(local
 (defthm fn-scat-string-list-has-no-nil
   (implies (fn-string-listp groups) (not (member-equal nil groups)))
   :hints (("Goal" :in-theory (enable fn-string-listp)))))

(local
 (defthm fn-scat-member-of-string-list-is-string
   (implies (and (fn-string-listp groups) (member-equal g groups)) (stringp g))
   :hints (("Goal" :in-theory (enable fn-string-listp)))))

(local
 (defthm fn-scat-filter-keeps-strings
   (implies (fn-string-listp groups)
            (fn-string-listp (fn-nntp-filter-groups-by-wildmat patterns groups)))
   :hints (("Goal" :induct (fn-nntp-filter-groups-by-wildmat patterns groups)
            :in-theory (e/d (fn-nntp-filter-groups-by-wildmat fn-string-listp)
                            (fn-nntp-group-matches-parsed-wildmatp))))))

(local
 (defthm fn-scat-state-groups-are-strings
   (implies (fn-statep archive) (fn-string-listp (fn-state-groups archive)))
   :hints (("Goal" :in-theory (enable fn-statep)))))

;; The pinned bucket arms of LISTGROUP and LIST COUNTS are the archive folds
;; for every state (books/group-bucket-invariants.lisp and
;; books/nntp-list-counts.lisp state them under fn-nntp-projectionp, of which
;; their proofs read only fn-statep and string group names).
(defthm fn-scat-built-listgroup-is-fold
   (implies (fn-statep archive)
            (equal (fn-gidx-listgroup-command
                    session archive (fn-gidx-build (fn-state-articles archive)) args)
                   (fn-nntp-listgroup-command session archive args)))
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
                   fn-nntp-token-string)
                 (fn-gidx-listgroup-result fn-nntp-listgroup-result
                  fn-nntp-parse-range fn-nntp-printable-tokenp)))))

(local
 (defthm fn-scat-gidx-counts-lines-of-build
   (implies (and (fn-statep archive)
                 (fn-string-listp groups))
            (equal (fn-gidx-counts-lines
                    archive (fn-gidx-build (fn-state-articles archive)) groups closed)
                   (fn-nntp-counts-lines archive groups closed)))
   :hints (("Goal" :induct (fn-nntp-counts-lines archive groups closed)
            :in-theory (e/d (fn-gidx-counts-lines fn-nntp-counts-lines
                             fn-gidx-counts-line fn-nntp-counts-line fn-string-listp)
                            (fn-gidx-build fn-statep fn-gidx-group-summary
                             fn-nntp-group-summary fn-nntp-counts-summary-line)))
           ("Subgoal *1/1" :use ((:instance fn-gidx-group-summary-of-build
                                  (group (car groups))))))))

(defthm fn-scat-gidx-list-counts-is-fold
   (implies (and (fn-statep archive)
                 (equal buckets (fn-gidx-build (fn-state-articles archive))))
            (equal (fn-gidx-list-counts-command session archive buckets closed args)
                   (fn-nntp-list-counts-command session archive closed args)))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-gidx-list-counts-command
                             fn-nntp-list-counts-command fn-nntp-list-counts)
                            (fn-gidx-build fn-statep
                             fn-gidx-counts-lines fn-nntp-counts-lines
                             fn-nntp-filter-groups-by-wildmat
                             fn-wildmat-parse fn-nntp-multi fn-nntp-single)))))

