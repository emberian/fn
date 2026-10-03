; served-catalog-dispatch.lisp -- the served archive dispatcher over the
; catalog (fn-nntp-archive-command-cat) and its boundary theorem
; fn-nntp-archive-command-cat-is-pinned, split from books/served-catalog.lisp
; (lane served-incremental-1, D26: that book was 9.99 s ACL2 time before the
; reader arms it now defines).  The arms are books/served-catalog.lisp's;
; this book is the case split over them and its equation with the pinned
; reference dispatcher (books/nntp.lisp fn-nntp-archive-command-pinned).
; The host reaches it through books/served-catalog-chain.lisp fn-scr-command.
(in-package "ACL2")
(include-book "served-catalog")
(include-book "newnews-metadata-cursor")

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

(local
 (defthm fn-scat-over-reference-one-reply
   (equal (list (fn-nntp-reply-effect
                 (fn-served-reply-octets
                  (cdr (fn-nntp-over-range session archive token fn-arena)))))
          (cdr (fn-nntp-over-range session archive token fn-arena)))
   :hints (("Goal" :in-theory (e/d (fn-nntp-over-range fn-nntp-single
                                      fn-nntp-multi fn-nntp-make-result
                                      fn-nntp-reply-effect fn-served-reply-octets)
                                     (fn-nntp-parse-range fn-nntp-group-range-numbers
                                      fn-nov-lines-for-numbers))))))

(local
 (defthm fn-scat-xover-reference-one-reply
   (equal (list (fn-nntp-reply-effect
                 (fn-served-reply-octets
                  (cdr (fn-nntp-xover-range session archive token fn-arena)))))
          (cdr (fn-nntp-xover-range session archive token fn-arena)))
   :hints (("Goal" :in-theory (e/d (fn-nntp-xover-range fn-nntp-single
                                      fn-nntp-multi fn-nntp-make-result
                                      fn-nntp-reply-effect fn-served-reply-octets)
                                     (fn-nntp-parse-range fn-nntp-group-range-numbers
                                      fn-nov-lines-for-numbers))))))

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

(defun fn-nntp-archive-command-cat
    (session archive index verdicts env keyword args v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (natp v)
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))
                  :verify-guards nil))
  (let ((xref (fn-nntp-xref-reply-cat session archive index env keyword args v fn-arena fn-cat)))
    (if xref xref
      (cond
       ((and (fn-nntp-keywordp keyword "LIST")
             (fn-gidx-pinp index)
             (consp args)
             (fn-nntp-keyword-tokenp (car args))
             (fn-nntp-keywordp (car args) "COUNTS"))
        (fn-nntp-list-counts-command-cat session archive (fn-nntp-env-closed env)
                                         (cdr args) v fn-cat))
       ((and (or (fn-nntp-keywordp keyword "ARTICLE")
                 (fn-nntp-keywordp keyword "HEAD")
                 (fn-nntp-keywordp keyword "BODY")
                 (fn-nntp-keywordp keyword "STAT"))
             (consp args) (null (cdr args))
             (fn-nntp-number-withdrawn-p-cat session index (car args) v fn-arena fn-cat))
        (fn-nntp-withdrawn-reply session nil))
       ((and (or (fn-nntp-keywordp keyword "ARTICLE")
                 (fn-nntp-keywordp keyword "HEAD")
                 (fn-nntp-keywordp keyword "BODY")
                 (fn-nntp-keywordp keyword "STAT"))
             (consp args) (null (cdr args))
             (fn-nntp-message-id-tokenp (car args))
             (fn-nntp-msgid-withdrawn-p-cat index (car args) v fn-arena fn-cat))
        (fn-nntp-withdrawn-reply session t))
       ;; PRF-243: the served compatibility arms, where the pinned dispatcher
       ;; has them (books/nntp.lisp fn-nntp-archive-command-pinned); ARTICLE
       ;; and HEAD find the article in the catalog (fn-rcompat-reply-cat).
       ;; A one-element clause answers with its test's value: the reply is
       ;; computed once.
       ((fn-rcompat-reply-cat session archive index env keyword args v fn-arena fn-cat))
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
        (fn-nntp-over-range-ovw session v (car args) (fn-nntp-keywordp keyword "XOVER")
                                nil fn-cat))
       ((and (fn-nntp-keywordp keyword "HDR")
             (consp args)
             (fn-nntp-keywordp (car args) ":FN-VERIFIED"))
        (fn-nntp-verdict-hdr-response-cat session verdicts args v fn-arena fn-cat))
       ((and (fn-nntp-keywordp keyword "HDR")
             (consp args)
             (fn-nntp-keywordp (car args) ":FN-CONTROL"))
        (fn-nntp-control-hdr-response-cat session archive index verdicts args v fn-arena fn-cat))
       ((and (fn-nntp-keywordp keyword "HDR")
             (consp args)
             (fn-nntp-keywordp (car args) ":FN-ENROLLMENT"))
        (fn-nntp-enrollment-hdr-response-cat session index verdicts args v fn-arena fn-cat))
       ((fn-nntp-keywordp keyword "GROUP")
        (if (and (consp args) (null (cdr args)) (fn-nntp-printable-tokenp (car args)))
            (fn-nntp-group-result-cat session archive (fn-nntp-token-string (car args)) v fn-cat)
          (fn-nntp-single session (fn-proto-text * :syntax))))
       ((fn-nntp-keywordp keyword "HDR")
        (fn-nntp-hdr-command-cat session args v nil fn-arena fn-cat))
       ((fn-nntp-keywordp keyword "XHDR")
        (fn-nntp-hdr-command-cat session args v t fn-arena fn-cat))
       ((fn-nntp-keywordp keyword "XPAT")
        (fn-nntp-xpat-response-cat session args v fn-arena fn-cat))
       ;; served-incremental-1: the arms the list model answered by walking
       ;; the view's articles, from the catalog (each -cat function's
       ;; theorem above equates it with the list model's answer).
       ((and (fn-nntp-keywordp keyword "LIST")
             (fn-scat-list-active-formp args))
        (fn-nntp-list-active-cat session archive (fn-nntp-env-closed env) args v fn-cat))
       ((and (fn-nntp-keywordp keyword "NEXT") (null args))
        (fn-nntp-next-or-last-cat session archive :next v fn-arena fn-cat))
       ((and (fn-nntp-keywordp keyword "LAST") (null args))
        (fn-nntp-next-or-last-cat session archive :last v fn-arena fn-cat))
       ((and (or (fn-nntp-keywordp keyword "ARTICLE")
                 (fn-nntp-keywordp keyword "HEAD")
                 (fn-nntp-keywordp keyword "BODY")
                 (fn-nntp-keywordp keyword "STAT"))
             (null args))
        (fn-nntp-current-retrieval-cat
         session
         (cond ((fn-nntp-keywordp keyword "ARTICLE") :article)
               ((fn-nntp-keywordp keyword "HEAD") :head)
               ((fn-nntp-keywordp keyword "BODY") :body)
               (t :stat))
         v fn-arena fn-cat))
       ;; cg-newnews-hang: the scan reads the tombstone column, no payload.
       ((fn-nntp-keywordp keyword "NEWNEWS")
        (fn-nntp-newnews-response-cursor session archive env args fn-arena fn-cat))
       (t (fn-nntp-archive-command session archive env keyword args fn-arena))))))

;;; KEYSTONE (the boundary theorem of this increment): under archive = the
;;; view's articles, trie = its Message-ID index and a fresh number column,
;;; the -cat dispatcher IS the pinned dispatcher.

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

(local
 (defthm fn-scat-statep-article-listp
   (implies (fn-statep archive)
            (fn-article-listp (fn-state-groups archive) (fn-state-articles archive)))
   :hints (("Goal" :in-theory (enable fn-statep)))))

; The dispatcher agrees with the pinned reference modulo the OVER cursor:
; the results' sessions are equal and their effects are equal once both are
; expanded (fn-ovw-expand; the OVER/XOVER range arms are the one place the two
; differ: with no Xref server name by fn-nntp-over-range-ovw-expands-to-over-
; range-cat, with one inside fn-nntp-xref-reply-cat, by fn-nntp-xref-reply-
; cat-is-col).  Proved once
; as the equality of the expanded results, then read component by component.
(defun fn-ovw-expand-result (result fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (cons (car result) (fn-ovw-expand (cdr result) fn-arena fn-cat)))

(local
 (defthm fn-nntp-archive-command-cat-is-pinned-expanded
  (implies (and (equal (fn-state-articles archive)
                       (fn-cat-view-articles v fn-arena fn-cat))
                (fn-statep archive)
                (fn-gidx-pin-correspondencep index archive)
                (fn-midx-correspondencep (fn-gidx-pin-trie index)
                                         (fn-state-articles archive))
                (fn-cnx-freshp fn-cat)
                (fn-scol-okp fn-arena fn-cat))
           (equal (fn-ovw-expand-result
                   (fn-nntp-archive-command-cat
                    session archive index verdicts env keyword args v fn-arena fn-cat)
                   fn-arena fn-cat)
                  (fn-ovw-expand-result
                   (fn-nntp-archive-command-pinned
                    session archive index verdicts env keyword args fn-arena)
                   fn-arena fn-cat)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nntp-archive-command-cat fn-nntp-archive-command-pinned
                            fn-ovw-expand-result fn-nntp-over-range-ovw-expands-to-over-range-cat
                            fn-nntp-newnews-response-cursor-expands-to-cat
                            fn-nntp-newnews-response-cursor-keeps-session
                            fn-nntp-archive-command fn-nntp-list-command
                            fn-nntp-hdr-response fn-nntp-xhdr-response
                            fn-nntp-over-response fn-nntp-xover-response
                            fn-nntp-retrieval)
                           (fn-rcompat-reply fn-nntp-xref-reply fn-gidx-list-counts-command
                            fn-rcompat-reply-cat fn-nntp-number-withdrawn-p-cat
                            fn-nntp-number-withdrawn-p fn-nntp-msgid-withdrawn-p
                            fn-nntp-withdrawn-reply fn-gidx-listgroup-command
                            fn-nntp-over-range-indexed fn-nntp-verdict-hdr-response
                            fn-nntp-verdict-hdr-response-cat
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
                            fn-gidx-pin-correspondencep
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
                            fn-nntp-over-range-indexed-is-walk
                            fn-nntp-xref-reply-cat fn-nntp-msgid-withdrawn-p-cat
                            fn-nntp-msgid-withdrawn-p-cat-is-trie
                            fn-nntp-control-hdr-response-cat fn-nntp-enrollment-hdr-response-cat
                            fn-nntp-over-range-ovw fn-ovw-expand fn-ovw-start fn-ovw-cursor-effect
                            fn-nntp-multi fn-nntp-multi-octets fn-nntp-reply-effect
                            fn-nntp-make-result
                            fn-nntp-list-active-cat fn-nntp-next-or-last-cat
                            fn-nntp-current-retrieval-cat fn-nntp-next-or-last
                            fn-scat-list-active-formp))
           :use ((:instance fn-nntp-xref-reply-cat-is-col (configured (fn-state-groups archive)))
                 (:instance fn-nntp-list-active-cat-is-list-command)
                 (:instance fn-nntp-next-or-last-cat-is-next-or-last (direction :next))
                 (:instance fn-nntp-next-or-last-cat-is-next-or-last (direction :last))
                 (:instance fn-nntp-current-retrieval-cat-is-current-retrieval (kind :article))
                 (:instance fn-nntp-current-retrieval-cat-is-current-retrieval (kind :head))
                 (:instance fn-nntp-current-retrieval-cat-is-current-retrieval (kind :body))
                 (:instance fn-nntp-current-retrieval-cat-is-current-retrieval (kind :stat))
                 (:instance fn-nntp-msgid-withdrawn-p-cat-is-trie (token (car args)))
                 (:instance fn-nntp-control-hdr-response-cat-is-pinned)
                 (:instance fn-nntp-enrollment-hdr-response-cat-is-pinned)
                 (:instance fn-scat-statep-article-listp)
                 (:instance fn-scat-pin-trie-is-built)
                 (:instance fn-scat-pin-buckets-are-built))))))

(defthm fn-nntp-archive-command-cat-is-pinned
  (implies (and (equal (fn-state-articles archive)
                       (fn-cat-view-articles v fn-arena fn-cat))
                (fn-statep archive)
                (fn-gidx-pin-correspondencep index archive)
                (fn-midx-correspondencep (fn-gidx-pin-trie index)
                                         (fn-state-articles archive))
                (fn-cnx-freshp fn-cat)
                (fn-scol-okp fn-arena fn-cat))
           (and (equal (fn-nntp-result-session
                        (fn-nntp-archive-command-cat
                         session archive index verdicts env keyword args v fn-arena fn-cat))
                       (fn-nntp-result-session
                        (fn-nntp-archive-command-pinned
                         session archive index verdicts env keyword args fn-arena)))
                (equal (fn-ovw-expand
                        (fn-nntp-result-effects
                         (fn-nntp-archive-command-cat
                          session archive index verdicts env keyword args v fn-arena fn-cat))
                        fn-arena fn-cat)
                       (fn-ovw-expand
                        (fn-nntp-result-effects
                         (fn-nntp-archive-command-pinned
                          session archive index verdicts env keyword args fn-arena))
                        fn-arena fn-cat))))
  :hints (("Goal" :use ((:instance fn-nntp-archive-command-cat-is-pinned-expanded))
           :in-theory (union-theories '(fn-ovw-expand-result fn-nntp-result-session
                                        fn-nntp-result-effects cons-equal)
                                      (theory 'minimal-theory)))))

(in-theory (disable fn-ovw-expand-result))

; Guards: every arm is guard-verified in books/served-catalog.lisp.
(verify-guards fn-nntp-archive-command-cat
  :hints (("Goal" :in-theory (enable (tau-system)))))
