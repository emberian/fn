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
; What is NOT here (the record names it): OVER/XOVER, LISTGROUP and LIST
; COUNTS over fn-cnx-view-range; the HDR/XHDR/XPAT walks; the lift through
; fn-nntp-command-pinned up to fn-served-dispatch-core; the host switch
; (step 8: the owner loads the catalog and hands the served connection its
; view as a count).  Until the host switch the archive stays the input of
; every other arm, so the -cat dispatcher takes it too and the equation is
; stated under archive = the view's articles.
(in-package "ACL2")
(include-book "catalog-number-index")
(include-book "nntp")

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
           kind nil nil)
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
              (fn-nntp-article-response session article number kind t group)
            (fn-nntp-single session "423 no article with that number")))))))

(verify-guards fn-nntp-msgid-retrieval-cat)
(verify-guards fn-nntp-number-retrieval-cat)

(defthm fn-nntp-msgid-retrieval-cat-is-scan
  (implies (equal (fn-state-articles archive)
                  (fn-cat-view-articles v fn-arena fn-cat))
           (equal (fn-nntp-msgid-retrieval-cat session v kind token fn-arena fn-cat)
                  (fn-nntp-msgid-retrieval session archive kind token)))
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
                  (fn-nntp-number-retrieval session archive kind token)))
  :hints (("Goal"
           :in-theory (e/d (fn-nntp-number-retrieval-cat fn-nntp-number-retrieval)
                           (fn-scat-number-article fn-nntp-find-group-number
                            fn-nntp-article-response fn-nntp-single
                            fn-cat-view-articles fn-nntp-number-tokenp
                            fn-nntp-decimal-value fn-nntp-session-group)))))

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
  (let ((xref (fn-nntp-xref-reply session archive index env keyword args)))
    (if xref xref
      (cond
       ((and (fn-nntp-keywordp keyword "LIST")
             (fn-gidx-pinp index)
             (consp args)
             (fn-nntp-keyword-tokenp (car args))
             (fn-nntp-keywordp (car args) "COUNTS"))
        (fn-gidx-list-counts-command
         session archive (fn-gidx-pin-buckets index) (cdr args)))
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
        (fn-gidx-listgroup-command
         session archive (fn-gidx-pin-buckets index) args))
       ((and (or (fn-nntp-keywordp keyword "OVER")
                 (fn-nntp-keywordp keyword "XOVER"))
             (fn-gidx-pinp index)
             (consp args) (null (cdr args))
             (fn-nntp-range-okp (fn-nntp-parse-range (car args))))
        (fn-nntp-over-range-indexed
         session (fn-gidx-pin-buckets index) (fn-gidx-pin-trie index)
         (car args) (fn-nntp-keywordp keyword "XOVER")))
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
       (t (fn-nntp-archive-command session archive env keyword args))))))

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
            (equal (fn-nntp-archive-command session archive env keyword args)
                   (fn-nntp-number-retrieval
                    session archive
                    (cond ((fn-nntp-keywordp keyword "ARTICLE") :article)
                          ((fn-nntp-keywordp keyword "HEAD") :head)
                          ((fn-nntp-keywordp keyword "BODY") :body)
                          (t :stat))
                    (car args))))
   :hints (("Goal" :in-theory (e/d (fn-nntp-archive-command fn-nntp-retrieval)
                                   (fn-nntp-number-retrieval fn-nntp-msgid-retrieval
                                    fn-nntp-current-retrieval fn-nntp-number-tokenp
                                    fn-nntp-message-id-tokenp fn-nntp-upcase-keyword))))))

(defthm fn-nntp-archive-command-cat-is-pinned
  (implies (and (equal (fn-state-articles archive)
                       (fn-cat-view-articles v fn-arena fn-cat))
                (fn-midx-correspondencep (fn-gidx-pin-trie index)
                                         (fn-state-articles archive))
                (fn-cnx-freshp fn-cat))
           (equal (fn-nntp-archive-command-cat
                   session archive index verdicts env keyword args v fn-arena fn-cat)
                  (fn-nntp-archive-command-pinned
                   session archive index verdicts env keyword args)))
  :hints (("Goal"
           :in-theory (e/d (fn-nntp-archive-command-cat fn-nntp-archive-command-pinned)
                           (fn-nntp-xref-reply fn-gidx-list-counts-command
                            fn-nntp-number-withdrawn-p fn-nntp-msgid-withdrawn-p
                            fn-nntp-withdrawn-reply fn-gidx-listgroup-command
                            fn-nntp-over-range-indexed fn-nntp-verdict-hdr-response
                            fn-nntp-control-hdr-response
                            fn-nntp-enrollment-hdr-response
                            fn-nntp-archive-command fn-nntp-upcase-keyword
                            fn-nntp-keyword-tokenp fn-gidx-pinp fn-gidx-pin-trie
                            fn-gidx-pin-buckets fn-nntp-message-id-tokenp
                            fn-nntp-number-tokenp fn-nntp-range-okp
                            fn-nntp-parse-range fn-nntp-msgid-retrieval-cat
                            fn-nntp-number-retrieval-cat
                            fn-nntp-msgid-retrieval-indexed
                            fn-nntp-msgid-retrieval fn-nntp-number-retrieval
                            fn-cat-view-articles fn-midx-correspondencep)))))
