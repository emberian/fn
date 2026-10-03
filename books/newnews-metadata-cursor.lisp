; NEWNEWS's first buffered cursor consumer. Metadata selection advances one
; captured article at a time; output drain does not repeat selection and does
; not depend on the shared payload cache. The captured archive/root belongs
; to CONTEXT; CUR carries groups/date/article tail/horizon, not a live count.
(in-package "ACL2")
(include-book "newnews-cursor-shape")
(include-book "nntp-newnews")
(include-book "served-columns")
(include-book "def-cursor")

(local (in-theory (disable (tau-system))))

;;; NEWNEWS over the catalog's tombstone column (lane served-live,
;;; cg-newnews-hang).  The reference scan (books/nntp-responses.lisp
;;; fn-nntp-newnews-scan) tests every candidate for a reclaim tombstone by
;;; reading its payload's head (fn-nntp-article-tombstonep).  On the served
;;; path that read runs under the realizer's no-I/O mode: a miss discards
;;; the whole line, the one missing entry is read off the owner mutex and
;;; the line runs again.  The realizer keeps fn-arx-read-cache-entries (8)
;;; entries, so a NEWNEWS with more candidates than that evicts its own
;;; earlier entries on every run and never completes: one client pinned the
;;; owner (no answer in 100 s at 12 articles; 225 s at 77% owner CPU at 50).
;;; This arm reads the tombstone from the article's catalog row
;;; (books/served-columns.lisp fn-scol-tombstonep): no payload octet, and
;;; under F it is the bytes' answer (fn-scol-tombstonep-is-bytes), so the
;;; reply is the reference's (fn-nntp-newnews-response-cat-is-newnews-
;;; response).
(defun fn-nntp-newnews-scan-cat-loop (groups threshold articles horizon fn-arena fn-cat acc)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard (true-listp acc) :verify-guards nil
                  :measure (acl2-count articles)))
  (if (not (consp articles))
      (revappend acc nil)
    (let* ((article (fn-ag-car articles))
           (stamp (fn-article-stamp article)))
      (fn-nntp-newnews-scan-cat-loop
       groups threshold (fn-ag-cdr articles) (if (natp stamp) stamp horizon) fn-arena fn-cat
       (if (and (fn-nntp-newnews-candidatep groups article)
                (not (fn-scol-tombstonep article fn-arena fn-cat))
                (fn-nntp-newnews-newp threshold stamp horizon))
           (cons (fn-nntp-string-octets (fn-article-msgid article)) acc)
         acc)))))

(defun fn-nntp-newnews-scan-cat (groups threshold articles horizon fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard t :verify-guards nil
                  :measure (acl2-count articles)))
  (mbe :logic
       (if (not (consp articles))
           nil
         (let* ((article (fn-ag-car articles))
                (stamp (fn-article-stamp article))
                (rest (fn-nntp-newnews-scan-cat
                       groups threshold (fn-ag-cdr articles)
                       (if (natp stamp) stamp horizon) fn-arena fn-cat)))
           (if (and (fn-nntp-newnews-candidatep groups article)
                    (not (fn-scol-tombstonep article fn-arena fn-cat))
                    (fn-nntp-newnews-newp threshold stamp horizon))
               (cons (fn-nntp-string-octets (fn-article-msgid article)) rest)
             rest)))
       :exec (fn-nntp-newnews-scan-cat-loop groups threshold articles horizon fn-arena fn-cat nil)))

(local
 (defthm fn-nntp-newnews-scan-cat-loop-is-revappend
   (equal (fn-nntp-newnews-scan-cat-loop groups threshold articles horizon fn-arena fn-cat acc)
          (revappend acc (fn-nntp-newnews-scan-cat groups threshold articles horizon fn-arena fn-cat)))
   :hints (("Goal" :in-theory (disable fn-nntp-newnews-candidatep fn-scol-tombstonep
                                       fn-nntp-newnews-newp fn-nntp-string-octets
                                       fn-article-stamp fn-article-msgid)))))

(defthm fn-nntp-newnews-scan-cat-is-scan
  (implies (fn-scol-okp fn-arena fn-cat)
           (equal (fn-nntp-newnews-scan-cat groups threshold articles horizon fn-arena fn-cat)
                  (fn-nntp-newnews-scan groups threshold articles horizon fn-arena)))
  :hints (("Goal" :induct (fn-nntp-newnews-scan-cat groups threshold articles horizon fn-arena fn-cat)
                  :in-theory (e/d (fn-nntp-newnews-scan fn-scol-tombstonep-is-bytes)
                                  (fn-nntp-newnews-scan-is-the-acceptance-filter
                                   fn-nntp-newnews-candidatep fn-scol-tombstonep
                                   fn-nntp-article-tombstonep fn-nntp-newnews-newp
                                   fn-nntp-string-octets fn-article-stamp fn-article-msgid)))))

(verify-guards fn-nntp-newnews-scan-cat-loop)

(verify-guards fn-nntp-newnews-scan-cat
  :hints (("Goal" :in-theory (disable fn-nntp-newnews-scan-cat-loop fn-nntp-newnews-candidatep
                                      fn-scol-tombstonep fn-nntp-newnews-newp
                                      fn-nntp-string-octets fn-article-stamp fn-article-msgid)
                  :use ((:instance fn-nntp-newnews-scan-cat-loop-is-revappend (acc nil))))))

(defun fn-nntp-newnews-response-cat (session archive env args fn-arena fn-cat)
  ; fn-nntp-newnews-response, its scan reading the catalog's tombstone
  ; column.  The parse is the reference's, form for form.
  (declare (xargs :stobjs (fn-arena fn-cat) :guard t :verify-guards nil))
  (if (not (and (consp args) (consp (cdr args)) (consp (cdr (cdr args)))
                (or (null (cdr (cdr (cdr args))))
                    (and (consp (cdr (cdr (cdr args))))
                         (null (cdr (cdr (cdr (cdr args)))))
                         (fn-nntp-keywordp (car (cdr (cdr (cdr args))))
                                           "GMT")))))
      (fn-nntp-single session (fn-proto-text * :syntax))
    (let ((date (fn-nntp-newgroups-date-parse
                 (car (cdr args))
                 (fn-nntp-observed-year (fn-nntp-env-observation env))))
          (time (fn-nntp-newgroups-time-parse (car (cdr (cdr args)))))
          (patterns (fn-wildmat-parse (car args))))
      (if (and (not (fn-nntp-parse-okp date))
               (equal (car (cdr date)) :no-century))
          (fn-nntp-single
           session (fn-proto-text * :no-century))
        (if (or (not (fn-nntp-parse-okp date))
                (not (fn-nntp-parse-okp time))
                (not (fn-wildmat-result-okp patterns)))
            (fn-nntp-single session (fn-proto-text * :syntax))
          (fn-nntp-multi
           session (fn-proto-text "NEWNEWS" :listed)
           (fn-nntp-newnews-scan-cat
            (fn-nntp-filter-groups-by-wildmat
             (fn-wildmat-result-value patterns)
             (fn-state-groups archive))
            (fn-nntp-civil-dtn-ms
             (fn-nntp-parse-1 date) (fn-nntp-parse-2 date)
             (fn-nntp-parse-3 date) (fn-nntp-parse-1 time)
             (fn-nntp-parse-2 time) (fn-nntp-parse-3 time))
            (fn-state-articles archive)
            (fn-nntp-newnews-reader-horizon env) fn-arena fn-cat)))))))

(defthm fn-nntp-newnews-response-cat-is-newnews-response
  (implies (fn-scol-okp fn-arena fn-cat)
           (equal (fn-nntp-newnews-response-cat session archive env args fn-arena fn-cat)
                  (fn-nntp-newnews-response session archive env args fn-arena)))
  :hints (("Goal" :do-not-induct t
                  :in-theory (e/d (fn-nntp-newnews-response-cat fn-nntp-newnews-response
                                   fn-nntp-newnews-scan-cat-is-scan)
                                  (fn-nntp-newnews-scan-cat fn-nntp-newnews-scan
                                   fn-nntp-filter-groups-by-wildmat fn-wildmat-parse
                                   fn-nntp-newgroups-date-parse fn-nntp-newgroups-time-parse
                                   fn-nntp-civil-dtn-ms fn-nntp-multi fn-nntp-single)))))

(verify-guards fn-nntp-newnews-response-cat)

(in-theory (disable fn-nntp-newnews-response-cat))

(defun fn-nnw-meta-one (progress fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard t :verify-guards nil))
  (let ((tail (fn-nnw-tail progress)))
    (if (atom tail)
        (mv '(46 13 10) nil)
      (let* ((article (car tail))
             (stamp (fn-article-stamp article))
             (horizon (fn-nnw-horizon progress))
             (next (and (consp (cdr tail))
                        (fn-nnw-cursor (fn-nnw-groups progress)
                                       (fn-nnw-threshold progress)
                                       (cdr tail) nil
                                       (if (natp stamp) stamp horizon))))
             (matched (and (fn-nntp-newnews-candidatep (fn-nnw-groups progress) article)
                           (not (fn-scol-tombstonep article fn-arena fn-cat))
                           (fn-nntp-newnews-newp (fn-nnw-threshold progress) stamp horizon))))
        (mv (append (if matched
                        (fn-nntp-stuff-lines
                         (list (fn-nntp-string-octets (fn-article-msgid article))))
                      nil)
                    (if next nil '(46 13 10)))
            next)))))

; This one candidate primitive examines only CAR TAIL and installs CDR TAIL
; as the next scan state. Sparse no-match selection still advances. Unlike
; fn-nnw-step it uses the catalog's tombstone column, never a payload read.
(defthm fn-nnw-meta-one-progresses
  (let ((next (mv-nth 1 (fn-nnw-meta-one progress fn-arena fn-cat))))
    (implies next
             (< (acl2-count (fn-nnw-tail next))
                (acl2-count (fn-nnw-tail progress)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-nnw-meta-one fn-nnw-cursor fn-nnw-tail fn-nnw-at))))

(defthm fn-nnw-meta-one-visits-at-most-one
  (<= (- (len (fn-nnw-tail progress))
         (len (fn-nnw-tail (mv-nth 1 (fn-nnw-meta-one progress fn-arena fn-cat)))))
      1)
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-nnw-meta-one fn-nnw-cursor fn-nnw-tail fn-nnw-at))))

(def-cursor fn-nnw-meta (fn-arena fn-cat)
  :stobjs (fn-arena fn-cat)
  :call (fn-nnw-meta-one progress fn-arena fn-cat)
  :visit-proof fn-nnw-meta-one-visits-at-most-one)

; Complete reply residual after its initially buffered status line. A
; pending suffix belongs to the continuation even when scan progress ended.
(defun fn-nnw-meta-owes (progress fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard t :verify-guards nil))
  (if progress
      (append (fn-nntp-stuff-lines
               (fn-nntp-newnews-scan-cat
                (fn-nnw-groups progress) (fn-nnw-threshold progress)
                (fn-nnw-tail progress) (fn-nnw-horizon progress) fn-arena fn-cat))
              '(46 13 10))
    nil))

(defthm fn-nnw-meta-one-residual
  (implies progress
   (equal (append (mv-nth 0 (fn-nnw-meta-one progress fn-arena fn-cat))
                 (fn-nnw-meta-owes
                  (mv-nth 1 (fn-nnw-meta-one progress fn-arena fn-cat)) fn-arena fn-cat))
         (fn-nnw-meta-owes progress fn-arena fn-cat)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nnw-meta-one fn-nnw-meta-owes fn-nnw-cursor fn-nnw-at
                             fn-nnw-tail fn-nnw-groups fn-nnw-threshold fn-nnw-horizon
                             fn-nntp-stuff-lines)
                            (fn-nntp-newnews-candidatep fn-nntp-newnews-newp fn-scol-tombstonep
                             fn-nntp-string-octets fn-article-msgid fn-article-stamp))
           :expand ((fn-nntp-newnews-scan-cat
                     (fn-nnw-at 1 progress) (fn-nnw-at 2 progress)
                     (fn-nnw-at 3 progress) (fn-nnw-at 5 progress) fn-arena fn-cat)))))

(defun fn-nnw-meta-remaining (cur fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard t :verify-guards nil))
  (append (fn-cur-pending cur)
          (fn-nnw-meta-owes (fn-cur-progress cur) fn-arena fn-cat)))

(local
 (defthm fn-nnw-meta-append-associative
   (equal (append (append a b) c) (append a b c))))

(local
 (defthm fn-nnw-meta-split-residual-onto
   (equal (append (mv-nth 0 (fn-cur-split xs n))
                  (mv-nth 1 (fn-cur-split xs n)) suffix)
          (append xs suffix))
   :hints (("Goal" :in-theory (disable fn-cur-split fn-nnw-meta-append-associative)
            :use ((:instance fn-nnw-meta-append-associative
                              (a (mv-nth 0 (fn-cur-split xs n)))
                              (b (mv-nth 1 (fn-cur-split xs n))) (c suffix)))))))

(defthm fn-nnw-meta-step-residual
  (equal
            (append (mv-nth 0 (fn-nnw-meta-step cur visits bytes fn-arena fn-cat))
                    (fn-nnw-meta-remaining
                     (mv-nth 1 (fn-nnw-meta-step cur visits bytes fn-arena fn-cat))
                     fn-arena fn-cat))
            (fn-nnw-meta-remaining cur fn-arena fn-cat))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nnw-meta-step fn-nnw-meta-remaining)
                            (fn-cur-split fn-cur-split-residual fn-nnw-meta-one fn-nnw-meta-owes))
           :use ((:instance fn-nnw-meta-one-residual (progress (fn-cur-progress cur)))
                 (:instance fn-cur-split-residual (xs (fn-cur-pending cur)) (n bytes))
                 (:instance fn-cur-split-residual
                            (xs (mv-nth 0 (fn-nnw-meta-one (fn-cur-progress cur) fn-arena fn-cat)))
                            (n bytes))))))

(defthm fn-nnw-meta-step-residual-onto
  (equal (append (mv-nth 0 (fn-nnw-meta-step cur visits bytes fn-arena fn-cat))
                 (fn-nnw-meta-remaining
                  (mv-nth 1 (fn-nnw-meta-step cur visits bytes fn-arena fn-cat)) fn-arena fn-cat)
                 suffix)
         (append (fn-nnw-meta-remaining cur fn-arena fn-cat) suffix))
  :hints (("Goal" :in-theory (disable fn-nnw-meta-step fn-nnw-meta-remaining
                                     fn-nnw-meta-append-associative)
           :use ((:instance fn-nnw-meta-step-residual)
                 (:instance fn-nnw-meta-append-associative
                            (a (mv-nth 0 (fn-nnw-meta-step cur visits bytes fn-arena fn-cat)))
                            (b (fn-nnw-meta-remaining
                                (mv-nth 1 (fn-nnw-meta-step cur visits bytes fn-arena fn-cat))
                                fn-arena fn-cat))
                            (c suffix))))))

(verify-guards fn-nnw-meta-one)
(verify-guards fn-nnw-meta-step)

(defun fn-nnw-meta-effect (cur)
  (declare (xargs :guard t))
  (list :newnews-cursor cur))

(defun fn-nnw-meta-effectp (e)
  (declare (xargs :guard t))
  (and (consp e) (equal (car e) :newnews-cursor) (consp (cdr e))))

(defun fn-nnw-meta-livep (cur)
  (declare (xargs :guard t))
  (or (fn-cur-progress cur) (consp (fn-cur-pending cur)) (fn-cur-dependency cur)))

(defun fn-nntp-newnews-response-cursor (session archive env args fn-arena fn-cat)
  ; fn-nntp-newnews-response, its scan reading the catalog's tombstone
  ; column.  The parse is the reference's, form for form.
  (declare (ignore fn-arena fn-cat)
           (xargs :stobjs (fn-arena fn-cat) :guard t :verify-guards nil))
  (if (not (and (consp args) (consp (cdr args)) (consp (cdr (cdr args)))
                (or (null (cdr (cdr (cdr args))))
                    (and (consp (cdr (cdr (cdr args))))
                         (null (cdr (cdr (cdr (cdr args)))))
                         (fn-nntp-keywordp (car (cdr (cdr (cdr args))))
                                           "GMT")))))
      (fn-nntp-single session (fn-proto-text * :syntax))
    (let ((date (fn-nntp-newgroups-date-parse
                 (car (cdr args))
                 (fn-nntp-observed-year (fn-nntp-env-observation env))))
          (time (fn-nntp-newgroups-time-parse (car (cdr (cdr args)))))
          (patterns (fn-wildmat-parse (car args))))
      (if (and (not (fn-nntp-parse-okp date))
               (equal (car (cdr date)) :no-century))
          (fn-nntp-single
           session (fn-proto-text * :no-century))
        (if (or (not (fn-nntp-parse-okp date))
                (not (fn-nntp-parse-okp time))
                (not (fn-wildmat-result-okp patterns)))
            (fn-nntp-single session (fn-proto-text * :syntax))
          (fn-nntp-make-result
           session
           (list
            (fn-nnw-meta-effect
             (fn-cur-make
              (list archive env args)
              (fn-nnw-cursor
               (fn-nntp-filter-groups-by-wildmat
                (fn-wildmat-result-value patterns) (fn-state-groups archive))
               (fn-nntp-civil-dtn-ms
                (fn-nntp-parse-1 date) (fn-nntp-parse-2 date)
                (fn-nntp-parse-3 date) (fn-nntp-parse-1 time)
                (fn-nntp-parse-2 time) (fn-nntp-parse-3 time))
               (fn-state-articles archive) nil (fn-nntp-newnews-reader-horizon env))
              (fn-nntp-crlf (fn-nntp-string-octets (fn-proto-text "NEWNEWS" :listed)))
              nil)))))))))

(verify-guards fn-nntp-newnews-response-cursor)

(defun fn-nnw-meta-expand (effects fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard t :verify-guards nil))
  (if (consp effects)
      (cons (if (fn-nnw-meta-effectp (car effects))
                (fn-nntp-reply-effect
                 (fn-nnw-meta-remaining (car (cdr (car effects))) fn-arena fn-cat))
              (car effects))
            (fn-nnw-meta-expand (cdr effects) fn-arena fn-cat))
    effects))

(defthm fn-nntp-newnews-response-cursor-is-cat
  (equal (fn-nnw-meta-expand
          (cdr (fn-nntp-newnews-response-cursor session archive env args fn-arena fn-cat))
          fn-arena fn-cat)
         (cdr (fn-nntp-newnews-response-cat session archive env args fn-arena fn-cat)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nntp-newnews-response-cursor fn-nntp-newnews-response-cat
                             fn-nnw-meta-expand fn-nnw-meta-effectp fn-nnw-meta-effect
                             fn-nnw-meta-remaining fn-nnw-meta-owes fn-nnw-cursor fn-nnw-at
                             fn-nnw-tail fn-nnw-groups fn-nnw-threshold fn-nnw-horizon
                             fn-nntp-multi fn-nntp-make-result fn-nntp-single fn-nntp-reply-effect)
                            (fn-nntp-newnews-scan-cat fn-wildmat-parse
                             fn-nntp-newgroups-date-parse fn-nntp-newgroups-time-parse
                             fn-nntp-civil-dtn-ms fn-nntp-string-octets fn-nntp-crlf
                             fn-nntp-filter-groups-by-wildmat)))))

(defthm fn-nntp-newnews-response-cursor-keeps-session
  (equal (car (fn-nntp-newnews-response-cursor session archive env args fn-arena fn-cat))
         session)
  :hints (("Goal" :in-theory (enable fn-nntp-newnews-response-cursor fn-nntp-make-result
                                     fn-nntp-single))))

(defthm fn-nnw-meta-one-output-true-listp
  (true-listp (mv-nth 0 (fn-nnw-meta-one progress fn-arena fn-cat)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (e/d (fn-nnw-meta-one) (fn-nntp-stuff-lines)))))

(defthm fn-nnw-meta-one-output-list
  (true-listp (car (fn-nnw-meta-one progress fn-arena fn-cat)))
  :hints (("Goal" :use fn-nnw-meta-one-output-true-listp)))

(defthm fn-nnw-meta-step-keeps-pending-true-listp
  (implies (true-listp (fn-cur-pending cur))
           (true-listp
            (fn-cur-pending (mv-nth 1 (fn-nnw-meta-step cur visits bytes fn-arena fn-cat)))))
  :hints (("Goal" :in-theory (e/d (fn-nnw-meta-step) (fn-nnw-meta-one)))))

(defthm fn-nnw-meta-remaining-of-not-live
  (implies (not (fn-nnw-meta-livep cur))
           (equal (fn-nnw-meta-remaining cur fn-arena fn-cat) nil))
  :hints (("Goal" :in-theory (enable fn-nnw-meta-livep fn-nnw-meta-remaining fn-nnw-meta-owes))))

(defun fn-nnw-meta-initialp (cur)
  (declare (xargs :guard t))
  (equal (fn-cur-pending cur)
         (fn-nntp-crlf (fn-nntp-string-octets (fn-proto-text "NEWNEWS" :listed)))))

(defthm fn-nnw-meta-initial-status-first
  (implies (fn-nnw-meta-initialp cur)
           (let ((octets (fn-nnw-meta-remaining cur fn-arena fn-cat)))
             (not (and (consp octets) (equal (car octets) 50)
                       (consp (cdr octets)) (equal (car (cdr octets)) 49)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-nnw-meta-initialp fn-nnw-meta-remaining))))

(in-theory (disable fn-nnw-meta-one fn-nnw-meta-step fn-nnw-meta-owes
                    fn-nnw-meta-remaining fn-nntp-newnews-response-cursor))
