; PRF-010: a rebuildable group/local-number index over committed articles.
; The index is a derived materialization.  Its range query scans only the
; materialized entries; the reference functions below independently enumerate
; the authoritative article memberships for correspondence theorems.
(in-package "ACL2")
(include-book "acceptance")
(include-book "acceptance-invariants")

(defun fn-index-entry (group number msgid)
  (declare (xargs :guard t :verify-guards nil))
  (list group number msgid))
(verify-guards fn-index-entry)

(defun fn-index-entry-group (entry)
  (declare (xargs :guard t :verify-guards nil))
  (fn-ag-car entry))
(verify-guards fn-index-entry-group)
(defun fn-index-entry-number (entry)
  (declare (xargs :guard t :verify-guards nil))
  (fn-ag-car (fn-ag-cdr entry)))
(verify-guards fn-index-entry-number)
(defun fn-index-entry-msgid (entry)
  (declare (xargs :guard t :verify-guards nil))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr entry))))
(verify-guards fn-index-entry-msgid)

(defun fn-index-entryp (entry)
  (declare (xargs :guard t :verify-guards nil))
  (and (true-listp entry)
       (equal (len entry) 3)
       (stringp (fn-index-entry-group entry))
       (posp (fn-index-entry-number entry))
       (stringp (fn-index-entry-msgid entry))))
(verify-guards fn-index-entryp)

(defun fn-index-listp (index)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp index)
      (and (fn-index-entryp (car index))
           (fn-index-listp (cdr index)))
    (null index)))
(verify-guards fn-index-listp)

(defun fn-index-entry-key (entry)
  (declare (xargs :guard t :verify-guards nil))
  (cons (fn-index-entry-group entry)
        (fn-index-entry-number entry)))
(verify-guards fn-index-entry-key)

; Materialization follows the source article order, then each article's
; configured membership order.  A number is local to its group: the key always
; contains both fields and is never merged into a global number namespace.
(defun fn-index-membership-entries (msgid memberships)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp memberships)
      (cons (fn-index-entry
             (fn-ag-car (fn-ag-car memberships))
             (fn-ag-cdr (fn-ag-car memberships))
             msgid)
            (fn-index-membership-entries msgid
                                         (fn-ag-cdr memberships)))
    nil))
(verify-guards fn-index-membership-entries)

(defun fn-index-article-entries (article)
  (declare (xargs :guard t :verify-guards nil))
  (fn-index-membership-entries
   (fn-article-msgid article)
   (fn-article-memberships article)))
(verify-guards fn-index-article-entries)

(defun fn-index-build (articles)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp articles)
      (append (fn-index-article-entries (car articles))
              (fn-index-build (cdr articles)))
    nil))
(verify-guards fn-index-build)

(defun fn-index-rebuild (st)
  (declare (xargs :guard (fn-statep st) :verify-guards nil))
  (fn-index-build (fn-state-articles st)))
(verify-guards fn-index-rebuild)

; The public query is total: malformed index/range inputs refuse with NIL.  On
; valid inputs it scans only INDEX and never consults source articles.
(defun fn-index-entry-in-range-p (group low high entry)
  (declare (xargs :guard t :verify-guards nil))
  (and (equal group (fn-index-entry-group entry))
       (not (fn-ag-less (fn-index-entry-number entry) low))
       (not (fn-ag-less high (fn-index-entry-number entry)))))
(verify-guards fn-index-entry-in-range-p)

(defun fn-index-range-query-raw (index group low high)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp index)
      (if (fn-index-entry-in-range-p group low high (car index))
          (cons (car index)
                (fn-index-range-query-raw (cdr index) group low high))
        (fn-index-range-query-raw (cdr index) group low high))
    nil))
(verify-guards fn-index-range-query-raw)

(defun fn-index-query-range (index group low high)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (fn-index-listp index)
           (stringp group)
           (natp low)
           (natp high))
      (fn-index-range-query-raw index group low high)
    nil))
(verify-guards fn-index-query-range)

; A sourced entry is an exact materialized member of the authoritative
; article list.  Soundness and completeness are stated as separate subset
; directions over that source materialization.  Together they reject both an
; invented entry and an omitted membership.
(defun fn-index-entry-sourcedp (entry articles)
  (declare (xargs :guard t :verify-guards nil))
  (member-equal entry (fn-index-build articles)))
(verify-guards fn-index-entry-sourcedp)

(defun fn-index-soundp (index articles)
  (declare (xargs :guard t :verify-guards nil))
  (fn-subsetp index (fn-index-build articles)))
(verify-guards fn-index-soundp)

(defun fn-index-completep (index articles)
  (declare (xargs :guard t :verify-guards nil))
  (fn-subsetp (fn-index-build articles) index))
(verify-guards fn-index-completep)

(defun fn-index-correspondencep (index articles)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-index-listp index)
       (fn-index-soundp index articles)
       (fn-index-completep index articles)))
(verify-guards fn-index-correspondencep)

; Independent reference enumeration for range correctness.  This is proof and
; test oracle code; the public query above only traverses the materialized list.
(defun fn-index-reference-memberships (group low high msgid memberships)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp memberships)
      (let ((membership (fn-ag-car memberships)))
        (if (and (equal group (fn-ag-car membership))
                 (not (fn-ag-less (fn-ag-cdr membership) low))
                 (not (fn-ag-less high (fn-ag-cdr membership))))
            (cons (fn-index-entry group (fn-ag-cdr membership) msgid)
                  (fn-index-reference-memberships
                   group low high msgid (fn-ag-cdr memberships)))
          (fn-index-reference-memberships
           group low high msgid (fn-ag-cdr memberships))))
    nil))
(verify-guards fn-index-reference-memberships)

(defun fn-index-reference-range (group low high articles)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp articles)
      (append
       (fn-index-reference-memberships
        group low high
        (fn-article-msgid (car articles))
        (fn-article-memberships (car articles)))
       (fn-index-reference-range group low high (cdr articles)))
    nil))
(verify-guards fn-index-reference-range)

(defthm fn-index-query-append
  (equal (fn-index-range-query-raw (append xs ys) group low high)
         (append (fn-index-range-query-raw xs group low high)
                 (fn-index-range-query-raw ys group low high)))
  :hints (("Goal" :induct (fn-index-range-query-raw xs group low high))))

(defthm fn-index-query-memberships-build
  (equal (fn-index-range-query-raw
          (fn-index-membership-entries msgid memberships)
          group low high)
         (fn-index-reference-memberships
          group low high msgid memberships))
  :hints (("Goal" :induct (fn-index-membership-entries msgid memberships))))

(defthm fn-index-range-query-correct
  (implies (and (fn-article-listp configured articles)
                (fn-index-listp (fn-index-build articles))
                (stringp group)
                (natp low)
                (natp high))
           (equal (fn-index-query-range
                   (fn-index-build articles) group low high)
                  (fn-index-reference-range group low high articles)))
  :hints (("Goal" :induct (fn-index-build articles))))

(defthm fn-index-build-subset-self
  (fn-subsetp (fn-index-build articles) (fn-index-build articles))
  :hints (("Goal" :use (:instance fn-subset-self
                                      (groups (fn-index-build articles))))))

(defthm fn-index-build-sound
  (implies (fn-article-listp configured articles)
           (fn-index-soundp (fn-index-build articles) articles))
  :hints (("Goal" :induct (fn-index-build articles))))

(defthm fn-index-build-complete
  (implies (fn-article-listp configured articles)
           (fn-index-completep (fn-index-build articles) articles))
  :hints (("Goal" :induct (fn-index-build articles))))

(defthm fn-index-build-correspondence
  (implies (fn-article-listp configured articles)
           (fn-index-correspondencep (fn-index-build articles) articles))
  :hints (("Goal" :induct (fn-index-build articles))))

(defthm fn-index-rebuild-correspondence
  (implies (fn-statep st)
           (fn-index-correspondencep
            (fn-index-rebuild st)
            (fn-state-articles st)))
  :hints (("Goal" :use (:instance fn-index-build-correspondence
                                      (configured (fn-state-groups st))
                                      (articles (fn-state-articles st)))))
)
