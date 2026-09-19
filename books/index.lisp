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

; A sourced entry corresponds to an actual (group . number) membership of some
; article in ARTICLES: some article whose message id is the entry's msgid
; records that exact (group . number) pair in FN-ARTICLE-MEMBERSHIPS.  This
; scans ARTICLES and their memberships directly; it never calls
; FN-INDEX-BUILD, so it is a check against the authoritative source, not a
; restatement of the build's own output.
(defun fn-index-membership-hasp (group number memberships)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp memberships)
      (or (and (equal group (fn-ag-car (fn-ag-car memberships)))
               (equal number (fn-ag-cdr (fn-ag-car memberships))))
          (fn-index-membership-hasp group number (fn-ag-cdr memberships)))
    nil))
(verify-guards fn-index-membership-hasp)

(defun fn-index-entry-sourcedp (entry articles)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp articles)
      (or (and (equal (fn-index-entry-msgid entry)
                      (fn-article-msgid (fn-ag-car articles)))
               (fn-index-membership-hasp (fn-index-entry-group entry)
                                         (fn-index-entry-number entry)
                                         (fn-article-memberships (fn-ag-car articles))))
          (fn-index-entry-sourcedp entry (fn-ag-cdr articles)))
    nil))
(verify-guards fn-index-entry-sourcedp)

; Soundness: every INDEX entry is sourced.  Completeness: every authoritative
; membership of every article in ARTICLES is present in INDEX.  Both scan
; ARTICLES/memberships directly, never FN-INDEX-BUILD; the correspondence
; theorems below connect them to a fresh build by induction, not by
; definition.
(defun fn-index-soundp (index articles)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp index)
      (and (fn-index-entry-sourcedp (fn-ag-car index) articles)
           (fn-index-soundp (fn-ag-cdr index) articles))
    t))
(verify-guards fn-index-soundp)

; MEMBER-EQUAL's guard requires (true-listp index), which an arbitrary guard-T
; INDEX parameter does not carry; FN-AG-MEMBER is the guard-T equivalent
; (FN-AG-MEMBER-IS-MEMBER, acceptance.lisp) already used the same way by
; FN-SUBSETP's :exec branch.
(defun fn-index-memberships-completep (msgid memberships index)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp memberships)
      (and (fn-ag-member
            (fn-index-entry (fn-ag-car (fn-ag-car memberships))
                            (fn-ag-cdr (fn-ag-car memberships))
                            msgid)
            index)
           (fn-index-memberships-completep msgid (fn-ag-cdr memberships) index))
    t))
(verify-guards fn-index-memberships-completep)

(defun fn-index-completep (index articles)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp articles)
      (and (fn-index-memberships-completep
            (fn-article-msgid (fn-ag-car articles))
            (fn-article-memberships (fn-ag-car articles))
            index)
           (fn-index-completep index (fn-ag-cdr articles)))
    t))
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

; -----------------------------------------------------------------------------
; FN-INDEX-BUILD is guard-t and well typed for a valid article list.  Proved
; separately from soundness/completeness so FN-INDEX-RANGE-QUERY-CORRECT below
; can derive it instead of assuming it.

(defthm fn-index-membership-entries-listp
  (implies (and (stringp msgid)
                (fn-string-listp groups)
                (fn-membership-listp groups memberships))
           (fn-index-listp (fn-index-membership-entries msgid memberships)))
  :hints (("Goal" :induct (fn-membership-listp groups memberships))))

(defthm fn-index-article-entries-listp
  (implies (fn-articlep configured article)
           (fn-index-listp (fn-index-article-entries article)))
  :hints (("Goal" :use (:instance fn-index-membership-entries-listp
                                  (msgid (fn-article-msgid article))
                                  (memberships (fn-article-memberships article))
                                  (groups (fn-article-groups article)))
           :in-theory (enable fn-index-article-entries fn-articlep
                              fn-selection-validp))))

(defthm fn-index-listp-append
  (implies (and (fn-index-listp xs) (fn-index-listp ys))
           (fn-index-listp (append xs ys)))
  :hints (("Goal" :induct (fn-index-listp xs))))

(defthm fn-index-build-listp
  (implies (fn-article-listp configured articles)
           (fn-index-listp (fn-index-build articles)))
  :hints (("Goal" :induct (fn-index-build articles))))

(defthm fn-index-range-query-correct
  (implies (and (fn-article-listp configured articles)
                (stringp group)
                (natp low)
                (natp high))
           (equal (fn-index-query-range
                   (fn-index-build articles) group low high)
                  (fn-index-reference-range group low high articles)))
  :hints (("Goal" :induct (fn-index-build articles)
                  :in-theory (enable fn-index-query-range))))

; -----------------------------------------------------------------------------
; Soundness and completeness of a fresh build against the authoritative source
; memberships.  Each is proved by induction connecting FN-INDEX-BUILD's append
; recursion to the membership-level predicates above; neither instantiates the
; soundness/completeness predicate with the build as its own reference, so
; these are not `X SUBSET X` restatements.

(defthm member-equal-append-right
  (implies (member-equal x xs)
           (member-equal x (append xs ys))))

(defthm member-equal-append-left
  (implies (member-equal x xs)
           (member-equal x (append ys xs)))
  :hints (("Goal" :induct (append ys xs))))

; Stated with raw CAR/CDR, not FN-AG-CAR/FN-AG-CDR: FN-AG-CAR-IS-CAR rewrites
; FN-AG-CAR to CAR, so a goal built from FN-INDEX-MEMBERSHIP-HASP's own
; (already-normalized) unfolding has CAR/CDR by the time this rule would
; apply, and a trigger stated in FN-AG-CAR terms would never match it.
(defthm fn-index-membership-hasp-of-member
  (implies (member-equal membership memberships)
           (fn-index-membership-hasp
            (car membership) (cdr membership) memberships)))

(defthm fn-index-entry-sourcedp-cons
  (implies (fn-index-entry-sourcedp entry articles)
           (fn-index-entry-sourcedp entry (cons article articles))))

(defthm fn-index-soundp-cons-articles
  (implies (fn-index-soundp index articles)
           (fn-index-soundp index (cons article articles)))
  :hints (("Goal" :induct (fn-index-soundp index articles))))

(defthm fn-index-soundp-append-index
  (equal (fn-index-soundp (append xs ys) articles)
         (and (fn-index-soundp xs articles)
              (fn-index-soundp ys articles)))
  :hints (("Goal" :induct (append xs ys))))

(defthm fn-index-membership-entries-sourced
  (implies (and (equal (fn-article-msgid article) msgid)
                (fn-subsetp memberships (fn-article-memberships article)))
           (fn-index-soundp
            (fn-index-membership-entries msgid memberships)
            (cons article rest)))
  :hints (("Goal" :induct (fn-index-membership-entries msgid memberships))))

(defthm fn-index-article-entries-self-sourced
  (fn-index-soundp (fn-index-article-entries article) (cons article rest))
  :hints (("Goal" :use ((:instance fn-index-membership-entries-sourced
                                   (msgid (fn-article-msgid article))
                                   (memberships (fn-article-memberships article)))
                        (:instance fn-subset-self
                                   (groups (fn-article-memberships article))))
           :in-theory (enable fn-index-article-entries))))

(defthm fn-index-build-sound
  (implies (fn-article-listp configured articles)
           (fn-index-soundp (fn-index-build articles) articles))
  :hints (("Goal" :induct (fn-index-build articles))))

(defthm fn-index-memberships-completep-cons-index
  (implies (fn-index-memberships-completep msgid memberships index)
           (fn-index-memberships-completep msgid memberships (cons entry index)))
  :hints (("Goal" :induct (fn-index-memberships-completep msgid memberships index))))

(defthm fn-index-memberships-completep-self
  (fn-index-memberships-completep
   msgid memberships (fn-index-membership-entries msgid memberships))
  :hints (("Goal" :induct (fn-index-membership-entries msgid memberships))))

(defthm fn-index-memberships-completep-append-right
  (implies (fn-index-memberships-completep msgid memberships index)
           (fn-index-memberships-completep msgid memberships (append index more)))
  :hints (("Goal" :induct (fn-index-memberships-completep msgid memberships index))))

(defthm fn-index-memberships-completep-append-left
  (implies (fn-index-memberships-completep msgid memberships index)
           (fn-index-memberships-completep msgid memberships (append more index)))
  :hints (("Goal" :induct (fn-index-memberships-completep msgid memberships index))))

(defthm fn-index-completep-append-left
  (implies (fn-index-completep index2 articles)
           (fn-index-completep (append index1 index2) articles))
  :hints (("Goal" :induct (fn-index-completep index2 articles))))

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
