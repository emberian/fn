; fn: the served readers over the overview COLUMN (lane served-columns,
; 2026-09-27; PRF-332).  Prefix `fn-scol-'.
;
; Never do at read time what could have been done once at write time.  The
; intern decides a row's FACTS once from the article's bytes
; (books/catalog-record.lisp fn-held-facts-of; the open's one parse,
; books/store-intern-once.lisp; the POST's carried parse,
; books/owner-parse-carried.lisp), and since this lane the facts carry the
; overview column (fn-hnov-of: the five RFC 3977 section 8.3.2 fields, the
; parse verdict and the tombstone flag) beside the octet count and the body
; line count.  The served OVER/XOVER, HDR/XHDR and XPAT read that column
; instead of materializing and parsing the payload for every article of a
; range (served-leftovers measured OVER 1-2000 at 9 to 13 ms of owner CPU
; per request in that work).
;
; THE RELATION F (fn-scol-okp fn-arena fn-cat): every catalog row whose
; column is decided (nov non-nil) has exactly the facts of the octets its
; handle names in the arena.  Rows the intern made satisfy it by
; construction (fn-scol-row-okp-of-intern-list); a row made by an entry that
; reads no bytes (books/held-record.lisp fn-held-plain) has no column and
; satisfies it vacuously; the catalog's commit, withdrawal, redecision and
; clear keep it (they never change a row's facts or handle), and so does
; every arena seal while the rows' handles are inside the arena
; (fn-cat-handles-inp, part of books/catalog-relation.lisp's R).  The
; entries' preservation lemmas are below; the owner-level establishment at
; the opens is the same open obligation as the join's (sca-join-4).
;
; THE LOOKUP.  A served reader holds an archive ARTICLE (Message-ID and
; handle), not a row.  fn-scol-facts finds a row of the article's
; Message-ID (the catalog's Message-ID column, one hash-table read) whose
; handle IS the article's handle, and answers its facts when the column is
; decided.  Under F ANY such row's facts are the facts of the article's
; bytes (fn-scol-facts-are-the-bytes-facts), so no uniqueness, join or
; version fact is needed; when no row matches, the reader reads the bytes
; as before.
;
; KEYSTONES (the subject is the per-article reader the served functions
; call; each served twin below is equated to the function it replaces):
;   fn-scol-tombstonep-is-bytes   the column's tombstone flag
;   fn-scol-overview-of-is-bytes  the column's overview tuple = fn-nov-overview
;   fn-scol-hdr-content-is-bytes  the column's HDR content = fn-nntp-hdr-content
; each under F alone.

(in-package "ACL2")
(include-book "catalog")
(include-book "catalog-record")
(include-book "nntp-xref")

(local (in-theory (disable fn-article-parse)))
; A row's column is read through fn-hf-nov-of-held-facts-of, never by
; opening the control list.
(local (in-theory (disable fn-hf-nov)))

; -----------------------------------------------------------------------------
; The relation F.

; A row's column, when decided, is the column of its bytes.
(defun fn-scol-row-okp (row fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (or (not (fn-hf-nov (fn-held-facts row)))
      (equal (fn-held-facts row)
             (fn-held-facts-of (fn-nntp-payload-bytes (fn-record-payload row) fn-arena)))))

(defun fn-scol-rows-okp (rows fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (if (consp rows)
      (and (fn-scol-row-okp (car rows) fn-arena)
           (fn-scol-rows-okp (cdr rows) fn-arena))
    t))

(defun-nx fn-scol-okp (fn-arena fn-cat)
  (and (fn-arena-p fn-arena)
       (fn-scol-rows-okp fn-cat fn-arena)))

(defthm fn-scol-rows-okp-nth
  (implies (and (fn-scol-rows-okp rows fn-arena)
                (natp seq) (< seq (len rows)))
           (fn-scol-row-okp (nth seq rows) fn-arena))
  :hints (("Goal" :in-theory (disable fn-scol-row-okp))))

(in-theory (disable fn-scol-row-okp))

; -----------------------------------------------------------------------------
; The lookup: a row of the article's Message-ID with the article's handle.

(fn-payload-kind fn-scol-find-row :handle "compares each candidate row's handle with H; reads no octets")
(defun fn-scol-find-row (h seqs fn-cat)
  (declare (xargs :stobjs fn-cat :guard t))
  (if (atom seqs)
      nil
    (let ((s (car seqs)))
      (if (and (natp s) (< s (fn-cat-count fn-cat))
               (equal (fn-record-payload (fn-cat-at s fn-cat)) h))
          (fn-cat-at s fn-cat)
        (fn-scol-find-row h (cdr seqs) fn-cat)))))

(defthm fn-scol-find-row-payload
  (implies (fn-scol-find-row h seqs fn-cat)
           (equal (fn-record-payload (fn-scol-find-row h seqs fn-cat)) h)))

(defthm fn-scol-find-row-okp
  (implies (and (fn-scol-rows-okp fn-cat fn-arena)
                (fn-scol-find-row h seqs fn-cat))
           (fn-scol-row-okp (fn-scol-find-row h seqs fn-cat) fn-arena))
  :hints (("Goal" :in-theory (disable fn-cat-at-is-nth fn-cat-count-is-len))
          ("Subgoal *1/2" :use ((:instance fn-scol-rows-okp-nth
                                           (rows fn-cat) (seq (car seqs))))
           :in-theory (e/d (fn-cat-at-is-nth fn-cat-count-is-len)
                           (fn-scol-rows-okp-nth)))))

(in-theory (disable fn-scol-find-row))

; The facts of the article's row when its column is decided, else nil.
(defun fn-scol-facts (article fn-cat)
  (declare (xargs :stobjs fn-cat :guard t))
  (let ((h (fn-article-payload article)))
    (if (natp h)
        (let ((row (fn-scol-find-row h (fn-cat-msgid-seqs (fn-article-msgid article) fn-cat)
                                     fn-cat)))
          (if (and row (fn-hf-nov (fn-held-facts row)))
              (fn-held-facts row)
            nil))
      nil)))

; KEYSTONE (the lookup): under F, facts the lookup answers are the facts of
; the article's bytes.
(defthm fn-scol-facts-are-the-bytes-facts
  (implies (and (fn-scol-okp fn-arena fn-cat)
                (fn-scol-facts article fn-cat))
           (equal (fn-scol-facts article fn-cat)
                  (fn-held-facts-of (fn-nntp-article-bytes article fn-arena))))
  :hints (("Goal" :in-theory (enable fn-scol-row-okp fn-nntp-article-bytes)
           :use ((:instance fn-scol-find-row-okp
                            (h (fn-article-payload article))
                            (seqs (fn-cat-msgid-seqs (fn-article-msgid article) fn-cat)))))))

(in-theory (disable fn-scol-facts))

; -----------------------------------------------------------------------------
; The column's strings render back to the octets they were decided from.

(local
 (defthm fn-scol-octets-chars-are-characters
   (implies (fn-cbor-octet-listp octets)
            (character-listp (fn-record-octets-chars octets)))
   :hints (("Goal" :induct (fn-record-octets-chars octets)
            :in-theory (enable fn-cbor-octet-listp fn-record-octets-chars)))))

(local
 (defthm fn-scol-string-octets-aux-of-octets-chars
   (implies (fn-cbor-octet-listp octets)
            (equal (fn-record-string-octets-aux (fn-record-octets-chars octets))
                   octets))
   :hints (("Goal" :induct (fn-record-octets-chars octets)
            :in-theory (enable fn-cbor-octet-listp fn-cbor-octetp fn-record-octets-chars
                               fn-record-string-octets-aux)))))

(defthm fn-scol-string-octets-of-octets-string
  (implies (fn-cbor-octet-listp octets)
           (equal (fn-record-string-octets (fn-record-octets-string octets))
                  octets))
  :hints (("Goal" :use ((:instance coerce-inverse-1 (x (fn-record-octets-chars octets)))
                        (:instance fn-scol-octets-chars-are-characters))
           :in-theory (enable fn-record-string-octets fn-record-octets-string))))

(local
 (defthm fn-scol-scrub-octets
   (fn-cbor-octet-listp (fn-nov-scrub bytes))
   :hints (("Goal" :induct (fn-nov-scrub bytes)
            :in-theory (enable fn-nov-scrub fn-nov-scrub-byte fn-cbor-octet-listp
                               fn-cbor-octetp)))))

(defthm fn-scol-header-content-octets
  (fn-cbor-octet-listp (fn-nov-header-content view name))
  :hints (("Goal" :in-theory (enable fn-nov-header-content fn-cbor-octet-listp))))

; A column field renders the header content it was decided from.
(defthm fn-scol-hnov-field-renders
  (equal (fn-record-string-octets (fn-hnov-field view name))
         (fn-nov-header-content view name))
  :hints (("Goal" :in-theory (e/d (fn-hnov-field) (fn-nov-header-content)))))

; -----------------------------------------------------------------------------
; The per-article readers.  Each answers from the column when the lookup
; finds a decided row, and reads the bytes exactly as before otherwise.

(local
 (defthm fn-scol-cbor-octets-are-octets
   (implies (fn-cbor-octet-listp x) (fn-octet-listp x))
   :hints (("Goal" :in-theory (enable fn-cbor-octet-listp fn-cbor-octetp fn-octet-listp
                                      fn-octetp)))))

(local
 (defthm fn-scol-arena-nth-octets
   (implies (fn-arn-payload-listp a)
            (fn-cbor-octet-listp (nth h a)))
   :hints (("Goal" :in-theory (enable fn-arn-payload-listp nth fn-cbor-octet-listp)))))

(defthm fn-scol-handle-bytes-octets
  (implies (and (fn-arena-p fn-arena) (natp (fn-article-payload article)))
           (fn-octet-listp (fn-nntp-article-bytes article fn-arena)))
  :hints (("Goal" :in-theory (enable fn-nntp-article-bytes fn-nntp-payload-bytes
                                     fn-arena-p-is-payload-listp))))

; The overview tuple from the column (fn-nov-overview's shape): the five
; fields, the octet count (the arena's O(1) length) and the body lines.
(defun fn-scol-nov-overview (article facts fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (let ((nov (fn-hf-nov facts)))
    (if (fn-hnov-ok nov)
        (list :ok
              (fn-record-string-octets (fn-hnov-subject nov))
              (fn-record-string-octets (fn-hnov-from nov))
              (fn-record-string-octets (fn-hnov-date nov))
              (fn-record-string-octets (fn-hnov-msgid nov))
              (fn-record-string-octets (fn-hnov-references nov))
              (fn-nntp-article-length article fn-arena)
              (fn-hf-body-lines facts))
      (list :error))))

(defthm fn-scol-body-lines-of-held-facts-of
  (equal (fn-hf-body-lines (fn-held-facts-of bytes))
         (fn-hf-body-lines-of bytes))
  :hints (("Goal" :in-theory (e/d (fn-held-facts-of fn-hf-internals)
                                  (fn-hf-body-lines-of fn-hnov-of fn-ctl-control-of
                                   fn-hf-split-index)))))

; The column's facts are read through fn-hf-nov-of-held-facts-of and the
; line count above: the facts' record and its control list stay closed
; (opened, the control list's constructor took this proof to 4.8 million
; steps).
(defthm fn-scol-nov-overview-of-bytes-facts
  (implies (and (fn-arena-p fn-arena) (natp (fn-article-payload article)))
           (equal (fn-scol-nov-overview
                   article (fn-held-facts-of (fn-nntp-article-bytes article fn-arena)) fn-arena)
                  (fn-nov-overview article fn-arena)))
  :hints (("Goal" :in-theory (e/d (fn-nov-overview fn-hnov-of fn-hnov-of-parsed
                                   fn-hnov-parsed-okp fn-hnov-internals
                                   fn-nov-body-line-count fn-hf-body-lines-of-is-nov-body-line-count-by-definition)
                                  (fn-held-facts-of fn-nov-header-content fn-hnov-field fn-nntp-article-bytes
                                   fn-rcl-tombstonep fn-ctl-control-of fn-hf-split-index
                                   fn-hf-body-lines-of fn-nntp-split-article fn-nntp-crlf-lines
                                   fn-nntp-article-length)))))

(defthm fn-scol-facts-handle
  (implies (fn-scol-facts article fn-cat)
           (natp (fn-article-payload article)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-scol-facts))))

(in-theory (disable fn-scol-nov-overview))

; Whether the article is a reclaim tombstone.
(defun fn-scol-tombstonep (article fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard t))
  (let ((facts (fn-scol-facts article fn-cat)))
    (if facts
        (fn-hnov-tomb (fn-hf-nov facts))
      (fn-nntp-article-tombstonep article fn-arena))))

; KEYSTONE.
(defthm fn-scol-tombstonep-is-bytes
  (implies (fn-scol-okp fn-arena fn-cat)
           (equal (fn-scol-tombstonep article fn-arena fn-cat)
                  (fn-nntp-article-tombstonep article fn-arena)))
  :hints (("Goal" :in-theory (e/d (fn-hnov-of fn-hnov-of-parsed fn-hnov-internals)
                                  (fn-held-facts-of fn-scol-okp fn-nntp-article-bytes fn-hnov-field
                                   fn-rcl-tombstonep fn-ctl-control-of fn-hf-split-index
                                   fn-hf-body-lines-of fn-hnov-parsed-okp)))))

(defthm fn-scol-okp-arena-p
  (implies (fn-scol-okp fn-arena fn-cat) (fn-arena-p fn-arena))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-scol-okp))))

; The overview tuple.
(defun fn-scol-overview-of (article fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard t))
  (let ((facts (fn-scol-facts article fn-cat)))
    (if facts
        (fn-scol-nov-overview article facts fn-arena)
      (fn-nov-overview article fn-arena))))

; KEYSTONE.
(defthm fn-scol-overview-of-is-bytes
  (implies (fn-scol-okp fn-arena fn-cat)
           (equal (fn-scol-overview-of article fn-arena fn-cat)
                  (fn-nov-overview article fn-arena)))
  :hints (("Goal" :in-theory (disable fn-scol-okp fn-nov-overview fn-nntp-article-bytes
                                      fn-held-facts-of fn-scol-facts-are-the-bytes-facts
                                      fn-scol-nov-overview-of-bytes-facts)
           :use ((:instance fn-scol-facts-are-the-bytes-facts)
                 (:instance fn-scol-nov-overview-of-bytes-facts)))))

; HDR/XHDR/XPAT content.  A header lookup depends only on the lowercased
; name (books/article.lisp fn-article-field-name-equalp), so a field token
; that lowercases to one of the five overview names reads that column.
(defthm fn-scol-get-headers-aux-by-downcase
  (implies (equal (fn-article-ascii-downcase a) (fn-article-ascii-downcase b))
           (equal (fn-article-get-headers-aux fields a)
                  (fn-article-get-headers-aux fields b)))
  :rule-classes nil
  :hints (("Goal" :induct (fn-article-get-headers-aux fields a)
           :in-theory (enable fn-article-get-headers-aux fn-article-field-name-equalp))))

(defthm fn-scol-header-content-by-downcase
  (implies (equal (fn-article-ascii-downcase a) (fn-article-ascii-downcase b))
           (equal (fn-nov-header-content view a)
                  (fn-nov-header-content view b)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-nov-header-content fn-article-get-headers)
           :use ((:instance fn-scol-get-headers-aux-by-downcase
                            (fields (fn-article-fields view)))))))

(defun fn-scol-field-index (field)
  (declare (xargs :guard t))
  (let ((d (fn-article-ascii-downcase field)))
    (cond ((equal d *fn-nov-subject-name*) 0)
          ((equal d *fn-nov-from-name*) 1)
          ((equal d *fn-nov-date-name*) 2)
          ((equal d *fn-nov-message-id-name*) 3)
          ((equal d *fn-nov-references-name*) 4)
          (t nil))))

(defun fn-scol-field-name (k)
  (declare (xargs :guard t))
  (case k
    (0 *fn-nov-subject-name*)
    (1 *fn-nov-from-name*)
    (2 *fn-nov-date-name*)
    (3 *fn-nov-message-id-name*)
    (otherwise *fn-nov-references-name*)))

(defun fn-scol-hnov-at (k nov)
  (declare (xargs :guard t))
  (case k
    (0 (fn-hnov-subject nov))
    (1 (fn-hnov-from nov))
    (2 (fn-hnov-date nov))
    (3 (fn-hnov-msgid nov))
    (otherwise (fn-hnov-references nov))))

(defthm fn-scol-field-index-names
  (implies (fn-scol-field-index field)
           (equal (fn-article-ascii-downcase field)
                  (fn-article-ascii-downcase (fn-scol-field-name (fn-scol-field-index field))))))

(defun fn-scol-hdr-content (field article fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard t))
  (let ((facts (fn-scol-facts article fn-cat)))
    (cond ((not facts)
           (fn-nntp-hdr-content field article fn-arena))
          ((fn-nntp-hdr-metadata-tokenp field)
           (list :ok
                 (fn-nntp-decimal-field
                  (if (fn-nntp-keywordp field ":BYTES")
                      (fn-nntp-article-length article fn-arena)
                    (fn-hf-body-lines facts)))))
          ((fn-scol-field-index field)
           (let ((nov (fn-hf-nov facts)))
             (if (fn-hnov-ok nov)
                 (list :ok (fn-record-string-octets
                            (fn-scol-hnov-at (fn-scol-field-index field) nov)))
               (list :error))))
          (t (fn-nntp-hdr-content field article fn-arena)))))

(defthm fn-scol-hdr-content-of-bytes-facts
  (implies (and (fn-arena-p fn-arena) (natp (fn-article-payload article))
                (equal facts (fn-held-facts-of (fn-nntp-article-bytes article fn-arena))))
           (equal (let ((nov (fn-hf-nov facts)))
                    (cond ((fn-nntp-hdr-metadata-tokenp field)
                           (list :ok
                                 (fn-nntp-decimal-field
                                  (if (fn-nntp-keywordp field ":BYTES")
                                      (fn-nntp-article-length article fn-arena)
                                    (fn-hf-body-lines facts)))))
                          ((fn-scol-field-index field)
                           (if (fn-hnov-ok nov)
                               (list :ok (fn-record-string-octets
                                          (fn-scol-hnov-at (fn-scol-field-index field) nov)))
                             (list :error)))
                          (t (fn-nntp-hdr-content field article fn-arena))))
                  (fn-nntp-hdr-content field article fn-arena)))
  :hints (("Goal" :in-theory (e/d (fn-nntp-hdr-content fn-hnov-of fn-hnov-of-parsed
                                   fn-hnov-parsed-okp fn-hnov-internals
                                   fn-nov-body-line-count
                                   fn-hf-body-lines-of-is-nov-body-line-count-by-definition)
                                  (fn-held-facts-of fn-nov-header-content fn-hnov-field fn-nntp-article-bytes
                                   fn-rcl-tombstonep fn-ctl-control-of fn-hf-split-index
                                   fn-hf-body-lines-of fn-nntp-split-article fn-nntp-crlf-lines
                                   fn-nntp-article-length fn-scol-field-index-names
                                   fn-nntp-hdr-metadata-tokenp fn-nntp-keywordp
                                   fn-nntp-decimal-field))
           :cases ((fn-scol-field-index field)))
          ("Subgoal 1" :use ((:instance fn-scol-header-content-by-downcase
                                        (view (fn-article-result-article
                                               (fn-article-parse
                                                (fn-nntp-article-bytes article fn-arena))))
                                        (a field)
                                        (b (fn-scol-field-name (fn-scol-field-index field))))
                             (:instance fn-scol-field-index-names)))))

; KEYSTONE.
(defthm fn-scol-hdr-content-is-bytes
  (implies (fn-scol-okp fn-arena fn-cat)
           (equal (fn-scol-hdr-content field article fn-arena fn-cat)
                  (fn-nntp-hdr-content field article fn-arena)))
  :hints (("Goal" :in-theory (disable fn-scol-okp fn-nntp-hdr-content fn-nntp-article-bytes
                                      fn-held-facts-of fn-scol-facts-are-the-bytes-facts
                                      fn-scol-hdr-content-of-bytes-facts
                                      fn-nntp-hdr-metadata-tokenp fn-nntp-keywordp
                                      fn-scol-field-index fn-scol-hnov-at)
           :use ((:instance fn-scol-facts-are-the-bytes-facts)
                 (:instance fn-scol-hdr-content-of-bytes-facts
                            (facts (fn-scol-facts article fn-cat)))))))

(in-theory (disable fn-scol-tombstonep fn-scol-overview-of fn-scol-hdr-content))

; -----------------------------------------------------------------------------
; The served OVER/XOVER arms over the column (books/nntp-xref.lisp's arms
; with the catalog carried; the host's dispatcher reaches them through
; books/served-catalog.lisp fn-nntp-archive-command-cat).  Each is its
; nntp-xref arm with the two per-article reads replaced, and is equated to
; it under F.

(defun fn-nov-served-lines-numbered-col (numbers nidx trie server fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard t))
  (if (consp numbers)
      (let* ((number (car numbers))
             (article (fn-gidx-nidx-number-article number nidx trie))
             (over (if (and (consp article)
                            (not (fn-scol-tombstonep article fn-arena fn-cat)))
                       (fn-scol-overview-of article fn-arena fn-cat)
                     (list :error))))
        (if (fn-nov-okp over)
            (cons (fn-nov-served-line number over server article)
                  (fn-nov-served-lines-numbered-col (cdr numbers) nidx trie server
                                                    fn-arena fn-cat))
          (fn-nov-served-lines-numbered-col (cdr numbers) nidx trie server fn-arena fn-cat)))
    nil))

(defthm fn-nov-served-lines-numbered-col-is-served
  (implies (fn-scol-okp fn-arena fn-cat)
           (equal (fn-nov-served-lines-numbered-col numbers nidx trie server fn-arena fn-cat)
                  (fn-nov-served-lines-numbered numbers nidx trie server fn-arena)))
  :hints (("Goal" :induct (fn-nov-served-lines-numbered-col numbers nidx trie server
                                                             fn-arena fn-cat)
           :in-theory (e/d (fn-nov-served-lines-numbered)
                           (fn-scol-okp fn-nov-overview fn-nov-okp fn-nov-served-line
                            fn-gidx-nidx-number-article fn-nntp-article-tombstonep)))))

(defun fn-nntp-over-range-served-col (session buckets trie token legacyp server fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard t))
  (let ((group (fn-nntp-session-group session))
        (range (fn-nntp-parse-range token)))
    (if (null group)
        (fn-nntp-single session "412 no newsgroup selected")
      (let* ((entries (fn-gidx-bucket group buckets))
             (numbers (fn-nntp-index-group-range-numbers
                       entries group (fn-nntp-range-low range)
                       (fn-nntp-range-high range)))
             (lines (fn-nov-served-lines-numbered-col
                     numbers (fn-gidx-bucket-numbers group buckets) trie
                     server fn-arena fn-cat)))
        (if (consp lines)
            (fn-nntp-multi session "224 overview information follows" lines)
          (fn-nntp-single
           session (if legacyp "420 no article(s) selected"
                     "423 no articles in that range")))))))

(defthm fn-nntp-over-range-served-col-is-served
  (implies (fn-scol-okp fn-arena fn-cat)
           (equal (fn-nntp-over-range-served-col session buckets trie token legacyp server
                                                 fn-arena fn-cat)
                  (fn-nntp-over-range-served session buckets trie token legacyp server
                                             fn-arena)))
  :hints (("Goal" :in-theory (e/d (fn-nntp-over-range-served)
                                  (fn-scol-okp fn-nov-served-lines-numbered-col
                                   fn-nov-served-lines-numbered
                                   fn-gidx-bucket fn-gidx-bucket-numbers
                                   fn-nntp-index-group-range-numbers
                                   fn-nntp-multi fn-nntp-single fn-nntp-parse-range)))))

(defun fn-nntp-over-current-served-col (session archive server fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard t))
  (let ((group (fn-nntp-session-group session))
        (current (fn-nntp-session-current session)))
    (if (null group)
        (fn-nntp-single session "412 no newsgroup selected")
      (if (null current)
          (fn-nntp-single session "420 no current article")
        (let ((article (fn-nntp-available-article
                        group current (fn-state-articles archive))))
          (if (not (consp article))
              (fn-nntp-single session "420 no current article")
            (if (fn-scol-tombstonep article fn-arena fn-cat)
                (fn-nntp-single session "423 article reclaimed")
              (let ((over (fn-scol-overview-of article fn-arena fn-cat)))
                (if (fn-nov-okp over)
                    (fn-nntp-multi session "224 overview information follows"
                                   (list (fn-nov-served-line current over
                                                             server article)))
                  (fn-nntp-single
                   session "503 stored article framing unavailable"))))))))))

(defthm fn-nntp-over-current-served-col-is-served
  (implies (fn-scol-okp fn-arena fn-cat)
           (equal (fn-nntp-over-current-served-col session archive server fn-arena fn-cat)
                  (fn-nntp-over-current-served session archive server fn-arena)))
  :hints (("Goal" :in-theory (e/d (fn-nntp-over-current-served)
                                  (fn-scol-okp fn-nov-overview fn-nov-okp fn-nov-served-line
                                   fn-nntp-available-article fn-nntp-article-tombstonep
                                   fn-nntp-multi fn-nntp-single)))))

(defun fn-nntp-over-msgid-served-col (session archive token server fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard t))
  (let ((article (fn-find-article (fn-nntp-token-string token)
                                  (fn-state-articles archive))))
    (if (not (consp article))
        (fn-nntp-single session "430 no article with that message-id")
      (if (fn-scol-tombstonep article fn-arena fn-cat)
          (fn-nntp-single session "430 article reclaimed")
        (let ((over (fn-scol-overview-of article fn-arena fn-cat)))
          (if (fn-nov-okp over)
              (fn-nntp-multi session "224 overview information follows"
                             (list (fn-nov-served-line 0 over server article)))
            (fn-nntp-single session
                            "503 stored article framing unavailable")))))))

(defthm fn-nntp-over-msgid-served-col-is-served
  (implies (fn-scol-okp fn-arena fn-cat)
           (equal (fn-nntp-over-msgid-served-col session archive token server fn-arena fn-cat)
                  (fn-nntp-over-msgid-served session archive token server fn-arena)))
  :hints (("Goal" :in-theory (e/d (fn-nntp-over-msgid-served)
                                  (fn-scol-okp fn-nov-overview fn-nov-okp fn-nov-served-line
                                   fn-find-article fn-nntp-article-tombstonep
                                   fn-nntp-multi fn-nntp-single)))))

(defun fn-nntp-xref-reply-col (session archive index env keyword args fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard t))
  (cond
   ((and (fn-nntp-keywordp keyword "LIST")
         (fn-nntp-xref-server env)
         (consp args) (null (cdr args))
         (fn-nntp-keyword-tokenp (car args))
         (fn-nntp-keywordp (car args) "OVERVIEW.FMT"))
    (fn-nntp-list-overview-fmt-served session))
   ((and (or (fn-nntp-keywordp keyword "OVER")
             (fn-nntp-keywordp keyword "XOVER"))
         (fn-nntp-xref-server env)
         (fn-gidx-pinp index)
         (consp args) (null (cdr args))
         (fn-nntp-range-okp (fn-nntp-parse-range (car args))))
    (fn-nntp-over-range-served-col
     session (fn-gidx-pin-buckets index) (fn-gidx-pin-trie index)
     (car args) (fn-nntp-keywordp keyword "XOVER") (fn-nntp-xref-server env) fn-arena fn-cat))
   ((and (or (fn-nntp-keywordp keyword "OVER")
             (fn-nntp-keywordp keyword "XOVER"))
         (fn-nntp-xref-server env)
         (null args))
    (fn-nntp-over-current-served-col session archive (fn-nntp-xref-server env) fn-arena fn-cat))
   ((and (fn-nntp-keywordp keyword "OVER")
         (fn-nntp-xref-server env)
         (consp args) (null (cdr args))
         (not (fn-nntp-range-okp (fn-nntp-parse-range (car args))))
         (fn-nntp-message-id-tokenp (car args)))
    (fn-nntp-over-msgid-served-col session archive (car args)
                                   (fn-nntp-xref-server env) fn-arena fn-cat))
   (t nil)))

; KEYSTONE (the served OVER arms): the dispatcher's column arm is the
; nntp-xref arm under F.
(defthm fn-nntp-xref-reply-col-is-xref-reply
  (implies (fn-scol-okp fn-arena fn-cat)
           (equal (fn-nntp-xref-reply-col session archive index env keyword args fn-arena fn-cat)
                  (fn-nntp-xref-reply session archive index env keyword args fn-arena)))
  :hints (("Goal" :in-theory (e/d (fn-nntp-xref-reply)
                                  (fn-scol-okp fn-nntp-keywordp fn-nntp-xref-server
                                   fn-gidx-pinp fn-nntp-parse-range
                                   fn-nntp-range-okp fn-nntp-keyword-tokenp
                                   fn-nntp-message-id-tokenp
                                   fn-nntp-over-range-served
                                   fn-nntp-over-current-served
                                   fn-nntp-over-msgid-served
                                   fn-nntp-over-range-served-col
                                   fn-nntp-over-current-served-col
                                   fn-nntp-over-msgid-served-col
                                   fn-nntp-list-overview-fmt-served)))))

(in-theory (disable fn-nov-served-lines-numbered-col fn-nntp-over-range-served-col
                    fn-nntp-over-current-served-col fn-nntp-over-msgid-served-col
                    fn-nntp-xref-reply-col))

; -----------------------------------------------------------------------------
; F at the catalog's and the arena's transitions.  The catalog's exports
; never change a row's facts or handle; an arena seal appends a payload and
; so leaves every handle inside the arena reading what it read.

(defthm fn-scol-rows-okp-of-append
  (equal (fn-scol-rows-okp (append a b) fn-arena)
         (and (fn-scol-rows-okp a fn-arena) (fn-scol-rows-okp b fn-arena))))

(defthm fn-scol-rows-okp-of-update-nth
  (implies (and (fn-scol-rows-okp rows fn-arena)
                (fn-scol-row-okp row fn-arena)
                (natp seq) (< seq (len rows)))
           (fn-scol-rows-okp (update-nth seq row rows) fn-arena))
  :hints (("Goal" :in-theory (enable update-nth))))

(local
 (defthm fn-scol-row-okp-of-same-facts-and-handle
   (implies (and (fn-scol-row-okp h fn-arena)
                 (equal (fn-held-facts r) (fn-held-facts h))
                 (equal (fn-record-payload r) (fn-record-payload h)))
            (fn-scol-row-okp r fn-arena))
   :hints (("Goal" :in-theory (enable fn-scol-row-okp)))))

(defthm fn-scol-row-okp-of-assign
  (implies (fn-scol-row-okp h fn-arena)
           (fn-scol-row-okp (fn-cat-assign h c) fn-arena))
  :hints (("Goal" :in-theory (enable fn-cat-assign fn-held-with-numbers))))

(defthm fn-scol-okp-of-commit
  (implies (and (fn-scol-okp fn-arena fn-cat)
                (fn-scol-row-okp h fn-arena))
           (fn-scol-okp fn-arena (fn-cat-commit h fn-cat)))
  :hints (("Goal" :in-theory (enable fn-scol-okp))))

(defthm fn-scol-row-okp-of-with-withdrawn
  (implies (fn-scol-row-okp h fn-arena)
           (fn-scol-row-okp (fn-held-with-withdrawn h w) fn-arena))
  :hints (("Goal" :in-theory (enable fn-held-with-withdrawn))))

(defthm fn-scol-okp-of-withdraw
  (implies (and (fn-scol-okp fn-arena fn-cat) (natp target))
           (fn-scol-okp fn-arena (fn-cat-withdraw target by fn-cat)))
  :hints (("Goal" :in-theory (e/d (fn-scol-okp fn-cat-mark-withdrawn)
                                  (fn-held-with-withdrawn fn-scol-rows-okp
                                   fn-scol-row-okp-of-with-withdrawn fn-scol-rows-okp-nth
                                   fn-scol-rows-okp-of-update-nth))
           :use ((:instance fn-scol-rows-okp-of-update-nth
                            (rows fn-cat) (seq target)
                            (row (fn-held-with-withdrawn (nth target fn-cat)
                                                         (cons (len fn-cat) by))))
                 (:instance fn-scol-row-okp-of-with-withdrawn
                            (h (nth target fn-cat)) (w (cons (len fn-cat) by)))
                 (:instance fn-scol-rows-okp-nth (rows fn-cat) (seq target))))))

(defthm fn-scol-okp-of-redecide
  (implies (and (fn-scol-okp fn-arena fn-cat) (natp seq) (< seq (len fn-cat)))
           (fn-scol-okp fn-arena (fn-cat-redecide seq context fn-cat)))
  :hints (("Goal" :in-theory (enable fn-scol-okp fn-held-with-context))))

(defthm fn-scol-okp-of-clear
  (implies (fn-arena-p fn-arena)
           (fn-scol-okp fn-arena (fn-cat-clear fn-cat)))
  :hints (("Goal" :in-theory (enable fn-scol-okp))))

; The arena side.  Every row's handle inside the arena (the list form of
; books/catalog-commit.lisp fn-cat-handles-inp, which R carries).
(defun fn-scol-handles-below (rows n)
  (declare (xargs :guard t))
  (if (consp rows)
      (and (natp (fn-record-payload (car rows)))
           (< (fn-record-payload (car rows)) (nfix n))
           (fn-scol-handles-below (cdr rows) n))
    t))

(local
 (defthm fn-scol-len-append
   (equal (len (append a b)) (+ (len a) (len b)))))

(local
 (defthm fn-scol-nth-append-below
   (implies (and (natp n) (< n (len a)))
            (equal (nth n (append a b)) (nth n a)))
   :hints (("Goal" :in-theory (enable nth)))))

(local
 (defthm fn-scol-nth-append-at
   (equal (nth (len a) (append a (list x))) x)
   :hints (("Goal" :in-theory (enable nth)))))

(local
 (defthm fn-scol-payload-bytes-of-append
   (implies (and (natp p) (< p (len a)))
            (equal (fn-nntp-payload-bytes p (append a b))
                   (fn-nntp-payload-bytes p a)))
   :hints (("Goal" :in-theory (enable fn-nntp-payload-bytes)))))

(defthm fn-scol-rows-okp-of-arena-append
  (implies (and (fn-scol-rows-okp rows a)
                (fn-scol-handles-below rows (len a)))
           (fn-scol-rows-okp rows (append a b)))
  :hints (("Goal" :induct (fn-scol-rows-okp rows a)
           :in-theory (enable fn-scol-row-okp))))

; Every arena seal is an append of one payload (books/payload-arena.lisp
; fn-arena-seal-*-is-append): F survives it while the rows' handles are
; inside the arena.
(defthm fn-scol-okp-of-arena-append
  (implies (and (fn-scol-okp a fn-cat)
                (fn-scol-handles-below fn-cat (len a))
                (fn-arena-p (append a (list xs))))
           (fn-scol-okp (append a (list xs)) fn-cat))
  :hints (("Goal" :in-theory (enable fn-scol-okp))))

(defthm fn-scol-okp-of-seal-list
  (implies (and (fn-scol-okp fn-arena fn-cat)
                (fn-scol-handles-below fn-cat (len fn-arena))
                (fn-cbor-octet-listp xs))
           (fn-scol-okp (fn-arena-seal-list xs fn-arena) fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-arena-p-is-payload-listp) (fn-scol-okp))
           :use ((:instance fn-arn-payload-listp-of-append-one (a fn-arena))))))

; A faithful reseat (the log wrote the payload the handle held) leaves the
; arena as it was (fn-arena-reseat-extent-keeps-a-faithful-arena).
(defthm fn-scol-okp-of-faithful-reseat
  (implies (and (fn-scol-okp fn-arena fn-cat)
                (natp h) (< h (fn-arena-count fn-arena))
                (equal (fn-durable-octets file poff plen) (fn-arena-payload h fn-arena)))
           (fn-scol-okp (fn-arena-reseat-extent h file eoff elen poff plen trailer fn-arena)
                        fn-cat))
  :hints (("Goal" :in-theory (disable fn-scol-okp fn-arena-payload-is-nth fn-arena-count-is-len))))

; The intern: the row the open's list intern makes is decided and
; faithful to the arena its seal makes, and the seal keeps every older row.
(defthm fn-scol-intern-list-facts
  (equal (fn-held-facts (mv-nth 0 (fn-cat-intern-list w keyring generation fn-arena)))
         (fn-held-facts-of (fn-record-payload w)))
  :hints (("Goal" :in-theory (e/d (fn-cat-intern-list)
                                  (fn-held-facts-of fn-held-context-of)))))

(defthm fn-scol-row-okp-of-intern-list
  (implies (and (fn-arena-p fn-arena) (fn-cbor-octet-listp (fn-record-payload w)))
           (fn-scol-row-okp (mv-nth 0 (fn-cat-intern-list w keyring generation fn-arena))
                            (mv-nth 1 (fn-cat-intern-list w keyring generation fn-arena))))
  :hints (("Goal" :in-theory (e/d (fn-scol-row-okp fn-nntp-payload-bytes)
                                  (fn-held-facts-of fn-held-context-of fn-cat-intern-list)))))

(defthm fn-scol-okp-of-intern-list
  (implies (and (fn-scol-okp fn-arena fn-cat)
                (fn-scol-handles-below fn-cat (len fn-arena))
                (fn-cbor-octet-listp (fn-record-payload w)))
           (fn-scol-okp (mv-nth 1 (fn-cat-intern-list w keyring generation fn-arena)) fn-cat))
  :hints (("Goal" :in-theory (disable fn-scol-okp fn-cat-intern-list fn-scol-okp-of-seal-list)
           :use ((:instance fn-scol-okp-of-seal-list (xs (fn-record-payload w)))))))

(in-theory (disable fn-scol-okp))
