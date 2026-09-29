; fn: the Message-ID index on pages (lane paged-history, 2026-09-29; row P2
; of planning/design-paged-history-2026-09-29.md, PRF-957).  Prefix fn-mpx-.
;
; The heap holds three Message-ID indexes today (fn-hist$c-mids, the
; catalog's fn-cat$c-msgids, the owner's view trie fn-mxc): 12,000 of the
; 16,096 octets the figure charges a record.  This book is the LOGICAL side
; of their replacement, an open-addressed table of digest tags on 16 KiB
; pages: a table is a list of pages, a page a list of entries (TAG . SEQ),
; an entry names the sequence number of one record whose key Message-ID
; has that tag.  A lookup reads the tag's HOME page (TAG mod the page
; count) and, at an overflow, the next page, merges the two pages' seqs
; for the tag (ascending), and CONFIRMS each candidate against the row's
; exact Message-ID: a tag collision costs one row read, never a wrong
; answer.  Worst case one page a lookup, two at an overflow.
;
; Two layers, so the same proof serves every paged index:
;
;   A. THE INDEXED-ACCESS REFINEMENT (GPT-6's class, reusable): for ANY
;      candidate list of sequence numbers that is ascending, below the
;      history's length, and COMPLETE (holds every sequence whose row has
;      the Message-ID), confirming the candidates against the rows is the
;      specification `fn-cei-article-records-for' (the logic of
;      `fn-hist-msgid-records', books/history-columns), in history order:
;      `fn-mpx-confirm-is-the-records-for'.
;   B. THE PAGES specialise it: `fn-mpx-candidates' (the merge of the home
;      and overflow pages' seqs for the tag) is ascending and below the
;      length whenever every page is (`fn-mpx-table-okp'), and complete
;      whenever the table is FAITHFUL to the rows (`fn-mpx-faithful': every
;      held row's sequence is among its tag's candidates).  KEYSTONE
;      `fn-mpx-records-is-the-records-for': the paged reader equals the heap
;      reader under `fn-mpx-faithful' -- the theorem every moved host line
;      cites (the 5u method, one reader at a time).
;
; The TAG is a constrained function of the Message-ID (section 0): the
; theorems hold for every tag function, because correctness is the
; confirmation's, not the hash's.  The executable half (books/msgid-pages-
; exec, the next READY) instantiates it with the first word of the
; attached BLAKE3 digest (0 reserved for an empty slot) and reads the
; pages from the page store's words; the suffix since the adopted image is
; a resident index merged into the pages at the checkpoint.
;
; Nothing here bounds data (D27): a table has as many pages as its entries
; need; the work of a lookup is two pages and the candidates' rows.

(in-package "ACL2")
(include-book "history-columns")

;; The tau system is off in this book (lane tau-pass, tools/tau_cost.py).
(local (in-theory (disable (tau-system))))

; -----------------------------------------------------------------------------
; 0. The tag: any natural of a Message-ID.  A parameter, not an assumption:
; the local witness is total and the constraint is only its type.

(encapsulate
  (((fn-mpx-tag *) => *))
  (local (defun fn-mpx-tag (msgid) (declare (ignore msgid)) 1))
  (defthm fn-mpx-tag-natp
    (natp (fn-mpx-tag msgid))
    :rule-classes :type-prescription))

; -----------------------------------------------------------------------------
; A. The indexed-access refinement.

; A hit: the row at S is a held article whose Message-ID is MSGID (the
; specification's own test, `fn-cei-article-records-for').
(defun fn-mpx-hitp (msgid s rows)
  (declare (xargs :guard (and (natp s) (true-listp rows))))
  (let ((rec (fn-cei-event-article (nth s rows))))
    (and (fn-held-p rec) (equal msgid (fn-record-msgid rec)))))

; The specification from position I: the records for the sequences at or
; after I, in order.
(defun fn-mpx-spec-from (i msgid rows)
  (declare (xargs :guard (and (natp i) (true-listp rows))
                  :measure (nfix (- (len rows) (nfix i)))))
  (if (>= (nfix i) (len rows))
      nil
    (let ((rest (fn-mpx-spec-from (1+ (nfix i)) msgid rows)))
      (if (fn-mpx-hitp msgid (nfix i) rows)
          (cons (fn-cei-event-article (nth (nfix i) rows)) rest)
        rest))))

(local
 (defthm fn-mpx-nthcdr-cdr
   (implies (natp i)
            (equal (nthcdr (+ 1 i) l) (cdr (nthcdr i l))))))

(local
 (defthm fn-mpx-car-nthcdr
   (implies (natp i)
            (equal (car (nthcdr i l)) (nth i l)))))

(local
 (defthm fn-mpx-consp-nthcdr
   (implies (natp i)
            (iff (consp (nthcdr i l)) (< i (len l))))
   :hints (("Goal" :induct (nthcdr i l)))))

; The specification from 0 is the specification.
(defthm fn-mpx-spec-from-is-records-for
  (implies (natp i)
           (equal (fn-mpx-spec-from i msgid rows)
                  (fn-cei-article-records-for msgid (nthcdr i rows))))
  :hints (("Goal" :induct (fn-mpx-spec-from i msgid rows)
           :in-theory (enable fn-cei-article-records-for))))

; Candidates: strictly ascending naturals, every one at least FROM and
; below N.
(defun fn-mpx-ascendingp (seqs)
  (declare (xargs :guard (nat-listp seqs)))
  (or (atom seqs) (atom (cdr seqs))
      (and (< (car seqs) (cadr seqs)) (fn-mpx-ascendingp (cdr seqs)))))

(defun fn-mpx-from-p (seqs from)
  (declare (xargs :guard (and (nat-listp seqs) (natp from))))
  (or (atom seqs)
      (and (<= from (car seqs)) (fn-mpx-from-p (cdr seqs) from))))

(defun fn-mpx-below-p (seqs n)
  (declare (xargs :guard (and (nat-listp seqs) (natp n))))
  (or (atom seqs)
      (and (< (car seqs) n) (fn-mpx-below-p (cdr seqs) n))))

; Complete from I: every hit at or after I is among the candidates.
(defun fn-mpx-complete-from (i msgid seqs rows)
  (declare (xargs :guard (and (natp i) (nat-listp seqs) (true-listp rows))
                  :measure (nfix (- (len rows) (nfix i)))))
  (if (>= (nfix i) (len rows))
      t
    (and (or (not (fn-mpx-hitp msgid (nfix i) rows))
             (member-equal (nfix i) seqs))
         (fn-mpx-complete-from (1+ (nfix i)) msgid seqs rows))))

; The confirmation: the records at the candidates whose Message-ID is
; MSGID, in candidate order.
(defun fn-mpx-confirm (msgid seqs rows)
  (declare (xargs :guard (and (nat-listp seqs) (true-listp rows))))
  (if (consp seqs)
      (let ((rest (fn-mpx-confirm msgid (cdr seqs) rows)))
        (if (fn-mpx-hitp msgid (car seqs) rows)
            (cons (fn-cei-event-article (nth (car seqs) rows)) rest)
          rest))
    nil))

(local
 (defthm fn-mpx-from-p-member
   (implies (and (fn-mpx-from-p seqs from) (member-equal s seqs))
            (<= from s))
   :rule-classes nil))

(local
 (defthm fn-mpx-ascending-cdr-from
   (implies (and (fn-mpx-ascendingp seqs) (consp seqs) (nat-listp seqs))
            (fn-mpx-from-p (cdr seqs) (+ 1 (car seqs))))))

(local
 (defthm fn-mpx-member-of-from-is-car
   ; ascending, all at least I, I a member: I is the first
   (implies (and (fn-mpx-ascendingp seqs) (nat-listp seqs)
                 (fn-mpx-from-p seqs i) (member-equal i seqs))
            (equal (car seqs) i))
   :hints (("Goal" :use ((:instance fn-mpx-from-p-member
                                    (seqs (cdr seqs)) (from (+ 1 (car seqs))) (s i)))))))

(local
 (defthm fn-mpx-from-p-monotone
   (implies (and (fn-mpx-from-p seqs from) (natp from) (natp from2) (<= from2 from))
            (fn-mpx-from-p seqs from2))))

(local
 (defthm fn-mpx-from-p-cdr-when-car-below
   ; all at least I and the first is not I: all at least I + 1
   (implies (and (fn-mpx-ascendingp seqs) (fn-mpx-from-p seqs i)
                 (nat-listp seqs) (natp i)
                 (not (equal (car seqs) i)))
            (fn-mpx-from-p seqs (+ 1 i)))
   :hints (("Goal" :in-theory (disable fn-mpx-ascendingp fn-mpx-from-p-monotone)
            :expand ((fn-mpx-from-p seqs (+ 1 i)) (fn-mpx-from-p seqs i))
            :use (fn-mpx-ascending-cdr-from
                  (:instance fn-mpx-from-p-monotone
                             (seqs (cdr seqs)) (from (+ 1 (car seqs))) (from2 (+ 1 i))))))))

(local
 (defthm fn-mpx-complete-from-cdr
   ; completeness from J survives dropping a first candidate below J
   (implies (and (fn-mpx-complete-from j msgid seqs rows)
                 (natp j) (consp seqs) (natp (car seqs)) (< (car seqs) j))
            (fn-mpx-complete-from j msgid (cdr seqs) rows))
   :hints (("Goal" :induct (fn-mpx-complete-from j msgid seqs rows)))))

(local
 (defthm fn-mpx-complete-from-next
   (implies (and (fn-mpx-complete-from i msgid seqs rows) (natp i))
            (fn-mpx-complete-from (+ 1 i) msgid seqs rows))
   :hints (("Goal" :do-not-induct t
            :in-theory (disable fn-mpx-complete-from fn-mpx-hitp)
            :expand ((fn-mpx-complete-from i msgid seqs rows)
                     (fn-mpx-complete-from (+ 1 i) msgid seqs rows))))))

(local
 (defthm fn-mpx-from-p-below-empty
   (implies (and (fn-mpx-from-p seqs i) (fn-mpx-below-p seqs n) (nat-listp seqs)
                 (natp i) (natp n) (<= n i))
            (not (consp seqs)))))

(local
 (defthm fn-mpx-ascending-cdr
   (implies (fn-mpx-ascendingp seqs)
            (fn-mpx-ascendingp (cdr seqs)))))

(local
 (defun fn-mpx-ind (i seqs rows)
   (declare (xargs :measure (nfix (- (len rows) (nfix i)))))
   (if (>= (nfix i) (len rows))
       (list i seqs)
     (if (and (consp seqs) (equal (car seqs) (nfix i)))
         (fn-mpx-ind (1+ (nfix i)) (cdr seqs) rows)
       (fn-mpx-ind (1+ (nfix i)) seqs rows)))))

(local
 (defthm fn-mpx-confirm-is-spec-from
   (implies (and (natp i) (nat-listp seqs)
                 (fn-mpx-ascendingp seqs)
                 (fn-mpx-from-p seqs i)
                 (fn-mpx-below-p seqs (len rows))
                 (fn-mpx-complete-from i msgid seqs rows))
            (equal (fn-mpx-confirm msgid seqs rows)
                   (fn-mpx-spec-from i msgid rows)))
   :hints (("Goal" :induct (fn-mpx-ind i seqs rows)
            :do-not '(generalize)
            :in-theory (e/d (fn-mpx-confirm fn-mpx-spec-from fn-mpx-complete-from)
                            (fn-mpx-spec-from-is-records-for fn-mpx-hitp fn-mpx-ascendingp
                             fn-cei-article-records-for))))))

(local
 (defthm fn-mpx-from-p-zero
   (implies (nat-listp seqs) (fn-mpx-from-p seqs 0))))

; THE REFINEMENT: an ascending, in-range, complete candidate list confirmed
; against the rows is the specification.
(defthm fn-mpx-confirm-is-the-records-for
  (implies (and (nat-listp seqs)
                (fn-mpx-ascendingp seqs)
                (fn-mpx-below-p seqs (len rows))
                (fn-mpx-complete-from 0 msgid seqs rows))
           (equal (fn-mpx-confirm msgid seqs rows)
                  (fn-cei-article-records-for msgid rows)))
  :hints (("Goal" :use ((:instance fn-mpx-confirm-is-spec-from (i 0))
                        (:instance fn-mpx-spec-from-is-records-for (i 0))
                        fn-mpx-from-p-zero)
           :in-theory (union-theories '(nthcdr zp natp (:executable-counterpart zp)
                                        (:executable-counterpart natp))
                                      (theory 'minimal-theory)))))

; -----------------------------------------------------------------------------
; B. The pages.

; An entry (TAG . SEQ); a page a list of entries with strictly ascending
; SEQs; a table a list of pages.
(defun fn-mpx-entryp (e)
  (declare (xargs :guard t))
  (and (consp e) (natp (car e)) (natp (cdr e))))

(defun fn-mpx-pagep (page)
  (declare (xargs :guard t))
  (if (consp page)
      (and (fn-mpx-entryp (car page)) (fn-mpx-pagep (cdr page)))
    (null page)))

(defun fn-mpx-tablep (tab)
  (declare (xargs :guard t))
  (if (consp tab)
      (and (fn-mpx-pagep (car tab)) (fn-mpx-tablep (cdr tab)))
    (null tab)))

; The seqs of a page's entries tagged TAG, in page order.
(defun fn-mpx-page-seqs (tag page)
  (declare (xargs :guard (fn-mpx-pagep page)))
  (if (consp page)
      (if (equal tag (car (car page)))
          (cons (cdr (car page)) (fn-mpx-page-seqs tag (cdr page)))
        (fn-mpx-page-seqs tag (cdr page)))
    nil))

(defun fn-mpx-page-seq-list (page)
  (declare (xargs :guard (fn-mpx-pagep page)))
  (if (consp page)
      (cons (cdr (car page)) (fn-mpx-page-seq-list (cdr page)))
    nil))

; Every page's seqs ascending and below N.
(defun fn-mpx-table-okp (tab n)
  (declare (xargs :guard (and (fn-mpx-tablep tab) (natp n))))
  (if (consp tab)
      (and (fn-mpx-ascendingp (fn-mpx-page-seq-list (car tab)))
           (fn-mpx-below-p (fn-mpx-page-seq-list (car tab)) n)
           (fn-mpx-table-okp (cdr tab) n))
    t))

; The merge of two ascending lists.
(defun fn-mpx-merge (a b)
  (declare (xargs :guard (and (nat-listp a) (nat-listp b))
                  :measure (+ (len a) (len b))))
  (cond ((atom a) b)
        ((atom b) a)
        ((< (car a) (car b)) (cons (car a) (fn-mpx-merge (cdr a) b)))
        ((< (car b) (car a)) (cons (car b) (fn-mpx-merge a (cdr b))))
        (t (cons (car a) (fn-mpx-merge (cdr a) (cdr b))))))

; The home page of a tag, and the overflow page after it (wrapping).
(defun fn-mpx-home (tag npages)
  (declare (xargs :guard (and (natp tag) (natp npages))))
  (if (zp npages) 0 (nfix (mod tag npages))))

(defthm fn-mpx-home-natp
  (natp (fn-mpx-home tag npages))
  :rule-classes :type-prescription)

(defun fn-mpx-page (i tab)
  (declare (xargs :guard (and (natp i) (fn-mpx-tablep tab))))
  (if (< i (len tab)) (nth i tab) nil))

(local
 (defthm fn-mpx-page-seqs-nat-listp
   (implies (fn-mpx-pagep page)
            (nat-listp (fn-mpx-page-seqs tag page)))))

(local
 (defthm fn-mpx-page-seq-list-nat-listp
   (implies (fn-mpx-pagep page)
            (nat-listp (fn-mpx-page-seq-list page)))))

(local
 (defthm fn-mpx-merge-nat-listp
   (implies (and (nat-listp a) (nat-listp b))
            (nat-listp (fn-mpx-merge a b)))))

(local
 (defthm fn-mpx-nth-tablep
   (implies (and (fn-mpx-tablep tab) (natp i) (< i (len tab)))
            (fn-mpx-pagep (nth i tab)))))

(local
 (defthm fn-mpx-page-pagep
   (implies (and (fn-mpx-tablep tab) (natp i))
            (fn-mpx-pagep (fn-mpx-page i tab)))))

; The candidates for a tag: the home page's seqs merged with the overflow
; page's (the page after the home page; none when the table is one page).
(defun fn-mpx-candidates (tag tab)
  (declare (xargs :guard (and (natp tag) (fn-mpx-tablep tab))
                  :guard-hints (("Goal" :in-theory (disable fn-mpx-page fn-mpx-page-seqs
                                                            fn-mpx-merge fn-mpx-home)))))
  (let* ((n (len tab))
         (h (fn-mpx-home tag n)))
    (fn-mpx-merge (fn-mpx-page-seqs tag (fn-mpx-page h tab))
                  (if (< 1 n)
                      (fn-mpx-page-seqs tag (fn-mpx-page (fn-mpx-home (+ 1 h) n) tab))
                    nil))))

(defthm fn-mpx-candidates-nat-listp
  (implies (fn-mpx-tablep tab)
           (nat-listp (fn-mpx-candidates tag tab)))
  :hints (("Goal" :in-theory (e/d (fn-mpx-candidates)
                                  (fn-mpx-page fn-mpx-page-seqs fn-mpx-merge fn-mpx-home
                                   fn-mpx-tablep fn-mpx-table-okp fn-mpx-page-seq-list)))))

; THE PAGED READER: the candidates for the Message-ID's tag, confirmed.
(defun fn-mpx-records (msgid tab rows)
  (declare (xargs :guard (and (fn-mpx-tablep tab) (true-listp rows))))
  (fn-mpx-confirm msgid (fn-mpx-candidates (fn-mpx-tag msgid) tab) rows))

(local
 (defthm fn-mpx-nat-listp-true-listp
   (implies (nat-listp x) (true-listp x))))

; FAITHFUL from I: every held row's sequence at or after I is among its own
; tag's candidates.
(defun fn-mpx-faithful-from (i tab rows)
  (declare (xargs :guard (and (natp i) (fn-mpx-tablep tab) (true-listp rows))
                  :measure (nfix (- (len rows) (nfix i)))
                  :guard-hints (("Goal" :in-theory (disable fn-mpx-candidates fn-mpx-tablep
                                                            fn-mpx-hitp fn-cei-event-article)))))
  (if (>= (nfix i) (len rows))
      t
    (and (let ((rec (fn-cei-event-article (nth (nfix i) rows))))
           (or (not (fn-held-p rec))
               (member-equal (nfix i)
                             (fn-mpx-candidates (fn-mpx-tag (fn-record-msgid rec)) tab))))
         (fn-mpx-faithful-from (1+ (nfix i)) tab rows))))

; The relation the host establishes at adoption and every commit keeps.
(defun fn-mpx-faithful (tab rows)
  (declare (xargs :guard (and (fn-mpx-tablep tab) (true-listp rows))))
  (and (fn-mpx-table-okp tab (len rows))
       (fn-mpx-faithful-from 0 tab rows)))

; --- the candidates are nat-listp, ascending and below N ---

(local
 (defthm fn-mpx-page-seqs-sublist-from
   (implies (fn-mpx-from-p (fn-mpx-page-seq-list page) from)
            (fn-mpx-from-p (fn-mpx-page-seqs tag page) from))))

(local
 (defthm fn-mpx-from-p-cons-ascending
   ; a head below every element of an ascending rest: ascending
   (implies (and (fn-mpx-from-p rest (+ 1 x)) (fn-mpx-ascendingp rest)
                 (nat-listp rest) (natp x))
            (fn-mpx-ascendingp (cons x rest)))
   :hints (("Goal" :expand ((fn-mpx-ascendingp (cons x rest)) (fn-mpx-from-p rest (+ 1 x)))))))

(local
 (defthm fn-mpx-ascending-from-car
   ; an ascending list is at least any bound its head meets
   (implies (and (fn-mpx-ascendingp l) (nat-listp l) (consp l) (natp from) (<= from (car l)))
            (fn-mpx-from-p l from))
   :hints (("Goal" :expand ((fn-mpx-from-p l from))
            :in-theory (disable fn-mpx-ascendingp fn-mpx-from-p-monotone)
            :use (fn-mpx-ascending-cdr-from
                  (:instance fn-mpx-from-p-monotone (seqs (cdr l)) (from (+ 1 (car l))) (from2 from)))))))

(local
 (defthm fn-mpx-ascending-of-cons
   (implies (fn-mpx-ascendingp (cons x l))
            (fn-mpx-ascendingp l))
   :hints (("Goal" :expand ((fn-mpx-ascendingp (cons x l)))))))

(local
 (defthm fn-mpx-ascending-cons-from
   (implies (and (fn-mpx-ascendingp (cons x l)) (nat-listp l) (natp x))
            (fn-mpx-from-p l (+ 1 x)))
   :hints (("Goal" :expand ((fn-mpx-ascendingp (cons x l)) (fn-mpx-from-p l (+ 1 x)))
            :in-theory (disable fn-mpx-ascendingp fn-mpx-from-p-monotone)
            :use ((:instance fn-mpx-ascending-cdr-from (seqs l))
                  (:instance fn-mpx-from-p-monotone (seqs (cdr l)) (from (+ 1 (car l))) (from2 (+ 1 x))))))))

(local
 (defthm fn-mpx-page-seqs-ascending
   (implies (and (fn-mpx-pagep page)
                 (fn-mpx-ascendingp (fn-mpx-page-seq-list page)))
            (fn-mpx-ascendingp (fn-mpx-page-seqs tag page)))
   :hints (("Goal" :induct (fn-mpx-page-seqs tag page)
            :in-theory (disable fn-mpx-ascendingp)
            :expand ((fn-mpx-page-seq-list page))))))

(local
 (defthm fn-mpx-page-seqs-below
   (implies (fn-mpx-below-p (fn-mpx-page-seq-list page) n)
            (fn-mpx-below-p (fn-mpx-page-seqs tag page) n))))

(local
 (defthm fn-mpx-nth-page-okp
   (implies (and (fn-mpx-table-okp tab n) (natp i) (< i (len tab)))
            (and (fn-mpx-ascendingp (fn-mpx-page-seq-list (nth i tab)))
                 (fn-mpx-below-p (fn-mpx-page-seq-list (nth i tab)) n)))))

(local
 (defthm fn-mpx-merge-from
   (implies (and (fn-mpx-from-p a from) (fn-mpx-from-p b from))
            (fn-mpx-from-p (fn-mpx-merge a b) from))))

(local
 (defthm fn-mpx-ascending-is-from-cadr
   (implies (and (fn-mpx-ascendingp seqs) (nat-listp seqs) (consp seqs))
            (fn-mpx-from-p (cdr seqs) (+ 1 (car seqs))))))

(local
 (defthm fn-mpx-ascending-cdr-from-le
   ; the rest of an ascending list is at least any bound within one of its head
   (implies (and (fn-mpx-ascendingp l) (nat-listp l) (consp l)
                 (natp from) (<= from (+ 1 (car l))))
            (fn-mpx-from-p (cdr l) from))
   :hints (("Goal" :in-theory (disable fn-mpx-ascendingp fn-mpx-from-p-monotone)
            :use ((:instance fn-mpx-ascending-cdr-from (seqs l))
                  (:instance fn-mpx-from-p-monotone (seqs (cdr l)) (from (+ 1 (car l))) (from2 from)))))))

(local
 (defthm fn-mpx-merge-ascending
   (implies (and (nat-listp a) (nat-listp b)
                 (fn-mpx-ascendingp a) (fn-mpx-ascendingp b))
            (fn-mpx-ascendingp (fn-mpx-merge a b)))
   :hints (("Goal" :induct (fn-mpx-merge a b)
            :in-theory (disable fn-mpx-ascendingp)
            :expand ((fn-mpx-merge a b)
                     (fn-mpx-from-p b (+ 1 (car a)))
                     (fn-mpx-from-p a (+ 1 (car b))))))))

(local
 (defthm fn-mpx-merge-below
   (implies (and (fn-mpx-below-p a n) (fn-mpx-below-p b n))
            (fn-mpx-below-p (fn-mpx-merge a b) n))))

(local
 (defthm fn-mpx-page-of-okp
   (implies (and (fn-mpx-table-okp tab n) (natp i))
            (and (fn-mpx-ascendingp (fn-mpx-page-seq-list (fn-mpx-page i tab)))
                 (fn-mpx-below-p (fn-mpx-page-seq-list (fn-mpx-page i tab)) n)))))

(defthm fn-mpx-candidates-ascending
  (implies (and (fn-mpx-tablep tab) (fn-mpx-table-okp tab n))
           (fn-mpx-ascendingp (fn-mpx-candidates tag tab)))
  :hints (("Goal" :in-theory (e/d (fn-mpx-candidates)
                                  (fn-mpx-page fn-mpx-page-seqs fn-mpx-merge fn-mpx-home
                                   fn-mpx-tablep fn-mpx-table-okp fn-mpx-page-seq-list)))))

(defthm fn-mpx-candidates-below
  (implies (and (fn-mpx-tablep tab) (fn-mpx-table-okp tab n))
           (fn-mpx-below-p (fn-mpx-candidates tag tab) n))
  :hints (("Goal" :in-theory (e/d (fn-mpx-candidates)
                                  (fn-mpx-page fn-mpx-page-seqs fn-mpx-merge fn-mpx-home
                                   fn-mpx-tablep fn-mpx-table-okp fn-mpx-page-seq-list)))))

; --- faithful gives completeness for every Message-ID ---

(local
 (defthm fn-mpx-faithful-from-complete
   (implies (and (fn-mpx-faithful-from i tab rows) (natp i))
            (fn-mpx-complete-from i msgid (fn-mpx-candidates (fn-mpx-tag msgid) tab) rows))
   :hints (("Goal" :induct (fn-mpx-faithful-from i tab rows)
            :in-theory (e/d (fn-mpx-faithful-from fn-mpx-complete-from fn-mpx-hitp)
                            (fn-mpx-candidates fn-mpx-tablep fn-cei-event-article
                             fn-held-p fn-record-msgid))))))

; KEYSTONE (PRF-957): the paged reader is the heap reader's logic.  The
; host's `fn-hist-msgid-records' is `fn-cei-article-records-for' over the
; history (books/history-columns `fn-hist$a-msgid-records'), so every host
; line that reads a Message-ID may read the pages instead under
; `fn-mpx-faithful'.
(defthm fn-mpx-records-is-the-records-for
  (implies (and (fn-mpx-tablep tab)
                (fn-mpx-faithful tab rows))
           (equal (fn-mpx-records msgid tab rows)
                  (fn-cei-article-records-for msgid rows)))
  :hints (("Goal" :in-theory (e/d (fn-mpx-records fn-mpx-faithful)
                                  (fn-mpx-candidates fn-mpx-confirm fn-mpx-faithful-from
                                   fn-mpx-table-okp fn-cei-article-records-for))
           :use ((:instance fn-mpx-confirm-is-the-records-for
                            (seqs (fn-mpx-candidates (fn-mpx-tag msgid) tab)))
                 (:instance fn-mpx-faithful-from-complete (i 0))
                 (:instance fn-mpx-candidates-ascending (tag (fn-mpx-tag msgid)) (n (len rows)))
                 (:instance fn-mpx-candidates-below (tag (fn-mpx-tag msgid)) (n (len rows)))
                 (:instance fn-mpx-candidates-nat-listp (tag (fn-mpx-tag msgid)))))))

; The same, stated against the abstract stobj's logic function.
(defthm fn-mpx-records-is-hist-msgid-records
  (implies (and (fn-mpx-tablep tab)
                (fn-mpx-faithful tab fn-hist$a))
           (equal (fn-mpx-records msgid tab fn-hist$a)
                  (fn-hist$a-msgid-records msgid fn-hist$a)))
  :hints (("Goal" :in-theory (e/d (fn-hist$a-msgid-records)
                                  (fn-mpx-records fn-mpx-faithful fn-cei-article-records-for)))))
