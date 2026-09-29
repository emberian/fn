; fn: the Message-ID table, executable (lane paged-history-2, 2026-09-29; row
; P2 of planning/design-paged-history-2026-09-29.md, the second READY; the
; logical side is books/msgid-pages, PRF-957).  Prefix fn-mpxt-.
;
; A stobj holding the table's WORDS in page-store pages: 2048 little-endian
; u64 words a page (`*pgs-page-words*', books/pagestore-words), 1,024 slots
; of two words each, (TAG, SEQ + 1); TAG 0 is an empty slot.  The words are
; the page store's pages so that P8 (the checkpoint as dirty pages) commits
; them as pages with the BLAKE3 digest `pgs-x-words-digest' computes over
; the same words; until then they are resident (the served node has no page
; store yet: host/native/proto-pagestore.lisp is the prototype), which is
; the figure's Message-ID term at 32 octets a record instead of 12,000
; (books/heap-store-figure, when the catalog's hash is deleted).
;
; THE TAG is a natural of the Message-ID: the first eight octets of
; `fn-digest' (BLAKE3, attached in books/crypto-attach) of the Message-ID's
; octets as a little-endian word, floored at 1 (0 is the empty slot).  The
; theorems never depend on it: a tag collision costs a confirmation against
; the row, never a wrong answer (`fn-mpxt-confirm').
;
; THE READER `fn-mpxt-candidates' scans the tag's HOME page (TAG mod the
; page count) whole -- every slot, so no placement invariant is needed --
; and continues to the next page only while the page it scanned was FULL
; (no empty slot), so an entry the writer placed past a full home page is
; always reached.  Each matching SEQ is inserted into an ascending list
; (`fn-mpxt-ins'), so the candidates are ascending by construction, and
; below N whenever every slot's SEQ is (`fn-mpxt-okp').  The page need of a
; lookup is one page plus the run of full pages after the home page; with
; the writer's growth at a load of 1/2 a full page needs 1,024 entries where
; the mean is at most 512 (a Poisson tail below e^-100), so the need is one
; page, at most two, in every non-adversarial store, and the function is
; correct and bounded by the page count in every store (design B.3's L-MPX-
; OVERFLOW; nothing here bounds data, D27).
;
; THE WRITER `fn-mpxt-put' places the entry at the first empty slot of the
; first non-full page from the home page; `fn-mpxt-add' grows the table
; (double the pages, re-place every entry) when the count reaches half the
; slots, so the words are at most 8 a record (32 octets at a load of 1/4).
; The writer's preservation theorems (put and grow keep `fn-mpxt-faithful')
; are the next READY; this book's keystone is the reader's.
;
; KEYSTONE `fn-mpxt-seqs-is-spec-from': under `fn-mpxt-faithful' (every
; slot's SEQ below the row count; every row's own sequence among its tag's
; candidates), the confirmed candidates for MSGID are the sequences of the
; rows whose Message-ID is MSGID, ascending -- the walk `fn-mpxt-spec-from',
; which books/msgid-pages-catalog equates to the catalog's logic function
; `fn-cat$a-msgid-seqs' (the 5u method: the concrete stobj's reader becomes
; this one, the {correspondence} theorem cites that book).

(in-package "ACL2")
(include-book "msgid-pages")
(include-book "crypto-seam")
(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
(local (include-book "arithmetic/top" :dir :system))

;; The tau system is off in this book (lane tau-pass, tools/tau_cost.py).
(local (in-theory (disable (tau-system))))

; -----------------------------------------------------------------------------
; 0. The tag.

(defconst *fn-mpxt-word-limit* (expt 2 64))

; The first K octets of OCTETS as a little-endian natural; an octet outside
; 0..255 is clamped, so the value is below 256^K whatever the list.
(defun fn-mpxt-word (k octets)
  (declare (xargs :guard (and (natp k) (true-listp octets))))
  (if (zp k)
      0
    (+ (min 255 (nfix (car octets)))
       (* 256 (fn-mpxt-word (1- k) (cdr octets))))))

(defthm fn-mpxt-word-natp
  (natp (fn-mpxt-word k octets))
  :rule-classes :type-prescription)

(defthm fn-mpxt-word-bound
  (< (fn-mpxt-word k octets) (expt 256 (nfix k)))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-mpxt-word k octets)
           :expand ((fn-mpxt-word k octets)) :in-theory (enable min))))

(defun fn-mpxt-tag (msgid)
  (declare (xargs :guard t))
  (if (stringp msgid)
      (max 1 (fn-mpxt-word 8 (fn-digest (fn-record-string-octets msgid))))
    1))

(defthm fn-mpxt-tag-posp
  (posp (fn-mpxt-tag msgid))
  :rule-classes :type-prescription)

(defthm fn-mpxt-tag-is-a-word
  (< (fn-mpxt-tag msgid) *fn-mpxt-word-limit*)
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn-mpxt-word-bound
                                   (k 8) (octets (fn-digest (fn-record-string-octets msgid))))))))

(in-theory (disable fn-mpxt-tag))

; -----------------------------------------------------------------------------
; 1. The stobj and the geometry.

(defconst *fn-mpxt-page-words* 2048)
(defconst *fn-mpxt-page-slots* 1024)

(defstobj fn-mpxt
  (fn-mpxt-w :type (array (unsigned-byte 64) (0)) :initially 0 :resizable t)
  (fn-mpxt-pages :type (integer 0 *) :initially 0)
  (fn-mpxt-count :type (integer 0 *) :initially 0)
  :inline t)

;; The stobj's facts, stated over its accessors.
(local (defthm fn-mpxt-wp-nth
  (implies (fn-mpxt-wp l)
           (< (nfix (nth i l)) *fn-mpxt-word-limit*))
  :hints (("Goal" :in-theory (enable nth unsigned-byte-p)))))
(local (defthm fn-mpxt-wp-of-update-nth
  (implies (and (fn-mpxt-wp l) (natp i) (< i (len l)) (unsigned-byte-p 64 v))
           (fn-mpxt-wp (update-nth i v l)))
  :hints (("Goal" :in-theory (enable update-nth)))))
(local (defthm fn-mpxt-len-of-resize-list
  (equal (len (resize-list l n d)) (nfix n))))
(local (defthm fn-mpxt-wp-of-resize-list
  (implies (fn-mpxt-wp l)
           (fn-mpxt-wp (resize-list l n 0)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p)))))
(local (defthm fn-mpxt-wp-true-listp
  (implies (fn-mpxt-wp l) (true-listp l))))

(defthm fn-mpxt-wi-is-a-word
  (implies (fn-mpxtp fn-mpxt)
           (< (nfix (fn-mpxt-wi i fn-mpxt)) *fn-mpxt-word-limit*))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn-mpxt-wp-nth (l (nth *fn-mpxt-wi* fn-mpxt))))
           :in-theory (disable fn-mpxt-wp-nth))))

(defthm fn-mpxtp-of-updates
  (implies (fn-mpxtp fn-mpxt)
           (and (implies (and (natp i) (< i (fn-mpxt-w-length fn-mpxt)) (unsigned-byte-p 64 v))
                         (fn-mpxtp (update-fn-mpxt-wi i v fn-mpxt)))
                (implies (natp n) (fn-mpxtp (resize-fn-mpxt-w n fn-mpxt)))
                (implies (natp n) (fn-mpxtp (update-fn-mpxt-pages n fn-mpxt)))
                (implies (natp n) (fn-mpxtp (update-fn-mpxt-count n fn-mpxt))))))

(defthm fn-mpxt-lengths-of-updates
  (and (implies (and (natp i) (< i (fn-mpxt-w-length fn-mpxt)))
                (equal (fn-mpxt-w-length (update-fn-mpxt-wi i v fn-mpxt)) (fn-mpxt-w-length fn-mpxt)))
       (equal (fn-mpxt-w-length (resize-fn-mpxt-w n fn-mpxt)) (nfix n))
       (equal (fn-mpxt-w-length (update-fn-mpxt-pages n fn-mpxt)) (fn-mpxt-w-length fn-mpxt))
       (equal (fn-mpxt-w-length (update-fn-mpxt-count n fn-mpxt)) (fn-mpxt-w-length fn-mpxt))))

(defthm fn-mpxt-fields-natp
  (implies (fn-mpxtp fn-mpxt)
           (and (natp (fn-mpxt-pages fn-mpxt)) (natp (fn-mpxt-count fn-mpxt))))
  :rule-classes ((:rewrite)
                 (:type-prescription :corollary (implies (fn-mpxtp fn-mpxt) (natp (fn-mpxt-pages fn-mpxt))))
                 (:type-prescription :corollary (implies (fn-mpxtp fn-mpxt) (natp (fn-mpxt-count fn-mpxt))))))

(defthm fn-mpxt-fields-of-updates
  (and (equal (fn-mpxt-pages (update-fn-mpxt-wi i v fn-mpxt)) (fn-mpxt-pages fn-mpxt))
       (equal (fn-mpxt-pages (resize-fn-mpxt-w n fn-mpxt)) (fn-mpxt-pages fn-mpxt))
       (equal (fn-mpxt-pages (update-fn-mpxt-pages n fn-mpxt)) n)
       (equal (fn-mpxt-pages (update-fn-mpxt-count n fn-mpxt)) (fn-mpxt-pages fn-mpxt))
       (equal (fn-mpxt-count (update-fn-mpxt-wi i v fn-mpxt)) (fn-mpxt-count fn-mpxt))
       (equal (fn-mpxt-count (resize-fn-mpxt-w n fn-mpxt)) (fn-mpxt-count fn-mpxt))
       (equal (fn-mpxt-count (update-fn-mpxt-pages n fn-mpxt)) (fn-mpxt-count fn-mpxt))
       (equal (fn-mpxt-count (update-fn-mpxt-count n fn-mpxt)) n)
       (equal (fn-mpxt-wi i (update-fn-mpxt-pages n fn-mpxt)) (fn-mpxt-wi i fn-mpxt))
       (equal (fn-mpxt-wi i (update-fn-mpxt-count n fn-mpxt)) (fn-mpxt-wi i fn-mpxt))
       (implies (and (natp i) (natp j))
                (equal (fn-mpxt-wi i (update-fn-mpxt-wi j v fn-mpxt))
                       (if (equal i j) v (fn-mpxt-wi i fn-mpxt))))))

;; The primitives are closed from here on: every fact about them is above.
(in-theory (disable fn-mpxtp fn-mpxt-wi update-fn-mpxt-wi fn-mpxt-w-length resize-fn-mpxt-w
                    fn-mpxt-pages update-fn-mpxt-pages fn-mpxt-count update-fn-mpxt-count))

; Well formed: the pages fit the words.
(defun fn-mpxt-wfp (fn-mpxt)
  (declare (xargs :stobjs fn-mpxt))
  (<= (* *fn-mpxt-page-words* (fn-mpxt-pages fn-mpxt)) (fn-mpxt-w-length fn-mpxt)))

; The word index of slot J's TAG on page P.
(defun fn-mpxt-slot (p j)
  (declare (xargs :guard (and (natp p) (natp j))))
  (+ (* *fn-mpxt-page-words* p) (* 2 j)))

(defun fn-mpxt-slot-guardp (p j fn-mpxt)
  (declare (xargs :stobjs fn-mpxt))
  (and (natp p) (natp j) (< j *fn-mpxt-page-slots*)
       (< p (fn-mpxt-pages fn-mpxt)) (fn-mpxt-wfp fn-mpxt)))

(defun fn-mpxt-tag-at (p j fn-mpxt)
  (declare (xargs :stobjs fn-mpxt :guard (fn-mpxt-slot-guardp p j fn-mpxt)))
  (nfix (fn-mpxt-wi (fn-mpxt-slot p j) fn-mpxt)))

; The SEQ word: 1 + the sequence; 0 in an empty slot.
(defun fn-mpxt-seq-at (p j fn-mpxt)
  (declare (xargs :stobjs fn-mpxt :guard (fn-mpxt-slot-guardp p j fn-mpxt)))
  (nfix (fn-mpxt-wi (+ 1 (fn-mpxt-slot p j)) fn-mpxt)))

(defthm fn-mpxt-tag-at-natp
  (natp (fn-mpxt-tag-at p j fn-mpxt))
  :rule-classes :type-prescription)

(defthm fn-mpxt-seq-at-natp
  (natp (fn-mpxt-seq-at p j fn-mpxt))
  :rule-classes :type-prescription)

(defthm fn-mpxt-tag-at-is-a-word
  (implies (fn-mpxtp fn-mpxt)
           (< (fn-mpxt-tag-at p j fn-mpxt) *fn-mpxt-word-limit*))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn-mpxt-wi-is-a-word (i (fn-mpxt-slot p j))))
           :in-theory (e/d (fn-mpxt-tag-at) (fn-mpxt-wi-is-a-word)))))

(defthm fn-mpxt-seq-at-is-a-word
  (implies (fn-mpxtp fn-mpxt)
           (< (fn-mpxt-seq-at p j fn-mpxt) *fn-mpxt-word-limit*))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn-mpxt-wi-is-a-word (i (+ 1 (fn-mpxt-slot p j)))))
           :in-theory (e/d (fn-mpxt-seq-at) (fn-mpxt-wi-is-a-word)))))

(in-theory (disable fn-mpxt-tag-at fn-mpxt-seq-at))


; The next page, wrapping.
(defun fn-mpxt-next (p np)
  (declare (xargs :guard (and (natp p) (natp np))))
  (if (< (1+ p) np) (1+ p) 0))

(defthm fn-mpxt-next-below
  (implies (and (natp p) (natp np) (< p np))
           (< (fn-mpxt-next p np) np))
  :rule-classes :linear)

(defthm fn-mpx-home-below
  (implies (and (natp tag) (posp np))
           (< (fn-mpx-home tag np) np))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (fn-mpx-home) (mod))
           :use ((:instance mod-bounded-by-modulus (x tag) (y np))))))

(in-theory (disable fn-mpx-home))

; -----------------------------------------------------------------------------
; 2. The reader.

; Insert S into an ascending list, once.
(defun fn-mpxt-ins (s seqs)
  (declare (xargs :guard (and (natp s) (nat-listp seqs))))
  (cond ((atom seqs) (list s))
        ((< s (car seqs)) (cons s seqs))
        ((equal s (car seqs)) seqs)
        (t (cons (car seqs) (fn-mpxt-ins s (cdr seqs))))))

(defthm fn-mpxt-ins-nat-listp
  (implies (and (natp s) (nat-listp seqs))
           (nat-listp (fn-mpxt-ins s seqs))))

(defthm fn-mpxt-ins-consp
  (consp (fn-mpxt-ins s seqs))
  :rule-classes :type-prescription)

(defthm fn-mpxt-ins-car-above
  (implies (and (natp s) (nat-listp seqs) (< a s)
                (or (atom seqs) (< a (car seqs))))
           (< a (car (fn-mpxt-ins s seqs)))))

(defthm fn-mpxt-ins-ascending
  (implies (and (natp s) (nat-listp seqs) (fn-mpx-ascendingp seqs))
           (fn-mpx-ascendingp (fn-mpxt-ins s seqs)))
  :hints (("Goal" :induct (fn-mpxt-ins s seqs))))

(defthm fn-mpxt-ins-member
  (implies (and (natp s) (nat-listp seqs))
           (iff (member-equal x (fn-mpxt-ins s seqs))
                (or (equal x s) (member-equal x seqs)))))

(defthm fn-mpxt-ins-below
  (implies (and (fn-mpx-below-p seqs n) (< s n))
           (fn-mpx-below-p (fn-mpxt-ins s seqs) n)))

; The slots below J of page P whose TAG is TAG, their SEQs inserted into ACC.
(defun fn-mpxt-scan (tag p j acc fn-mpxt)
  (declare (xargs :stobjs fn-mpxt :measure (nfix j)
                  :guard (and (natp tag) (natp p) (natp j) (<= j *fn-mpxt-page-slots*)
                              (< p (fn-mpxt-pages fn-mpxt)) (fn-mpxt-wfp fn-mpxt)
                              (nat-listp acc))))
  (if (zp j)
      acc
    (let* ((j (1- j))
           (acc (if (and (equal tag (fn-mpxt-tag-at p j fn-mpxt))
                         (<= 1 (fn-mpxt-seq-at p j fn-mpxt)))
                    (fn-mpxt-ins (1- (fn-mpxt-seq-at p j fn-mpxt)) acc)
                  acc)))
      (fn-mpxt-scan tag p j acc fn-mpxt))))

; No empty slot below J on page P.
(defun fn-mpxt-page-fullp (p j fn-mpxt)
  (declare (xargs :stobjs fn-mpxt :measure (nfix j)
                  :guard (and (natp p) (natp j) (<= j *fn-mpxt-page-slots*)
                              (< p (fn-mpxt-pages fn-mpxt)) (fn-mpxt-wfp fn-mpxt))))
  (if (zp j)
      t
    (let ((j (1- j)))
      (and (not (equal 0 (fn-mpxt-tag-at p j fn-mpxt)))
           (fn-mpxt-page-fullp p j fn-mpxt)))))

(defthm fn-mpxt-scan-nat-listp
  (implies (nat-listp acc)
           (nat-listp (fn-mpxt-scan tag p j acc fn-mpxt))))

(defthm fn-mpxt-scan-ascending
  (implies (and (nat-listp acc) (fn-mpx-ascendingp acc))
           (fn-mpx-ascendingp (fn-mpxt-scan tag p j acc fn-mpxt))))

; Scan page P, then the next while the page scanned was full; at most K pages.
(defun fn-mpxt-run (tag p k acc fn-mpxt)
  (declare (xargs :stobjs fn-mpxt :measure (nfix k)
                  :guard (and (natp tag) (natp p) (natp k)
                              (< p (fn-mpxt-pages fn-mpxt)) (fn-mpxt-wfp fn-mpxt)
                              (nat-listp acc))))
  (if (zp k)
      acc
    (let ((acc (fn-mpxt-scan tag p *fn-mpxt-page-slots* acc fn-mpxt)))
      (if (fn-mpxt-page-fullp p *fn-mpxt-page-slots* fn-mpxt)
          (fn-mpxt-run tag (fn-mpxt-next p (fn-mpxt-pages fn-mpxt)) (1- k) acc fn-mpxt)
        acc))))

; THE CANDIDATES: the SEQs tagged TAG on the home page and its full run.
(defun fn-mpxt-candidates (tag fn-mpxt)
  (declare (xargs :stobjs fn-mpxt :guard (and (natp tag) (fn-mpxt-wfp fn-mpxt))))
  (let ((np (fn-mpxt-pages fn-mpxt)))
    (if (zp np)
        nil
      (fn-mpxt-run tag (fn-mpx-home tag np) np nil fn-mpxt))))

; --- ascending and nat-listp by construction ---

(defthm fn-mpxt-run-nat-listp
  (implies (nat-listp acc)
           (nat-listp (fn-mpxt-run tag p k acc fn-mpxt))))

(defthm fn-mpxt-run-ascending
  (implies (and (nat-listp acc) (fn-mpx-ascendingp acc))
           (fn-mpx-ascendingp (fn-mpxt-run tag p k acc fn-mpxt))))

(defthm fn-mpxt-candidates-nat-listp
  (nat-listp (fn-mpxt-candidates tag fn-mpxt)))

(defthm fn-mpxt-candidates-ascending
  (fn-mpx-ascendingp (fn-mpxt-candidates tag fn-mpxt)))

(defthm fn-mpxt-candidates-true-listp
  (true-listp (fn-mpxt-candidates tag fn-mpxt))
  :hints (("Goal" :use fn-mpxt-candidates-nat-listp
           :in-theory (disable fn-mpxt-candidates-nat-listp fn-mpxt-candidates))))

; --- below N under the slot invariant ---

; Every slot below J on page P: empty, or 1 <= SEQ word <= N.
(defun fn-mpxt-page-okp (p j n fn-mpxt)
  (declare (xargs :stobjs fn-mpxt :measure (nfix j)
                  :guard (and (natp p) (natp j) (<= j *fn-mpxt-page-slots*) (natp n)
                              (< p (fn-mpxt-pages fn-mpxt)) (fn-mpxt-wfp fn-mpxt))))
  (if (zp j)
      t
    (let ((j (1- j)))
      (and (or (equal 0 (fn-mpxt-tag-at p j fn-mpxt))
               (and (<= 1 (fn-mpxt-seq-at p j fn-mpxt))
                    (<= (fn-mpxt-seq-at p j fn-mpxt) n)))
           (fn-mpxt-page-okp p j n fn-mpxt)))))

; Every page below P.
(defun fn-mpxt-pages-okp (p n fn-mpxt)
  (declare (xargs :stobjs fn-mpxt :measure (nfix p)
                  :guard (and (natp p) (natp n) (<= p (fn-mpxt-pages fn-mpxt))
                              (fn-mpxt-wfp fn-mpxt))))
  (if (zp p)
      t
    (and (fn-mpxt-page-okp (1- p) *fn-mpxt-page-slots* n fn-mpxt)
         (fn-mpxt-pages-okp (1- p) n fn-mpxt))))

; The slot invariant: every SEQ in the table is below N.
(defun fn-mpxt-okp (n fn-mpxt)
  (declare (xargs :stobjs fn-mpxt :guard (and (natp n) (fn-mpxt-wfp fn-mpxt))))
  (fn-mpxt-pages-okp (fn-mpxt-pages fn-mpxt) n fn-mpxt))

(defthm fn-mpxt-scan-below
  (implies (and (fn-mpxt-page-okp p j n fn-mpxt) (fn-mpx-below-p acc n) (posp tag))
           (fn-mpx-below-p (fn-mpxt-scan tag p j acc fn-mpxt) n))
  :hints (("Goal" :induct (fn-mpxt-scan tag p j acc fn-mpxt))))

(defthm fn-mpxt-pages-okp-page
  (implies (and (fn-mpxt-pages-okp np n fn-mpxt) (natp np) (natp p) (< p np))
           (fn-mpxt-page-okp p *fn-mpxt-page-slots* n fn-mpxt))
  :hints (("Goal" :induct (fn-mpxt-pages-okp np n fn-mpxt))))

(defthm fn-mpxt-run-below
  (implies (and (fn-mpxt-pages-okp (fn-mpxt-pages fn-mpxt) n fn-mpxt)
                (natp (fn-mpxt-pages fn-mpxt))
                (natp p) (< p (fn-mpxt-pages fn-mpxt))
                (fn-mpx-below-p acc n) (posp tag))
           (fn-mpx-below-p (fn-mpxt-run tag p k acc fn-mpxt) n))
  :hints (("Goal" :induct (fn-mpxt-run tag p k acc fn-mpxt)
           :in-theory (disable fn-mpxt-page-okp fn-mpxt-pages-okp fn-mpxt-scan
                               fn-mpxt-page-fullp))))

(defthm fn-mpxt-candidates-below
  (implies (and (fn-mpxt-okp n fn-mpxt) (posp tag))
           (fn-mpx-below-p (fn-mpxt-candidates tag fn-mpxt) n))
  :hints (("Goal" :in-theory (disable fn-mpxt-run fn-mpxt-pages-okp fn-mpx-home))))

; -----------------------------------------------------------------------------
; 3. The confirmation, the walk and the keystone.

; The row at S carries MSGID.
(defun fn-mpxt-hitp (msgid s rows)
  (declare (xargs :guard (and (natp s) (true-listp rows))))
  (equal msgid (fn-record-msgid (nth s rows))))

; The sequences at or after I whose row carries MSGID, ascending: the spec.
(defun fn-mpxt-spec-from (i msgid rows)
  (declare (xargs :guard (and (natp i) (true-listp rows))
                  :measure (nfix (- (len rows) (nfix i)))))
  (if (>= (nfix i) (len rows))
      nil
    (let ((rest (fn-mpxt-spec-from (1+ (nfix i)) msgid rows)))
      (if (fn-mpxt-hitp msgid (nfix i) rows)
          (cons (nfix i) rest)
        rest))))

; Every row at or after I carrying MSGID is among SEQS.
(defun fn-mpxt-complete-from (i msgid seqs rows)
  (declare (xargs :guard (and (natp i) (nat-listp seqs) (true-listp rows))
                  :measure (nfix (- (len rows) (nfix i)))))
  (if (>= (nfix i) (len rows))
      t
    (and (or (not (fn-mpxt-hitp msgid (nfix i) rows))
             (member-equal (nfix i) seqs))
         (fn-mpxt-complete-from (1+ (nfix i)) msgid seqs rows))))

; The candidates whose row carries MSGID.
(defun fn-mpxt-confirm (msgid seqs rows)
  (declare (xargs :guard (and (nat-listp seqs) (true-listp rows))))
  (if (consp seqs)
      (let ((rest (fn-mpxt-confirm msgid (cdr seqs) rows)))
        (if (fn-mpxt-hitp msgid (car seqs) rows)
            (cons (car seqs) rest)
          rest))
    nil))

; THE PAGED READER: the candidates for MSGID's tag, confirmed against the rows.
(defun fn-mpxt-seqs (msgid rows fn-mpxt)
  (declare (xargs :stobjs fn-mpxt :guard (and (true-listp rows) (fn-mpxt-wfp fn-mpxt))))
  (fn-mpxt-confirm msgid (fn-mpxt-candidates (fn-mpxt-tag msgid) fn-mpxt) rows))

; FAITHFUL from I: every row at or after I is among its own tag's candidates.
(defun fn-mpxt-faithful-from (i rows fn-mpxt)
  (declare (xargs :stobjs fn-mpxt
                  :guard (and (natp i) (true-listp rows) (fn-mpxt-wfp fn-mpxt))
                  :measure (nfix (- (len rows) (nfix i)))
                  :guard-hints (("Goal" :in-theory (disable fn-mpxt-candidates)))))
  (if (>= (nfix i) (len rows))
      t
    (and (member-equal (nfix i)
                       (fn-mpxt-candidates (fn-mpxt-tag (fn-record-msgid (nth (nfix i) rows)))
                                           fn-mpxt))
         (fn-mpxt-faithful-from (1+ (nfix i)) rows fn-mpxt))))

; The relation the host establishes at load and every commit keeps.
(defun fn-mpxt-faithful (rows fn-mpxt)
  (declare (xargs :stobjs fn-mpxt :guard (and (true-listp rows) (fn-mpxt-wfp fn-mpxt))))
  (and (fn-mpxt-okp (len rows) fn-mpxt)
       (fn-mpxt-faithful-from 0 rows fn-mpxt)))

; --- faithful gives complete ---

(defthm fn-mpxt-faithful-from-complete
  (implies (fn-mpxt-faithful-from i rows fn-mpxt)
           (fn-mpxt-complete-from i msgid (fn-mpxt-candidates (fn-mpxt-tag msgid) fn-mpxt) rows))
  :hints (("Goal" :induct (fn-mpxt-faithful-from i rows fn-mpxt)
           :in-theory (e/d (fn-mpxt-hitp) (fn-mpxt-candidates)))))

; --- the confirmation of an ascending, complete candidate list is the walk ---

(local
 (defthm fn-mpxt-from-p-member
   (implies (and (fn-mpx-from-p seqs from) (member-equal s seqs))
            (<= from s))
   :rule-classes nil))
(local
 (defthm fn-mpxt-ascending-cdr-from
   (implies (and (fn-mpx-ascendingp seqs) (consp seqs) (nat-listp seqs))
            (fn-mpx-from-p (cdr seqs) (+ 1 (car seqs))))))
(local
 (defthm fn-mpxt-member-of-from-is-car
   (implies (and (fn-mpx-ascendingp seqs) (nat-listp seqs)
                 (fn-mpx-from-p seqs i) (member-equal i seqs))
            (equal (car seqs) i))
   :hints (("Goal" :use ((:instance fn-mpxt-from-p-member
                                    (seqs (cdr seqs)) (from (+ 1 (car seqs))) (s i)))))))
(local
 (defthm fn-mpxt-from-p-monotone
   (implies (and (fn-mpx-from-p seqs from) (natp from) (natp from2) (<= from2 from))
            (fn-mpx-from-p seqs from2))))
(local
 (defthm fn-mpxt-from-p-cdr-when-car-below
   (implies (and (fn-mpx-ascendingp seqs) (fn-mpx-from-p seqs i)
                 (nat-listp seqs) (natp i)
                 (not (equal (car seqs) i)))
            (fn-mpx-from-p seqs (+ 1 i)))
   :hints (("Goal" :in-theory (disable fn-mpx-ascendingp fn-mpxt-from-p-monotone)
            :expand ((fn-mpx-from-p seqs (+ 1 i)) (fn-mpx-from-p seqs i))
            :use (fn-mpxt-ascending-cdr-from
                  (:instance fn-mpxt-from-p-monotone
                             (seqs (cdr seqs)) (from (+ 1 (car seqs))) (from2 (+ 1 i))))))))
(local
 (defthm fn-mpxt-from-p-below-empty
   (implies (and (fn-mpx-from-p seqs i) (fn-mpx-below-p seqs n) (nat-listp seqs)
                 (natp i) (natp n) (<= n i))
            (not (consp seqs)))))
(local
 (defthm fn-mpxt-ascending-cdr
   (implies (fn-mpx-ascendingp seqs)
            (fn-mpx-ascendingp (cdr seqs)))))
(local
 (defthm fn-mpxt-from-p-zero
   (implies (nat-listp seqs) (fn-mpx-from-p seqs 0))))

(local
 (defthm fn-mpxt-complete-from-cdr
   (implies (and (fn-mpxt-complete-from j msgid seqs rows)
                 (natp j) (consp seqs) (natp (car seqs)) (< (car seqs) j))
            (fn-mpxt-complete-from j msgid (cdr seqs) rows))
   :hints (("Goal" :induct (fn-mpxt-complete-from j msgid seqs rows)))))

(local
 (defthm fn-mpxt-complete-from-next
   (implies (and (fn-mpxt-complete-from i msgid seqs rows) (natp i))
            (fn-mpxt-complete-from (+ 1 i) msgid seqs rows))
   :hints (("Goal" :do-not-induct t
            :in-theory (disable fn-mpxt-complete-from fn-mpxt-hitp)
            :expand ((fn-mpxt-complete-from i msgid seqs rows)
                     (fn-mpxt-complete-from (+ 1 i) msgid seqs rows))))))

(local
 (defun fn-mpxt-ind (i seqs rows)
   (declare (xargs :measure (nfix (- (len rows) (nfix i)))))
   (if (>= (nfix i) (len rows))
       (list i seqs)
     (if (and (consp seqs) (equal (car seqs) (nfix i)))
         (fn-mpxt-ind (1+ (nfix i)) (cdr seqs) rows)
       (fn-mpxt-ind (1+ (nfix i)) seqs rows)))))

(local
 (defthm fn-mpxt-confirm-is-spec-from
   (implies (and (natp i) (nat-listp seqs)
                 (fn-mpx-ascendingp seqs)
                 (fn-mpx-from-p seqs i)
                 (fn-mpx-below-p seqs (len rows))
                 (fn-mpxt-complete-from i msgid seqs rows))
            (equal (fn-mpxt-confirm msgid seqs rows)
                   (fn-mpxt-spec-from i msgid rows)))
   :hints (("Goal" :induct (fn-mpxt-ind i seqs rows)
            :do-not '(generalize)
            :in-theory (e/d (fn-mpxt-confirm fn-mpxt-spec-from fn-mpxt-complete-from)
                            (fn-mpxt-hitp fn-mpx-ascendingp))))))

(defthm fn-mpxt-confirm-is-the-spec
  (implies (and (nat-listp seqs)
                (fn-mpx-ascendingp seqs)
                (fn-mpx-below-p seqs (len rows))
                (fn-mpxt-complete-from 0 msgid seqs rows))
           (equal (fn-mpxt-confirm msgid seqs rows)
                  (fn-mpxt-spec-from 0 msgid rows)))
  :hints (("Goal" :use ((:instance fn-mpxt-confirm-is-spec-from (i 0))
                        fn-mpxt-from-p-zero)
           :in-theory (union-theories '(natp (:executable-counterpart natp))
                                      (theory 'minimal-theory)))))

; KEYSTONE: the paged reader is the walk, under the faithful relation.
(defthm fn-mpxt-seqs-is-spec-from
  (implies (fn-mpxt-faithful rows fn-mpxt)
           (equal (fn-mpxt-seqs msgid rows fn-mpxt)
                  (fn-mpxt-spec-from 0 msgid rows)))
  :hints (("Goal" :in-theory (e/d (fn-mpxt-seqs fn-mpxt-faithful)
                                  (fn-mpxt-candidates fn-mpxt-confirm fn-mpxt-faithful-from
                                   fn-mpxt-okp fn-mpxt-spec-from fn-mpxt-complete-from))
           :use ((:instance fn-mpxt-confirm-is-the-spec
                            (seqs (fn-mpxt-candidates (fn-mpxt-tag msgid) fn-mpxt)))
                 (:instance fn-mpxt-faithful-from-complete (i 0))
                 (:instance fn-mpxt-candidates-below (tag (fn-mpxt-tag msgid)) (n (len rows)))
                 (:instance fn-mpxt-candidates-ascending (tag (fn-mpxt-tag msgid)))
                 (:instance fn-mpxt-candidates-nat-listp (tag (fn-mpxt-tag msgid)))))))

; -----------------------------------------------------------------------------
; 4. The writer: put at the first empty slot of the first non-full page of
; the run; grow at a load of 1/2.  (Preservation of `fn-mpxt-faithful': the
; next READY.)

; The least empty slot at or after J on page P, or nil.
(defun fn-mpxt-find-empty (p j fn-mpxt)
  (declare (xargs :stobjs fn-mpxt
                  :guard (and (natp p) (natp j) (< p (fn-mpxt-pages fn-mpxt)) (fn-mpxt-wfp fn-mpxt))
                  :measure (nfix (- *fn-mpxt-page-slots* (nfix j)))))
  (if (>= (nfix j) *fn-mpxt-page-slots*)
      nil
    (if (equal 0 (fn-mpxt-tag-at p (nfix j) fn-mpxt))
        (nfix j)
      (fn-mpxt-find-empty p (1+ (nfix j)) fn-mpxt))))

(defthm fn-mpxt-find-empty-in-page
  (implies (fn-mpxt-find-empty p j fn-mpxt)
           (and (natp (fn-mpxt-find-empty p j fn-mpxt))
                (< (fn-mpxt-find-empty p j fn-mpxt) *fn-mpxt-page-slots*)))
  :rule-classes ((:rewrite)
                 (:linear :corollary (implies (fn-mpxt-find-empty p j fn-mpxt)
                                              (< (fn-mpxt-find-empty p j fn-mpxt) *fn-mpxt-page-slots*)))))

(defun fn-mpxt-write-slot (p j tag seq fn-mpxt)
  (declare (xargs :stobjs fn-mpxt
                  :guard (and (fn-mpxt-slot-guardp p j fn-mpxt)
                              (natp tag) (< tag *fn-mpxt-word-limit*)
                              (natp seq) (< (+ 1 seq) *fn-mpxt-word-limit*))))
  (let* ((fn-mpxt (update-fn-mpxt-wi (fn-mpxt-slot p j) tag fn-mpxt))
         (fn-mpxt (update-fn-mpxt-wi (+ 1 (fn-mpxt-slot p j)) (+ 1 seq) fn-mpxt)))
    fn-mpxt))

(defthm fn-mpxt-write-slot-frame
  (and (equal (fn-mpxt-pages (fn-mpxt-write-slot p j tag seq fn-mpxt)) (fn-mpxt-pages fn-mpxt))
       (equal (fn-mpxt-count (fn-mpxt-write-slot p j tag seq fn-mpxt)) (fn-mpxt-count fn-mpxt))))

(defthm fn-mpxt-write-slot-shape
  (implies (and (fn-mpxtp fn-mpxt) (fn-mpxt-slot-guardp p j fn-mpxt)
                (natp tag) (< tag *fn-mpxt-word-limit*)
                (natp seq) (< (+ 1 seq) *fn-mpxt-word-limit*))
           (and (fn-mpxtp (fn-mpxt-write-slot p j tag seq fn-mpxt))
                (equal (fn-mpxt-w-length (fn-mpxt-write-slot p j tag seq fn-mpxt))
                       (fn-mpxt-w-length fn-mpxt))))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

(in-theory (disable fn-mpxt-write-slot))

; Place (TAG, SEQ) on page P or the next non-full page, at most K pages on;
; (mv placed fn-mpxt).
(defun fn-mpxt-put-run (tag seq p k fn-mpxt)
  (declare (xargs :stobjs fn-mpxt :measure (nfix k)
                  :guard (and (natp tag) (< tag *fn-mpxt-word-limit*)
                              (natp seq) (< (+ 1 seq) *fn-mpxt-word-limit*)
                              (natp p) (natp k) (< p (fn-mpxt-pages fn-mpxt)) (fn-mpxt-wfp fn-mpxt))
                  :guard-hints (("Goal" :in-theory (disable fn-mpxt-find-empty)))))
  (if (zp k)
      (mv nil fn-mpxt)
    (let ((j (fn-mpxt-find-empty p 0 fn-mpxt)))
      (if j
          (let ((fn-mpxt (fn-mpxt-write-slot p j tag seq fn-mpxt)))
            (mv t fn-mpxt))
        (fn-mpxt-put-run tag seq (fn-mpxt-next p (fn-mpxt-pages fn-mpxt)) (1- k) fn-mpxt)))))

(defthm fn-mpxt-put-run-frame
  (and (equal (fn-mpxt-pages (mv-nth 1 (fn-mpxt-put-run tag seq p k fn-mpxt))) (fn-mpxt-pages fn-mpxt))
       (equal (fn-mpxt-count (mv-nth 1 (fn-mpxt-put-run tag seq p k fn-mpxt))) (fn-mpxt-count fn-mpxt))))

(defthm fn-mpxt-put-run-shape
  (implies (and (fn-mpxtp fn-mpxt) (fn-mpxt-wfp fn-mpxt)
                (natp p) (< p (fn-mpxt-pages fn-mpxt))
                (natp tag) (< tag *fn-mpxt-word-limit*)
                (natp seq) (< (+ 1 seq) *fn-mpxt-word-limit*))
           (and (fn-mpxtp (mv-nth 1 (fn-mpxt-put-run tag seq p k fn-mpxt)))
                (equal (fn-mpxt-w-length (mv-nth 1 (fn-mpxt-put-run tag seq p k fn-mpxt)))
                       (fn-mpxt-w-length fn-mpxt))))
  :hints (("Goal" :induct (fn-mpxt-put-run tag seq p k fn-mpxt)
           :in-theory (disable fn-mpxt-find-empty))))

; Place (TAG, SEQ) from its home page; (mv placed fn-mpxt).  Nil only when
; every page is full, which the growth below keeps from happening.
(defun fn-mpxt-put (tag seq fn-mpxt)
  (declare (xargs :stobjs fn-mpxt
                  :guard (and (natp tag) (< tag *fn-mpxt-word-limit*)
                              (natp seq) (< (+ 1 seq) *fn-mpxt-word-limit*)
                              (fn-mpxt-wfp fn-mpxt))))
  (let ((np (fn-mpxt-pages fn-mpxt)))
    (if (zp np)
        (mv nil fn-mpxt)
      (fn-mpxt-put-run tag seq (fn-mpx-home tag np) np fn-mpxt))))

(defthm fn-mpxt-put-frame
  (and (equal (fn-mpxt-pages (mv-nth 1 (fn-mpxt-put tag seq fn-mpxt))) (fn-mpxt-pages fn-mpxt))
       (equal (fn-mpxt-count (mv-nth 1 (fn-mpxt-put tag seq fn-mpxt))) (fn-mpxt-count fn-mpxt))))

(defthm fn-mpxt-put-shape
  (implies (and (fn-mpxtp fn-mpxt) (fn-mpxt-wfp fn-mpxt)
                (natp tag) (< tag *fn-mpxt-word-limit*)
                (natp seq) (< (+ 1 seq) *fn-mpxt-word-limit*))
           (and (fn-mpxtp (mv-nth 1 (fn-mpxt-put tag seq fn-mpxt)))
                (equal (fn-mpxt-w-length (mv-nth 1 (fn-mpxt-put tag seq fn-mpxt)))
                       (fn-mpxt-w-length fn-mpxt))))
  :hints (("Goal" :in-theory (disable fn-mpxt-put-run))))

(in-theory (disable fn-mpxt-put))

; The entries of the slots below J on page P, consed onto ACC.
(defun fn-mpxt-page-entries (p j acc fn-mpxt)
  (declare (xargs :stobjs fn-mpxt :measure (nfix j)
                  :guard (and (natp p) (natp j) (<= j *fn-mpxt-page-slots*)
                              (< p (fn-mpxt-pages fn-mpxt)) (fn-mpxt-wfp fn-mpxt))))
  (if (zp j)
      acc
    (let* ((j (1- j))
           (acc (if (and (not (equal 0 (fn-mpxt-tag-at p j fn-mpxt)))
                         (<= 1 (fn-mpxt-seq-at p j fn-mpxt)))
                    (cons (cons (fn-mpxt-tag-at p j fn-mpxt) (1- (fn-mpxt-seq-at p j fn-mpxt))) acc)
                  acc)))
      (fn-mpxt-page-entries p j acc fn-mpxt))))

; The entries of the pages below P.
(defun fn-mpxt-entries (p acc fn-mpxt)
  (declare (xargs :stobjs fn-mpxt :measure (nfix p)
                  :guard (and (natp p) (<= p (fn-mpxt-pages fn-mpxt)) (fn-mpxt-wfp fn-mpxt))))
  (if (zp p)
      acc
    (fn-mpxt-entries (1- p) (fn-mpxt-page-entries (1- p) *fn-mpxt-page-slots* acc fn-mpxt) fn-mpxt)))

(defun fn-mpxt-entriesp (es)
  (declare (xargs :guard t))
  (if (consp es)
      (and (consp (car es))
           (natp (caar es)) (< (caar es) *fn-mpxt-word-limit*)
           (natp (cdar es)) (< (+ 1 (cdar es)) *fn-mpxt-word-limit*)
           (fn-mpxt-entriesp (cdr es)))
    (null es)))

(defthm fn-mpxt-page-entries-entriesp
  (implies (and (fn-mpxtp fn-mpxt) (fn-mpxt-entriesp acc))
           (fn-mpxt-entriesp (fn-mpxt-page-entries p j acc fn-mpxt))))

(defthm fn-mpxt-entries-entriesp
  (implies (and (fn-mpxtp fn-mpxt) (fn-mpxt-entriesp acc))
           (fn-mpxt-entriesp (fn-mpxt-entries p acc fn-mpxt)))
  :hints (("Goal" :in-theory (disable fn-mpxt-page-entries))))

; Zero every word of the pages below P.
(defun fn-mpxt-zero-words (i fn-mpxt)
  (declare (xargs :stobjs fn-mpxt :measure (nfix i)
                  :guard (and (natp i) (<= i (fn-mpxt-w-length fn-mpxt)))))
  (if (zp i)
      fn-mpxt
    (let ((fn-mpxt (update-fn-mpxt-wi (1- i) 0 fn-mpxt)))
      (fn-mpxt-zero-words (1- i) fn-mpxt))))

(defthm fn-mpxt-zero-words-frame
  (and (equal (fn-mpxt-pages (fn-mpxt-zero-words i fn-mpxt)) (fn-mpxt-pages fn-mpxt))
       (equal (fn-mpxt-count (fn-mpxt-zero-words i fn-mpxt)) (fn-mpxt-count fn-mpxt))))

(defthm fn-mpxt-zero-words-shape
  (implies (and (fn-mpxtp fn-mpxt) (<= i (fn-mpxt-w-length fn-mpxt)))
           (and (fn-mpxtp (fn-mpxt-zero-words i fn-mpxt))
                (equal (fn-mpxt-w-length (fn-mpxt-zero-words i fn-mpxt))
                       (fn-mpxt-w-length fn-mpxt))))
  :hints (("Goal" :induct (fn-mpxt-zero-words i fn-mpxt)
           :in-theory (enable unsigned-byte-p))))

; Re-place every entry of ES.  A placement that fails leaves the entry out:
; growth keeps the slots at least twice the entries, so it never does.
(defun fn-mpxt-put-all (es fn-mpxt)
  (declare (xargs :stobjs fn-mpxt
                  :guard (and (fn-mpxt-entriesp es) (fn-mpxt-wfp fn-mpxt))
                  :guard-hints (("Goal" :in-theory (disable fn-mpxt-put)))))
  (if (consp es)
      (mv-let (placed fn-mpxt)
        (fn-mpxt-put (caar es) (cdar es) fn-mpxt)
        (declare (ignore placed))
        (fn-mpxt-put-all (cdr es) fn-mpxt))
    fn-mpxt))

(defthm fn-mpxt-put-all-frame
  (and (equal (fn-mpxt-pages (fn-mpxt-put-all es fn-mpxt)) (fn-mpxt-pages fn-mpxt))
       (equal (fn-mpxt-count (fn-mpxt-put-all es fn-mpxt)) (fn-mpxt-count fn-mpxt))))

(defthm fn-mpxt-put-all-shape
  (implies (and (fn-mpxtp fn-mpxt) (fn-mpxt-wfp fn-mpxt) (fn-mpxt-entriesp es))
           (and (fn-mpxtp (fn-mpxt-put-all es fn-mpxt))
                (equal (fn-mpxt-w-length (fn-mpxt-put-all es fn-mpxt))
                       (fn-mpxt-w-length fn-mpxt))))
  :hints (("Goal" :induct (fn-mpxt-put-all es fn-mpxt))))

; Double the pages (one from none) and re-place every entry.
(defun fn-mpxt-grow (fn-mpxt)
  (declare (xargs :stobjs fn-mpxt :guard (fn-mpxt-wfp fn-mpxt)
                  :guard-hints (("Goal" :in-theory (disable fn-mpxt-entries fn-mpxt-put-all
                                                            fn-mpxt-zero-words)))))
  (let* ((np (fn-mpxt-pages fn-mpxt))
         (es (fn-mpxt-entries np nil fn-mpxt))
         (np2 (if (zp np) 1 (* 2 np)))
         (fn-mpxt (resize-fn-mpxt-w (* *fn-mpxt-page-words* np2) fn-mpxt))
         (fn-mpxt (fn-mpxt-zero-words (* *fn-mpxt-page-words* np2) fn-mpxt))
         (fn-mpxt (update-fn-mpxt-pages np2 fn-mpxt)))
    (fn-mpxt-put-all es fn-mpxt)))

(defthm fn-mpxt-grow-shape
  (implies (and (fn-mpxtp fn-mpxt) (fn-mpxt-wfp fn-mpxt))
           (and (fn-mpxtp (fn-mpxt-grow fn-mpxt))
                (equal (fn-mpxt-pages (fn-mpxt-grow fn-mpxt))
                       (if (zp (fn-mpxt-pages fn-mpxt)) 1 (* 2 (fn-mpxt-pages fn-mpxt))))
                (equal (fn-mpxt-w-length (fn-mpxt-grow fn-mpxt))
                       (* *fn-mpxt-page-words*
                          (if (zp (fn-mpxt-pages fn-mpxt)) 1 (* 2 (fn-mpxt-pages fn-mpxt)))))
                (equal (fn-mpxt-count (fn-mpxt-grow fn-mpxt)) (fn-mpxt-count fn-mpxt))))
  :hints (("Goal" :in-theory (disable fn-mpxt-entries fn-mpxt-put-all fn-mpxt-zero-words))))

(in-theory (disable fn-mpxt-grow))

; ADD (TAG, SEQ) as the N-th entry: grow at half the slots, then place.
(defun fn-mpxt-add (tag seq fn-mpxt)
  (declare (xargs :stobjs fn-mpxt
                  :guard (and (natp tag) (< tag *fn-mpxt-word-limit*)
                              (natp seq) (< (+ 1 seq) *fn-mpxt-word-limit*)
                              (fn-mpxt-wfp fn-mpxt))
                  :guard-hints (("Goal" :in-theory (disable fn-mpxt-grow fn-mpxt-put)))))
  (let* ((fn-mpxt (if (>= (* 2 (fn-mpxt-count fn-mpxt))
                          (* *fn-mpxt-page-slots* (fn-mpxt-pages fn-mpxt)))
                      (fn-mpxt-grow fn-mpxt)
                    fn-mpxt)))
    (mv-let (placed fn-mpxt)
      (fn-mpxt-put tag seq fn-mpxt)
      (let ((fn-mpxt (if placed (update-fn-mpxt-count (+ 1 (fn-mpxt-count fn-mpxt)) fn-mpxt) fn-mpxt)))
        (mv placed fn-mpxt)))))

(defthm fn-mpxt-add-shape
  (implies (and (fn-mpxtp fn-mpxt) (fn-mpxt-wfp fn-mpxt)
                (natp tag) (< tag *fn-mpxt-word-limit*)
                (natp seq) (< (+ 1 seq) *fn-mpxt-word-limit*))
           (and (fn-mpxtp (mv-nth 1 (fn-mpxt-add tag seq fn-mpxt)))
                (<= (* *fn-mpxt-page-words* (fn-mpxt-pages (mv-nth 1 (fn-mpxt-add tag seq fn-mpxt))))
                    (fn-mpxt-w-length (mv-nth 1 (fn-mpxt-add tag seq fn-mpxt))))))
  :hints (("Goal" :in-theory (disable fn-mpxt-put fn-mpxt-grow))))

(in-theory (disable fn-mpxt-add))

; Empty the table (no pages).
(defun fn-mpxt-clear (fn-mpxt)
  (declare (xargs :stobjs fn-mpxt))
  (let* ((fn-mpxt (update-fn-mpxt-pages 0 fn-mpxt))
         (fn-mpxt (update-fn-mpxt-count 0 fn-mpxt)))
    fn-mpxt))

(defthm fn-mpxt-clear-candidates
  (equal (fn-mpxt-candidates tag (fn-mpxt-clear fn-mpxt)) nil))

(defthm fn-mpxt-clear-faithful-nil
  (fn-mpxt-faithful nil (fn-mpxt-clear fn-mpxt)))
