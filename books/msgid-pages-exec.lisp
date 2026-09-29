; fn: the Message-ID table, executable (lane paged-history-2, 2026-09-29; row
; P2 of planning/design-paged-history-2026-09-29.md, the second READY; the
; logical side is books/msgid-pages, PRF-957).  Prefix fn-mpxt-.
;
; A stobj holding the table's WORDS in page-store pages: 2048 little-endian
; u64 words a page (`*pgs-page-words*', books/pagestore-words), 1,024 slots
; a page in two columns: slot J's TAG is word J and its SEQ + 1 is word
; 1024 + J (a column read is one word; the tag scan reads one contiguous
; 8 KiB run); TAG 0 is an empty slot.  The words are
; the page store's pages so that P8 (the checkpoint as dirty pages) commits
; them as pages with the BLAKE3 digest `pgs-x-words-digest' computes over
; the same words; until then they are resident (the served node has no page
; store yet: host/native/proto-pagestore.lisp is the prototype), which is
; the figure's Message-ID term at 32 octets a record instead of 12,000
; (books/heap-store-figure, when the catalog's hash is deleted).
;
; THE TAG is a natural of the Message-ID under the table's KEY (ember's
; PKT-774 ruling, row W2b): the first eight octets of the BLAKE3 keyed hash
; (`fn-ns-mac', books/node-secret: keyed_hash under a 32-octet key) of the
; Message-ID's octets as a little-endian word, floored at 1 (0 is the empty
; slot).  The key is a purpose key of the node secret (`fn-mpxt-key-of-
; entry': BLAKE3 derive_key over the current entry's root and identity under
; the label "fn/msgid-index/v1", which differs from the cancel-lock and
; posting-account labels by definition), set into an emptied table at the
; open (`fn-mpxt-set-key') and kept through every write (the -key frame
; clauses).  Nobody outside the node can compute a Message-ID's home page,
; so filling a home page and its overflow takes 2,048 entries whose tags the
; adversary cannot choose.  The theorems never depend on the tag's value: a
; tag collision costs a confirmation against the row, never a wrong answer
; (`fn-mpxt-confirm'); section 6 states the page need.
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
(include-book "node-secret")
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

(defconst *fn-mpxt-key-octets* 32)

; "fn/msgid-index/v1": the purpose label of the table's key.
(defconst *fn-mpxt-key-info*
  '(102 110 47 109 115 103 105 100 45 105 110 100 101 120 47 118 49))

; The table's key from a node-secret entry (the ring's current one).
(defun fn-mpxt-key-of-entry (entry)
  (declare (xargs :guard t))
  (fn-ns-purpose-key entry *fn-mpxt-key-info*))

(defthm fn-mpxt-key-of-entry-shape
  (and (true-listp (fn-mpxt-key-of-entry entry))
       (equal (len (fn-mpxt-key-of-entry entry)) 32)
       (fn-b3-octet-listp (fn-mpxt-key-of-entry entry))))

(defthm fn-mpxt-key-info-separate-by-definition
  (and (not (equal *fn-mpxt-key-info* *fn-ns-cancel-lock-info*))
       (not (equal *fn-mpxt-key-info* *fn-ns-posting-account-info*)))
  :rule-classes nil)

(in-theory (disable fn-mpxt-key-of-entry))

; THE KEYED TAG.
(defun fn-mpxt-tag (msgid key)
  (declare (xargs :guard t))
  (if (stringp msgid)
      (max 1 (fn-mpxt-word 8 (fn-ns-mac key (fn-record-string-octets msgid))))
    1))

(defthm fn-mpxt-tag-posp
  (posp (fn-mpxt-tag msgid key))
  :rule-classes :type-prescription)

(defthm fn-mpxt-tag-is-a-word
  (< (fn-mpxt-tag msgid key) *fn-mpxt-word-limit*)
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn-mpxt-word-bound
                                   (k 8) (octets (fn-ns-mac key (fn-record-string-octets msgid))))))))

(in-theory (disable fn-mpxt-tag))

; -----------------------------------------------------------------------------
; 1. The stobj and the geometry.

(defconst *fn-mpxt-page-words* 2048)
(defconst *fn-mpxt-page-slots* 1024)

(defstobj fn-mpxt
  (fn-mpxt-w :type (array (unsigned-byte 64) (0)) :initially 0 :resizable t)
  (fn-mpxt-pages :type (integer 0 *) :initially 0)
  (fn-mpxt-count :type (integer 0 *) :initially 0)
  (fn-mpxt-key :type (array (unsigned-byte 8) (32)) :initially 0)
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
(local (defthm fn-mpxt-keyp-of-update-nth
  (implies (and (fn-mpxt-keyp l) (natp i) (< i (len l)) (unsigned-byte-p 8 v))
           (fn-mpxt-keyp (update-nth i v l)))
  :hints (("Goal" :in-theory (enable update-nth)))))
(local (defthm fn-mpxt-keyp-nth
  (implies (and (fn-mpxt-keyp l) (natp i) (< i (len l)))
           (unsigned-byte-p 8 (nth i l)))
  :hints (("Goal" :in-theory (enable nth)))))

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
                (implies (natp n) (fn-mpxtp (update-fn-mpxt-count n fn-mpxt)))
                (implies (and (natp i) (< i *fn-mpxt-key-octets*) (unsigned-byte-p 8 v))
                         (fn-mpxtp (update-fn-mpxt-keyi i v fn-mpxt))))))

(defthm fn-mpxt-key-length-is-32
  (implies (fn-mpxtp fn-mpxt)
           (equal (fn-mpxt-key-length fn-mpxt) *fn-mpxt-key-octets*)))

(defthm fn-mpxt-keyi-is-an-octet
  (implies (and (fn-mpxtp fn-mpxt) (natp i) (< i *fn-mpxt-key-octets*))
           (unsigned-byte-p 8 (fn-mpxt-keyi i fn-mpxt))))

(defthm fn-mpxt-lengths-of-updates
  (and (implies (and (natp i) (< i (fn-mpxt-w-length fn-mpxt)))
                (equal (fn-mpxt-w-length (update-fn-mpxt-wi i v fn-mpxt)) (fn-mpxt-w-length fn-mpxt)))
       (equal (fn-mpxt-w-length (resize-fn-mpxt-w n fn-mpxt)) (nfix n))
       (equal (fn-mpxt-w-length (update-fn-mpxt-pages n fn-mpxt)) (fn-mpxt-w-length fn-mpxt))
       (equal (fn-mpxt-w-length (update-fn-mpxt-count n fn-mpxt)) (fn-mpxt-w-length fn-mpxt))
       (equal (fn-mpxt-w-length (update-fn-mpxt-keyi i v fn-mpxt)) (fn-mpxt-w-length fn-mpxt))))

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
       (equal (fn-mpxt-wi i (update-fn-mpxt-keyi j v fn-mpxt)) (fn-mpxt-wi i fn-mpxt))
       (equal (fn-mpxt-pages (update-fn-mpxt-keyi j v fn-mpxt)) (fn-mpxt-pages fn-mpxt))
       (equal (fn-mpxt-count (update-fn-mpxt-keyi j v fn-mpxt)) (fn-mpxt-count fn-mpxt))
       (equal (fn-mpxt-keyi i (update-fn-mpxt-wi j v fn-mpxt)) (fn-mpxt-keyi i fn-mpxt))
       (equal (fn-mpxt-keyi i (resize-fn-mpxt-w n fn-mpxt)) (fn-mpxt-keyi i fn-mpxt))
       (equal (fn-mpxt-keyi i (update-fn-mpxt-pages n fn-mpxt)) (fn-mpxt-keyi i fn-mpxt))
       (equal (fn-mpxt-keyi i (update-fn-mpxt-count n fn-mpxt)) (fn-mpxt-keyi i fn-mpxt))
       (implies (and (natp i) (natp j))
                (equal (fn-mpxt-keyi i (update-fn-mpxt-keyi j v fn-mpxt))
                       (if (equal i j) v (fn-mpxt-keyi i fn-mpxt))))
       (implies (and (natp i) (natp j))
                (equal (fn-mpxt-wi i (update-fn-mpxt-wi j v fn-mpxt))
                       (if (equal i j) v (fn-mpxt-wi i fn-mpxt))))))

;; The primitives are closed from here on: every fact about them is above.
(in-theory (disable fn-mpxtp fn-mpxt-wi update-fn-mpxt-wi fn-mpxt-w-length resize-fn-mpxt-w
                    fn-mpxt-pages update-fn-mpxt-pages fn-mpxt-count update-fn-mpxt-count
                    fn-mpxt-keyi update-fn-mpxt-keyi fn-mpxt-key-length))

; The table's key, as the list of its 32 octets from index I.
(defun fn-mpxt-key-from (i fn-mpxt)
  (declare (xargs :stobjs fn-mpxt :guard (natp i)
                  :measure (nfix (- *fn-mpxt-key-octets* (nfix i)))))
  (if (>= (nfix i) *fn-mpxt-key-octets*)
      nil
    (cons (fn-mpxt-keyi (nfix i) fn-mpxt) (fn-mpxt-key-from (1+ (nfix i)) fn-mpxt))))

(defun fn-mpxt-key-octets (fn-mpxt)
  (declare (xargs :stobjs fn-mpxt))
  (fn-mpxt-key-from 0 fn-mpxt))

; The key is untouched by every write to the words, the pages and the count.
(defthm fn-mpxt-key-from-of-updates
  (and (equal (fn-mpxt-key-from i (update-fn-mpxt-wi j v fn-mpxt)) (fn-mpxt-key-from i fn-mpxt))
       (equal (fn-mpxt-key-from i (resize-fn-mpxt-w n fn-mpxt)) (fn-mpxt-key-from i fn-mpxt))
       (equal (fn-mpxt-key-from i (update-fn-mpxt-pages n fn-mpxt)) (fn-mpxt-key-from i fn-mpxt))
       (equal (fn-mpxt-key-from i (update-fn-mpxt-count n fn-mpxt)) (fn-mpxt-key-from i fn-mpxt))))

(defthm fn-mpxt-key-octets-of-updates
  (and (equal (fn-mpxt-key-octets (update-fn-mpxt-wi j v fn-mpxt)) (fn-mpxt-key-octets fn-mpxt))
       (equal (fn-mpxt-key-octets (resize-fn-mpxt-w n fn-mpxt)) (fn-mpxt-key-octets fn-mpxt))
       (equal (fn-mpxt-key-octets (update-fn-mpxt-pages n fn-mpxt)) (fn-mpxt-key-octets fn-mpxt))
       (equal (fn-mpxt-key-octets (update-fn-mpxt-count n fn-mpxt)) (fn-mpxt-key-octets fn-mpxt))))

(in-theory (disable fn-mpxt-key-octets))

; Well formed: the pages fit the words.
(defun fn-mpxt-wfp (fn-mpxt)
  (declare (xargs :stobjs fn-mpxt))
  (<= (* *fn-mpxt-page-words* (fn-mpxt-pages fn-mpxt)) (fn-mpxt-w-length fn-mpxt)))

; The word index of slot J's TAG on page P; its SEQ word is 1024 further.
(defun fn-mpxt-slot (p j)
  (declare (xargs :guard (and (natp p) (natp j))))
  (+ (* *fn-mpxt-page-words* p) j))

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
  (nfix (fn-mpxt-wi (+ *fn-mpxt-page-slots* (fn-mpxt-slot p j)) fn-mpxt)))

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
  :hints (("Goal" :use ((:instance fn-mpxt-wi-is-a-word (i (+ *fn-mpxt-page-slots* (fn-mpxt-slot p j)))))
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
  (fn-mpxt-confirm msgid (fn-mpxt-candidates (fn-mpxt-tag msgid (fn-mpxt-key-octets fn-mpxt)) fn-mpxt) rows))

; FAITHFUL from I: every row at or after I is among its own tag's candidates.
(defun fn-mpxt-faithful-from (i rows fn-mpxt)
  (declare (xargs :stobjs fn-mpxt
                  :guard (and (natp i) (true-listp rows) (fn-mpxt-wfp fn-mpxt))
                  :measure (nfix (- (len rows) (nfix i)))
                  :guard-hints (("Goal" :in-theory (disable fn-mpxt-candidates)))))
  (if (>= (nfix i) (len rows))
      t
    (and (member-equal (nfix i)
                       (fn-mpxt-candidates (fn-mpxt-tag (fn-record-msgid (nth (nfix i) rows))
                                                        (fn-mpxt-key-octets fn-mpxt))
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
           (fn-mpxt-complete-from i msgid (fn-mpxt-candidates (fn-mpxt-tag msgid (fn-mpxt-key-octets fn-mpxt)) fn-mpxt) rows))
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
                            (seqs (fn-mpxt-candidates (fn-mpxt-tag msgid (fn-mpxt-key-octets fn-mpxt)) fn-mpxt)))
                 (:instance fn-mpxt-faithful-from-complete (i 0))
                 (:instance fn-mpxt-candidates-below (tag (fn-mpxt-tag msgid (fn-mpxt-key-octets fn-mpxt))) (n (len rows)))
                 (:instance fn-mpxt-candidates-ascending (tag (fn-mpxt-tag msgid (fn-mpxt-key-octets fn-mpxt))))
                 (:instance fn-mpxt-candidates-nat-listp (tag (fn-mpxt-tag msgid (fn-mpxt-key-octets fn-mpxt))))))))

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
         (fn-mpxt (update-fn-mpxt-wi (+ *fn-mpxt-page-slots* (fn-mpxt-slot p j)) (+ 1 seq) fn-mpxt)))
    fn-mpxt))

(defthm fn-mpxt-write-slot-frame
  (and (equal (fn-mpxt-pages (fn-mpxt-write-slot p j tag seq fn-mpxt)) (fn-mpxt-pages fn-mpxt))
       (equal (fn-mpxt-count (fn-mpxt-write-slot p j tag seq fn-mpxt)) (fn-mpxt-count fn-mpxt))
       (equal (fn-mpxt-key-octets (fn-mpxt-write-slot p j tag seq fn-mpxt)) (fn-mpxt-key-octets fn-mpxt))))

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
       (equal (fn-mpxt-count (mv-nth 1 (fn-mpxt-put-run tag seq p k fn-mpxt))) (fn-mpxt-count fn-mpxt))
       (equal (fn-mpxt-key-octets (mv-nth 1 (fn-mpxt-put-run tag seq p k fn-mpxt))) (fn-mpxt-key-octets fn-mpxt))))

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
       (equal (fn-mpxt-count (mv-nth 1 (fn-mpxt-put tag seq fn-mpxt))) (fn-mpxt-count fn-mpxt))
       (equal (fn-mpxt-key-octets (mv-nth 1 (fn-mpxt-put tag seq fn-mpxt))) (fn-mpxt-key-octets fn-mpxt))))

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
       (equal (fn-mpxt-count (fn-mpxt-zero-words i fn-mpxt)) (fn-mpxt-count fn-mpxt))
       (equal (fn-mpxt-key-octets (fn-mpxt-zero-words i fn-mpxt)) (fn-mpxt-key-octets fn-mpxt))))

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
       (equal (fn-mpxt-count (fn-mpxt-put-all es fn-mpxt)) (fn-mpxt-count fn-mpxt))
       (equal (fn-mpxt-key-octets (fn-mpxt-put-all es fn-mpxt)) (fn-mpxt-key-octets fn-mpxt))))

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

(defthm fn-mpxt-grow-key
  (equal (fn-mpxt-key-octets (fn-mpxt-grow fn-mpxt)) (fn-mpxt-key-octets fn-mpxt))
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

(defthm fn-mpxt-add-key
  (equal (fn-mpxt-key-octets (mv-nth 1 (fn-mpxt-add tag seq fn-mpxt))) (fn-mpxt-key-octets fn-mpxt))
  :hints (("Goal" :in-theory (disable fn-mpxt-put fn-mpxt-grow))))

(in-theory (disable fn-mpxt-add))

; Empty the table: no pages, no words (a cleared table keeps no reference to
; what it held, and is the value the fold from nothing builds).
(defun fn-mpxt-clear (fn-mpxt)
  (declare (xargs :stobjs fn-mpxt))
  (let* ((fn-mpxt (update-fn-mpxt-pages 0 fn-mpxt))
         (fn-mpxt (update-fn-mpxt-count 0 fn-mpxt))
         (fn-mpxt (resize-fn-mpxt-w 0 fn-mpxt)))
    fn-mpxt))

(defthm fn-mpxt-clear-shape
  (implies (fn-mpxtp fn-mpxt)
           (and (fn-mpxtp (fn-mpxt-clear fn-mpxt))
                (equal (fn-mpxt-pages (fn-mpxt-clear fn-mpxt)) 0)
                (equal (fn-mpxt-count (fn-mpxt-clear fn-mpxt)) 0)
                (equal (fn-mpxt-w-length (fn-mpxt-clear fn-mpxt)) 0)
                (equal (fn-mpxt-key-octets (fn-mpxt-clear fn-mpxt)) (fn-mpxt-key-octets fn-mpxt)))))

(defthm fn-mpxt-clear-candidates
  (equal (fn-mpxt-candidates tag (fn-mpxt-clear fn-mpxt)) nil))

(defthm fn-mpxt-clear-faithful-nil
  (fn-mpxt-faithful nil (fn-mpxt-clear fn-mpxt)))

; Write KEY's octets (clamped, missing ones 0) from index I.
(defun fn-mpxt-set-key-from (i key fn-mpxt)
  (declare (xargs :stobjs fn-mpxt :guard (natp i)
                  :measure (nfix (- *fn-mpxt-key-octets* (nfix i)))))
  (if (>= (nfix i) *fn-mpxt-key-octets*)
      fn-mpxt
    (let ((fn-mpxt (update-fn-mpxt-keyi (nfix i) (fn-ns-octet (if (consp key) (car key) 0)) fn-mpxt)))
      (fn-mpxt-set-key-from (1+ (nfix i)) (if (consp key) (cdr key) nil) fn-mpxt))))

(defthm fn-mpxt-set-key-from-shape
  (implies (fn-mpxtp fn-mpxt)
           (and (fn-mpxtp (fn-mpxt-set-key-from i key fn-mpxt))
                (equal (fn-mpxt-pages (fn-mpxt-set-key-from i key fn-mpxt)) (fn-mpxt-pages fn-mpxt))
                (equal (fn-mpxt-count (fn-mpxt-set-key-from i key fn-mpxt)) (fn-mpxt-count fn-mpxt))
                (equal (fn-mpxt-w-length (fn-mpxt-set-key-from i key fn-mpxt)) (fn-mpxt-w-length fn-mpxt))))
  :hints (("Goal" :induct (fn-mpxt-set-key-from i key fn-mpxt)
           :in-theory (enable unsigned-byte-p))))

; INSTALL the key into an emptied table (the open's step): the tags of the
; entries a table holds are its key's, so a key change empties it.
(defun fn-mpxt-set-key (key fn-mpxt)
  (declare (xargs :stobjs fn-mpxt))
  (let ((fn-mpxt (fn-mpxt-clear fn-mpxt)))
    (fn-mpxt-set-key-from 0 key fn-mpxt)))

(defthm fn-mpxt-set-key-shape
  (implies (fn-mpxtp fn-mpxt)
           (and (fn-mpxtp (fn-mpxt-set-key key fn-mpxt))
                (equal (fn-mpxt-pages (fn-mpxt-set-key key fn-mpxt)) 0)
                (equal (fn-mpxt-count (fn-mpxt-set-key key fn-mpxt)) 0)
                (equal (fn-mpxt-w-length (fn-mpxt-set-key key fn-mpxt)) 0))))

(defthm fn-mpxt-set-key-faithful-nil
  (fn-mpxt-faithful nil (fn-mpxt-set-key key fn-mpxt))
  :hints (("Goal" :in-theory (enable fn-mpxt-faithful fn-mpxt-okp fn-mpxt-candidates))))

; -----------------------------------------------------------------------------
; 5. The writer's frame: what a write into an empty slot does to the
; reader (toward `fn-mpxt-put-preserves-faithful', the next READY).


(defthm fn-mpxt-wi-of-write-slot
  (implies (and (natp w) (natp p) (natp j))
           (equal (fn-mpxt-wi w (fn-mpxt-write-slot p j tag seq fn-mpxt))
                  (cond ((equal w (fn-mpxt-slot p j)) tag)
                        ((equal w (+ *fn-mpxt-page-slots* (fn-mpxt-slot p j))) (+ 1 seq))
                        (t (fn-mpxt-wi w fn-mpxt)))))
  :hints (("Goal" :in-theory (enable fn-mpxt-write-slot))))

(defthm fn-mpxt-ins-commutes
  (implies (and (natp a) (natp b) (nat-listp l))
           (equal (fn-mpxt-ins a (fn-mpxt-ins b l))
                  (fn-mpxt-ins b (fn-mpxt-ins a l)))))

(defthm fn-mpxt-scan-of-ins
  (implies (and (natp s) (nat-listp acc))
           (equal (fn-mpxt-scan tag p j (fn-mpxt-ins s acc) fn-mpxt)
                  (fn-mpxt-ins s (fn-mpxt-scan tag p j acc fn-mpxt))))
  :hints (("Goal" :induct (fn-mpxt-scan tag p j acc fn-mpxt))))

(defthm fn-mpxt-slot-equal
  (implies (and (natp q) (natp i) (< i *fn-mpxt-page-slots*)
                (natp p) (natp j) (< j *fn-mpxt-page-slots*))
           (iff (equal (fn-mpxt-slot q i) (fn-mpxt-slot p j))
                (and (equal q p) (equal i j))))
  :hints (("Goal" :in-theory (enable fn-mpxt-slot) :cases ((< q p) (< p q)))))

(defthm fn-mpxt-slot-is-not-a-seq-word
  (implies (and (natp q) (natp i) (< i *fn-mpxt-page-slots*)
                (natp p) (natp j) (< j *fn-mpxt-page-slots*))
           (not (equal (fn-mpxt-slot q i) (+ *fn-mpxt-page-slots* (fn-mpxt-slot p j)))))
  :hints (("Goal" :in-theory (enable fn-mpxt-slot) :cases ((< q p) (< p q)))))

(defthm fn-mpxt-slot-natp
  (implies (and (natp p) (natp j))
           (natp (fn-mpxt-slot p j)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn-mpxt-slot))))


(in-theory (disable fn-mpxt-slot))


(defthm fn-mpxt-tag-at-of-write-slot
  (implies (and (natp q) (natp i) (< i *fn-mpxt-page-slots*)
                (natp p) (natp j) (< j *fn-mpxt-page-slots*))
           (equal (fn-mpxt-tag-at q i (fn-mpxt-write-slot p j tag seq fn-mpxt))
                  (if (and (equal q p) (equal i j)) (nfix tag) (fn-mpxt-tag-at q i fn-mpxt))))
  :hints (("Goal" :in-theory (enable fn-mpxt-tag-at))))

(defthm fn-mpxt-seq-at-of-write-slot
  (implies (and (natp q) (natp i) (< i *fn-mpxt-page-slots*)
                (natp p) (natp j) (< j *fn-mpxt-page-slots*))
           (equal (fn-mpxt-seq-at q i (fn-mpxt-write-slot p j tag seq fn-mpxt))
                  (if (and (equal q p) (equal i j)) (nfix (+ 1 seq)) (fn-mpxt-seq-at q i fn-mpxt))))
  :hints (("Goal" :in-theory (enable fn-mpxt-seq-at))))

(defthm fn-mpxt-find-empty-is-empty
  (implies (fn-mpxt-find-empty p j fn-mpxt)
           (equal (fn-mpxt-tag-at p (fn-mpxt-find-empty p j fn-mpxt) fn-mpxt) 0))
  :hints (("Goal" :induct (fn-mpxt-find-empty p j fn-mpxt))))

(defthm fn-mpxt-find-empty-nil-slot
  (implies (and (not (fn-mpxt-find-empty p j fn-mpxt)) (natp j) (natp i) (<= j i)
                (< i *fn-mpxt-page-slots*))
           (not (equal 0 (fn-mpxt-tag-at p i fn-mpxt))))
  :hints (("Goal" :induct (fn-mpxt-find-empty p j fn-mpxt))))

(defthm fn-mpxt-find-empty-nil-is-full
  (implies (and (not (fn-mpxt-find-empty p 0 fn-mpxt)) (natp k) (<= k *fn-mpxt-page-slots*))
           (fn-mpxt-page-fullp p k fn-mpxt))
  :hints (("Goal" :induct (fn-mpxt-page-fullp p k fn-mpxt)
           :in-theory (disable fn-mpxt-find-empty))))

(defthm fn-mpxt-subsetp-cons
  (implies (subsetp-equal a b)
           (subsetp-equal a (cons e b))))

(defthm fn-mpxt-subsetp-refl
  (subsetp-equal a a)
  :hints (("Goal" :induct (len a))))

(defthm fn-mpxt-subsetp-trans
  (implies (and (subsetp-equal a b) (subsetp-equal b c))
           (subsetp-equal a c)))

(defthm fn-mpxt-subsetp-ins
  (implies (and (natp e) (nat-listp b) (subsetp-equal a b))
           (subsetp-equal a (fn-mpxt-ins e b))))

(defthm fn-mpxt-subsetp-ins-both
  (implies (and (natp e) (nat-listp a) (nat-listp b) (subsetp-equal a b))
           (subsetp-equal (fn-mpxt-ins e a) (fn-mpxt-ins e b))))

(defthm fn-mpxt-scan-grows-general
  (implies (and (nat-listp acc) (subsetp-equal a acc))
           (subsetp-equal a (fn-mpxt-scan tag p k acc fn-mpxt)))
  :hints (("Goal" :induct (fn-mpxt-scan tag p k acc fn-mpxt)
           :in-theory (disable fn-mpxt-ins fn-mpxt-scan-of-ins))))
(defthm fn-mpxt-scan-grows
  (implies (nat-listp acc)
           (subsetp-equal acc (fn-mpxt-scan tag p k acc fn-mpxt))))
(local
 (defun fn-mpxt-scan2-ind (tag p k a b fn-mpxt)
   (declare (xargs :stobjs fn-mpxt :verify-guards nil :measure (nfix k)))
   (if (zp k)
       (list a b)
     (let* ((j (1- k))
            (m (and (equal tag (fn-mpxt-tag-at p j fn-mpxt)) (<= 1 (fn-mpxt-seq-at p j fn-mpxt))))
            (e (1- (fn-mpxt-seq-at p j fn-mpxt))))
       (fn-mpxt-scan2-ind tag p j (if m (fn-mpxt-ins e a) a) (if m (fn-mpxt-ins e b) b) fn-mpxt)))))
(defthm fn-mpxt-scan-subsetp
  (implies (and (nat-listp a) (nat-listp b) (subsetp-equal a b))
           (subsetp-equal (fn-mpxt-scan tag p k a fn-mpxt) (fn-mpxt-scan tag p k b fn-mpxt)))
  :hints (("Goal" :induct (fn-mpxt-scan2-ind tag p k a b fn-mpxt)
           :in-theory (disable fn-mpxt-ins fn-mpxt-scan-of-ins))))
(defthm fn-mpxt-run-grows-general
  (implies (and (nat-listp acc) (subsetp-equal a acc))
           (subsetp-equal a (fn-mpxt-run tag p k acc fn-mpxt)))
  :hints (("Goal" :induct (fn-mpxt-run tag p k acc fn-mpxt)
           :in-theory (disable fn-mpxt-scan fn-mpxt-page-fullp fn-mpxt-ins fn-mpxt-scan-of-ins))))
(defthm fn-mpxt-run-grows
  (implies (nat-listp acc)
           (subsetp-equal acc (fn-mpxt-run tag p k acc fn-mpxt))))
(local
 (defun fn-mpxt-run2-ind (tag p k a b fn-mpxt)
   (declare (xargs :stobjs fn-mpxt :verify-guards nil :measure (nfix k)))
   (if (zp k)
       (list a b)
     (fn-mpxt-run2-ind tag (fn-mpxt-next p (fn-mpxt-pages fn-mpxt)) (1- k)
                       (fn-mpxt-scan tag p *fn-mpxt-page-slots* a fn-mpxt)
                       (fn-mpxt-scan tag p *fn-mpxt-page-slots* b fn-mpxt)
                       fn-mpxt))))
(defthm fn-mpxt-run-subsetp
  (implies (and (nat-listp a) (nat-listp b) (subsetp-equal a b))
           (subsetp-equal (fn-mpxt-run tag p k a fn-mpxt) (fn-mpxt-run tag p k b fn-mpxt)))
  :hints (("Goal" :induct (fn-mpxt-run2-ind tag p k a b fn-mpxt)
           :in-theory (disable fn-mpxt-scan fn-mpxt-page-fullp fn-mpxt-ins fn-mpxt-scan-of-ins))))

(defthm fn-mpxt-scan-of-write-slot-other
  (implies (and (natp q) (natp p) (not (equal q p)) (natp j) (< j *fn-mpxt-page-slots*)
                (natp k) (<= k *fn-mpxt-page-slots*))
           (equal (fn-mpxt-scan tag q k acc (fn-mpxt-write-slot p j wtag seq fn-mpxt))
                  (fn-mpxt-scan tag q k acc fn-mpxt)))
  :hints (("Goal" :induct (fn-mpxt-scan tag q k acc fn-mpxt))))

(defthm fn-mpxt-page-fullp-of-write-slot
  (implies (and (natp q) (natp p) (natp j) (< j *fn-mpxt-page-slots*) (natp k) (<= k *fn-mpxt-page-slots*)
                (posp wtag) (fn-mpxt-page-fullp q k fn-mpxt))
           (fn-mpxt-page-fullp q k (fn-mpxt-write-slot p j wtag seq fn-mpxt)))
  :hints (("Goal" :induct (fn-mpxt-page-fullp q k fn-mpxt))))

(defthm fn-mpxt-subsetp-member
  (implies (and (subsetp-equal a b) (member-equal s a))
           (member-equal s b)))
(defthm fn-mpxt-scan-member
  (implies (and (member-equal s acc) (nat-listp acc))
           (member-equal s (fn-mpxt-scan tag p k acc fn-mpxt)))
  :hints (("Goal" :induct (fn-mpxt-scan tag p k acc fn-mpxt)
           :in-theory (disable fn-mpxt-ins fn-mpxt-scan-of-ins))))
(defthm fn-mpxt-run-member
  (implies (and (member-equal s acc) (nat-listp acc))
           (member-equal s (fn-mpxt-run tag p k acc fn-mpxt)))
  :hints (("Goal" :induct (fn-mpxt-run tag p k acc fn-mpxt)
           :in-theory (disable fn-mpxt-scan fn-mpxt-page-fullp fn-mpxt-ins))))
(defthm fn-mpxt-run-scan-member
  (implies (and (not (zp k)) (nat-listp acc)
                (member-equal s (fn-mpxt-scan tag p *fn-mpxt-page-slots* acc fn-mpxt)))
           (member-equal s (fn-mpxt-run tag p k acc fn-mpxt)))
  :hints (("Goal" :expand ((fn-mpxt-run tag p k acc fn-mpxt))
           :in-theory (disable fn-mpxt-scan fn-mpxt-page-fullp fn-mpxt-run))))
(defthm fn-mpxt-scan-of-write-slot-subsetp
  (implies (and (natp q) (natp p) (natp j) (< j *fn-mpxt-page-slots*) (natp k) (<= k *fn-mpxt-page-slots*)
                (equal (fn-mpxt-tag-at p j fn-mpxt) 0)
                (posp tag) (posp wtag) (natp seq) (nat-listp acc))
           (subsetp-equal (fn-mpxt-scan tag q k acc fn-mpxt)
                          (fn-mpxt-scan tag q k acc (fn-mpxt-write-slot p j wtag seq fn-mpxt))))
  :hints (("Goal" :induct (fn-mpxt-scan tag q k acc fn-mpxt)
           :expand ((fn-mpxt-scan tag q k acc (fn-mpxt-write-slot p j wtag seq fn-mpxt)))
           :in-theory (disable fn-mpxt-ins fn-mpxt-scan-of-ins fn-mpxt-scan-of-write-slot-other))))
(defthm fn-mpxt-scan-of-write-slot-finds
  (implies (and (natp p) (natp j) (< j k) (natp k) (<= k *fn-mpxt-page-slots*)
                (posp wtag) (natp seq) (nat-listp acc))
           (member-equal seq (fn-mpxt-scan wtag p k acc (fn-mpxt-write-slot p j wtag seq fn-mpxt))))
  :hints (("Goal" :induct (fn-mpxt-scan wtag p k acc fn-mpxt)
           :expand ((fn-mpxt-scan wtag p k acc (fn-mpxt-write-slot p j wtag seq fn-mpxt)))
           :in-theory (disable fn-mpxt-ins fn-mpxt-scan-of-ins fn-mpxt-scan-of-write-slot-other))))

(in-theory (disable fn-mpxt-find-empty))

(defthm fn-mpxt-put-run-keeps-full
  (implies (and (natp q) (natp k2) (<= k2 *fn-mpxt-page-slots*)
                (natp p) (< p (fn-mpxt-pages fn-mpxt)) (natp (fn-mpxt-pages fn-mpxt))
                (posp wtag) (fn-mpxt-page-fullp q k2 fn-mpxt))
           (fn-mpxt-page-fullp q k2 (mv-nth 1 (fn-mpxt-put-run wtag seq p k fn-mpxt))))
  :hints (("Goal" :induct (fn-mpxt-put-run wtag seq p k fn-mpxt)
           :in-theory (disable fn-mpxt-page-fullp))))
(defthm fn-mpxt-put-run-scan-subsetp
  (implies (and (natp q) (natp k2) (<= k2 *fn-mpxt-page-slots*)
                (natp p) (< p (fn-mpxt-pages fn-mpxt)) (natp (fn-mpxt-pages fn-mpxt))
                (posp tag) (posp wtag) (natp seq) (nat-listp acc))
           (subsetp-equal (fn-mpxt-scan tag q k2 acc fn-mpxt)
                          (fn-mpxt-scan tag q k2 acc (mv-nth 1 (fn-mpxt-put-run wtag seq p k fn-mpxt)))))
  :hints (("Goal" :induct (fn-mpxt-put-run wtag seq p k fn-mpxt)
           :in-theory (disable fn-mpxt-scan))))

(defthm fn-mpxt-run-first-scan-subsetp
  (implies (and (not (zp k)) (nat-listp acc)
                (subsetp-equal a (fn-mpxt-scan tag p *fn-mpxt-page-slots* acc fn-mpxt)))
           (subsetp-equal a (fn-mpxt-run tag p k acc fn-mpxt)))
  :hints (("Goal" :expand ((fn-mpxt-run tag p k acc fn-mpxt))
           :in-theory (disable fn-mpxt-scan fn-mpxt-page-fullp fn-mpxt-run))))
(defthm fn-mpxt-put-run-run-subsetp
  (implies (and (natp q) (natp p) (< p (fn-mpxt-pages fn-mpxt)) (natp (fn-mpxt-pages fn-mpxt))
                (posp tag) (posp wtag) (natp seq) (nat-listp acc))
           (subsetp-equal (fn-mpxt-run tag q k2 acc fn-mpxt)
                          (fn-mpxt-run tag q k2 acc (mv-nth 1 (fn-mpxt-put-run wtag seq p k fn-mpxt)))))
  :hints (("Goal" :induct (fn-mpxt-run tag q k2 acc fn-mpxt)
           :expand ((fn-mpxt-run tag q k2 acc (mv-nth 1 (fn-mpxt-put-run wtag seq p k fn-mpxt))))
           :in-theory (disable fn-mpxt-scan fn-mpxt-page-fullp fn-mpxt-put-run fn-mpxt-ins))))
(defthm fn-mpxt-put-run-run-member
  (implies (and (natp q) (natp p) (< p (fn-mpxt-pages fn-mpxt)) (natp (fn-mpxt-pages fn-mpxt))
                (posp tag) (posp wtag) (natp seq) (nat-listp acc)
                (member-equal s (fn-mpxt-run tag q k2 acc fn-mpxt)))
           (member-equal s (fn-mpxt-run tag q k2 acc (mv-nth 1 (fn-mpxt-put-run wtag seq p k fn-mpxt)))))
  :hints (("Goal" :use fn-mpxt-put-run-run-subsetp
           :in-theory (disable fn-mpxt-put-run-run-subsetp fn-mpxt-run fn-mpxt-put-run))))

(defthm fn-mpxt-page-okp-of-write-slot
  (implies (and (natp q) (natp p) (natp j) (< j *fn-mpxt-page-slots*) (natp k2) (<= k2 *fn-mpxt-page-slots*)
                (posp wtag) (natp seq) (natp n) (natp n2) (<= n n2) (<= (+ 1 seq) n2)
                (fn-mpxt-page-okp q k2 n fn-mpxt))
           (fn-mpxt-page-okp q k2 n2 (fn-mpxt-write-slot p j wtag seq fn-mpxt)))
  :hints (("Goal" :induct (fn-mpxt-page-okp q k2 n fn-mpxt))))
(defthm fn-mpxt-pages-okp-of-write-slot
  (implies (and (natp np) (natp p) (natp j) (< j *fn-mpxt-page-slots*)
                (posp wtag) (natp seq) (natp n) (natp n2) (<= n n2) (<= (+ 1 seq) n2)
                (fn-mpxt-pages-okp np n fn-mpxt))
           (fn-mpxt-pages-okp np n2 (fn-mpxt-write-slot p j wtag seq fn-mpxt)))
  :hints (("Goal" :induct (fn-mpxt-pages-okp np n fn-mpxt)
           :in-theory (disable fn-mpxt-page-okp))))
(defthm fn-mpxt-faithful-from-of-put-run
  (implies (and (natp p) (< p (fn-mpxt-pages fn-mpxt)) (natp (fn-mpxt-pages fn-mpxt))
                (posp wtag) (natp seq)
                (fn-mpxt-faithful-from i rows fn-mpxt))
           (fn-mpxt-faithful-from i rows (mv-nth 1 (fn-mpxt-put-run wtag seq p k fn-mpxt))))
  :hints (("Goal" :induct (fn-mpxt-faithful-from i rows fn-mpxt)
           :in-theory (e/d (fn-mpxt-candidates) (fn-mpxt-run fn-mpxt-put-run)))))

(defthm fn-mpxt-page-okp-mono
  (implies (and (natp n) (natp n2) (<= n n2) (fn-mpxt-page-okp q k2 n fn-mpxt))
           (fn-mpxt-page-okp q k2 n2 fn-mpxt))
  :hints (("Goal" :induct (fn-mpxt-page-okp q k2 n fn-mpxt))))
(defthm fn-mpxt-pages-okp-mono
  (implies (and (natp n) (natp n2) (<= n n2) (fn-mpxt-pages-okp np n fn-mpxt))
           (fn-mpxt-pages-okp np n2 fn-mpxt))
  :hints (("Goal" :induct (fn-mpxt-pages-okp np n fn-mpxt)
           :in-theory (disable fn-mpxt-page-okp))))
(defthm fn-mpxt-pages-okp-of-put-run
  (implies (and (natp p) (< p (fn-mpxt-pages fn-mpxt)) (natp (fn-mpxt-pages fn-mpxt)) (natp np)
                (posp wtag) (natp seq) (natp n) (natp n2) (<= n n2) (<= (+ 1 seq) n2)
                (fn-mpxt-pages-okp np n fn-mpxt))
           (fn-mpxt-pages-okp np n2 (mv-nth 1 (fn-mpxt-put-run wtag seq p k fn-mpxt))))
  :hints (("Goal" :induct (fn-mpxt-put-run wtag seq p k fn-mpxt)
           :in-theory (disable fn-mpxt-pages-okp))))
(defthm fn-mpxt-run-member-from-nil
  (implies (and (nat-listp acc) (member-equal s (fn-mpxt-run tag p k nil fn-mpxt)))
           (member-equal s (fn-mpxt-run tag p k acc fn-mpxt)))
  :hints (("Goal" :use ((:instance fn-mpxt-run-subsetp (a nil) (b acc)))
           :in-theory (disable fn-mpxt-run-subsetp fn-mpxt-run))))
(defthm fn-mpxt-put-run-finds
  (implies (and (natp p) (< p (fn-mpxt-pages fn-mpxt)) (natp (fn-mpxt-pages fn-mpxt))
                (posp wtag) (natp seq)
                (mv-nth 0 (fn-mpxt-put-run wtag seq p k fn-mpxt)))
           (member-equal seq (fn-mpxt-run wtag p k nil (mv-nth 1 (fn-mpxt-put-run wtag seq p k fn-mpxt)))))
  :hints (("Goal" :induct (fn-mpxt-put-run wtag seq p k fn-mpxt)
           :expand ((:free (x) (fn-mpxt-run wtag p k nil x)))
           :in-theory (disable fn-mpxt-scan fn-mpxt-page-fullp fn-mpxt-run fn-mpxt-ins))))

(defthm fn-mpxt-faithful-from-beyond
  (implies (>= (nfix i) (len rows))
           (fn-mpxt-faithful-from i rows fn-mpxt)))
(local
 (defthm fn-mpxt-len-append
   (equal (len (append a b)) (+ (len a) (len b)))))
(local
 (defthm fn-mpxt-nth-append
   (implies (natp i)
            (equal (nth i (append a b))
                   (if (< i (len a)) (nth i a) (nth (- i (len a)) b))))))

(defthm fn-mpxt-faithful-from-append
  (implies (and (true-listp rows) (natp i)
                (fn-mpxt-faithful-from i rows fn-mpxt)
                (member-equal (len rows) (fn-mpxt-candidates (fn-mpxt-tag (fn-record-msgid h) (fn-mpxt-key-octets fn-mpxt)) fn-mpxt)))
           (fn-mpxt-faithful-from i (append rows (list h)) fn-mpxt))
  :hints (("Goal" :induct (fn-mpxt-faithful-from i (append rows (list h)) fn-mpxt)
           :in-theory (disable fn-mpxt-candidates))))

; KEYSTONE (the writer): placing the new row's entry keeps the table faithful
; to the rows with that row appended -- the commit path's obligation.  (Growth's
; preservation, a slot-counting argument, is the next READY: LANEDUMP NEXT 1.)
(defthm fn-mpxt-put-preserves-faithful
  (implies (and (true-listp rows) (natp (fn-mpxt-pages fn-mpxt))
                (fn-mpxt-faithful rows fn-mpxt)
                (mv-nth 0 (fn-mpxt-put (fn-mpxt-tag (fn-record-msgid h) (fn-mpxt-key-octets fn-mpxt)) (len rows) fn-mpxt)))
           (fn-mpxt-faithful (append rows (list h))
                             (mv-nth 1 (fn-mpxt-put (fn-mpxt-tag (fn-record-msgid h) (fn-mpxt-key-octets fn-mpxt)) (len rows) fn-mpxt))))
  :hints (("Goal" :in-theory (e/d (fn-mpxt-put fn-mpxt-faithful fn-mpxt-okp fn-mpxt-candidates)
                                  (fn-mpxt-put-run fn-mpxt-run fn-mpxt-pages-okp fn-mpxt-faithful-from
                                   fn-mpxt-faithful-from-append fn-mpxt-pages-okp-of-put-run))
           :do-not-induct t
           :use ((:instance fn-mpxt-put-run-finds
                            (wtag (fn-mpxt-tag (fn-record-msgid h) (fn-mpxt-key-octets fn-mpxt))) (seq (len rows))
                            (p (fn-mpx-home (fn-mpxt-tag (fn-record-msgid h) (fn-mpxt-key-octets fn-mpxt)) (fn-mpxt-pages fn-mpxt)))
                            (k (fn-mpxt-pages fn-mpxt)))
                 (:instance fn-mpxt-pages-okp-of-put-run
                            (wtag (fn-mpxt-tag (fn-record-msgid h) (fn-mpxt-key-octets fn-mpxt))) (seq (len rows))
                            (p (fn-mpx-home (fn-mpxt-tag (fn-record-msgid h) (fn-mpxt-key-octets fn-mpxt)) (fn-mpxt-pages fn-mpxt)))
                            (k (fn-mpxt-pages fn-mpxt)) (np (fn-mpxt-pages fn-mpxt))
                            (n (len rows)) (n2 (+ 1 (len rows))))
                 (:instance fn-mpxt-faithful-from-append
                            (i 0)
                            (fn-mpxt (mv-nth 1 (fn-mpxt-put-run (fn-mpxt-tag (fn-record-msgid h) (fn-mpxt-key-octets fn-mpxt)) (len rows)
                                                                (fn-mpx-home (fn-mpxt-tag (fn-record-msgid h) (fn-mpxt-key-octets fn-mpxt)) (fn-mpxt-pages fn-mpxt))
                                                                (fn-mpxt-pages fn-mpxt) fn-mpxt))))))))

; -----------------------------------------------------------------------------
; 6. The page need (ember's PKT-774 ruling, row W2b).  The work of a lookup
; is the pages its run reads: one plus the run of full pages after the home
; page, for EVERY table and EVERY tag -- the adversary's Message-IDs choose
; tags, never the bound -- and at most the page count.  Under the table
; condition "no page and its successor are both full" it is at most two
; (design B.3's L-MPX-OVERFLOW).  `fn-mpxt-skewp' is the pre-check the
; served POST refuses by name (`:mpx-skew'): a home page whose overflow is
; full, so the placement would go past it -- evidence of crafted tags under
; a leaked key, never a longer run written by a POST; a not-skewed placement
; lands, and its tag's lookup reads at most two pages.

; The pages a run of at most K from P reads: P, then the next while full.
(defun fn-mpxt-run-pages (p k fn-mpxt)
  (declare (xargs :stobjs fn-mpxt :measure (nfix k)
                  :guard (and (natp p) (natp k) (< p (fn-mpxt-pages fn-mpxt)) (fn-mpxt-wfp fn-mpxt))))
  (if (zp k)
      0
    (if (fn-mpxt-page-fullp p *fn-mpxt-page-slots* fn-mpxt)
        (+ 1 (fn-mpxt-run-pages (fn-mpxt-next p (fn-mpxt-pages fn-mpxt)) (1- k) fn-mpxt))
      1)))

; The run, counting the pages it reads: (mv candidates pages).
(defun fn-mpxt-run-counted (tag p k acc fn-mpxt)
  (declare (xargs :stobjs fn-mpxt :measure (nfix k)
                  :guard (and (natp tag) (natp p) (natp k)
                              (< p (fn-mpxt-pages fn-mpxt)) (fn-mpxt-wfp fn-mpxt)
                              (nat-listp acc))))
  (if (zp k)
      (mv acc 0)
    (let ((acc (fn-mpxt-scan tag p *fn-mpxt-page-slots* acc fn-mpxt)))
      (if (fn-mpxt-page-fullp p *fn-mpxt-page-slots* fn-mpxt)
          (mv-let (acc pages)
            (fn-mpxt-run-counted tag (fn-mpxt-next p (fn-mpxt-pages fn-mpxt)) (1- k) acc fn-mpxt)
            (mv acc (+ 1 pages)))
        (mv acc 1)))))

; The counted run is the run, and its count is the run's pages.
(defthm fn-mpxt-run-counted-is-run
  (and (equal (mv-nth 0 (fn-mpxt-run-counted tag p k acc fn-mpxt))
              (fn-mpxt-run tag p k acc fn-mpxt))
       (equal (mv-nth 1 (fn-mpxt-run-counted tag p k acc fn-mpxt))
              (fn-mpxt-run-pages p k fn-mpxt)))
  :hints (("Goal" :induct (fn-mpxt-run-counted tag p k acc fn-mpxt)
           :in-theory (disable fn-mpxt-scan fn-mpxt-page-fullp))))

; The full run from P: the consecutive full pages, at most K.
(defun fn-mpxt-full-run (p k fn-mpxt)
  (declare (xargs :stobjs fn-mpxt :measure (nfix k)
                  :guard (and (natp p) (natp k) (< p (fn-mpxt-pages fn-mpxt)) (fn-mpxt-wfp fn-mpxt))))
  (if (or (zp k) (not (fn-mpxt-page-fullp p *fn-mpxt-page-slots* fn-mpxt)))
      0
    (+ 1 (fn-mpxt-full-run (fn-mpxt-next p (fn-mpxt-pages fn-mpxt)) (1- k) fn-mpxt))))

(defthm fn-mpxt-run-pages-is-one-plus-the-full-run
  (equal (fn-mpxt-run-pages p k fn-mpxt)
         (if (zp k) 0 (+ 1 (fn-mpxt-full-run p (1- k) fn-mpxt))))
  :hints (("Goal" :induct (fn-mpxt-run-pages p k fn-mpxt)
           :in-theory (disable fn-mpxt-page-fullp))))

(defthm fn-mpxt-run-pages-at-most-k
  (<= (fn-mpxt-run-pages p k fn-mpxt) (nfix k))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-mpxt-run-pages p k fn-mpxt)
           :in-theory (disable fn-mpxt-page-fullp fn-mpxt-run-pages-is-one-plus-the-full-run))))

; THE PAGE NEED of a lookup: the pages the reader reads for TAG.
(defun fn-mpxt-candidates-pages (tag fn-mpxt)
  (declare (xargs :stobjs fn-mpxt :guard (and (natp tag) (fn-mpxt-wfp fn-mpxt))))
  (let ((np (fn-mpxt-pages fn-mpxt)))
    (if (zp np)
        0
      (fn-mpxt-run-pages (fn-mpx-home tag np) np fn-mpxt))))

; The reader, counting: its candidates are the reader's, its pages the need.
(defun fn-mpxt-candidates-counted (tag fn-mpxt)
  (declare (xargs :stobjs fn-mpxt :guard (and (natp tag) (fn-mpxt-wfp fn-mpxt))))
  (let ((np (fn-mpxt-pages fn-mpxt)))
    (if (zp np)
        (mv nil 0)
      (fn-mpxt-run-counted tag (fn-mpx-home tag np) np nil fn-mpxt))))

(defthm fn-mpxt-candidates-counted-is-candidates
  (and (equal (mv-nth 0 (fn-mpxt-candidates-counted tag fn-mpxt)) (fn-mpxt-candidates tag fn-mpxt))
       (equal (mv-nth 1 (fn-mpxt-candidates-counted tag fn-mpxt)) (fn-mpxt-candidates-pages tag fn-mpxt))))

; KEYSTONE (the page need): for every table and every tag, the lookup reads
; one page plus the run of full pages after the home page, and at most the
; page count.  No hypothesis restricts the tag beyond its type.
(defthm fn-mpxt-candidates-page-need
  (implies (natp tag)
           (and (equal (fn-mpxt-candidates-pages tag fn-mpxt)
                       (if (zp (fn-mpxt-pages fn-mpxt))
                           0
                         (+ 1 (fn-mpxt-full-run (fn-mpx-home tag (fn-mpxt-pages fn-mpxt))
                                                (1- (fn-mpxt-pages fn-mpxt)) fn-mpxt))))
                (<= (fn-mpxt-candidates-pages tag fn-mpxt) (nfix (fn-mpxt-pages fn-mpxt)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-mpxt-run-pages-is-one-plus-the-full-run)
           :use ((:instance fn-mpxt-run-pages-is-one-plus-the-full-run
                            (p (fn-mpx-home tag (fn-mpxt-pages fn-mpxt))) (k (fn-mpxt-pages fn-mpxt)))
                 (:instance fn-mpxt-run-pages-at-most-k
                            (p (fn-mpx-home tag (fn-mpxt-pages fn-mpxt))) (k (fn-mpxt-pages fn-mpxt)))))))

; No page below P and its successor are both full: the table condition.
(defun fn-mpxt-no-adjacent-fullp (p fn-mpxt)
  (declare (xargs :stobjs fn-mpxt :measure (nfix p)
                  :guard (and (natp p) (<= p (fn-mpxt-pages fn-mpxt)) (fn-mpxt-wfp fn-mpxt))))
  (if (zp p)
      t
    (and (not (and (fn-mpxt-page-fullp (1- p) *fn-mpxt-page-slots* fn-mpxt)
                   (fn-mpxt-page-fullp (fn-mpxt-next (1- p) (fn-mpxt-pages fn-mpxt))
                                       *fn-mpxt-page-slots* fn-mpxt)))
         (fn-mpxt-no-adjacent-fullp (1- p) fn-mpxt))))

(defthm fn-mpxt-no-adjacent-fullp-page
  (implies (and (fn-mpxt-no-adjacent-fullp np fn-mpxt) (natp q) (< q np)
                (fn-mpxt-page-fullp q *fn-mpxt-page-slots* fn-mpxt))
           (not (fn-mpxt-page-fullp (fn-mpxt-next q (fn-mpxt-pages fn-mpxt)) *fn-mpxt-page-slots* fn-mpxt)))
  :hints (("Goal" :induct (fn-mpxt-no-adjacent-fullp np fn-mpxt)
           :in-theory (disable fn-mpxt-page-fullp))))

(defthm fn-mpxt-full-run-at-most-one
  (implies (and (fn-mpxt-no-adjacent-fullp (fn-mpxt-pages fn-mpxt) fn-mpxt)
                (natp p) (< p (fn-mpxt-pages fn-mpxt)))
           (<= (fn-mpxt-full-run p k fn-mpxt) 1))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fn-mpxt-page-fullp)
           :expand ((fn-mpxt-full-run p k fn-mpxt)
                    (fn-mpxt-full-run (fn-mpxt-next p (fn-mpxt-pages fn-mpxt)) (+ -1 k) fn-mpxt)))))

; L-MPX-OVERFLOW: under the condition, every lookup reads at most two pages.
(defthm fn-mpxt-candidates-page-need-two
  (implies (and (fn-mpxtp fn-mpxt) (natp tag)
                (fn-mpxt-no-adjacent-fullp (fn-mpxt-pages fn-mpxt) fn-mpxt))
           (<= (fn-mpxt-candidates-pages tag fn-mpxt) 2))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fn-mpxt-candidates-pages fn-mpxt-full-run)
           :use (fn-mpxt-candidates-page-need
                 (:instance fn-mpxt-full-run-at-most-one
                            (p (fn-mpx-home tag (fn-mpxt-pages fn-mpxt)))
                            (k (1- (fn-mpxt-pages fn-mpxt))))))))

; THE SKEW: TAG's home page and its overflow are both full, so a placement
; would go past the overflow page.
(defun fn-mpxt-skewp (tag fn-mpxt)
  (declare (xargs :stobjs fn-mpxt :guard (and (natp tag) (fn-mpxt-wfp fn-mpxt))))
  (let ((np (fn-mpxt-pages fn-mpxt)))
    (and (not (zp np))
         (fn-mpxt-page-fullp (fn-mpx-home tag np) *fn-mpxt-page-slots* fn-mpxt)
         (fn-mpxt-page-fullp (fn-mpxt-next (fn-mpx-home tag np) np) *fn-mpxt-page-slots* fn-mpxt))))

; A placement that is not skewed lands (within the home page and its overflow).
(defthm fn-mpxt-put-places-unless-skewed
  (implies (and (fn-mpxtp fn-mpxt) (natp tag) (posp (fn-mpxt-pages fn-mpxt))
                (not (fn-mpxt-skewp tag fn-mpxt)))
           (mv-nth 0 (fn-mpxt-put tag seq fn-mpxt)))
  :hints (("Goal" :in-theory (e/d (fn-mpxt-put) (fn-mpxt-page-fullp fn-mpxt-find-empty))
           :expand ((fn-mpxt-put-run tag seq (fn-mpx-home tag (fn-mpxt-pages fn-mpxt)) (fn-mpxt-pages fn-mpxt) fn-mpxt)
                    (fn-mpxt-put-run tag seq (fn-mpxt-next (fn-mpx-home tag (fn-mpxt-pages fn-mpxt)) (fn-mpxt-pages fn-mpxt))
                                     (+ -1 (fn-mpxt-pages fn-mpxt)) fn-mpxt)))))

; A tag that is not skewed reads at most two pages.
(defthm fn-mpxt-page-need-two-unless-skewed
  (implies (and (natp tag) (not (fn-mpxt-skewp tag fn-mpxt)))
           (<= (fn-mpxt-candidates-pages tag fn-mpxt) 2))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fn-mpxt-page-fullp fn-mpxt-run-pages-is-one-plus-the-full-run)
           :expand ((fn-mpxt-run-pages (fn-mpx-home tag (fn-mpxt-pages fn-mpxt)) (fn-mpxt-pages fn-mpxt) fn-mpxt)
                    (fn-mpxt-run-pages (fn-mpxt-next (fn-mpx-home tag (fn-mpxt-pages fn-mpxt)) (fn-mpxt-pages fn-mpxt))
                                       (+ -1 (fn-mpxt-pages fn-mpxt)) fn-mpxt)))))

; Under the condition nothing is refused: no tag is skewed.
(defthm fn-mpxt-no-skew-under-the-condition
  (implies (and (fn-mpxtp fn-mpxt) (natp tag)
                (fn-mpxt-no-adjacent-fullp (fn-mpxt-pages fn-mpxt) fn-mpxt))
           (not (fn-mpxt-skewp tag fn-mpxt)))
  :hints (("Goal" :in-theory (disable fn-mpxt-page-fullp fn-mpxt-no-adjacent-fullp-page)
           :use ((:instance fn-mpxt-no-adjacent-fullp-page
                            (np (fn-mpxt-pages fn-mpxt))
                            (q (fn-mpx-home tag (fn-mpxt-pages fn-mpxt))))))))
