; fn: the linear-hashing Message-ID table, executable (lane msgid-linear-
; hash, 2026-10-01; stage 7 of planning/design-store-representation-
; 2026-10-01.md, the index part; the logical side is books/msgid-linear,
; PRF-1218).  Prefix fn-mlh-.
;
; A stobj holding the table's WORDS in page-store pages: 2,048 words a
; page, 1,024 slots a page in two columns (slot J's TAG is word J, its
; SEQ + 1 is word 1024 + J), TAG 0 an empty slot -- the geometry of
; books/msgid-pages-exec (fn-mpxt), with three changes:
;
;   FIXNUM WORDS.  The array's elements are (unsigned-byte 61): the tag is
;   the keyed BLAKE3 word of books/msgid-pages-exec reduced to 60 bits
;   (`fn-mlh-tag': floored at 1), the seq word is SEQ + 1 below 2^60, and
;   bit 60 of slot 0's seq word is the page's OVERFLOW FLAG.  Every word
;   is a fixnum on SBCL x86-64, so the stobj's accessor returns it unboxed
;   and the scan allocates nothing (the representation scholar's finding:
;   fn-mpxt's full 64-bit tags box three slots in four); the slot accessors
;   are `defun-inline'.  MEASURED (persvati, ACL2 8.7 on SBCL, proof_repl
;   mlx, 2026-10-01; sb-ext:get-bytes-consed around 10,000 lookups of
;   distinct Message-IDs <i@x> on tables of 10,000 entries, one candidate
;   each): fn-mpxt-candidates 6,364 bytes consed per lookup (7,548 of the
;   10,000 old tags are at or above 2^62: boxed on every scan step);
;   fn-mlh-candidates 16 bytes per lookup -- the one cons of the
;   single-candidate result list; the scan allocates nothing.  The flag
;   lives in the words so that pages are the state (P8).
;
;   THE ROOT: the round modulus N and the split pointer S beside the page
;   count (N + S pages; N = S = 0 with no pages); the home page is
;   `fn-mpxl-addr' of the tag.
;
;   THE READER follows the home page's flag to the next page, never its
;   fullness (books/msgid-linear explains why a split needs that).
;
; THE ABSTRACTION `fn-mlh-abs' reads the stobj as the logical table of
; books/msgid-linear ((FLAG . ENTRIES) pages in slot order, the root), and
; `fn-mlh-candidates-is-cands' says the word reader IS the logical reader
; of the abstraction: every theorem of the logical book transfers.
; KEYSTONE `fn-mlh-seqs-is-spec-from': under `fn-mlh-faithful' the reader
; equals the walk `fn-mpxt-spec-from' (the catalog's specification,
; books/msgid-pages-exec section 3), by `fn-mpxt-confirm-is-the-spec'.
;
; THE WRITER `fn-mlh-put' places at the first empty slot of the home page,
; else of the next page with the home page's flag set, else NOT AT ALL
; (`:mpx-saturated'; `fn-mlh-saturatedp'); `fn-mlh-put-keeps-candidate'
; and `fn-mlh-put-finds' are its membership facts, `fn-mlh-put-preserves-
; faithful' the commit path's obligation.  THE SPLIT, THE ADD and THE FOLD
; (the catalog's correspondence) follow in the next sections.
;
; GEN: def-representation (the stobj's facts, section 1) and def-loop (the
; scan, the page entries, the move loops) once the generators land.

(in-package "ACL2")
(include-book "msgid-linear")
(include-book "msgid-pages-exec")
(local (include-book "arithmetic/top" :dir :system))

;; The tau system is off in this book (lane tau-pass, tools/tau_cost.py).
(local (in-theory (disable (tau-system))))

; -----------------------------------------------------------------------------
; 0. The 60-bit keyed tag.

(defconst *fn-mlh-page-words* 2048)
(defconst *fn-mlh-page-slots* 1024)
(defconst *fn-mlh-tag-limit* (expt 2 60))    ; tags and seq words are below it
(defconst *fn-mlh-flag* (expt 2 60))         ; the overflow flag, in slot 0's seq word
(defconst *fn-mlh-word-limit* (expt 2 61))   ; every word is below it: a fixnum

; THE KEYED TAG: the first word of the keyed BLAKE3 of the Message-ID
; (books/msgid-pages-exec `fn-mpxt-word' of `fn-ns-mac') reduced to 60
; bits, floored at 1 (0 is the empty slot).
(defun fn-mlh-tag (msgid key)
  (declare (xargs :guard t))
  (if (stringp msgid)
      (max 1 (mod (fn-mpxt-word 8 (fn-ns-mac key (fn-record-string-octets msgid))) *fn-mlh-tag-limit*))
    1))

(defthm fn-mlh-tag-posp
  (posp (fn-mlh-tag msgid key))
  :rule-classes :type-prescription)

(defthm fn-mlh-tag-below
  (< (fn-mlh-tag msgid key) *fn-mlh-tag-limit*)
  :rule-classes :linear)

(in-theory (disable fn-mlh-tag))

; -----------------------------------------------------------------------------
; 1. The stobj and its facts.  GEN: def-representation.

(defstobj fn-mlh
  (fn-mlh-w :type (array (unsigned-byte 61) (0)) :initially 0 :resizable t)
  (fn-mlh-pages :type (integer 0 *) :initially 0)
  (fn-mlh-n :type (integer 0 *) :initially 0)
  (fn-mlh-s :type (integer 0 *) :initially 0)
  (fn-mlh-count :type (integer 0 *) :initially 0)
  (fn-mlh-key :type (array (unsigned-byte 8) (32)) :initially 0)
  (fn-mlh-stuck :type (integer 0 1) :initially 0)
  :inline t)

(local (defthm fn-mlh-wp-nth
  (implies (fn-mlh-wp l)
           (< (nfix (nth i l)) *fn-mlh-word-limit*))
  :hints (("Goal" :in-theory (enable nth unsigned-byte-p)))))
(local (defthm fn-mlh-wp-nth-word
  (implies (and (fn-mlh-wp l) (natp i) (< i (len l)))
           (unsigned-byte-p 61 (nth i l)))
  :hints (("Goal" :in-theory (enable nth)))))
(local (defthm fn-mlh-wp-of-update-nth
  (implies (and (fn-mlh-wp l) (natp i) (< i (len l)) (unsigned-byte-p 61 v))
           (fn-mlh-wp (update-nth i v l)))
  :hints (("Goal" :in-theory (enable update-nth)))))
(local (defthm fn-mlh-len-of-resize-list
  (equal (len (resize-list l n d)) (nfix n))))
(local (defthm fn-mlh-wp-of-resize-list
  (implies (fn-mlh-wp l)
           (fn-mlh-wp (resize-list l n 0)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p)))))
(local (defthm fn-mlh-wp-true-listp
  (implies (fn-mlh-wp l) (true-listp l))))
(local (defthm fn-mlh-keyp-of-update-nth
  (implies (and (fn-mlh-keyp l) (natp i) (< i (len l)) (unsigned-byte-p 8 v))
           (fn-mlh-keyp (update-nth i v l)))
  :hints (("Goal" :in-theory (enable update-nth)))))
(local (defthm fn-mlh-keyp-nth
  (implies (and (fn-mlh-keyp l) (natp i) (< i (len l)))
           (unsigned-byte-p 8 (nth i l)))
  :hints (("Goal" :in-theory (enable nth)))))

(defthm fn-mlh-wi-is-a-word
  (implies (fn-mlhp fn-mlh)
           (< (nfix (fn-mlh-wi i fn-mlh)) *fn-mlh-word-limit*))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn-mlh-wp-nth (l (nth *fn-mlh-wi* fn-mlh))))
           :in-theory (disable fn-mlh-wp-nth))))

(defthm fn-mlh-wi-word
  (implies (and (fn-mlhp fn-mlh) (natp i) (< i (fn-mlh-w-length fn-mlh)))
           (unsigned-byte-p 61 (fn-mlh-wi i fn-mlh)))
  :hints (("Goal" :in-theory (enable fn-mlhp fn-mlh-wi fn-mlh-w-length))))

(defthm fn-mlhp-of-updates
  (implies (fn-mlhp fn-mlh)
           (and (implies (and (natp i) (< i (fn-mlh-w-length fn-mlh)) (unsigned-byte-p 61 v))
                         (fn-mlhp (update-fn-mlh-wi i v fn-mlh)))
                (implies (natp m) (fn-mlhp (resize-fn-mlh-w m fn-mlh)))
                (implies (natp m) (fn-mlhp (update-fn-mlh-pages m fn-mlh)))
                (implies (natp m) (fn-mlhp (update-fn-mlh-n m fn-mlh)))
                (implies (natp m) (fn-mlhp (update-fn-mlh-s m fn-mlh)))
                (implies (natp m) (fn-mlhp (update-fn-mlh-count m fn-mlh)))
                (implies (and (natp i) (< i 32) (unsigned-byte-p 8 v))
                         (fn-mlhp (update-fn-mlh-keyi i v fn-mlh)))
                (implies (or (equal m 0) (equal m 1))
                         (fn-mlhp (update-fn-mlh-stuck m fn-mlh))))))

(defthm fn-mlh-key-length-is-32
  (implies (fn-mlhp fn-mlh)
           (equal (fn-mlh-key-length fn-mlh) 32)))

(defthm fn-mlh-keyi-is-an-octet
  (implies (and (fn-mlhp fn-mlh) (natp i) (< i 32))
           (unsigned-byte-p 8 (fn-mlh-keyi i fn-mlh))))

(defthm fn-mlh-scalars-natp
  (implies (fn-mlhp fn-mlh)
           (and (natp (fn-mlh-pages fn-mlh)) (natp (fn-mlh-n fn-mlh)) (natp (fn-mlh-s fn-mlh))
                (natp (fn-mlh-count fn-mlh)) (natp (fn-mlh-stuck fn-mlh)) (<= (fn-mlh-stuck fn-mlh) 1)))
  :rule-classes ((:rewrite)
                 (:type-prescription :corollary (implies (fn-mlhp fn-mlh) (natp (fn-mlh-pages fn-mlh))))
                 (:type-prescription :corollary (implies (fn-mlhp fn-mlh) (natp (fn-mlh-n fn-mlh))))
                 (:type-prescription :corollary (implies (fn-mlhp fn-mlh) (natp (fn-mlh-s fn-mlh))))
                 (:type-prescription :corollary (implies (fn-mlhp fn-mlh) (natp (fn-mlh-count fn-mlh))))
                 (:type-prescription :corollary (implies (fn-mlhp fn-mlh) (natp (fn-mlh-stuck fn-mlh))))
                 (:linear :corollary (implies (fn-mlhp fn-mlh) (<= (fn-mlh-stuck fn-mlh) 1)))))

; Every field against every write (the frame).
(defthm fn-mlh-w-length-of-updates
  (and (implies (and (natp i) (< i (fn-mlh-w-length fn-mlh)))
                (equal (fn-mlh-w-length (update-fn-mlh-wi i v fn-mlh)) (fn-mlh-w-length fn-mlh)))
       (equal (fn-mlh-w-length (resize-fn-mlh-w m fn-mlh)) (nfix m))
       (equal (fn-mlh-w-length (update-fn-mlh-pages m fn-mlh)) (fn-mlh-w-length fn-mlh))
       (equal (fn-mlh-w-length (update-fn-mlh-n m fn-mlh)) (fn-mlh-w-length fn-mlh))
       (equal (fn-mlh-w-length (update-fn-mlh-s m fn-mlh)) (fn-mlh-w-length fn-mlh))
       (equal (fn-mlh-w-length (update-fn-mlh-count m fn-mlh)) (fn-mlh-w-length fn-mlh))
       (equal (fn-mlh-w-length (update-fn-mlh-keyi i v fn-mlh)) (fn-mlh-w-length fn-mlh))
       (equal (fn-mlh-w-length (update-fn-mlh-stuck m fn-mlh)) (fn-mlh-w-length fn-mlh))))

(defthm fn-mlh-wi-of-updates
  (and (implies (and (natp i) (natp j))
                (equal (fn-mlh-wi i (update-fn-mlh-wi j v fn-mlh))
                       (if (equal i j) v (fn-mlh-wi i fn-mlh))))
       (equal (fn-mlh-wi i (update-fn-mlh-pages m fn-mlh)) (fn-mlh-wi i fn-mlh))
       (equal (fn-mlh-wi i (update-fn-mlh-n m fn-mlh)) (fn-mlh-wi i fn-mlh))
       (equal (fn-mlh-wi i (update-fn-mlh-s m fn-mlh)) (fn-mlh-wi i fn-mlh))
       (equal (fn-mlh-wi i (update-fn-mlh-count m fn-mlh)) (fn-mlh-wi i fn-mlh))
       (equal (fn-mlh-wi i (update-fn-mlh-keyi j v fn-mlh)) (fn-mlh-wi i fn-mlh))
       (equal (fn-mlh-wi i (update-fn-mlh-stuck m fn-mlh)) (fn-mlh-wi i fn-mlh))))

(defthm fn-mlh-scalars-of-updates
  (and (equal (fn-mlh-pages (update-fn-mlh-wi i v fn-mlh)) (fn-mlh-pages fn-mlh))
       (equal (fn-mlh-pages (resize-fn-mlh-w m fn-mlh)) (fn-mlh-pages fn-mlh))
       (equal (fn-mlh-pages (update-fn-mlh-pages m fn-mlh)) m)
       (equal (fn-mlh-pages (update-fn-mlh-n m fn-mlh)) (fn-mlh-pages fn-mlh))
       (equal (fn-mlh-pages (update-fn-mlh-s m fn-mlh)) (fn-mlh-pages fn-mlh))
       (equal (fn-mlh-pages (update-fn-mlh-count m fn-mlh)) (fn-mlh-pages fn-mlh))
       (equal (fn-mlh-pages (update-fn-mlh-keyi i v fn-mlh)) (fn-mlh-pages fn-mlh))
       (equal (fn-mlh-pages (update-fn-mlh-stuck m fn-mlh)) (fn-mlh-pages fn-mlh))
       (equal (fn-mlh-n (update-fn-mlh-wi i v fn-mlh)) (fn-mlh-n fn-mlh))
       (equal (fn-mlh-n (resize-fn-mlh-w m fn-mlh)) (fn-mlh-n fn-mlh))
       (equal (fn-mlh-n (update-fn-mlh-pages m fn-mlh)) (fn-mlh-n fn-mlh))
       (equal (fn-mlh-n (update-fn-mlh-n m fn-mlh)) m)
       (equal (fn-mlh-n (update-fn-mlh-s m fn-mlh)) (fn-mlh-n fn-mlh))
       (equal (fn-mlh-n (update-fn-mlh-count m fn-mlh)) (fn-mlh-n fn-mlh))
       (equal (fn-mlh-n (update-fn-mlh-keyi i v fn-mlh)) (fn-mlh-n fn-mlh))
       (equal (fn-mlh-n (update-fn-mlh-stuck m fn-mlh)) (fn-mlh-n fn-mlh))
       (equal (fn-mlh-s (update-fn-mlh-wi i v fn-mlh)) (fn-mlh-s fn-mlh))
       (equal (fn-mlh-s (resize-fn-mlh-w m fn-mlh)) (fn-mlh-s fn-mlh))
       (equal (fn-mlh-s (update-fn-mlh-pages m fn-mlh)) (fn-mlh-s fn-mlh))
       (equal (fn-mlh-s (update-fn-mlh-n m fn-mlh)) (fn-mlh-s fn-mlh))
       (equal (fn-mlh-s (update-fn-mlh-s m fn-mlh)) m)
       (equal (fn-mlh-s (update-fn-mlh-count m fn-mlh)) (fn-mlh-s fn-mlh))
       (equal (fn-mlh-s (update-fn-mlh-keyi i v fn-mlh)) (fn-mlh-s fn-mlh))
       (equal (fn-mlh-s (update-fn-mlh-stuck m fn-mlh)) (fn-mlh-s fn-mlh))
       (equal (fn-mlh-count (update-fn-mlh-wi i v fn-mlh)) (fn-mlh-count fn-mlh))
       (equal (fn-mlh-count (resize-fn-mlh-w m fn-mlh)) (fn-mlh-count fn-mlh))
       (equal (fn-mlh-count (update-fn-mlh-pages m fn-mlh)) (fn-mlh-count fn-mlh))
       (equal (fn-mlh-count (update-fn-mlh-n m fn-mlh)) (fn-mlh-count fn-mlh))
       (equal (fn-mlh-count (update-fn-mlh-s m fn-mlh)) (fn-mlh-count fn-mlh))
       (equal (fn-mlh-count (update-fn-mlh-count m fn-mlh)) m)
       (equal (fn-mlh-count (update-fn-mlh-keyi i v fn-mlh)) (fn-mlh-count fn-mlh))
       (equal (fn-mlh-count (update-fn-mlh-stuck m fn-mlh)) (fn-mlh-count fn-mlh))
       (equal (fn-mlh-stuck (update-fn-mlh-wi i v fn-mlh)) (fn-mlh-stuck fn-mlh))
       (equal (fn-mlh-stuck (resize-fn-mlh-w m fn-mlh)) (fn-mlh-stuck fn-mlh))
       (equal (fn-mlh-stuck (update-fn-mlh-pages m fn-mlh)) (fn-mlh-stuck fn-mlh))
       (equal (fn-mlh-stuck (update-fn-mlh-n m fn-mlh)) (fn-mlh-stuck fn-mlh))
       (equal (fn-mlh-stuck (update-fn-mlh-s m fn-mlh)) (fn-mlh-stuck fn-mlh))
       (equal (fn-mlh-stuck (update-fn-mlh-count m fn-mlh)) (fn-mlh-stuck fn-mlh))
       (equal (fn-mlh-stuck (update-fn-mlh-keyi i v fn-mlh)) (fn-mlh-stuck fn-mlh))
       (equal (fn-mlh-stuck (update-fn-mlh-stuck m fn-mlh)) m)
       (equal (fn-mlh-keyi i (update-fn-mlh-wi j v fn-mlh)) (fn-mlh-keyi i fn-mlh))
       (equal (fn-mlh-keyi i (resize-fn-mlh-w m fn-mlh)) (fn-mlh-keyi i fn-mlh))
       (equal (fn-mlh-keyi i (update-fn-mlh-pages m fn-mlh)) (fn-mlh-keyi i fn-mlh))
       (equal (fn-mlh-keyi i (update-fn-mlh-n m fn-mlh)) (fn-mlh-keyi i fn-mlh))
       (equal (fn-mlh-keyi i (update-fn-mlh-s m fn-mlh)) (fn-mlh-keyi i fn-mlh))
       (equal (fn-mlh-keyi i (update-fn-mlh-count m fn-mlh)) (fn-mlh-keyi i fn-mlh))
       (equal (fn-mlh-keyi i (update-fn-mlh-stuck m fn-mlh)) (fn-mlh-keyi i fn-mlh))
       (implies (and (natp i) (natp j))
                (equal (fn-mlh-keyi i (update-fn-mlh-keyi j v fn-mlh))
                       (if (equal i j) v (fn-mlh-keyi i fn-mlh))))))

;; The primitives are closed from here on: every fact about them is above.
(in-theory (disable fn-mlhp fn-mlh-wi update-fn-mlh-wi fn-mlh-w-length resize-fn-mlh-w
                    fn-mlh-pages update-fn-mlh-pages fn-mlh-n update-fn-mlh-n
                    fn-mlh-s update-fn-mlh-s fn-mlh-count update-fn-mlh-count
                    fn-mlh-keyi update-fn-mlh-keyi fn-mlh-key-length
                    fn-mlh-stuck update-fn-mlh-stuck))

; The table's key, as the list of its 32 octets from index I.
(defun fn-mlh-key-from (i fn-mlh)
  (declare (xargs :stobjs fn-mlh :guard (natp i) :measure (nfix (- 32 (nfix i)))))
  (if (>= (nfix i) 32)
      nil
    (cons (fn-mlh-keyi (nfix i) fn-mlh) (fn-mlh-key-from (1+ (nfix i)) fn-mlh))))

(defun fn-mlh-key-octets (fn-mlh)
  (declare (xargs :stobjs fn-mlh))
  (fn-mlh-key-from 0 fn-mlh))

(defthm fn-mlh-key-from-of-updates
  (and (equal (fn-mlh-key-from i (update-fn-mlh-wi j v fn-mlh)) (fn-mlh-key-from i fn-mlh))
       (equal (fn-mlh-key-from i (resize-fn-mlh-w m fn-mlh)) (fn-mlh-key-from i fn-mlh))
       (equal (fn-mlh-key-from i (update-fn-mlh-pages m fn-mlh)) (fn-mlh-key-from i fn-mlh))
       (equal (fn-mlh-key-from i (update-fn-mlh-n m fn-mlh)) (fn-mlh-key-from i fn-mlh))
       (equal (fn-mlh-key-from i (update-fn-mlh-s m fn-mlh)) (fn-mlh-key-from i fn-mlh))
       (equal (fn-mlh-key-from i (update-fn-mlh-count m fn-mlh)) (fn-mlh-key-from i fn-mlh))
       (equal (fn-mlh-key-from i (update-fn-mlh-stuck m fn-mlh)) (fn-mlh-key-from i fn-mlh))))

(defthm fn-mlh-key-octets-of-updates
  (and (equal (fn-mlh-key-octets (update-fn-mlh-wi j v fn-mlh)) (fn-mlh-key-octets fn-mlh))
       (equal (fn-mlh-key-octets (resize-fn-mlh-w m fn-mlh)) (fn-mlh-key-octets fn-mlh))
       (equal (fn-mlh-key-octets (update-fn-mlh-pages m fn-mlh)) (fn-mlh-key-octets fn-mlh))
       (equal (fn-mlh-key-octets (update-fn-mlh-n m fn-mlh)) (fn-mlh-key-octets fn-mlh))
       (equal (fn-mlh-key-octets (update-fn-mlh-s m fn-mlh)) (fn-mlh-key-octets fn-mlh))
       (equal (fn-mlh-key-octets (update-fn-mlh-count m fn-mlh)) (fn-mlh-key-octets fn-mlh))
       (equal (fn-mlh-key-octets (update-fn-mlh-stuck m fn-mlh)) (fn-mlh-key-octets fn-mlh))))

(in-theory (disable fn-mlh-key-octets))

; -----------------------------------------------------------------------------
; 2. The geometry, the root and the slot accessors.

; The root: no pages at all, or N + S pages with 0 <= S < N.
(defun fn-mlh-rootp (fn-mlh)
  (declare (xargs :stobjs fn-mlh))
  (if (zp (fn-mlh-pages fn-mlh))
      (and (equal (fn-mlh-n fn-mlh) 0) (equal (fn-mlh-s fn-mlh) 0))
    (and (posp (fn-mlh-n fn-mlh)) (< (fn-mlh-s fn-mlh) (fn-mlh-n fn-mlh))
         (equal (fn-mlh-pages fn-mlh) (+ (fn-mlh-n fn-mlh) (fn-mlh-s fn-mlh))))))

; Well formed: the pages fit the words and the root is a root.
(defun fn-mlh-wfp (fn-mlh)
  (declare (xargs :stobjs fn-mlh))
  (and (<= (* *fn-mlh-page-words* (fn-mlh-pages fn-mlh)) (fn-mlh-w-length fn-mlh))
       (fn-mlh-rootp fn-mlh)))

(defun fn-mlh-slot (p j)
  (declare (xargs :guard (and (natp p) (natp j))))
  (+ (* *fn-mlh-page-words* p) j))

(defun fn-mlh-slot-guardp (p j fn-mlh)
  (declare (xargs :stobjs fn-mlh))
  (and (natp p) (natp j) (< j *fn-mlh-page-slots*)
       (< p (fn-mlh-pages fn-mlh)) (fn-mlh-wfp fn-mlh)))

; The tag word of slot J on page P, a fixnum.
(defun-inline fn-mlh-tag-at (p j fn-mlh)
  (declare (xargs :stobjs fn-mlh :guard (fn-mlh-slot-guardp p j fn-mlh)))
  (nfix (fn-mlh-wi (fn-mlh-slot p j) fn-mlh)))

; The seq word of slot J (SEQ + 1 with the flag bit, 0 in an empty slot).
(defun-inline fn-mlh-seqw (p j fn-mlh)
  (declare (xargs :stobjs fn-mlh :guard (fn-mlh-slot-guardp p j fn-mlh)))
  (nfix (fn-mlh-wi (+ *fn-mlh-page-slots* (fn-mlh-slot p j)) fn-mlh)))

; The flag part of a seq word, and the word without it.
(defun fn-mlh-flag-part (w)
  (declare (xargs :guard (natp w)))
  (if (< w *fn-mlh-flag*) 0 *fn-mlh-flag*))

(defun-inline fn-mlh-seq-at (p j fn-mlh)
  (declare (xargs :stobjs fn-mlh :guard (fn-mlh-slot-guardp p j fn-mlh)))
  (let ((w (fn-mlh-seqw p j fn-mlh)))
    (if (< w *fn-mlh-flag*) w (- w *fn-mlh-flag*))))

; THE OVERFLOW FLAG of page P: bit 60 of slot 0's seq word.
(defun-inline fn-mlh-ovf (p fn-mlh)
  (declare (xargs :stobjs fn-mlh :guard (and (natp p) (< p (fn-mlh-pages fn-mlh)) (fn-mlh-wfp fn-mlh))))
  (<= *fn-mlh-flag* (fn-mlh-seqw p 0 fn-mlh)))

;; The inline accessors' macro names serve in theory expressions.
(add-macro-fn fn-mlh-tag-at fn-mlh-tag-at$inline)
(add-macro-fn fn-mlh-seqw fn-mlh-seqw$inline)
(add-macro-fn fn-mlh-seq-at fn-mlh-seq-at$inline)
(add-macro-fn fn-mlh-ovf fn-mlh-ovf$inline)

(defthm fn-mlh-tag-at-natp
  (natp (fn-mlh-tag-at p j fn-mlh))
  :rule-classes :type-prescription)
(defthm fn-mlh-seqw-natp
  (natp (fn-mlh-seqw p j fn-mlh))
  :rule-classes :type-prescription)
(defthm fn-mlh-seq-at-natp
  (natp (fn-mlh-seq-at p j fn-mlh))
  :rule-classes :type-prescription)
(defthm fn-mlh-ovf-booleanp
  (booleanp (fn-mlh-ovf p fn-mlh))
  :rule-classes :type-prescription)

(defthm fn-mlh-tag-at-is-a-word
  (implies (fn-mlhp fn-mlh)
           (< (fn-mlh-tag-at p j fn-mlh) *fn-mlh-word-limit*))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn-mlh-wi-is-a-word (i (fn-mlh-slot p j))))
           :in-theory (disable fn-mlh-wi-is-a-word))))

(defthm fn-mlh-seqw-is-a-word
  (implies (fn-mlhp fn-mlh)
           (< (fn-mlh-seqw p j fn-mlh) *fn-mlh-word-limit*))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn-mlh-wi-is-a-word (i (+ *fn-mlh-page-slots* (fn-mlh-slot p j)))))
           :in-theory (disable fn-mlh-wi-is-a-word))))

(defthm fn-mlh-seq-at-below
  (implies (fn-mlhp fn-mlh)
           (< (fn-mlh-seq-at p j fn-mlh) *fn-mlh-tag-limit*))
  :rule-classes :linear
  :hints (("Goal" :use fn-mlh-seqw-is-a-word :in-theory (disable fn-mlh-seqw-is-a-word))))

(defthm fn-mlh-slot-natp
  (implies (and (natp p) (natp j)) (natp (fn-mlh-slot p j)))
  :rule-classes :type-prescription)

(defthm fn-mlh-slot-equal
  (implies (and (natp q) (natp i) (< i *fn-mlh-page-slots*)
                (natp p) (natp j) (< j *fn-mlh-page-slots*))
           (iff (equal (fn-mlh-slot q i) (fn-mlh-slot p j))
                (and (equal q p) (equal i j))))
  :hints (("Goal" :cases ((< q p) (< p q)))))

(defthm fn-mlh-slot-is-not-a-seq-word
  (implies (and (natp q) (natp i) (< i *fn-mlh-page-slots*)
                (natp p) (natp j) (< j *fn-mlh-page-slots*))
           (not (equal (fn-mlh-slot q i) (+ *fn-mlh-page-slots* (fn-mlh-slot p j)))))
  :hints (("Goal" :cases ((< q p) (< p q)))))

(in-theory (disable fn-mlh-slot fn-mlh-tag-at fn-mlh-seqw fn-mlh-seq-at fn-mlh-ovf))

; The slot accessors against the scalar writes.
(defthm fn-mlh-accessors-of-scalar-updates
  (and (equal (fn-mlh-tag-at p j (update-fn-mlh-pages m fn-mlh)) (fn-mlh-tag-at p j fn-mlh))
       (equal (fn-mlh-tag-at p j (update-fn-mlh-n m fn-mlh)) (fn-mlh-tag-at p j fn-mlh))
       (equal (fn-mlh-tag-at p j (update-fn-mlh-s m fn-mlh)) (fn-mlh-tag-at p j fn-mlh))
       (equal (fn-mlh-tag-at p j (update-fn-mlh-count m fn-mlh)) (fn-mlh-tag-at p j fn-mlh))
       (equal (fn-mlh-tag-at p j (update-fn-mlh-stuck m fn-mlh)) (fn-mlh-tag-at p j fn-mlh))
       (equal (fn-mlh-tag-at p j (update-fn-mlh-keyi i v fn-mlh)) (fn-mlh-tag-at p j fn-mlh))
       (equal (fn-mlh-seqw p j (update-fn-mlh-pages m fn-mlh)) (fn-mlh-seqw p j fn-mlh))
       (equal (fn-mlh-seqw p j (update-fn-mlh-n m fn-mlh)) (fn-mlh-seqw p j fn-mlh))
       (equal (fn-mlh-seqw p j (update-fn-mlh-s m fn-mlh)) (fn-mlh-seqw p j fn-mlh))
       (equal (fn-mlh-seqw p j (update-fn-mlh-count m fn-mlh)) (fn-mlh-seqw p j fn-mlh))
       (equal (fn-mlh-seqw p j (update-fn-mlh-stuck m fn-mlh)) (fn-mlh-seqw p j fn-mlh))
       (equal (fn-mlh-seqw p j (update-fn-mlh-keyi i v fn-mlh)) (fn-mlh-seqw p j fn-mlh)))
  :hints (("Goal" :in-theory (enable fn-mlh-tag-at fn-mlh-seqw))))

(defthm fn-mlh-seq-at-is-seqw
  (equal (fn-mlh-seq-at p j fn-mlh)
         (if (< (fn-mlh-seqw p j fn-mlh) *fn-mlh-flag*)
             (fn-mlh-seqw p j fn-mlh)
           (- (fn-mlh-seqw p j fn-mlh) *fn-mlh-flag*)))
  :hints (("Goal" :in-theory (enable fn-mlh-seq-at))))

(defthm fn-mlh-ovf-is-seqw
  (equal (fn-mlh-ovf p fn-mlh)
         (<= *fn-mlh-flag* (fn-mlh-seqw p 0 fn-mlh)))
  :hints (("Goal" :in-theory (enable fn-mlh-ovf))))

; -----------------------------------------------------------------------------
; 3. The reader: the scan of one page (tail recursive, fixnum compares),
; the candidates of a tag.  GEN: def-loop.

; The slots below J of page P whose tag is TAG, their seqs inserted into ACC.
(defun fn-mlh-scan (tag p j acc fn-mlh)
  (declare (xargs :stobjs fn-mlh :measure (nfix j)
                  :guard (and (natp tag) (natp p) (natp j) (<= j *fn-mlh-page-slots*)
                              (< p (fn-mlh-pages fn-mlh)) (fn-mlh-wfp fn-mlh)
                              (nat-listp acc)))
           (type (unsigned-byte 60) tag))
  (if (zp j)
      acc
    (let* ((j (1- j))
           (acc (if (and (= tag (fn-mlh-tag-at p j fn-mlh))
                         (<= 1 (fn-mlh-seq-at p j fn-mlh)))
                    (fn-mpxt-ins (1- (fn-mlh-seq-at p j fn-mlh)) acc)
                  acc)))
      (fn-mlh-scan tag p j acc fn-mlh))))

(defthm fn-mlh-scan-nat-listp
  (implies (nat-listp acc)
           (nat-listp (fn-mlh-scan tag p j acc fn-mlh))))

(defthm fn-mlh-scan-ascending
  (implies (and (nat-listp acc) (fn-mpx-ascendingp acc))
           (fn-mpx-ascendingp (fn-mlh-scan tag p j acc fn-mlh))))

; THE CANDIDATES: the home page's seqs for TAG and, under the home page's
; flag, the next page's.  At most two pages read, by construction.
(defun fn-mlh-candidates (tag fn-mlh)
  (declare (xargs :stobjs fn-mlh
                  :guard (and (natp tag) (< tag *fn-mlh-tag-limit*) (fn-mlh-wfp fn-mlh))
                  :guard-hints (("Goal" :use ((:instance fn-mpxl-addr-below (n (fn-mlh-n fn-mlh)) (s (fn-mlh-s fn-mlh))))
                                 :in-theory (disable fn-mpxl-addr-below)))))
  (let ((np (fn-mlh-pages fn-mlh)))
    (if (zp np)
        nil
      (let* ((h (fn-mpxl-addr tag (fn-mlh-n fn-mlh) (fn-mlh-s fn-mlh)))
             (acc (fn-mlh-scan tag h *fn-mlh-page-slots* nil fn-mlh)))
        (if (and (fn-mlh-ovf h fn-mlh) (< (+ 1 h) np))
            (fn-mlh-scan tag (+ 1 h) *fn-mlh-page-slots* acc fn-mlh)
          acc)))))

(defthm fn-mlh-candidates-nat-listp
  (nat-listp (fn-mlh-candidates tag fn-mlh)))

(defthm fn-mlh-candidates-ascending
  (fn-mpx-ascendingp (fn-mlh-candidates tag fn-mlh)))

(defthm fn-mlh-candidates-true-listp
  (true-listp (fn-mlh-candidates tag fn-mlh))
  :hints (("Goal" :use fn-mlh-candidates-nat-listp
           :in-theory (disable fn-mlh-candidates-nat-listp fn-mlh-candidates))))

; THE PAGED READER (the catalog's shape): the candidates of the Message-ID's
; keyed tag, confirmed against the rows by fn-mpxt-confirm.
(defun fn-mlh-seqs (msgid rows fn-mlh)
  (declare (xargs :stobjs fn-mlh :guard (and (true-listp rows) (fn-mlh-wfp fn-mlh))))
  (fn-mpxt-confirm msgid (fn-mlh-candidates (fn-mlh-tag msgid (fn-mlh-key-octets fn-mlh)) fn-mlh) rows))

; -----------------------------------------------------------------------------
; 4. THE ABSTRACTION: the stobj read as the logical table.  The entries of
; page P from slot J up, in slot order; the pages from P up as (FLAG .
; ENTRIES); the table with its root.  GEN: def-loop.

(defun fn-mlh-pe (p j fn-mlh)
  (declare (xargs :stobjs fn-mlh :measure (nfix (- *fn-mlh-page-slots* (nfix j)))
                  :guard (and (natp p) (natp j) (< p (fn-mlh-pages fn-mlh)) (fn-mlh-wfp fn-mlh))))
  (if (>= (nfix j) *fn-mlh-page-slots*)
      nil
    (if (and (not (equal 0 (fn-mlh-tag-at p (nfix j) fn-mlh)))
             (<= 1 (fn-mlh-seq-at p (nfix j) fn-mlh)))
        (cons (cons (fn-mlh-tag-at p (nfix j) fn-mlh) (1- (fn-mlh-seq-at p (nfix j) fn-mlh)))
              (fn-mlh-pe p (1+ (nfix j)) fn-mlh))
      (fn-mlh-pe p (1+ (nfix j)) fn-mlh))))

(defthm fn-mlh-pe-pagep
  (fn-mpx-pagep (fn-mlh-pe p j fn-mlh)))

(defun fn-mlh-abs-pages (p fn-mlh)
  (declare (xargs :stobjs fn-mlh :measure (nfix (- (nfix (fn-mlh-pages fn-mlh)) (nfix p)))
                  :guard (and (natp p) (<= p (fn-mlh-pages fn-mlh)) (fn-mlh-wfp fn-mlh))))
  (if (>= (nfix p) (nfix (fn-mlh-pages fn-mlh)))
      nil
    (cons (cons (fn-mlh-ovf (nfix p) fn-mlh) (fn-mlh-pe (nfix p) 0 fn-mlh))
          (fn-mlh-abs-pages (1+ (nfix p)) fn-mlh))))

(defun fn-mlh-abs (fn-mlh)
  (declare (xargs :stobjs fn-mlh :guard (fn-mlh-wfp fn-mlh)))
  (fn-mpxl-make (fn-mlh-abs-pages 0 fn-mlh) (fn-mlh-n fn-mlh) (fn-mlh-s fn-mlh)))

(defthm fn-mlh-abs-pages-pagesp
  (fn-mpxl-pagesp (fn-mlh-abs-pages p fn-mlh)))

(defthm fn-mlh-abs-pages-len
  (implies (natp (fn-mlh-pages fn-mlh))
           (equal (len (fn-mlh-abs-pages p fn-mlh)) (nfix (- (fn-mlh-pages fn-mlh) (nfix p))))))

; The page at I of the abstraction from P: page P + I of the stobj.
(local (defun fn-mlh-pa-ind (i p fn-mlh)
  (declare (xargs :stobjs fn-mlh :verify-guards nil
                  :measure (nfix (- (nfix (fn-mlh-pages fn-mlh)) (nfix p)))))
  (if (or (>= (nfix p) (nfix (fn-mlh-pages fn-mlh))) (zp i))
      (list i p)
    (fn-mlh-pa-ind (1- i) (1+ (nfix p)) fn-mlh))))

(local (defthm fn-mlh-nth-of-abs-pages
  (implies (and (natp i) (natp p) (natp (fn-mlh-pages fn-mlh)))
           (equal (nth i (fn-mlh-abs-pages p fn-mlh))
                  (if (< (+ p i) (fn-mlh-pages fn-mlh))
                      (cons (fn-mlh-ovf (+ p i) fn-mlh) (fn-mlh-pe (+ p i) 0 fn-mlh))
                    nil)))
  :hints (("Goal" :induct (fn-mlh-pa-ind i p fn-mlh)
           :in-theory (e/d (nth) (fn-mlh-pe))
           :expand ((fn-mlh-abs-pages p fn-mlh))))))

(defthm fn-mlh-page-of-abs-pages
  (implies (and (natp i) (natp p) (natp (fn-mlh-pages fn-mlh)))
           (equal (fn-mpxl-page i (fn-mlh-abs-pages p fn-mlh))
                  (if (< (+ p i) (fn-mlh-pages fn-mlh))
                      (cons (fn-mlh-ovf (+ p i) fn-mlh) (fn-mlh-pe (+ p i) 0 fn-mlh))
                    nil)))
  :hints (("Goal" :in-theory (e/d (fn-mpxl-page) (fn-mlh-abs-pages fn-mlh-pe)))))

(defthm fn-mlh-abs-tabp
  (implies (and (fn-mlhp fn-mlh) (fn-mlh-wfp fn-mlh) (posp (fn-mlh-pages fn-mlh)))
           (fn-mpxl-tabp (fn-mlh-abs fn-mlh))))

(in-theory (disable fn-mlh-abs))

; --- the scan is the logical seqs of the page's entries ---

; The entries of the slots below J, in slot order.
(defun fn-mlh-pe-upto (p j fn-mlh)
  (declare (xargs :stobjs fn-mlh :measure (nfix j) :verify-guards nil))
  (if (zp j)
      nil
    (let ((j (1- j)))
      (append (fn-mlh-pe-upto p j fn-mlh)
              (if (and (not (equal 0 (fn-mlh-tag-at p j fn-mlh)))
                       (<= 1 (fn-mlh-seq-at p j fn-mlh)))
                  (list (cons (fn-mlh-tag-at p j fn-mlh) (1- (fn-mlh-seq-at p j fn-mlh))))
                nil)))))

(local (defthm fn-mlh-ins-is-mpxl-ins
  (equal (fn-mpxt-ins s l) (fn-mpxl-ins s l))
  :hints (("Goal" :in-theory (enable fn-mpxl-ins)))))

(defthm fn-mlh-scan-is-seqs-upto
  (implies (posp tag)
           (equal (fn-mlh-scan tag p j acc fn-mlh)
                  (fn-mpxl-seqs tag (fn-mlh-pe-upto p j fn-mlh) acc)))
  :hints (("Goal" :induct (fn-mlh-scan tag p j acc fn-mlh))))

(local (defthm fn-mlh-append-assoc
  (equal (append (append a b) c) (append a (append b c)))))

(defthm fn-mlh-pe-upto-pe
  (implies (and (natp j) (<= j *fn-mlh-page-slots*))
           (equal (append (fn-mlh-pe-upto p j fn-mlh) (fn-mlh-pe p j fn-mlh))
                  (fn-mlh-pe p 0 fn-mlh)))
  :hints (("Goal" :induct (fn-mlh-pe-upto p j fn-mlh)
           :expand ((fn-mlh-pe p (+ -1 j) fn-mlh)))))

(defthm fn-mlh-pe-upto-all
  (equal (fn-mlh-pe-upto p *fn-mlh-page-slots* fn-mlh) (fn-mlh-pe p 0 fn-mlh))
  :hints (("Goal" :use ((:instance fn-mlh-pe-upto-pe (j *fn-mlh-page-slots*)))
           :expand ((fn-mlh-pe p *fn-mlh-page-slots* fn-mlh))
           :in-theory (disable fn-mlh-pe-upto-pe fn-mlh-pe-upto fn-mlh-pe))))

(defthm fn-mlh-scan-is-seqs
  (implies (posp tag)
           (equal (fn-mlh-scan tag p *fn-mlh-page-slots* acc fn-mlh)
                  (fn-mpxl-seqs tag (fn-mlh-pe p 0 fn-mlh) acc)))
  :hints (("Goal" :in-theory (disable fn-mlh-scan fn-mlh-pe fn-mlh-pe-upto))))

(in-theory (disable fn-mlh-scan-is-seqs-upto))

; THE BRIDGE: the word reader is the logical reader of the abstraction.
(defthm fn-mlh-candidates-is-cands
  (implies (and (fn-mlhp fn-mlh) (fn-mlh-wfp fn-mlh) (posp (fn-mlh-pages fn-mlh)) (posp tag))
           (equal (fn-mlh-candidates tag fn-mlh)
                  (fn-mpxl-cands tag (fn-mlh-abs fn-mlh))))
  :hints (("Goal" :in-theory (e/d (fn-mlh-abs fn-mpxl-cands) (fn-mlh-scan fn-mlh-pe fn-mpxl-addr-below))
           :use ((:instance fn-mpxl-addr-below (n (fn-mlh-n fn-mlh)) (s (fn-mlh-s fn-mlh)))))))

; -----------------------------------------------------------------------------
; 5. The faithful relation and the reader keystone.

; FAITHFUL from I (the catalog's row model): every row at or after I is
; among its own keyed tag's candidates.
(defun fn-mlh-faithful-from (i rows fn-mlh)
  (declare (xargs :stobjs fn-mlh
                  :guard (and (natp i) (true-listp rows) (fn-mlh-wfp fn-mlh))
                  :measure (nfix (- (len rows) (nfix i)))
                  :guard-hints (("Goal" :in-theory (disable fn-mlh-candidates)))))
  (if (>= (nfix i) (len rows))
      t
    (and (member-equal (nfix i)
                       (fn-mlh-candidates (fn-mlh-tag (fn-record-msgid (nth (nfix i) rows))
                                                      (fn-mlh-key-octets fn-mlh))
                                          fn-mlh))
         (fn-mlh-faithful-from (1+ (nfix i)) rows fn-mlh))))

; The slot invariant: every seq in the table below N (the logical okp of
; the abstraction; nothing with no pages).
(defun fn-mlh-okp (n fn-mlh)
  (declare (xargs :stobjs fn-mlh :guard (and (natp n) (fn-mlh-wfp fn-mlh))))
  (or (zp (fn-mlh-pages fn-mlh))
      (fn-mpxl-okp (fn-mlh-abs fn-mlh) n)))

(defun fn-mlh-faithful (rows fn-mlh)
  (declare (xargs :stobjs fn-mlh :guard (and (true-listp rows) (fn-mlh-wfp fn-mlh))))
  (and (fn-mlh-okp (len rows) fn-mlh)
       (fn-mlh-faithful-from 0 rows fn-mlh)))

(defthm fn-mlh-faithful-from-complete
  (implies (fn-mlh-faithful-from i rows fn-mlh)
           (fn-mpxt-complete-from i msgid (fn-mlh-candidates (fn-mlh-tag msgid (fn-mlh-key-octets fn-mlh)) fn-mlh) rows))
  :hints (("Goal" :induct (fn-mlh-faithful-from i rows fn-mlh)
           :in-theory (e/d (fn-mpxt-hitp fn-mpxt-complete-from) (fn-mlh-candidates)))))

(defthm fn-mlh-candidates-no-pages
  (implies (zp (fn-mlh-pages fn-mlh))
           (equal (fn-mlh-candidates tag fn-mlh) nil)))

(defthm fn-mlh-candidates-below
  (implies (and (fn-mlhp fn-mlh) (fn-mlh-wfp fn-mlh) (posp tag) (fn-mlh-okp n fn-mlh))
           (fn-mpx-below-p (fn-mlh-candidates tag fn-mlh) n))
  :hints (("Goal" :in-theory (disable fn-mlh-candidates fn-mpxl-okp fn-mpxl-cands)
           :cases ((posp (fn-mlh-pages fn-mlh))))))

(in-theory (disable fn-mlh-candidates fn-mlh-okp))

; KEYSTONE: the word reader is the walk, under the faithful relation.
(defthm fn-mlh-seqs-is-spec-from
  (implies (and (fn-mlhp fn-mlh) (fn-mlh-wfp fn-mlh)
                (fn-mlh-faithful rows fn-mlh))
           (equal (fn-mlh-seqs msgid rows fn-mlh)
                  (fn-mpxt-spec-from 0 msgid rows)))
  :hints (("Goal" :in-theory (e/d (fn-mlh-seqs fn-mlh-faithful)
                                  (fn-mlh-candidates fn-mpxt-confirm fn-mlh-faithful-from
                                   fn-mlh-okp fn-mpxt-spec-from fn-mpxt-complete-from))
           :use ((:instance fn-mpxt-confirm-is-the-spec
                            (seqs (fn-mlh-candidates (fn-mlh-tag msgid (fn-mlh-key-octets fn-mlh)) fn-mlh)))
                 (:instance fn-mlh-faithful-from-complete (i 0))
                 (:instance fn-mlh-candidates-below (tag (fn-mlh-tag msgid (fn-mlh-key-octets fn-mlh))) (n (len rows)))
                 (:instance fn-mlh-candidates-ascending (tag (fn-mlh-tag msgid (fn-mlh-key-octets fn-mlh))))
                 (:instance fn-mlh-candidates-nat-listp (tag (fn-mlh-tag msgid (fn-mlh-key-octets fn-mlh))))))))

; -----------------------------------------------------------------------------
; 6. The writer: the first empty slot of the home page, else of the next
; page with the home page's flag set, else NOT AT ALL.

(defun fn-mlh-find-empty (p j fn-mlh)
  (declare (xargs :stobjs fn-mlh
                  :guard (and (natp p) (natp j) (< p (fn-mlh-pages fn-mlh)) (fn-mlh-wfp fn-mlh))
                  :measure (nfix (- *fn-mlh-page-slots* (nfix j)))))
  (if (>= (nfix j) *fn-mlh-page-slots*)
      nil
    (if (equal 0 (fn-mlh-tag-at p (nfix j) fn-mlh))
        (nfix j)
      (fn-mlh-find-empty p (1+ (nfix j)) fn-mlh))))

(defthm fn-mlh-find-empty-in-page
  (implies (fn-mlh-find-empty p j fn-mlh)
           (and (natp (fn-mlh-find-empty p j fn-mlh))
                (< (fn-mlh-find-empty p j fn-mlh) *fn-mlh-page-slots*)))
  :rule-classes ((:rewrite)
                 (:linear :corollary (implies (fn-mlh-find-empty p j fn-mlh)
                                              (< (fn-mlh-find-empty p j fn-mlh) *fn-mlh-page-slots*)))))

(defthm fn-mlh-find-empty-is-empty
  (implies (fn-mlh-find-empty p j fn-mlh)
           (equal (fn-mlh-tag-at p (fn-mlh-find-empty p j fn-mlh) fn-mlh) 0)))

(defthm fn-mlh-find-empty-ge
  (implies (and (fn-mlh-find-empty p j fn-mlh) (natp j))
           (<= j (fn-mlh-find-empty p j fn-mlh)))
  :rule-classes :linear)

; A write of (TAG, SEQ) into slot J of page P keeps the flag part of its
; seq word.
(defun fn-mlh-write-slot (p j tag seq fn-mlh)
  (declare (xargs :stobjs fn-mlh
                  :guard (and (fn-mlh-slot-guardp p j fn-mlh)
                              (natp tag) (< tag *fn-mlh-tag-limit*)
                              (natp seq) (< (+ 1 seq) *fn-mlh-tag-limit*))
                  :guard-hints (("Goal" :in-theory (enable fn-mlh-seqw fn-mlh-slot unsigned-byte-p)))))
  (let* ((flag (fn-mlh-flag-part (fn-mlh-seqw p j fn-mlh)))
         (fn-mlh (update-fn-mlh-wi (fn-mlh-slot p j) tag fn-mlh))
         (fn-mlh (update-fn-mlh-wi (+ *fn-mlh-page-slots* (fn-mlh-slot p j)) (+ 1 seq flag) fn-mlh)))
    fn-mlh))

; Set page P's overflow flag.
(defun fn-mlh-set-ovf (p fn-mlh)
  (declare (xargs :stobjs fn-mlh
                  :guard (and (natp p) (< p (fn-mlh-pages fn-mlh)) (fn-mlh-wfp fn-mlh))
                  :guard-hints (("Goal" :in-theory (enable fn-mlh-seqw fn-mlh-slot unsigned-byte-p)))))
  (let ((w (fn-mlh-seqw p 0 fn-mlh)))
    (if (< w *fn-mlh-flag*)
        (update-fn-mlh-wi (+ *fn-mlh-page-slots* (fn-mlh-slot p 0)) (+ w *fn-mlh-flag*) fn-mlh)
      fn-mlh)))

(defthm fn-mlh-write-slot-frame
  (and (equal (fn-mlh-pages (fn-mlh-write-slot p j tag seq fn-mlh)) (fn-mlh-pages fn-mlh))
       (equal (fn-mlh-n (fn-mlh-write-slot p j tag seq fn-mlh)) (fn-mlh-n fn-mlh))
       (equal (fn-mlh-s (fn-mlh-write-slot p j tag seq fn-mlh)) (fn-mlh-s fn-mlh))
       (equal (fn-mlh-count (fn-mlh-write-slot p j tag seq fn-mlh)) (fn-mlh-count fn-mlh))
       (equal (fn-mlh-stuck (fn-mlh-write-slot p j tag seq fn-mlh)) (fn-mlh-stuck fn-mlh))
       (equal (fn-mlh-key-octets (fn-mlh-write-slot p j tag seq fn-mlh)) (fn-mlh-key-octets fn-mlh))
       (equal (fn-mlh-pages (fn-mlh-set-ovf p fn-mlh)) (fn-mlh-pages fn-mlh))
       (equal (fn-mlh-n (fn-mlh-set-ovf p fn-mlh)) (fn-mlh-n fn-mlh))
       (equal (fn-mlh-s (fn-mlh-set-ovf p fn-mlh)) (fn-mlh-s fn-mlh))
       (equal (fn-mlh-count (fn-mlh-set-ovf p fn-mlh)) (fn-mlh-count fn-mlh))
       (equal (fn-mlh-stuck (fn-mlh-set-ovf p fn-mlh)) (fn-mlh-stuck fn-mlh))
       (equal (fn-mlh-key-octets (fn-mlh-set-ovf p fn-mlh)) (fn-mlh-key-octets fn-mlh))))

(defthm fn-mlh-write-slot-shape
  (implies (and (fn-mlhp fn-mlh) (fn-mlh-slot-guardp p j fn-mlh)
                (natp tag) (< tag *fn-mlh-tag-limit*)
                (natp seq) (< (+ 1 seq) *fn-mlh-tag-limit*))
           (and (fn-mlhp (fn-mlh-write-slot p j tag seq fn-mlh))
                (equal (fn-mlh-w-length (fn-mlh-write-slot p j tag seq fn-mlh)) (fn-mlh-w-length fn-mlh))))
  :hints (("Goal" :in-theory (enable unsigned-byte-p fn-mlh-seqw fn-mlh-slot))))

(defthm fn-mlh-set-ovf-shape
  (implies (and (fn-mlhp fn-mlh) (natp p) (< p (fn-mlh-pages fn-mlh)) (fn-mlh-wfp fn-mlh))
           (and (fn-mlhp (fn-mlh-set-ovf p fn-mlh))
                (equal (fn-mlh-w-length (fn-mlh-set-ovf p fn-mlh)) (fn-mlh-w-length fn-mlh))))
  :hints (("Goal" :in-theory (enable unsigned-byte-p fn-mlh-seqw fn-mlh-slot))))

; The slot accessors after a write: the written slot reads the entry, every
; other slot as before, and every flag as before.
(defthm fn-mlh-tag-at-of-write-slot
  (implies (and (natp q) (natp i) (< i *fn-mlh-page-slots*)
                (natp p) (natp j) (< j *fn-mlh-page-slots*))
           (equal (fn-mlh-tag-at q i (fn-mlh-write-slot p j tag seq fn-mlh))
                  (if (and (equal q p) (equal i j)) (nfix tag) (fn-mlh-tag-at q i fn-mlh))))
  :hints (("Goal" :in-theory (enable fn-mlh-tag-at fn-mlh-seqw))))

(defthm fn-mlh-seqw-of-write-slot
  (implies (and (natp q) (natp i) (< i *fn-mlh-page-slots*)
                (natp p) (natp j) (< j *fn-mlh-page-slots*))
           (equal (fn-mlh-seqw q i (fn-mlh-write-slot p j tag seq fn-mlh))
                  (if (and (equal q p) (equal i j))
                      (nfix (+ 1 seq (fn-mlh-flag-part (fn-mlh-seqw p j fn-mlh))))
                    (fn-mlh-seqw q i fn-mlh))))
  :hints (("Goal" :in-theory (enable fn-mlh-seqw))))

(defthm fn-mlh-tag-at-of-set-ovf
  (implies (and (fn-mlhp fn-mlh) (natp q) (natp i) (< i *fn-mlh-page-slots*) (natp p))
           (equal (fn-mlh-tag-at q i (fn-mlh-set-ovf p fn-mlh)) (fn-mlh-tag-at q i fn-mlh)))
  :hints (("Goal" :in-theory (enable fn-mlh-tag-at fn-mlh-seqw))))

(defthm fn-mlh-seqw-of-set-ovf
  (implies (and (fn-mlhp fn-mlh) (natp q) (natp i) (< i *fn-mlh-page-slots*) (natp p))
           (equal (fn-mlh-seqw q i (fn-mlh-set-ovf p fn-mlh))
                  (if (and (equal q p) (equal i 0) (< (fn-mlh-seqw p 0 fn-mlh) *fn-mlh-flag*))
                      (+ *fn-mlh-flag* (fn-mlh-seqw p 0 fn-mlh))
                    (fn-mlh-seqw q i fn-mlh))))
  :hints (("Goal" :in-theory (enable fn-mlh-seqw))))

(in-theory (disable fn-mlh-write-slot fn-mlh-set-ovf fn-mlh-flag-part))

(defthm fn-mlh-flag-part-of-seqw
  (implies (fn-mlhp fn-mlh)
           (equal (fn-mlh-flag-part (fn-mlh-seqw p j fn-mlh))
                  (if (< (fn-mlh-seqw p j fn-mlh) *fn-mlh-flag*) 0 *fn-mlh-flag*)))
  :hints (("Goal" :in-theory (enable fn-mlh-flag-part))))

; The seq read and the flag after the writes.
(defthm fn-mlh-seq-at-of-write-slot
  (implies (and (fn-mlhp fn-mlh) (natp q) (natp i) (< i *fn-mlh-page-slots*)
                (natp p) (natp j) (< j *fn-mlh-page-slots*)
                (natp seq) (< (+ 1 seq) *fn-mlh-tag-limit*))
           (equal (fn-mlh-seq-at q i (fn-mlh-write-slot p j tag seq fn-mlh))
                  (if (and (equal q p) (equal i j)) (+ 1 seq) (fn-mlh-seq-at q i fn-mlh)))))

(defthm fn-mlh-ovf-of-write-slot
  (implies (and (fn-mlhp fn-mlh) (natp q) (natp p) (natp j) (< j *fn-mlh-page-slots*)
                (natp seq) (< (+ 1 seq) *fn-mlh-tag-limit*))
           (equal (fn-mlh-ovf q (fn-mlh-write-slot p j tag seq fn-mlh))
                  (fn-mlh-ovf q fn-mlh))))

(defthm fn-mlh-seq-at-of-set-ovf
  (implies (and (fn-mlhp fn-mlh) (natp q) (natp i) (< i *fn-mlh-page-slots*) (natp p))
           (equal (fn-mlh-seq-at q i (fn-mlh-set-ovf p fn-mlh)) (fn-mlh-seq-at q i fn-mlh))))

(defthm fn-mlh-ovf-of-set-ovf
  (implies (and (fn-mlhp fn-mlh) (natp q) (natp p))
           (equal (fn-mlh-ovf q (fn-mlh-set-ovf p fn-mlh))
                  (or (equal q p) (fn-mlh-ovf q fn-mlh)))))

(in-theory (disable fn-mlh-seq-at-is-seqw fn-mlh-ovf-is-seqw))

; SATURATED at TAG: no empty slot on its home page, and none on the next
; page or no next page.
(defun fn-mlh-saturatedp (tag fn-mlh)
  (declare (xargs :stobjs fn-mlh
                  :guard (and (natp tag) (< tag *fn-mlh-tag-limit*) (fn-mlh-wfp fn-mlh))
                  :guard-hints (("Goal" :use ((:instance fn-mpxl-addr-below (n (fn-mlh-n fn-mlh)) (s (fn-mlh-s fn-mlh))))
                                 :in-theory (disable fn-mpxl-addr-below)))))
  (let ((np (fn-mlh-pages fn-mlh)))
    (and (not (zp np))
         (let ((h (fn-mpxl-addr tag (fn-mlh-n fn-mlh) (fn-mlh-s fn-mlh))))
           (and (not (fn-mlh-find-empty h 0 fn-mlh))
                (or (>= (+ 1 h) np)
                    (not (fn-mlh-find-empty (+ 1 h) 0 fn-mlh))))))))

; THE PUT; (mv placed fn-mlh).  Nil -- the table unchanged -- when saturated.
(defun fn-mlh-put (tag seq fn-mlh)
  (declare (xargs :stobjs fn-mlh
                  :guard (and (natp tag) (< tag *fn-mlh-tag-limit*)
                              (natp seq) (< (+ 1 seq) *fn-mlh-tag-limit*)
                              (fn-mlh-wfp fn-mlh))
                  :guard-hints (("Goal" :use ((:instance fn-mpxl-addr-below (n (fn-mlh-n fn-mlh)) (s (fn-mlh-s fn-mlh))))
                                 :in-theory (disable fn-mpxl-addr-below fn-mlh-find-empty)))))
  (let ((np (fn-mlh-pages fn-mlh)))
    (if (zp np)
        (mv nil fn-mlh)
      (let* ((h (fn-mpxl-addr tag (fn-mlh-n fn-mlh) (fn-mlh-s fn-mlh)))
             (j (fn-mlh-find-empty h 0 fn-mlh)))
        (if j
            (let ((fn-mlh (fn-mlh-write-slot h j tag seq fn-mlh)))
              (mv t fn-mlh))
          (if (< (+ 1 h) np)
              (let ((j1 (fn-mlh-find-empty (+ 1 h) 0 fn-mlh)))
                (if j1
                    (let* ((fn-mlh (fn-mlh-set-ovf h fn-mlh))
                           (fn-mlh (fn-mlh-write-slot (+ 1 h) j1 tag seq fn-mlh)))
                      (mv t fn-mlh))
                  (mv nil fn-mlh)))
            (mv nil fn-mlh)))))))

(defthm fn-mlh-put-places-iff-not-saturated
  (implies (posp (fn-mlh-pages fn-mlh))
           (iff (mv-nth 0 (fn-mlh-put tag seq fn-mlh))
                (not (fn-mlh-saturatedp tag fn-mlh))))
  :hints (("Goal" :in-theory (disable fn-mlh-find-empty))))

(defthm fn-mlh-put-unplaced-unchanged
  (implies (not (mv-nth 0 (fn-mlh-put tag seq fn-mlh)))
           (equal (mv-nth 1 (fn-mlh-put tag seq fn-mlh)) fn-mlh))
  :hints (("Goal" :in-theory (disable fn-mlh-find-empty))))

(defthm fn-mlh-put-frame
  (and (equal (fn-mlh-pages (mv-nth 1 (fn-mlh-put tag seq fn-mlh))) (fn-mlh-pages fn-mlh))
       (equal (fn-mlh-n (mv-nth 1 (fn-mlh-put tag seq fn-mlh))) (fn-mlh-n fn-mlh))
       (equal (fn-mlh-s (mv-nth 1 (fn-mlh-put tag seq fn-mlh))) (fn-mlh-s fn-mlh))
       (equal (fn-mlh-count (mv-nth 1 (fn-mlh-put tag seq fn-mlh))) (fn-mlh-count fn-mlh))
       (equal (fn-mlh-stuck (mv-nth 1 (fn-mlh-put tag seq fn-mlh))) (fn-mlh-stuck fn-mlh))
       (equal (fn-mlh-key-octets (mv-nth 1 (fn-mlh-put tag seq fn-mlh))) (fn-mlh-key-octets fn-mlh)))
  :hints (("Goal" :in-theory (disable fn-mlh-find-empty))))

(defthm fn-mlh-put-shape
  (implies (and (fn-mlhp fn-mlh) (fn-mlh-wfp fn-mlh)
                (natp tag) (< tag *fn-mlh-tag-limit*)
                (natp seq) (< (+ 1 seq) *fn-mlh-tag-limit*))
           (and (fn-mlhp (mv-nth 1 (fn-mlh-put tag seq fn-mlh)))
                (equal (fn-mlh-w-length (mv-nth 1 (fn-mlh-put tag seq fn-mlh))) (fn-mlh-w-length fn-mlh))
                (fn-mlh-wfp (mv-nth 1 (fn-mlh-put tag seq fn-mlh)))))
  :hints (("Goal" :in-theory (disable fn-mlh-find-empty fn-mpxl-addr-below)
           :use ((:instance fn-mpxl-addr-below (n (fn-mlh-n fn-mlh)) (s (fn-mlh-s fn-mlh)))))))

; --- the put's effect on the pages' entries: the written slot's entry joins
; its page, in slot position; every other page as before ---

; A page's entries from a slot above the written one are unchanged; from a
; slot at or below an EMPTY written slot, the entry joins them in slot
; position -- so the page's seqs for a tag gain the seq exactly when the
; tags agree.
(defthm fn-mlh-pe-of-write-slot-above
  (implies (and (natp p) (natp j) (< j *fn-mlh-page-slots*) (natp i) (< j i)
                (fn-mlhp fn-mlh) (natp seq) (< (+ 1 seq) *fn-mlh-tag-limit*))
           (equal (fn-mlh-pe p i (fn-mlh-write-slot p j tag seq fn-mlh))
                  (fn-mlh-pe p i fn-mlh)))
  :hints (("Goal" :induct (fn-mlh-pe p i fn-mlh))))

(defthm fn-mlh-pe-of-write-slot-other
  (implies (and (natp q) (natp p) (not (equal q p)) (natp j) (< j *fn-mlh-page-slots*)
                (natp i) (fn-mlhp fn-mlh) (natp seq) (< (+ 1 seq) *fn-mlh-tag-limit*))
           (equal (fn-mlh-pe q i (fn-mlh-write-slot p j tag seq fn-mlh))
                  (fn-mlh-pe q i fn-mlh)))
  :hints (("Goal" :induct (fn-mlh-pe q i fn-mlh))))

(defthm fn-mlh-pe-of-set-ovf
  (implies (and (natp q) (natp p) (natp i) (fn-mlhp fn-mlh))
           (equal (fn-mlh-pe q i (fn-mlh-set-ovf p fn-mlh))
                  (fn-mlh-pe q i fn-mlh)))
  :hints (("Goal" :induct (fn-mlh-pe q i fn-mlh))))

(local (defthm fn-mlh-mpxl-ins-commutes
  (implies (and (natp a) (natp b) (nat-listp l))
           (equal (fn-mpxl-ins a (fn-mpxl-ins b l)) (fn-mpxl-ins b (fn-mpxl-ins a l))))
  :hints (("Goal" :use fn-mpxt-ins-commutes :in-theory (disable fn-mpxt-ins-commutes)))))

; The seqs of a page after the write of (WTAG, SEQ) into its empty slot J.
(defthm fn-mlh-seqs-pe-of-write-slot-same
  (implies (and (natp p) (natp j) (< j *fn-mlh-page-slots*) (natp i) (<= i j)
                (fn-mlhp fn-mlh) (posp wtag) (natp seq) (< (+ 1 seq) *fn-mlh-tag-limit*)
                (equal (fn-mlh-tag-at p j fn-mlh) 0)
                (nat-listp acc))
           (equal (fn-mpxl-seqs tag (fn-mlh-pe p i (fn-mlh-write-slot p j wtag seq fn-mlh)) acc)
                  (if (equal tag wtag)
                      (fn-mpxl-ins seq (fn-mpxl-seqs tag (fn-mlh-pe p i fn-mlh) acc))
                    (fn-mpxl-seqs tag (fn-mlh-pe p i fn-mlh) acc))))
  :hints (("Goal" :induct (fn-mlh-pe p i fn-mlh)
           :expand ((fn-mlh-pe p i (fn-mlh-write-slot p j wtag seq fn-mlh)))
           :in-theory (disable fn-mlh-write-slot-frame))))

; The same for any page Q (the page comparison inside, so the rewriter
; decides it rather than stalling on two address terms).
(defthm fn-mlh-seqs-pe-of-write-slot
  (implies (and (natp q) (natp p) (natp j) (< j *fn-mlh-page-slots*) (natp i)
                (fn-mlhp fn-mlh) (posp wtag) (natp seq) (< (+ 1 seq) *fn-mlh-tag-limit*)
                (equal (fn-mlh-tag-at p j fn-mlh) 0)
                (nat-listp acc))
           (equal (fn-mpxl-seqs tag (fn-mlh-pe q i (fn-mlh-write-slot p j wtag seq fn-mlh)) acc)
                  (if (and (equal q p) (<= i j) (equal tag wtag))
                      (fn-mpxl-ins seq (fn-mpxl-seqs tag (fn-mlh-pe q i fn-mlh) acc))
                    (fn-mpxl-seqs tag (fn-mlh-pe q i fn-mlh) acc))))
  :hints (("Goal" :use (fn-mlh-seqs-pe-of-write-slot-same
                        (:instance fn-mlh-pe-of-write-slot-above (tag wtag))
                        (:instance fn-mlh-pe-of-write-slot-other (tag wtag)))
           :in-theory (disable fn-mlh-pe fn-mpxl-seqs fn-mlh-write-slot-frame
                               fn-mlh-seqs-pe-of-write-slot-same fn-mlh-pe-of-write-slot-above
                               fn-mlh-pe-of-write-slot-other))))

(in-theory (disable fn-mlh-seqs-pe-of-write-slot-same fn-mlh-pe-of-write-slot-other
                    fn-mlh-pe-of-write-slot-above))

(in-theory (disable fn-mlh-put fn-mlh-saturatedp fn-mlh-find-empty))

; THE PUT FINDS WHAT IT PLACED, AND KEEPS EVERY CANDIDATE: the membership
; facts, over the opened candidates of the pages written.
(defthm fn-mlh-put-finds
  (implies (and (fn-mlhp fn-mlh) (fn-mlh-wfp fn-mlh) (posp (fn-mlh-pages fn-mlh))
                (posp tag) (< tag *fn-mlh-tag-limit*) (natp seq) (< (+ 1 seq) *fn-mlh-tag-limit*)
                (mv-nth 0 (fn-mlh-put tag seq fn-mlh)))
           (member-equal seq (fn-mlh-candidates tag (mv-nth 1 (fn-mlh-put tag seq fn-mlh)))))
  :hints (("Goal" :in-theory (e/d (fn-mlh-put fn-mlh-candidates fn-mlh-scan-is-seqs)
                                  (fn-mlh-scan fn-mlh-pe fn-mpxl-addr-below fn-mpxl-seqs))
           :use ((:instance fn-mpxl-addr-below (n (fn-mlh-n fn-mlh)) (s (fn-mlh-s fn-mlh)))))))

(defthm fn-mlh-put-keeps-candidate
  (implies (and (fn-mlhp fn-mlh) (fn-mlh-wfp fn-mlh) (posp (fn-mlh-pages fn-mlh))
                (posp tag) (posp wtag) (< wtag *fn-mlh-tag-limit*) (natp seq) (< (+ 1 seq) *fn-mlh-tag-limit*)
                (member-equal q (fn-mlh-candidates tag fn-mlh)))
           (member-equal q (fn-mlh-candidates tag (mv-nth 1 (fn-mlh-put wtag seq fn-mlh)))))
  :hints (("Goal" :in-theory (e/d (fn-mlh-put fn-mlh-candidates fn-mlh-scan-is-seqs)
                                  (fn-mlh-scan fn-mlh-pe fn-mpxl-addr-below fn-mpxl-seqs
                                   fn-mlh-candidates-is-cands))
           :use ((:instance fn-mpxl-addr-below (n (fn-mlh-n fn-mlh)) (s (fn-mlh-s fn-mlh)))
                 (:instance fn-mpxl-addr-below (tag wtag) (n (fn-mlh-n fn-mlh)) (s (fn-mlh-s fn-mlh)))))))
