; fn: the linear-hashing Message-ID table, executable (lanes msgid-linear-
; hash and msgid-linear-hash-2, 2026-10-01; stage 7 of planning/design-
; store-representation-2026-10-01.md, the index part; the logical side is
; books/msgid-linear, PRF-1218).  Prefix fn-mlh- (the table), fn-mlg- (a
; page).
;
; THE PAGES ARE STOBJS.  The table is a two-level directory of PAGE stobjs
; (`fn-mlg'), each a fixed array of 2,048 words: 1,024 slots in two columns
; (slot J's TAG is word J, its SEQ + 1 is word 1024 + J), TAG 0 an empty
; slot -- the geometry of books/msgid-pages-exec (fn-mpxt).  Page P lives
; in TABLE PAGE (floor P 64) (`fn-mlt'), slot (mod P 64).  The table grows
; by ONE page per split: the table page's slot array grows by one (at most
; 63 pointers copied) and the new slot is a fresh page; the directory of
; table pages starts 256 wide (16,384 pages) and doubles past its width,
; and `fn-mlh-reserve' widens it once at open for the profile (Codex r42
; F1 / r48 F3: the flat predecessor resized a page-pointer array by one per
; split, O(P) a split and O(P^2) in all; MEASURED, hbox, 3.67M adds to 8,193
; pages: worst add 114,752 B and mean 168 B before, 49,408 B and 96 B now,
; SBCL counting 32 KiB regions).  No page is ever copied and no word moves
; but the movers of the one page split.  A slot never taken reads as empty
; (`fn-mlh-word'); the writers ready the directory, table page and page
; they write (`fn-mlh-put-word', `fn-mlh-fresh-page').  The hot loops read
; the page found once (`fn-mlh-scan-pg', `fn-mlh-find-empty-pg', each
; equal to its logical loop).
;
;   FIXNUM WORDS.  A page's words are (unsigned-byte 61): the tag is the
;   keyed BLAKE3 word of books/msgid-pages-exec reduced to 60 bits
;   (`fn-mlh-tag': floored at 1), the seq word is SEQ + 1 below 2^60, and
;   bit 60 of slot 0's seq word is the page's OVERFLOW FLAG.  Every word
;   is a fixnum on SBCL x86-64, so the accessor returns it unboxed and the
;   scan allocates nothing.  MEASURED on the flat predecessor of this
;   representation (persvati, 2026-10-01, sb-ext:get-bytes-consed around
;   10,000 lookups on tables of 10,000 entries): fn-mpxt-candidates 6,364
;   bytes consed per lookup, fn-mlh-candidates 16 (the one cons of the
;   result list).  The flag lives in the words so that pages are the state
;   (P8).
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
; (`:mpx-saturated'; `fn-mlh-saturatedp').  THE SPLIT `fn-mlh-split'
; (section 7) moves the movers of page S and of its overflow page onto one
; new page and advances the root; its words are `fn-mpxl-split' of the
; abstraction (`fn-mlh-abs-of-split').  THE ADD `fn-mlh-add' (section 8)
; is the put and at most one split per step; THE FOLD `fn-mlh-build' over
; the rows is the table the catalog holds (`fn-mlh-build-faithful').
;
; GEN: def-representation (the stobjs' facts, section 1) and def-loop (the
; scan, the page entries, the move loops) once the generators fit a page
; table of stobjs.

(in-package "ACL2")
(include-book "msgid-linear")
(include-book "msgid-pages-exec")
(include-book "msgid-tag-exec")
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
; bits, floored at 1 (0 is the empty slot).  It EXECUTES consing nothing
; (books/msgid-tag-exec `fn-mlh-tag-x', KEYSTONE `fn-mlh-tag-x-is-tag'): the
; string read by index, the key as eight words, the tag from the root's first
; two output words (lane served-incremental-3; measured, hbox: 2.9 KB per tag
; at 23 octets before, 0 bytes after).
(defun fn-mlh-tag (msgid key)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :use ((:instance fn-mlh-tag-x-is-tag))
                                 :in-theory (disable fn-mlh-tag-x-is-tag fn-mpxt-word fn-ns-mac
                                                     fn-mlh-key-word fn-record-string-octets)))))
  (if (stringp msgid)
      (mbe :logic (max 1 (mod (fn-mpxt-word 8 (fn-ns-mac key (fn-record-string-octets msgid))) *fn-mlh-tag-limit*))
           :exec (fn-mlh-tag-x msgid (fn-mlh-key-word 0 key) (fn-mlh-key-word 1 key)
                               (fn-mlh-key-word 2 key) (fn-mlh-key-word 3 key)
                               (fn-mlh-key-word 4 key) (fn-mlh-key-word 5 key)
                               (fn-mlh-key-word 6 key) (fn-mlh-key-word 7 key)))
    1))

(defthm fn-mlh-tag-posp
  (posp (fn-mlh-tag msgid key))
  :rule-classes :type-prescription)

(defthm fn-mlh-tag-below
  (< (fn-mlh-tag msgid key) *fn-mlh-tag-limit*)
  :rule-classes :linear)

(in-theory (disable fn-mlh-tag))

; -----------------------------------------------------------------------------
; 1. The stobjs and their facts.  GEN: def-representation.

; A PAGE: 2,048 words, fixed.
(defstobj fn-mlg
  (fn-mlg-w :type (array (unsigned-byte 61) (2048)) :initially 0)
  :inline t)

; A TABLE PAGE: up to *fn-mlh-tpages* pages, grown one page at a time (at
; most 63 pointers copied: Codex r42 F1's per-split bound).
(defconst *fn-mlh-tpages* 64)
(defconst *fn-mlh-dir-reserve* 256)

(defstobj fn-mlt
  (fn-mlt-pg :type (array fn-mlg (0)) :resizable t)
  :inline t)

; THE TABLE: the directory of table pages, the root, the count of entries,
; the key, and STUCK (a split was refused: no further split is tried).
; Page P lives in table page (floor P 64), slot (mod P 64).
(defstobj fn-mlh
  (fn-mlh-dir :type (array fn-mlt (0)) :resizable t)
  (fn-mlh-pages :type (integer 0 *) :initially 0)
  (fn-mlh-n :type (integer 0 *) :initially 0)
  (fn-mlh-s :type (integer 0 *) :initially 0)
  (fn-mlh-count :type (integer 0 *) :initially 0)
  (fn-mlh-key :type (array (unsigned-byte 8) (32)) :initially 0)
  (fn-mlh-stuck :type (integer 0 1) :initially 0)
  :inline t)

; --- list facts ---

(local (defthm fn-mlg-wp-nth-word
  (implies (and (fn-mlg-wp l) (natp i) (< i (len l)))
           (unsigned-byte-p 61 (nth i l)))
  :hints (("Goal" :in-theory (enable nth)))))
(local (defthm fn-mlg-wp-of-update-nth
  (implies (and (fn-mlg-wp l) (natp i) (< i (len l)) (unsigned-byte-p 61 v))
           (fn-mlg-wp (update-nth i v l)))
  :hints (("Goal" :in-theory (enable update-nth)))))
(local (defthm fn-mlh-len-update-nth
  (implies (and (natp i) (< i (len l)))
           (equal (len (update-nth i v l)) (len l)))
  :hints (("Goal" :in-theory (enable update-nth)))))
(local (defthm fn-mlh-keyp-of-update-nth
  (implies (and (fn-mlh-keyp l) (natp i) (< i (len l)) (unsigned-byte-p 8 v))
           (fn-mlh-keyp (update-nth i v l)))
  :hints (("Goal" :in-theory (enable update-nth)))))
(local (defthm fn-mlh-keyp-nth
  (implies (and (fn-mlh-keyp l) (natp i) (< i (len l)))
           (unsigned-byte-p 8 (nth i l)))
  :hints (("Goal" :in-theory (enable nth)))))
(local (defthm fn-mlh-len-resize-list
  (equal (len (resize-list l n d)) (nfix n))
  :hints (("Goal" :in-theory (enable resize-list)))))
(local (defthm fn-mlh-resize-list-0
  (equal (resize-list l 0 d) nil)
  :hints (("Goal" :in-theory (enable resize-list)))))
(local (defun fn-mlh-resize-ind (p l n)
  (if (or (zp n) (zp p)) (list p l n)
    (fn-mlh-resize-ind (1- p) (if (atom l) l (cdr l)) (1- n)))))
(local (defthm fn-mlh-nth-of-resize-list
  (implies (and (natp p) (natp n))
           (equal (nth p (resize-list l n d))
                  (if (< p n) (if (< p (len l)) (nth p l) d) nil)))
  :hints (("Goal" :induct (fn-mlh-resize-ind p l n)
           :expand ((resize-list l n d))
           :in-theory (e/d (nth) (fn-mlh-len-resize-list resize-list))))))
(local (defthm fn-mlt-pgp-nth
  (implies (and (fn-mlt-pgp l) (natp p) (< p (len l)))
           (fn-mlgp (nth p l)))
  :hints (("Goal" :in-theory (enable nth)))))
(local (defthm fn-mlt-pgp-of-update-nth
  (implies (and (fn-mlt-pgp l) (natp p) (< p (len l)) (fn-mlgp v))
           (fn-mlt-pgp (update-nth p v l)))
  :hints (("Goal" :in-theory (enable update-nth)))))
(local (defthm fn-mlt-pgp-of-resize-list
  (implies (and (fn-mlt-pgp l) (fn-mlgp d))
           (fn-mlt-pgp (resize-list l n d)))
  :hints (("Goal" :in-theory (enable resize-list)))))
(local (defthm fn-mlh-dirp-nth
  (implies (and (fn-mlh-dirp l) (natp p) (< p (len l)))
           (fn-mltp (nth p l)))
  :hints (("Goal" :in-theory (enable nth)))))
(local (defthm fn-mlh-dirp-of-update-nth
  (implies (and (fn-mlh-dirp l) (natp p) (< p (len l)) (fn-mltp v))
           (fn-mlh-dirp (update-nth p v l)))
  :hints (("Goal" :in-theory (enable update-nth)))))
(local (defthm fn-mlh-dirp-of-resize-list
  (implies (and (fn-mlh-dirp l) (fn-mltp d))
           (fn-mlh-dirp (resize-list l n d)))
  :hints (("Goal" :in-theory (enable resize-list)))))

(defthm fn-mlg-create-is-a-page
  (fn-mlgp (create-fn-mlg))
  :hints (("Goal" :in-theory (enable fn-mlgp create-fn-mlg))))
(defthm fn-mlt-create-is-a-table-page
  (fn-mltp (create-fn-mlt))
  :hints (("Goal" :in-theory (enable fn-mltp create-fn-mlt))))
(defthm fn-mlh-create-is-a-table
  (fn-mlhp (create-fn-mlh))
  :hints (("Goal" :in-theory (enable fn-mlhp))))

; --- the address of page P ---

(local (defthm fn-mlh-addr-facts
  (implies (natp p)
           (and (natp (floor p *fn-mlh-tpages*))
                (natp (mod p *fn-mlh-tpages*))
                (< (mod p *fn-mlh-tpages*) *fn-mlh-tpages*)
                (<= (floor p *fn-mlh-tpages*) p)))))
(local (defthm fn-mlh-addr-injective
  (implies (and (natp p) (natp q)
                (equal (floor q *fn-mlh-tpages*) (floor p *fn-mlh-tpages*))
                (equal (mod q *fn-mlh-tpages*) (mod p *fn-mlh-tpages*)))
           (equal q p))
  :rule-classes nil
  :hints (("Goal" :use ((:instance floor-mod-elim (x p) (y *fn-mlh-tpages*))
                        (:instance floor-mod-elim (x q) (y *fn-mlh-tpages*)))
           :in-theory (disable floor-mod-elim)))))

; The address in shifts (the executable side of the reader and writers).
(local (defthm fn-mlh-addr-shifts
  (implies (natp p)
           (and (equal (ash p -6) (floor p *fn-mlh-tpages*))
                (equal (- p (ash (floor p *fn-mlh-tpages*) 6)) (mod p *fn-mlh-tpages*))))
  :hints (("Goal" :in-theory (enable ash mod)))))

; THE WORD READER: word I of page P, 0 when the page or the word is not
; there (a page never taken reads as empty).
(defun-inline fn-mlh-word (p i fn-mlh)
  (declare (xargs :stobjs fn-mlh :guard (and (natp p) (natp i))))
  (let* ((p (mbe :logic (nfix p) :exec p))
         (jt (mbe :logic (floor p *fn-mlh-tpages*) :exec (ash p -6)))
         (it (mbe :logic (mod p *fn-mlh-tpages*) :exec (- p (ash jt 6)))))
    (if (< jt (fn-mlh-dir-length fn-mlh))
        (stobj-let ((fn-mlt (fn-mlh-diri jt fn-mlh)))
                   (v)
                   (if (< it (fn-mlt-pg-length fn-mlt))
                       (stobj-let ((fn-mlg (fn-mlt-pgi it fn-mlt)))
                                  (v)
                                  (let ((i (mbe :logic (nfix i) :exec i)))
                                    (if (< i *fn-mlh-page-words*) (nfix (fn-mlg-wi i fn-mlg)) 0))
                                  v)
                     0)
                   v)
      0)))

;; The inline reader's macro name serves in theory expressions.
(add-macro-fn fn-mlh-word fn-mlh-word$inline)

; THE WORD WRITER: word I of page P set to V; the directory, the table page
; and the page are made ready first when they are not (each kept reading
; as it did: a new slot reads as empty).  The directory doubles past its
; width (`fn-mlh-reserve' widens it once, at open, for the profile).
(defun fn-mlh-put-word (p i v fn-mlh)
  (declare (xargs :stobjs fn-mlh
                  :guard (and (natp p) (natp i) (< i *fn-mlh-page-words*) (unsigned-byte-p 61 v))))
  (let* ((p (mbe :logic (nfix p) :exec p))
         (jt (mbe :logic (floor p *fn-mlh-tpages*) :exec (ash p -6)))
         (it (mbe :logic (mod p *fn-mlh-tpages*) :exec (- p (ash jt 6))))
         (fn-mlh (if (< jt (fn-mlh-dir-length fn-mlh))
                     fn-mlh
                   (resize-fn-mlh-dir (max *fn-mlh-dir-reserve* (* 2 jt)) fn-mlh))))
    (stobj-let ((fn-mlt (fn-mlh-diri jt fn-mlh)))
               (fn-mlt)
               (let ((fn-mlt (if (< it (fn-mlt-pg-length fn-mlt))
                                 fn-mlt
                               (resize-fn-mlt-pg (+ 1 it) fn-mlt))))
                 (stobj-let ((fn-mlg (fn-mlt-pgi it fn-mlt)))
                            (fn-mlg)
                            (update-fn-mlg-wi i v fn-mlg)
                            fn-mlt))
               fn-mlh)))

; Every word of a page from K down set to 0.
(defun fn-mlg-zero (k fn-mlg)
  (declare (xargs :stobjs fn-mlg :guard (and (natp k) (<= k *fn-mlh-page-words*))))
  (if (zp k)
      fn-mlg
    (let ((fn-mlg (update-fn-mlg-wi (1- k) 0 fn-mlg)))
      (fn-mlg-zero (1- k) fn-mlg))))

; A FRESH PAGE at P: a new slot when P is the table page's next (the slot
; array grown by one: a fresh page, 16 KiB of zeros); an existing slot's
; 2,048 words set to 0.  Either way bounded by one page.
(defun fn-mlh-fresh-page (p fn-mlh)
  (declare (xargs :stobjs fn-mlh :guard (natp p)))
  (let* ((p (mbe :logic (nfix p) :exec p))
         (jt (mbe :logic (floor p *fn-mlh-tpages*) :exec (ash p -6)))
         (it (mbe :logic (mod p *fn-mlh-tpages*) :exec (- p (ash jt 6))))
         (fn-mlh (if (< jt (fn-mlh-dir-length fn-mlh))
                     fn-mlh
                   (resize-fn-mlh-dir (max *fn-mlh-dir-reserve* (* 2 jt)) fn-mlh))))
    (stobj-let ((fn-mlt (fn-mlh-diri jt fn-mlh)))
               (fn-mlt)
               (if (< it (fn-mlt-pg-length fn-mlt))
                   (stobj-let ((fn-mlg (fn-mlt-pgi it fn-mlt)))
                              (fn-mlg)
                              (fn-mlg-zero *fn-mlh-page-words* fn-mlg)
                              fn-mlt)
                 (resize-fn-mlt-pg (+ 1 it) fn-mlt))
               fn-mlh)))

; THE RESERVATION: the directory made wide enough, once, for PAGES pages
; (no table page or page is taken; each slot reads as empty).
(defun fn-mlh-reserve (pages fn-mlh)
  (declare (xargs :stobjs fn-mlh :guard (natp pages)))
  (let ((n (+ 1 (floor pages *fn-mlh-tpages*))))
    (if (< (fn-mlh-dir-length fn-mlh) n)
        (resize-fn-mlh-dir n fn-mlh)
      fn-mlh)))

; --- the reader's facts ---

(defthm fn-mlh-word-natp
  (natp (fn-mlh-word p i fn-mlh))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn-mlh-diri fn-mlt-pgi fn-mlg-wi))))

; --- the primitives' facts, then closed ---

(defthm fn-mlg-wi-word
  (implies (and (fn-mlgp pg) (natp i) (< i *fn-mlh-page-words*))
           (unsigned-byte-p 61 (fn-mlg-wi i pg)))
  :hints (("Goal" :in-theory (enable fn-mlgp fn-mlg-wi))))
(defthm fn-mlt-pgi-is-a-page
  (implies (and (fn-mltp tp) (natp it) (< it (fn-mlt-pg-length tp)))
           (fn-mlgp (fn-mlt-pgi it tp)))
  :hints (("Goal" :in-theory (enable fn-mltp fn-mlt-pgi fn-mlt-pg-length))))
(defthm fn-mlh-diri-is-a-table-page
  (implies (and (fn-mlhp fn-mlh) (natp jt) (< jt (fn-mlh-dir-length fn-mlh)))
           (fn-mltp (fn-mlh-diri jt fn-mlh)))
  :hints (("Goal" :in-theory (enable fn-mlhp fn-mlh-diri fn-mlh-dir-length))))

;; Each level's accessors against its writes.
(defthm fn-mlg-accessors-of-writes
  (and (implies (and (natp i) (natp j))
                (equal (fn-mlg-wi i (update-fn-mlg-wi j v pg)) (if (equal i j) v (fn-mlg-wi i pg)))))
  :hints (("Goal" :in-theory (enable fn-mlg-wi update-fn-mlg-wi))))
(defthm fn-mlg-wi-of-zero
  (implies (natp i)
           (equal (fn-mlg-wi i (fn-mlg-zero k pg)) (if (< i (nfix k)) 0 (fn-mlg-wi i pg))))
  :hints (("Goal" :induct (fn-mlg-zero k pg))))

; A fresh page reads 0 everywhere.
(local (defun fn-mlh-zerosp (l)
  (if (consp l) (and (equal (car l) 0) (fn-mlh-zerosp (cdr l))) t)))
(local (defthm fn-mlh-zerosp-make-list-ac
  (implies (fn-mlh-zerosp acc) (fn-mlh-zerosp (make-list-ac n 0 acc)))))
(local (defthm fn-mlh-zerosp-nth
  (implies (fn-mlh-zerosp l) (equal (nfix (nth i l)) 0))
  :hints (("Goal" :in-theory (enable nth)))))
(defthm fn-mlg-wi-of-create
  (equal (nfix (fn-mlg-wi i (create-fn-mlg))) 0)
  :hints (("Goal" :in-theory (e/d (fn-mlg-wi create-fn-mlg) ((:e create-fn-mlg) (:e make-list-ac) make-list-ac))
           :use ((:instance fn-mlh-zerosp-nth (l (make-list-ac 2048 0 nil)))))))
(defthm fn-mlgp-of-zero
  (implies (and (fn-mlgp pg) (natp k) (<= k *fn-mlh-page-words*))
           (fn-mlgp (fn-mlg-zero k pg)))
  :hints (("Goal" :induct (fn-mlg-zero k pg) :in-theory (enable fn-mlgp update-fn-mlg-wi))))
(defthm fn-mlt-accessors-of-writes
  (and (implies (and (natp i) (natp j))
                (equal (fn-mlt-pgi i (update-fn-mlt-pgi j v tp)) (if (equal i j) v (fn-mlt-pgi i tp))))
       (implies (and (natp j) (< j (fn-mlt-pg-length tp)))
                (equal (fn-mlt-pg-length (update-fn-mlt-pgi j v tp)) (fn-mlt-pg-length tp)))
       (implies (and (natp i) (natp n))
                (equal (fn-mlt-pgi i (resize-fn-mlt-pg n tp))
                       (if (< i n) (if (< i (fn-mlt-pg-length tp)) (fn-mlt-pgi i tp) (create-fn-mlg)) nil)))
       (equal (fn-mlt-pg-length (resize-fn-mlt-pg n tp)) (nfix n))
       (equal (fn-mlt-pg-length (create-fn-mlt)) 0))
  :hints (("Goal" :in-theory (enable fn-mlt-pgi update-fn-mlt-pgi resize-fn-mlt-pg fn-mlt-pg-length create-fn-mlt))))
(defthm fn-mlh-dir-accessors-of-writes
  (and (implies (and (natp i) (natp j))
                (equal (fn-mlh-diri i (update-fn-mlh-diri j v fn-mlh)) (if (equal i j) v (fn-mlh-diri i fn-mlh))))
       (implies (and (natp j) (< j (fn-mlh-dir-length fn-mlh)))
                (equal (fn-mlh-dir-length (update-fn-mlh-diri j v fn-mlh)) (fn-mlh-dir-length fn-mlh)))
       (implies (and (natp i) (natp n))
                (equal (fn-mlh-diri i (resize-fn-mlh-dir n fn-mlh))
                       (if (< i n) (if (< i (fn-mlh-dir-length fn-mlh)) (fn-mlh-diri i fn-mlh) (create-fn-mlt)) nil)))
       (equal (fn-mlh-dir-length (resize-fn-mlh-dir n fn-mlh)) (nfix n)))
  :hints (("Goal" :in-theory (enable fn-mlh-diri update-fn-mlh-diri resize-fn-mlh-dir fn-mlh-dir-length))))
(defthm fn-mlg-wi-of-nil
  (and (equal (fn-mlg-wi i nil) nil)
       (equal (fn-mlt-pg-length nil) 0))
  :hints (("Goal" :in-theory (enable fn-mlg-wi fn-mlt-pg-length))))

(in-theory (disable update-fn-mlg-wi fn-mlg-zero update-fn-mlt-pgi resize-fn-mlt-pg
                    update-fn-mlh-diri resize-fn-mlh-dir create-fn-mlg create-fn-mlt
                    (:e create-fn-mlg) (:e create-fn-mlt)))
(in-theory (disable fn-mlhp fn-mltp fn-mlgp fn-mlh-diri fn-mlt-pgi fn-mlg-wi
                    fn-mlh-dir-length fn-mlt-pg-length))

(defthm fn-mlh-word-is-a-word
  (implies (fn-mlhp fn-mlh)
           (< (fn-mlh-word p i fn-mlh) *fn-mlh-word-limit*))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (unsigned-byte-p) (floor mod fn-mlg-wi-word))
           :use ((:instance fn-mlg-wi-word (i (nfix i))
                            (pg (fn-mlt-pgi (mod (nfix p) 64) (fn-mlh-diri (floor (nfix p) 64) fn-mlh))))
                 (:instance fn-mlh-addr-facts (p (nfix p)))))))

(defthm fn-mlh-word-of-put-word
  (implies (and (natp p) (natp q) (natp i) (natp j) (< j *fn-mlh-page-words*))
           (equal (fn-mlh-word q i (fn-mlh-put-word p j v fn-mlh))
                  (if (and (equal q p) (equal i j)) (nfix v) (fn-mlh-word q i fn-mlh))))
  :hints (("Goal" :in-theory (disable floor mod)
           :use ((:instance fn-mlh-addr-injective)
                 (:instance fn-mlh-addr-facts) (:instance fn-mlh-addr-facts (p q))))))

(in-theory (enable fn-mlhp fn-mlh-diri fn-mlh-dir-length update-fn-mlh-diri resize-fn-mlh-dir))

(defthm fn-mlhp-of-updates
  (implies (fn-mlhp fn-mlh)
           (and (implies (and (natp p) (< p (fn-mlh-dir-length fn-mlh)) (fn-mltp pg))
                         (fn-mlhp (update-fn-mlh-diri p pg fn-mlh)))
                (implies (natp m) (fn-mlhp (resize-fn-mlh-dir m fn-mlh)))
                (implies (natp m) (fn-mlhp (update-fn-mlh-pages m fn-mlh)))
                (implies (natp m) (fn-mlhp (update-fn-mlh-n m fn-mlh)))
                (implies (natp m) (fn-mlhp (update-fn-mlh-s m fn-mlh)))
                (implies (natp m) (fn-mlhp (update-fn-mlh-count m fn-mlh)))
                (implies (and (natp i) (< i 32) (unsigned-byte-p 8 v))
                         (fn-mlhp (update-fn-mlh-keyi i v fn-mlh)))
                (implies (or (equal m 0) (equal m 1))
                         (fn-mlhp (update-fn-mlh-stuck m fn-mlh)))))
  :hints (("Goal" :in-theory (enable fn-mlhp update-fn-mlh-diri resize-fn-mlh-dir fn-mlh-dir-length
                                     update-fn-mlh-pages update-fn-mlh-n update-fn-mlh-s
                                     update-fn-mlh-count update-fn-mlh-keyi update-fn-mlh-stuck))))

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
(defthm fn-mlh-dir-length-of-updates
  (and (implies (and (natp p) (< p (fn-mlh-dir-length fn-mlh)))
                (equal (fn-mlh-dir-length (update-fn-mlh-diri p pg fn-mlh)) (fn-mlh-dir-length fn-mlh)))
       (equal (fn-mlh-dir-length (resize-fn-mlh-dir m fn-mlh)) (nfix m))
       (equal (fn-mlh-dir-length (update-fn-mlh-pages m fn-mlh)) (fn-mlh-dir-length fn-mlh))
       (equal (fn-mlh-dir-length (update-fn-mlh-n m fn-mlh)) (fn-mlh-dir-length fn-mlh))
       (equal (fn-mlh-dir-length (update-fn-mlh-s m fn-mlh)) (fn-mlh-dir-length fn-mlh))
       (equal (fn-mlh-dir-length (update-fn-mlh-count m fn-mlh)) (fn-mlh-dir-length fn-mlh))
       (equal (fn-mlh-dir-length (update-fn-mlh-keyi i v fn-mlh)) (fn-mlh-dir-length fn-mlh))
       (equal (fn-mlh-dir-length (update-fn-mlh-stuck m fn-mlh)) (fn-mlh-dir-length fn-mlh))))

(defthm fn-mlh-diri-of-scalar-updates
  (and (equal (fn-mlh-diri p (update-fn-mlh-pages m fn-mlh)) (fn-mlh-diri p fn-mlh))
       (equal (fn-mlh-diri p (update-fn-mlh-n m fn-mlh)) (fn-mlh-diri p fn-mlh))
       (equal (fn-mlh-diri p (update-fn-mlh-s m fn-mlh)) (fn-mlh-diri p fn-mlh))
       (equal (fn-mlh-diri p (update-fn-mlh-count m fn-mlh)) (fn-mlh-diri p fn-mlh))
       (equal (fn-mlh-diri p (update-fn-mlh-keyi j v fn-mlh)) (fn-mlh-diri p fn-mlh))
       (equal (fn-mlh-diri p (update-fn-mlh-stuck m fn-mlh)) (fn-mlh-diri p fn-mlh))))

(defthm fn-mlh-scalars-of-updates
  (and (equal (fn-mlh-pages (update-fn-mlh-diri i v fn-mlh)) (fn-mlh-pages fn-mlh))
       (equal (fn-mlh-pages (resize-fn-mlh-dir m fn-mlh)) (fn-mlh-pages fn-mlh))
       (equal (fn-mlh-pages (update-fn-mlh-pages m fn-mlh)) m)
       (equal (fn-mlh-pages (update-fn-mlh-n m fn-mlh)) (fn-mlh-pages fn-mlh))
       (equal (fn-mlh-pages (update-fn-mlh-s m fn-mlh)) (fn-mlh-pages fn-mlh))
       (equal (fn-mlh-pages (update-fn-mlh-count m fn-mlh)) (fn-mlh-pages fn-mlh))
       (equal (fn-mlh-pages (update-fn-mlh-keyi i v fn-mlh)) (fn-mlh-pages fn-mlh))
       (equal (fn-mlh-pages (update-fn-mlh-stuck m fn-mlh)) (fn-mlh-pages fn-mlh))
       (equal (fn-mlh-n (update-fn-mlh-diri i v fn-mlh)) (fn-mlh-n fn-mlh))
       (equal (fn-mlh-n (resize-fn-mlh-dir m fn-mlh)) (fn-mlh-n fn-mlh))
       (equal (fn-mlh-n (update-fn-mlh-pages m fn-mlh)) (fn-mlh-n fn-mlh))
       (equal (fn-mlh-n (update-fn-mlh-n m fn-mlh)) m)
       (equal (fn-mlh-n (update-fn-mlh-s m fn-mlh)) (fn-mlh-n fn-mlh))
       (equal (fn-mlh-n (update-fn-mlh-count m fn-mlh)) (fn-mlh-n fn-mlh))
       (equal (fn-mlh-n (update-fn-mlh-keyi i v fn-mlh)) (fn-mlh-n fn-mlh))
       (equal (fn-mlh-n (update-fn-mlh-stuck m fn-mlh)) (fn-mlh-n fn-mlh))
       (equal (fn-mlh-s (update-fn-mlh-diri i v fn-mlh)) (fn-mlh-s fn-mlh))
       (equal (fn-mlh-s (resize-fn-mlh-dir m fn-mlh)) (fn-mlh-s fn-mlh))
       (equal (fn-mlh-s (update-fn-mlh-pages m fn-mlh)) (fn-mlh-s fn-mlh))
       (equal (fn-mlh-s (update-fn-mlh-n m fn-mlh)) (fn-mlh-s fn-mlh))
       (equal (fn-mlh-s (update-fn-mlh-s m fn-mlh)) m)
       (equal (fn-mlh-s (update-fn-mlh-count m fn-mlh)) (fn-mlh-s fn-mlh))
       (equal (fn-mlh-s (update-fn-mlh-keyi i v fn-mlh)) (fn-mlh-s fn-mlh))
       (equal (fn-mlh-s (update-fn-mlh-stuck m fn-mlh)) (fn-mlh-s fn-mlh))
       (equal (fn-mlh-count (update-fn-mlh-diri i v fn-mlh)) (fn-mlh-count fn-mlh))
       (equal (fn-mlh-count (resize-fn-mlh-dir m fn-mlh)) (fn-mlh-count fn-mlh))
       (equal (fn-mlh-count (update-fn-mlh-pages m fn-mlh)) (fn-mlh-count fn-mlh))
       (equal (fn-mlh-count (update-fn-mlh-n m fn-mlh)) (fn-mlh-count fn-mlh))
       (equal (fn-mlh-count (update-fn-mlh-s m fn-mlh)) (fn-mlh-count fn-mlh))
       (equal (fn-mlh-count (update-fn-mlh-count m fn-mlh)) m)
       (equal (fn-mlh-count (update-fn-mlh-keyi i v fn-mlh)) (fn-mlh-count fn-mlh))
       (equal (fn-mlh-count (update-fn-mlh-stuck m fn-mlh)) (fn-mlh-count fn-mlh))
       (equal (fn-mlh-stuck (update-fn-mlh-diri i v fn-mlh)) (fn-mlh-stuck fn-mlh))
       (equal (fn-mlh-stuck (resize-fn-mlh-dir m fn-mlh)) (fn-mlh-stuck fn-mlh))
       (equal (fn-mlh-stuck (update-fn-mlh-pages m fn-mlh)) (fn-mlh-stuck fn-mlh))
       (equal (fn-mlh-stuck (update-fn-mlh-n m fn-mlh)) (fn-mlh-stuck fn-mlh))
       (equal (fn-mlh-stuck (update-fn-mlh-s m fn-mlh)) (fn-mlh-stuck fn-mlh))
       (equal (fn-mlh-stuck (update-fn-mlh-count m fn-mlh)) (fn-mlh-stuck fn-mlh))
       (equal (fn-mlh-stuck (update-fn-mlh-keyi i v fn-mlh)) (fn-mlh-stuck fn-mlh))
       (equal (fn-mlh-stuck (update-fn-mlh-stuck m fn-mlh)) m)
       (equal (fn-mlh-keyi i (update-fn-mlh-diri j v fn-mlh)) (fn-mlh-keyi i fn-mlh))
       (equal (fn-mlh-keyi i (resize-fn-mlh-dir m fn-mlh)) (fn-mlh-keyi i fn-mlh))
       (equal (fn-mlh-keyi i (update-fn-mlh-pages m fn-mlh)) (fn-mlh-keyi i fn-mlh))
       (equal (fn-mlh-keyi i (update-fn-mlh-n m fn-mlh)) (fn-mlh-keyi i fn-mlh))
       (equal (fn-mlh-keyi i (update-fn-mlh-s m fn-mlh)) (fn-mlh-keyi i fn-mlh))
       (equal (fn-mlh-keyi i (update-fn-mlh-count m fn-mlh)) (fn-mlh-keyi i fn-mlh))
       (equal (fn-mlh-keyi i (update-fn-mlh-stuck m fn-mlh)) (fn-mlh-keyi i fn-mlh))
       (implies (and (natp i) (natp j))
                (equal (fn-mlh-keyi i (update-fn-mlh-keyi j v fn-mlh))
                       (if (equal i j) v (fn-mlh-keyi i fn-mlh))))))

;; The primitives are closed from here on: every fact about them is above.
(in-theory (disable fn-mlhp fn-mlh-diri update-fn-mlh-diri fn-mlh-dir-length resize-fn-mlh-dir
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
  (and (equal (fn-mlh-key-from i (update-fn-mlh-diri j v fn-mlh)) (fn-mlh-key-from i fn-mlh))
       (equal (fn-mlh-key-from i (resize-fn-mlh-dir m fn-mlh)) (fn-mlh-key-from i fn-mlh))
       (equal (fn-mlh-key-from i (update-fn-mlh-pages m fn-mlh)) (fn-mlh-key-from i fn-mlh))
       (equal (fn-mlh-key-from i (update-fn-mlh-n m fn-mlh)) (fn-mlh-key-from i fn-mlh))
       (equal (fn-mlh-key-from i (update-fn-mlh-s m fn-mlh)) (fn-mlh-key-from i fn-mlh))
       (equal (fn-mlh-key-from i (update-fn-mlh-count m fn-mlh)) (fn-mlh-key-from i fn-mlh))
       (equal (fn-mlh-key-from i (update-fn-mlh-stuck m fn-mlh)) (fn-mlh-key-from i fn-mlh))))

(defthm fn-mlh-key-octets-of-updates
  (and (equal (fn-mlh-key-octets (update-fn-mlh-diri j v fn-mlh)) (fn-mlh-key-octets fn-mlh))
       (equal (fn-mlh-key-octets (resize-fn-mlh-dir m fn-mlh)) (fn-mlh-key-octets fn-mlh))
       (equal (fn-mlh-key-octets (update-fn-mlh-pages m fn-mlh)) (fn-mlh-key-octets fn-mlh))
       (equal (fn-mlh-key-octets (update-fn-mlh-n m fn-mlh)) (fn-mlh-key-octets fn-mlh))
       (equal (fn-mlh-key-octets (update-fn-mlh-s m fn-mlh)) (fn-mlh-key-octets fn-mlh))
       (equal (fn-mlh-key-octets (update-fn-mlh-count m fn-mlh)) (fn-mlh-key-octets fn-mlh))
       (equal (fn-mlh-key-octets (update-fn-mlh-stuck m fn-mlh)) (fn-mlh-key-octets fn-mlh))))

(in-theory (disable fn-mlh-key-octets))

; The key's word J read from the stobj (no key list built), and the tag of a
; Message-ID under the table's own key: what the catalog's probe and add
; execute (`fn-mlh-tag-of' is the logical (fn-mlh-tag msgid
; (fn-mlh-key-octets fn-mlh)), enabled, so every theorem about that term
; holds of it).
(local
 (defun fn-mlh-ind-key (i j)
   (if (zp j) i (fn-mlh-ind-key (1+ i) (1- j)))))

(local
 (defthm fn-mlh-nthx-of-key-from
   (implies (and (natp i) (natp j) (< (+ i j) 32))
            (equal (fn-b3-nthx j (fn-mlh-key-from i fn-mlh))
                   (fn-mlh-keyi (+ i j) fn-mlh)))
   :hints (("Goal" :induct (fn-mlh-ind-key i j)
            :expand ((fn-mlh-key-from i fn-mlh))
            :in-theory (enable fn-b3-nthx)))))

(defun fn-mlh-keyi-word (j fn-mlh)
  (declare (xargs :stobjs fn-mlh :guard (and (natp j) (< j 8))
                  :guard-hints (("Goal" :in-theory (e/d (fn-mlh-key-octets fn-mlh-key-word-is-le-word)
                                                        (fn-mlh-key-word fn-mlh-key-from fn-b3-nthx))))))
  (mbe :logic (fn-mlh-key-word j (fn-mlh-key-octets fn-mlh))
       :exec (fn-b3-le-word (fn-mlh-keyi (* 4 j) fn-mlh) (fn-mlh-keyi (+ 1 (* 4 j)) fn-mlh)
                            (fn-mlh-keyi (+ 2 (* 4 j)) fn-mlh) (fn-mlh-keyi (+ 3 (* 4 j)) fn-mlh))))

(defun fn-mlh-tag-of (msgid fn-mlh)
  (declare (xargs :stobjs fn-mlh
                  :guard-hints (("Goal" :use ((:instance fn-mlh-tag-x-is-tag (key (fn-mlh-key-octets fn-mlh))))
                                 :in-theory (e/d (fn-mlh-tag)
                                                 (fn-mlh-tag-x-is-tag fn-mlh-key-word fn-mpxt-word fn-ns-mac
                                                  fn-record-string-octets fn-mlh-key-octets))))))
  (mbe :logic (fn-mlh-tag msgid (fn-mlh-key-octets fn-mlh))
       :exec (if (stringp msgid)
                 (fn-mlh-tag-x msgid (fn-mlh-keyi-word 0 fn-mlh) (fn-mlh-keyi-word 1 fn-mlh)
                               (fn-mlh-keyi-word 2 fn-mlh) (fn-mlh-keyi-word 3 fn-mlh)
                               (fn-mlh-keyi-word 4 fn-mlh) (fn-mlh-keyi-word 5 fn-mlh)
                               (fn-mlh-keyi-word 6 fn-mlh) (fn-mlh-keyi-word 7 fn-mlh))
               1)))

; --- the page writers against everything else ---

(defthm fn-mlh-word-of-fresh-page
  (implies (and (natp p) (natp q))
           (equal (fn-mlh-word q i (fn-mlh-fresh-page p fn-mlh))
                  (if (equal q p) 0 (fn-mlh-word q i fn-mlh))))
  :hints (("Goal" :in-theory (disable floor mod)
           :use ((:instance fn-mlh-addr-injective)
                 (:instance fn-mlh-addr-facts) (:instance fn-mlh-addr-facts (p q))))))

(defthm fn-mlh-word-of-reserve
  (equal (fn-mlh-word q i (fn-mlh-reserve pages fn-mlh)) (fn-mlh-word q i fn-mlh))
  :hints (("Goal" :in-theory (disable floor mod)
           :use ((:instance fn-mlh-addr-facts (p (nfix q)))))))

(defthm fn-mlh-word-of-empty-dir
  (equal (fn-mlh-word q i (resize-fn-mlh-dir 0 fn-mlh)) 0))

(defthm fn-mlh-word-of-scalar-updates
  (and (equal (fn-mlh-word p i (update-fn-mlh-pages m fn-mlh)) (fn-mlh-word p i fn-mlh))
       (equal (fn-mlh-word p i (update-fn-mlh-n m fn-mlh)) (fn-mlh-word p i fn-mlh))
       (equal (fn-mlh-word p i (update-fn-mlh-s m fn-mlh)) (fn-mlh-word p i fn-mlh))
       (equal (fn-mlh-word p i (update-fn-mlh-count m fn-mlh)) (fn-mlh-word p i fn-mlh))
       (equal (fn-mlh-word p i (update-fn-mlh-stuck m fn-mlh)) (fn-mlh-word p i fn-mlh))
       (equal (fn-mlh-word p i (update-fn-mlh-keyi j v fn-mlh)) (fn-mlh-word p i fn-mlh))))

(defthm fn-mlh-page-writers-frame
  (and (equal (fn-mlh-pages (fn-mlh-put-word p i v fn-mlh)) (fn-mlh-pages fn-mlh))
       (equal (fn-mlh-n (fn-mlh-put-word p i v fn-mlh)) (fn-mlh-n fn-mlh))
       (equal (fn-mlh-s (fn-mlh-put-word p i v fn-mlh)) (fn-mlh-s fn-mlh))
       (equal (fn-mlh-count (fn-mlh-put-word p i v fn-mlh)) (fn-mlh-count fn-mlh))
       (equal (fn-mlh-stuck (fn-mlh-put-word p i v fn-mlh)) (fn-mlh-stuck fn-mlh))
       (equal (fn-mlh-key-octets (fn-mlh-put-word p i v fn-mlh)) (fn-mlh-key-octets fn-mlh))
       (equal (fn-mlh-pages (fn-mlh-fresh-page p fn-mlh)) (fn-mlh-pages fn-mlh))
       (equal (fn-mlh-n (fn-mlh-fresh-page p fn-mlh)) (fn-mlh-n fn-mlh))
       (equal (fn-mlh-s (fn-mlh-fresh-page p fn-mlh)) (fn-mlh-s fn-mlh))
       (equal (fn-mlh-count (fn-mlh-fresh-page p fn-mlh)) (fn-mlh-count fn-mlh))
       (equal (fn-mlh-stuck (fn-mlh-fresh-page p fn-mlh)) (fn-mlh-stuck fn-mlh))
       (equal (fn-mlh-key-octets (fn-mlh-fresh-page p fn-mlh)) (fn-mlh-key-octets fn-mlh))
       (equal (fn-mlh-pages (fn-mlh-reserve n fn-mlh)) (fn-mlh-pages fn-mlh))
       (equal (fn-mlh-n (fn-mlh-reserve n fn-mlh)) (fn-mlh-n fn-mlh))
       (equal (fn-mlh-s (fn-mlh-reserve n fn-mlh)) (fn-mlh-s fn-mlh))
       (equal (fn-mlh-count (fn-mlh-reserve n fn-mlh)) (fn-mlh-count fn-mlh))
       (equal (fn-mlh-stuck (fn-mlh-reserve n fn-mlh)) (fn-mlh-stuck fn-mlh))
       (equal (fn-mlh-key-octets (fn-mlh-reserve n fn-mlh)) (fn-mlh-key-octets fn-mlh))))

(local (defthm fn-mltp-of-update-resize
  (implies (and (fn-mltp tp) (natp it) (fn-mlgp pg))
           (fn-mltp (update-fn-mlt-pgi it pg (if (< it (fn-mlt-pg-length tp)) tp (resize-fn-mlt-pg (+ 1 it) tp)))))
  :hints (("Goal" :in-theory (enable fn-mltp update-fn-mlt-pgi resize-fn-mlt-pg fn-mlt-pg-length)))))
(local (defthm fn-mltp-of-resize
  (implies (fn-mltp tp) (fn-mltp (resize-fn-mlt-pg n tp)))
  :hints (("Goal" :in-theory (enable fn-mltp resize-fn-mlt-pg)))))

(local (defthm fn-mltp-of-update
  (implies (and (fn-mltp tp) (natp it) (< it (fn-mlt-pg-length tp)) (fn-mlgp pg))
           (fn-mltp (update-fn-mlt-pgi it pg tp)))
  :hints (("Goal" :in-theory (enable fn-mltp update-fn-mlt-pgi fn-mlt-pg-length)))))
(local (defthm fn-mlgp-of-update
  (implies (and (fn-mlgp pg) (natp i) (< i *fn-mlh-page-words*) (unsigned-byte-p 61 v))
           (fn-mlgp (update-fn-mlg-wi i v pg)))
  :hints (("Goal" :in-theory (enable fn-mlgp update-fn-mlg-wi)))))

(defthm fn-mlhp-of-page-writers
  (implies (fn-mlhp fn-mlh)
           (and (implies (and (natp i) (< i *fn-mlh-page-words*) (unsigned-byte-p 61 v))
                         (fn-mlhp (fn-mlh-put-word p i v fn-mlh)))
                (fn-mlhp (fn-mlh-fresh-page p fn-mlh))
                (fn-mlhp (fn-mlh-reserve n fn-mlh))))
  :hints (("Goal" :in-theory (disable floor mod)
           :use ((:instance fn-mlh-addr-facts (p (nfix p)))))))

(in-theory (disable fn-mlh-word fn-mlh-put-word fn-mlh-fresh-page fn-mlh-reserve))


; -----------------------------------------------------------------------------
; 2. The geometry, the root and the slot accessors.

; The root: no pages at all, or N + S pages with 0 <= S < N.
(defun fn-mlh-rootp (fn-mlh)
  (declare (xargs :stobjs fn-mlh))
  (if (zp (fn-mlh-pages fn-mlh))
      (and (equal (fn-mlh-n fn-mlh) 0) (equal (fn-mlh-s fn-mlh) 0))
    (and (posp (fn-mlh-n fn-mlh)) (< (fn-mlh-s fn-mlh) (fn-mlh-n fn-mlh))
         (equal (fn-mlh-pages fn-mlh) (+ (fn-mlh-n fn-mlh) (fn-mlh-s fn-mlh))))))

; The pages in use are addressable: a page is read and written through the
; directory whatever its width (a slot not yet taken reads as empty), so
; this asks only that the count is a count.
(defun fn-mlh-pgsp (fn-mlh)
  (declare (xargs :stobjs fn-mlh))
  (natp (fn-mlh-pages fn-mlh)))

; Well formed: that, and the root is a root.
(defun fn-mlh-wfp (fn-mlh)
  (declare (xargs :stobjs fn-mlh))
  (and (fn-mlh-pgsp fn-mlh)
       (fn-mlh-rootp fn-mlh)))

(defun fn-mlh-slot-guardp (p j fn-mlh)
  (declare (xargs :stobjs fn-mlh))
  (and (natp p) (natp j) (< j *fn-mlh-page-slots*)
       (< p (fn-mlh-pages fn-mlh)) (fn-mlh-pgsp fn-mlh)))

(defthm fn-mlh-pgsp-of-scalar-updates
  (and (equal (fn-mlh-pgsp (update-fn-mlh-n m fn-mlh)) (fn-mlh-pgsp fn-mlh))
       (equal (fn-mlh-pgsp (update-fn-mlh-s m fn-mlh)) (fn-mlh-pgsp fn-mlh))
       (equal (fn-mlh-pgsp (update-fn-mlh-count m fn-mlh)) (fn-mlh-pgsp fn-mlh))
       (equal (fn-mlh-pgsp (update-fn-mlh-stuck m fn-mlh)) (fn-mlh-pgsp fn-mlh))
       (equal (fn-mlh-pgsp (update-fn-mlh-keyi i v fn-mlh)) (fn-mlh-pgsp fn-mlh))))

(in-theory (disable fn-mlh-pgsp))

(defthm fn-mlh-wfp-pgsp
  (implies (fn-mlh-wfp fn-mlh) (fn-mlh-pgsp fn-mlh))
  :rule-classes :forward-chaining)

; The tag word of slot J on page P, a fixnum.
(defun-inline fn-mlh-tag-at (p j fn-mlh)
  (declare (xargs :stobjs fn-mlh :guard (fn-mlh-slot-guardp p j fn-mlh)))
  (fn-mlh-word p j fn-mlh))

; The seq word of slot J (SEQ + 1 with the flag bit, 0 in an empty slot).
(defun-inline fn-mlh-seqw (p j fn-mlh)
  (declare (xargs :stobjs fn-mlh :guard (fn-mlh-slot-guardp p j fn-mlh)))
  (fn-mlh-word p (+ *fn-mlh-page-slots* j) fn-mlh))

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
  :rule-classes :linear)

(defthm fn-mlh-seqw-is-a-word
  (implies (fn-mlhp fn-mlh)
           (< (fn-mlh-seqw p j fn-mlh) *fn-mlh-word-limit*))
  :rule-classes :linear)

(defthm fn-mlh-seq-at-below
  (implies (fn-mlhp fn-mlh)
           (< (fn-mlh-seq-at p j fn-mlh) *fn-mlh-tag-limit*))
  :rule-classes :linear
  :hints (("Goal" :use fn-mlh-seqw-is-a-word :in-theory (disable fn-mlh-seqw-is-a-word fn-mlh-seqw))))

(in-theory (disable fn-mlh-tag-at fn-mlh-seqw fn-mlh-seq-at fn-mlh-ovf))

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
; THE PAGE-LEVEL SCAN (the executable side of `fn-mlh-scan'): the page is
; found once through the directory, then its words are read directly.
(defthm fn-mlh-word-by-page
  (implies (and (natp p) (natp i))
           (equal (fn-mlh-word p i fn-mlh)
                  (if (and (< (floor p *fn-mlh-tpages*) (fn-mlh-dir-length fn-mlh))
                           (< (mod p *fn-mlh-tpages*)
                              (fn-mlt-pg-length (fn-mlh-diri (floor p *fn-mlh-tpages*) fn-mlh))))
                      (if (< i *fn-mlh-page-words*)
                          (nfix (fn-mlg-wi i (fn-mlt-pgi (mod p *fn-mlh-tpages*)
                                                         (fn-mlh-diri (floor p *fn-mlh-tpages*) fn-mlh))))
                        0)
                    0)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-mlh-word) (floor mod)))))

(defun fn-mlg-seq-of (w)
  (declare (xargs :guard (natp w)))
  (if (< w *fn-mlh-flag*) w (- w *fn-mlh-flag*)))

(defun fn-mlg-scan (tag j acc fn-mlg)
  (declare (xargs :stobjs fn-mlg :measure (nfix j)
                  :guard (and (natp tag) (natp j) (<= j *fn-mlh-page-slots*) (nat-listp acc)))
           (type (unsigned-byte 60) tag) (type (integer 0 1024) j))
  (if (zp j)
      acc
    (let* ((j (1- j))
           (acc (if (and (= tag (nfix (fn-mlg-wi j fn-mlg)))
                         (<= 1 (fn-mlg-seq-of (nfix (fn-mlg-wi (+ *fn-mlh-page-slots* j) fn-mlg)))))
                    (fn-mpxt-ins (1- (fn-mlg-seq-of (nfix (fn-mlg-wi (+ *fn-mlh-page-slots* j) fn-mlg)))) acc)
                  acc)))
      (fn-mlg-scan tag j acc fn-mlg))))

(defun fn-mlh-scan-pg (tag p j acc fn-mlh)
  (declare (xargs :stobjs fn-mlh
                  :guard (and (natp tag) (natp p) (natp j) (<= j *fn-mlh-page-slots*) (nat-listp acc))
                  :guard-hints (("Goal" :in-theory (disable floor mod)
                                 :use ((:instance fn-mlh-addr-shifts) (:instance fn-mlh-addr-facts)))))
           (type (unsigned-byte 60) tag))
  (let* ((jt (mbe :logic (floor p *fn-mlh-tpages*) :exec (ash p -6)))
         (it (mbe :logic (mod p *fn-mlh-tpages*) :exec (- p (ash jt 6)))))
    (if (< jt (fn-mlh-dir-length fn-mlh))
        (stobj-let ((fn-mlt (fn-mlh-diri jt fn-mlh)))
                   (v)
                   (if (< it (fn-mlt-pg-length fn-mlt))
                       (stobj-let ((fn-mlg (fn-mlt-pgi it fn-mlt)))
                                  (v)
                                  (fn-mlg-scan tag j acc fn-mlg)
                                  v)
                     acc)
                   v)
      acc)))

(local (defthm fn-mlh-slot-reads-by-page
  (implies (and (natp p) (natp j) (< j *fn-mlh-page-slots*))
           (and (equal (fn-mlh-tag-at p j fn-mlh)
                       (if (and (< (floor p *fn-mlh-tpages*) (fn-mlh-dir-length fn-mlh))
                     (< (mod p *fn-mlh-tpages*)
                        (fn-mlt-pg-length (fn-mlh-diri (floor p *fn-mlh-tpages*) fn-mlh)))) (nfix (fn-mlg-wi j (fn-mlt-pgi (mod p *fn-mlh-tpages*) (fn-mlh-diri (floor p *fn-mlh-tpages*) fn-mlh)))) 0))
                (equal (fn-mlh-seqw p j fn-mlh)
                       (if (and (< (floor p *fn-mlh-tpages*) (fn-mlh-dir-length fn-mlh))
                     (< (mod p *fn-mlh-tpages*)
                        (fn-mlt-pg-length (fn-mlh-diri (floor p *fn-mlh-tpages*) fn-mlh)))) (nfix (fn-mlg-wi (+ *fn-mlh-page-slots* j) (fn-mlt-pgi (mod p *fn-mlh-tpages*) (fn-mlh-diri (floor p *fn-mlh-tpages*) fn-mlh)))) 0))))
  :hints (("Goal" :in-theory (e/d (fn-mlh-tag-at fn-mlh-seqw) (floor mod))
           :use ((:instance fn-mlh-word-by-page (i j))
                 (:instance fn-mlh-word-by-page (i (+ *fn-mlh-page-slots* j))))))))

(local (defthm fn-mlh-scan-is-page-scan
  (implies (and (natp p) (natp j) (<= j *fn-mlh-page-slots*))
           (equal (fn-mlh-scan tag p j acc fn-mlh)
                  (if (and (< (floor p *fn-mlh-tpages*) (fn-mlh-dir-length fn-mlh))
                     (< (mod p *fn-mlh-tpages*)
                        (fn-mlt-pg-length (fn-mlh-diri (floor p *fn-mlh-tpages*) fn-mlh)))) (fn-mlg-scan tag j acc (fn-mlt-pgi (mod p *fn-mlh-tpages*) (fn-mlh-diri (floor p *fn-mlh-tpages*) fn-mlh))) acc)))
  :hints (("Goal" :induct (fn-mlh-scan tag p j acc fn-mlh)
           :expand ((:free (pg) (fn-mlg-scan tag j acc pg)))
           :in-theory (e/d (fn-mlh-scan fn-mlh-seq-at-is-seqw) (floor mod fn-mlh-word fn-mlh-tag-at fn-mlh-seqw fn-mlh-seq-at))))))

(defthm fn-mlh-scan-pg-is-scan
  (implies (and (natp p) (natp j) (<= j *fn-mlh-page-slots*))
           (equal (fn-mlh-scan-pg tag p j acc fn-mlh)
                  (fn-mlh-scan tag p j acc fn-mlh)))
  :hints (("Goal" :in-theory (e/d (fn-mlh-scan-pg) (floor mod fn-mlg-scan fn-mlh-scan)))))

(in-theory (disable fn-mlh-scan-pg))
(local (in-theory (disable fn-mlh-slot-reads-by-page fn-mlh-scan-is-page-scan)))

(defun fn-mlh-candidates (tag fn-mlh)
  (declare (xargs :stobjs fn-mlh
                  :guard (and (natp tag) (< tag *fn-mlh-tag-limit*) (fn-mlh-wfp fn-mlh))
                  :guard-hints (("Goal" :use ((:instance fn-mpxl-addr-below (n (fn-mlh-n fn-mlh)) (s (fn-mlh-s fn-mlh))))
                                 :in-theory (disable fn-mpxl-addr-below floor mod fn-mlh-ovf fn-mlh-scan)))))
  (let ((np (fn-mlh-pages fn-mlh)))
    (if (zp np)
        nil
      (let* ((h (fn-mpxl-addr tag (fn-mlh-n fn-mlh) (fn-mlh-s fn-mlh)))
             (acc (mbe :logic (fn-mlh-scan tag h *fn-mlh-page-slots* nil fn-mlh)
                       :exec (fn-mlh-scan-pg tag h *fn-mlh-page-slots* nil fn-mlh))))
        (if (and (fn-mlh-ovf h fn-mlh) (< (+ 1 h) np))
            (mbe :logic (fn-mlh-scan tag (+ 1 h) *fn-mlh-page-slots* acc fn-mlh)
                 :exec (fn-mlh-scan-pg tag (+ 1 h) *fn-mlh-page-slots* acc fn-mlh))
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
  (fn-mpxt-confirm msgid (fn-mlh-candidates (fn-mlh-tag-of msgid fn-mlh) fn-mlh) rows))

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

; THE PAGE-LEVEL FIRST EMPTY SLOT (the executable side of
; `fn-mlh-find-empty'), as the page-level scan.
(defun fn-mlg-find-empty (j fn-mlg)
  (declare (xargs :stobjs fn-mlg :guard (and (natp j) (<= j *fn-mlh-page-slots*))
                  :measure (nfix (- *fn-mlh-page-slots* (nfix j))))
           (type (integer 0 1024) j))
  (if (>= (nfix j) *fn-mlh-page-slots*)
      nil
    (if (equal 0 (nfix (fn-mlg-wi (nfix j) fn-mlg)))
        (nfix j)
      (fn-mlg-find-empty (1+ (nfix j)) fn-mlg))))

(defun fn-mlh-find-empty-pg (p j fn-mlh)
  (declare (xargs :stobjs fn-mlh
                  :guard (and (natp p) (natp j) (<= j *fn-mlh-page-slots*))
                  :guard-hints (("Goal" :in-theory (disable floor mod)
                                 :use ((:instance fn-mlh-addr-shifts) (:instance fn-mlh-addr-facts))))))
  (let* ((jt (mbe :logic (floor p *fn-mlh-tpages*) :exec (ash p -6)))
         (it (mbe :logic (mod p *fn-mlh-tpages*) :exec (- p (ash jt 6))))
         (absent (if (< (nfix j) *fn-mlh-page-slots*) (nfix j) nil)))
    (if (< jt (fn-mlh-dir-length fn-mlh))
        (stobj-let ((fn-mlt (fn-mlh-diri jt fn-mlh)))
                   (v)
                   (if (< it (fn-mlt-pg-length fn-mlt))
                       (stobj-let ((fn-mlg (fn-mlt-pgi it fn-mlt)))
                                  (v)
                                  (fn-mlg-find-empty j fn-mlg)
                                  v)
                     absent)
                   v)
      absent)))

(local (defthm fn-mlh-find-empty-is-page-find
  (implies (natp p)
           (equal (fn-mlh-find-empty p j fn-mlh)
                  (if (and (< (floor p *fn-mlh-tpages*) (fn-mlh-dir-length fn-mlh))
                           (< (mod p *fn-mlh-tpages*)
                              (fn-mlt-pg-length (fn-mlh-diri (floor p *fn-mlh-tpages*) fn-mlh))))
                      (fn-mlg-find-empty j (fn-mlt-pgi (mod p *fn-mlh-tpages*)
                                                       (fn-mlh-diri (floor p *fn-mlh-tpages*) fn-mlh)))
                    (if (< (nfix j) *fn-mlh-page-slots*) (nfix j) nil))))
  :hints (("Goal" :induct (fn-mlh-find-empty p j fn-mlh)
           :expand ((:free (pg) (fn-mlg-find-empty j pg)) (fn-mlh-find-empty p j fn-mlh))
           :in-theory (e/d (fn-mlh-find-empty fn-mlh-slot-reads-by-page) (floor mod fn-mlh-word fn-mlh-tag-at fn-mlh-seqw))))))

(defthm fn-mlh-find-empty-pg-is-find-empty
  (implies (natp p)
           (equal (fn-mlh-find-empty-pg p j fn-mlh)
                  (fn-mlh-find-empty p j fn-mlh)))
  :hints (("Goal" :in-theory (e/d (fn-mlh-find-empty-pg) (floor mod fn-mlg-find-empty fn-mlh-find-empty)))))

(in-theory (disable fn-mlh-find-empty-pg))
(local (in-theory (disable fn-mlh-find-empty-is-page-find)))

;; THE ONE PAGE WRITE: slot J of page P set to the words TW and SW.  Every
;; writer below is this.
(defun fn-mlh-set-words (p j tw sw fn-mlh)
  (declare (xargs :stobjs fn-mlh
                  :guard (and (fn-mlh-slot-guardp p j fn-mlh)
                              (unsigned-byte-p 61 tw) (unsigned-byte-p 61 sw))))
  (let ((fn-mlh (fn-mlh-put-word p j tw fn-mlh)))
    (fn-mlh-put-word p (+ *fn-mlh-page-slots* j) sw fn-mlh)))

(defthm fn-mlh-set-words-frame
  (and (equal (fn-mlh-pages (fn-mlh-set-words p j tw sw fn-mlh)) (fn-mlh-pages fn-mlh))
       (equal (fn-mlh-n (fn-mlh-set-words p j tw sw fn-mlh)) (fn-mlh-n fn-mlh))
       (equal (fn-mlh-s (fn-mlh-set-words p j tw sw fn-mlh)) (fn-mlh-s fn-mlh))
       (equal (fn-mlh-count (fn-mlh-set-words p j tw sw fn-mlh)) (fn-mlh-count fn-mlh))
       (equal (fn-mlh-stuck (fn-mlh-set-words p j tw sw fn-mlh)) (fn-mlh-stuck fn-mlh))
       (equal (fn-mlh-key-octets (fn-mlh-set-words p j tw sw fn-mlh)) (fn-mlh-key-octets fn-mlh))))

(defthm fn-mlh-set-words-shape
  (implies (and (fn-mlhp fn-mlh) (fn-mlh-slot-guardp p j fn-mlh)
                (unsigned-byte-p 61 tw) (unsigned-byte-p 61 sw))
           (and (fn-mlhp (fn-mlh-set-words p j tw sw fn-mlh))
                (fn-mlh-pgsp (fn-mlh-set-words p j tw sw fn-mlh))
                (equal (fn-mlh-wfp (fn-mlh-set-words p j tw sw fn-mlh)) (fn-mlh-wfp fn-mlh))))
  :hints (("Goal" :in-theory (enable fn-mlh-pgsp))))

(defthm fn-mlh-accessors-of-set-words
  (implies (and (natp q) (natp i) (< i *fn-mlh-page-slots*)
                (natp p) (natp j) (< j *fn-mlh-page-slots*))
           (and (equal (fn-mlh-tag-at q i (fn-mlh-set-words p j tw sw fn-mlh))
                       (if (and (equal q p) (equal i j)) (nfix tw) (fn-mlh-tag-at q i fn-mlh)))
                (equal (fn-mlh-seqw q i (fn-mlh-set-words p j tw sw fn-mlh))
                       (if (and (equal q p) (equal i j)) (nfix sw) (fn-mlh-seqw q i fn-mlh)))))
  :hints (("Goal" :in-theory (enable fn-mlh-tag-at fn-mlh-seqw))))

(in-theory (disable fn-mlh-set-words))

; A write of (TAG, SEQ) into slot J of page P keeps the flag part of its
; seq word.
(defun fn-mlh-write-slot (p j tag seq fn-mlh)
  (declare (xargs :stobjs fn-mlh
                  :guard (and (fn-mlh-slot-guardp p j fn-mlh)
                              (natp tag) (< tag *fn-mlh-tag-limit*)
                              (natp seq) (< (+ 1 seq) *fn-mlh-tag-limit*))
                  :guard-hints (("Goal" :in-theory (enable unsigned-byte-p)))))
  (fn-mlh-set-words p j tag (+ 1 seq (fn-mlh-flag-part (fn-mlh-seqw p j fn-mlh))) fn-mlh))

; Set page P's overflow flag.
(defun fn-mlh-set-ovf (p fn-mlh)
  (declare (xargs :stobjs fn-mlh
                  :guard (and (natp p) (< p (fn-mlh-pages fn-mlh)) (fn-mlh-wfp fn-mlh))
                  :guard-hints (("Goal" :in-theory (enable unsigned-byte-p)))))
  (let ((w (fn-mlh-seqw p 0 fn-mlh)))
    (if (< w *fn-mlh-flag*)
        (fn-mlh-set-words p 0 (fn-mlh-tag-at p 0 fn-mlh) (+ w *fn-mlh-flag*) fn-mlh)
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
  (implies (and (fn-mlhp fn-mlh) (fn-mlh-slot-guardp p j fn-mlh) (fn-mlh-wfp fn-mlh)
                (natp tag) (< tag *fn-mlh-tag-limit*)
                (natp seq) (< (+ 1 seq) *fn-mlh-tag-limit*))
           (and (fn-mlhp (fn-mlh-write-slot p j tag seq fn-mlh))
                (fn-mlh-pgsp (fn-mlh-write-slot p j tag seq fn-mlh))
                (fn-mlh-wfp (fn-mlh-write-slot p j tag seq fn-mlh))))
  :hints (("Goal" :in-theory (e/d (unsigned-byte-p) (fn-mlh-slot-guardp fn-mlh-wfp)))))

(defthm fn-mlh-set-ovf-shape
  (implies (and (fn-mlhp fn-mlh) (natp p) (< p (fn-mlh-pages fn-mlh)) (fn-mlh-wfp fn-mlh))
           (and (fn-mlhp (fn-mlh-set-ovf p fn-mlh))
                (fn-mlh-pgsp (fn-mlh-set-ovf p fn-mlh))
                (fn-mlh-wfp (fn-mlh-set-ovf p fn-mlh))))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

; The slot accessors after a write: the written slot reads the entry, every
; other slot as before, and every flag as before.
(defthm fn-mlh-tag-at-of-write-slot
  (implies (and (natp q) (natp i) (< i *fn-mlh-page-slots*)
                (natp p) (natp j) (< j *fn-mlh-page-slots*))
           (equal (fn-mlh-tag-at q i (fn-mlh-write-slot p j tag seq fn-mlh))
                  (if (and (equal q p) (equal i j)) (nfix tag) (fn-mlh-tag-at q i fn-mlh)))))

(defthm fn-mlh-seqw-of-write-slot
  (implies (and (natp q) (natp i) (< i *fn-mlh-page-slots*)
                (natp p) (natp j) (< j *fn-mlh-page-slots*))
           (equal (fn-mlh-seqw q i (fn-mlh-write-slot p j tag seq fn-mlh))
                  (if (and (equal q p) (equal i j))
                      (nfix (+ 1 seq (fn-mlh-flag-part (fn-mlh-seqw p j fn-mlh))))
                    (fn-mlh-seqw q i fn-mlh)))))

(defthm fn-mlh-tag-at-of-set-ovf
  (implies (and (fn-mlhp fn-mlh) (natp q) (natp i) (< i *fn-mlh-page-slots*) (natp p))
           (equal (fn-mlh-tag-at q i (fn-mlh-set-ovf p fn-mlh)) (fn-mlh-tag-at q i fn-mlh))))

(defthm fn-mlh-seqw-of-set-ovf
  (implies (and (fn-mlhp fn-mlh) (natp q) (natp i) (< i *fn-mlh-page-slots*) (natp p))
           (equal (fn-mlh-seqw q i (fn-mlh-set-ovf p fn-mlh))
                  (if (and (equal q p) (equal i 0) (< (fn-mlh-seqw p 0 fn-mlh) *fn-mlh-flag*))
                      (+ *fn-mlh-flag* (fn-mlh-seqw p 0 fn-mlh))
                    (fn-mlh-seqw q i fn-mlh)))))

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
                  :guard (and (posp tag) (< tag *fn-mlh-tag-limit*)
                              (natp seq) (< (+ 1 seq) *fn-mlh-tag-limit*)
                              (fn-mlh-wfp fn-mlh))
                  :guard-hints (("Goal" :use ((:instance fn-mpxl-addr-below (n (fn-mlh-n fn-mlh)) (s (fn-mlh-s fn-mlh))))
                                 :in-theory (disable fn-mpxl-addr-below fn-mlh-find-empty)))))
  (let ((np (fn-mlh-pages fn-mlh)))
    (if (zp np)
        (mv nil fn-mlh)
      (let* ((h (fn-mpxl-addr tag (fn-mlh-n fn-mlh) (fn-mlh-s fn-mlh)))
             (j (mbe :logic (fn-mlh-find-empty h 0 fn-mlh) :exec (fn-mlh-find-empty-pg h 0 fn-mlh))))
        (if j
            (let ((fn-mlh (fn-mlh-write-slot h j tag seq fn-mlh)))
              (mv t fn-mlh))
          (if (< (+ 1 h) np)
              (let ((j1 (mbe :logic (fn-mlh-find-empty (+ 1 h) 0 fn-mlh)
                             :exec (fn-mlh-find-empty-pg (+ 1 h) 0 fn-mlh))))
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
                (fn-mlh-pgsp (mv-nth 1 (fn-mlh-put tag seq fn-mlh)))
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

; -----------------------------------------------------------------------------
; 7. THE SPLIT.  The movers of page S (and of its overflow page S + 1, when
; there is one) are moved, in slot order, onto ONE new page N + S; the root
; advances.  The work is the two pages read and the one page written; the
; allocation is the one new page (and the page array's pointers).  Refused,
; the table unchanged, when the movers exceed a page.  GEN: def-loop (the
; count and the move).

(local (in-theory (disable mod)))

; Clear slot J of page P, keeping its seq word's flag part.
(defun fn-mlh-clear-slot (p j fn-mlh)
  (declare (xargs :stobjs fn-mlh
                  :guard (fn-mlh-slot-guardp p j fn-mlh)
                  :guard-hints (("Goal" :in-theory (enable unsigned-byte-p fn-mlh-flag-part)))))
  (fn-mlh-set-words p j 0 (fn-mlh-flag-part (fn-mlh-seqw p j fn-mlh)) fn-mlh))

(defthm fn-mlh-clear-slot-frame
  (and (equal (fn-mlh-pages (fn-mlh-clear-slot p j fn-mlh)) (fn-mlh-pages fn-mlh))
       (equal (fn-mlh-n (fn-mlh-clear-slot p j fn-mlh)) (fn-mlh-n fn-mlh))
       (equal (fn-mlh-s (fn-mlh-clear-slot p j fn-mlh)) (fn-mlh-s fn-mlh))
       (equal (fn-mlh-count (fn-mlh-clear-slot p j fn-mlh)) (fn-mlh-count fn-mlh))
       (equal (fn-mlh-stuck (fn-mlh-clear-slot p j fn-mlh)) (fn-mlh-stuck fn-mlh))
       (equal (fn-mlh-key-octets (fn-mlh-clear-slot p j fn-mlh)) (fn-mlh-key-octets fn-mlh))))

(defthm fn-mlh-clear-slot-shape
  (implies (and (fn-mlhp fn-mlh) (fn-mlh-slot-guardp p j fn-mlh))
           (and (fn-mlhp (fn-mlh-clear-slot p j fn-mlh))
                (fn-mlh-pgsp (fn-mlh-clear-slot p j fn-mlh))
                (equal (fn-mlh-wfp (fn-mlh-clear-slot p j fn-mlh)) (fn-mlh-wfp fn-mlh))))
  :hints (("Goal" :in-theory (e/d (unsigned-byte-p fn-mlh-flag-part) (fn-mlh-slot-guardp fn-mlh-wfp fn-mlh-pgsp)))))

(defthm fn-mlh-accessors-of-clear-slot
  (implies (and (natp q) (natp i) (< i *fn-mlh-page-slots*)
                (natp p) (natp j) (< j *fn-mlh-page-slots*))
           (and (equal (fn-mlh-tag-at q i (fn-mlh-clear-slot p j fn-mlh))
                       (if (and (equal q p) (equal i j)) 0 (fn-mlh-tag-at q i fn-mlh)))
                (equal (fn-mlh-seqw q i (fn-mlh-clear-slot p j fn-mlh))
                       (if (and (equal q p) (equal i j))
                           (fn-mlh-flag-part (fn-mlh-seqw p j fn-mlh))
                         (fn-mlh-seqw q i fn-mlh)))))
  :hints (("Goal" :in-theory (enable fn-mlh-flag-part))))

(defthm fn-mlh-ovf-of-clear-slot
  (implies (and (natp q) (natp p) (natp j) (< j *fn-mlh-page-slots*))
           (equal (fn-mlh-ovf q (fn-mlh-clear-slot p j fn-mlh))
                  (fn-mlh-ovf q fn-mlh)))
  :hints (("Goal" :in-theory (enable fn-mlh-ovf-is-seqw fn-mlh-flag-part))))

(defthm fn-mlh-seq-at-of-clear-slot
  (implies (and (fn-mlhp fn-mlh) (natp q) (natp i) (< i *fn-mlh-page-slots*)
                (natp p) (natp j) (< j *fn-mlh-page-slots*)
                (not (and (equal q p) (equal i j))))
           (equal (fn-mlh-seq-at q i (fn-mlh-clear-slot p j fn-mlh)) (fn-mlh-seq-at q i fn-mlh)))
  :hints (("Goal" :in-theory (enable fn-mlh-seq-at-is-seqw))))

(in-theory (disable fn-mlh-clear-slot))

; A raw write of an entry onto the new page: slot C of page P reads (TAG,
; SEQW) with no flag (the new page's flag is clear).
(defthm fn-mlh-ovf-of-set-words-other
  (implies (and (natp q) (natp p) (natp j) (< j *fn-mlh-page-slots*) (not (equal q p)))
           (equal (fn-mlh-ovf q (fn-mlh-set-words p j tw sw fn-mlh))
                  (fn-mlh-ovf q fn-mlh)))
  :hints (("Goal" :in-theory (enable fn-mlh-ovf-is-seqw))))

; Slot J of page Q holds an entry whose tag moves to page P (mod 2N).
(defun fn-mlh-mover-at (q j n p fn-mlh)
  (declare (xargs :stobjs fn-mlh
                  :guard (and (fn-mlh-slot-guardp q j fn-mlh) (posp n) (natp p))))
  (let ((tag (fn-mlh-tag-at q j fn-mlh)))
    (and (not (equal 0 tag))
         (<= 1 (fn-mlh-seq-at q j fn-mlh))
         (equal (mod tag (* 2 n)) p))))

; The movers of page Q from slot J, counted.
(defun fn-mlh-count-movers (q j n p fn-mlh)
  (declare (xargs :stobjs fn-mlh
                  :guard (and (natp q) (natp j) (< q (fn-mlh-pages fn-mlh)) (fn-mlh-pgsp fn-mlh)
                              (posp n) (natp p))
                  :measure (nfix (- *fn-mlh-page-slots* (nfix j)))))
  (if (>= (nfix j) *fn-mlh-page-slots*)
      0
    (+ (if (fn-mlh-mover-at q (nfix j) n p fn-mlh) 1 0)
       (fn-mlh-count-movers q (1+ (nfix j)) n p fn-mlh))))

(defthm fn-mlh-count-movers-is-len
  (implies (natp j)
           (equal (fn-mlh-count-movers q j n p fn-mlh)
                  (len (fn-mpxl-movers (fn-mlh-pe q j fn-mlh) n p))))
  :hints (("Goal" :induct (fn-mlh-count-movers q j n p fn-mlh)
           :in-theory (enable fn-mpxl-moverp)
           :expand ((fn-mlh-pe q j fn-mlh)))))

(in-theory (disable fn-mlh-mover-at))

; THE MOVE: the movers of page Q from slot J, in slot order, onto page P from
; slot C, each cleared on Q.
(defun fn-mlh-move (q j c p n fn-mlh)
  (declare (xargs :stobjs fn-mlh
                  :guard (and (natp q) (natp j) (natp c) (natp p) (posp n)
                              (< q (fn-mlh-pages fn-mlh)) (< p (fn-mlh-pages fn-mlh))
                              (fn-mlh-pgsp fn-mlh))
                  :measure (nfix (- *fn-mlh-page-slots* (nfix j)))
                  :guard-hints (("Goal" :in-theory (enable unsigned-byte-p)))))
  (if (>= (nfix j) *fn-mlh-page-slots*)
      fn-mlh
    (if (and (fn-mlh-mover-at q (nfix j) n p fn-mlh) (< (nfix c) *fn-mlh-page-slots*))
        (let* ((fn-mlh (fn-mlh-set-words p (nfix c) (fn-mlh-tag-at q (nfix j) fn-mlh)
                                         (fn-mlh-seq-at q (nfix j) fn-mlh) fn-mlh))
               (fn-mlh (fn-mlh-clear-slot q (nfix j) fn-mlh)))
          (fn-mlh-move q (1+ (nfix j)) (1+ (nfix c)) p n fn-mlh))
      (fn-mlh-move q (1+ (nfix j)) c p n fn-mlh))))

(defthm fn-mlh-move-frame
  (and (equal (fn-mlh-pages (fn-mlh-move q j c p n fn-mlh)) (fn-mlh-pages fn-mlh))
       (equal (fn-mlh-n (fn-mlh-move q j c p n fn-mlh)) (fn-mlh-n fn-mlh))
       (equal (fn-mlh-s (fn-mlh-move q j c p n fn-mlh)) (fn-mlh-s fn-mlh))
       (equal (fn-mlh-count (fn-mlh-move q j c p n fn-mlh)) (fn-mlh-count fn-mlh))
       (equal (fn-mlh-stuck (fn-mlh-move q j c p n fn-mlh)) (fn-mlh-stuck fn-mlh))
       (equal (fn-mlh-key-octets (fn-mlh-move q j c p n fn-mlh)) (fn-mlh-key-octets fn-mlh)))
  :hints (("Goal" :induct (fn-mlh-move q j c p n fn-mlh))))

(defthm fn-mlh-move-shape
  (implies (and (fn-mlhp fn-mlh) (fn-mlh-pgsp fn-mlh)
                (natp q) (< q (fn-mlh-pages fn-mlh)) (natp p) (< p (fn-mlh-pages fn-mlh)))
           (and (fn-mlhp (fn-mlh-move q j c p n fn-mlh))
                (fn-mlh-pgsp (fn-mlh-move q j c p n fn-mlh))))
  :hints (("Goal" :induct (fn-mlh-move q j c p n fn-mlh)
           :in-theory (e/d (unsigned-byte-p) (fn-mlh-wfp fn-mlh-pgsp fn-mlh-mover-at)))))

(defthm fn-mlh-wfp-of-move
  (equal (fn-mlh-wfp (fn-mlh-move q j c p n fn-mlh))
         (and (fn-mlh-pgsp (fn-mlh-move q j c p n fn-mlh)) (fn-mlh-rootp fn-mlh)))
  :hints (("Goal" :in-theory (disable fn-mlh-move))))

; THE MOVE'S FRAME: a slot of another page, of Q below J, or of P below C is
; as it was.
(defthm fn-mlh-accessors-of-move
  (implies (and (natp r) (natp i) (< i *fn-mlh-page-slots*)
                (natp q) (natp p) (not (equal p q)) (natp j) (natp c)
                (not (and (equal r q) (<= j i)))
                (not (and (equal r p) (<= c i))))
           (and (equal (fn-mlh-tag-at r i (fn-mlh-move q j c p n fn-mlh)) (fn-mlh-tag-at r i fn-mlh))
                (equal (fn-mlh-seqw r i (fn-mlh-move q j c p n fn-mlh)) (fn-mlh-seqw r i fn-mlh))))
  :hints (("Goal" :induct (fn-mlh-move q j c p n fn-mlh)
           :in-theory (disable fn-mlh-mover-at))))

(defthm fn-mlh-ovf-of-move
  (implies (and (natp r) (natp q) (natp p) (not (equal r p)) (natp j))
           (equal (fn-mlh-ovf r (fn-mlh-move q j c p n fn-mlh)) (fn-mlh-ovf r fn-mlh)))
  :hints (("Goal" :induct (fn-mlh-move q j c p n fn-mlh)
           :in-theory (disable fn-mlh-mover-at fn-mlh-ovf-is-seqw))))

; The new page's flag stays clear: every write onto it is a seq below the flag.
(defthm fn-mlh-ovf-of-move-dest
  (implies (and (fn-mlhp fn-mlh) (fn-mlh-pgsp fn-mlh)
                (natp q) (< q (fn-mlh-pages fn-mlh)) (natp p) (< p (fn-mlh-pages fn-mlh))
                (not (equal q p)) (natp j)
                (not (fn-mlh-ovf p fn-mlh)))
           (not (fn-mlh-ovf p (fn-mlh-move q j c p n fn-mlh))))
  :hints (("Goal" :induct (fn-mlh-move q j c p n fn-mlh)
           :in-theory (e/d (fn-mlh-ovf-is-seqw unsigned-byte-p) (fn-mlh-mover-at fn-mlh-pgsp)))))

; The entries of another page are as they were.
(defthm fn-mlh-pe-of-move-other
  (implies (and (natp r) (natp q) (natp p) (not (equal r q)) (not (equal r p)) (not (equal p q))
                (natp j) (natp c))
           (equal (fn-mlh-pe r i (fn-mlh-move q j c p n fn-mlh)) (fn-mlh-pe r i fn-mlh)))
  :hints (("Goal" :induct (fn-mlh-pe r i fn-mlh)
           :in-theory (e/d (fn-mlh-seq-at-is-seqw) (fn-mlh-move)))))

; --- the move's effect on the entries ---

(defthm fn-mlh-pe-of-set-words-frame
  (implies (and (natp r) (natp p) (natp j) (< j *fn-mlh-page-slots*) (natp i)
                (or (not (equal r p)) (< j i)))
           (equal (fn-mlh-pe r i (fn-mlh-set-words p j tw sw fn-mlh)) (fn-mlh-pe r i fn-mlh)))
  :hints (("Goal" :induct (fn-mlh-pe r i fn-mlh)
           :in-theory (enable fn-mlh-seq-at-is-seqw))))

(defthm fn-mlh-pe-of-clear-slot-frame
  (implies (and (natp r) (natp p) (natp j) (< j *fn-mlh-page-slots*) (natp i)
                (or (not (equal r p)) (< j i)))
           (equal (fn-mlh-pe r i (fn-mlh-clear-slot p j fn-mlh)) (fn-mlh-pe r i fn-mlh)))
  :hints (("Goal" :induct (fn-mlh-pe r i fn-mlh)
           :in-theory (enable fn-mlh-seq-at-is-seqw))))

; THE SOURCE PAGE keeps its stayers (the move has room for every mover).
(defthm fn-mlh-pe-of-move-source
  (implies (and (natp q) (natp p) (not (equal p q)) (natp j) (natp c)
                (<= (+ c (len (fn-mpxl-movers (fn-mlh-pe q j fn-mlh) n p))) *fn-mlh-page-slots*))
           (equal (fn-mlh-pe q j (fn-mlh-move q j c p n fn-mlh))
                  (fn-mpxl-stayers (fn-mlh-pe q j fn-mlh) n p)))
  :hints (("Goal" :induct (fn-mlh-move q j c p n fn-mlh)
           :in-theory (e/d (fn-mlh-mover-at fn-mpxl-moverp fn-mlh-seq-at-is-seqw) (fn-mlh-pe))
           :expand ((fn-mlh-pe q j fn-mlh)
                    (:free (x) (fn-mlh-pe q j x))))))

; Every slot of page P from C up is empty.
(defun fn-mlh-empty-from (p c fn-mlh)
  (declare (xargs :stobjs fn-mlh :verify-guards nil :measure (nfix (- *fn-mlh-page-slots* (nfix c)))))
  (if (>= (nfix c) *fn-mlh-page-slots*)
      t
    (and (equal 0 (fn-mlh-tag-at p (nfix c) fn-mlh))
         (fn-mlh-empty-from p (1+ (nfix c)) fn-mlh))))

(defthm fn-mlh-empty-from-pe
  (implies (fn-mlh-empty-from p c fn-mlh)
           (equal (fn-mlh-pe p c fn-mlh) nil))
  :hints (("Goal" :induct (fn-mlh-empty-from p c fn-mlh))))

(defthm fn-mlh-empty-from-of-set-words-frame
  (implies (and (natp r) (natp p) (natp j) (< j *fn-mlh-page-slots*) (natp k)
                (or (not (equal r p)) (< j k)))
           (equal (fn-mlh-empty-from r k (fn-mlh-set-words p j tw sw fn-mlh)) (fn-mlh-empty-from r k fn-mlh)))
  :hints (("Goal" :induct (fn-mlh-empty-from r k fn-mlh))))

(defthm fn-mlh-empty-from-of-clear-slot-frame
  (implies (and (natp r) (natp p) (natp j) (< j *fn-mlh-page-slots*) (natp k) (not (equal r p)))
           (equal (fn-mlh-empty-from r k (fn-mlh-clear-slot p j fn-mlh)) (fn-mlh-empty-from r k fn-mlh)))
  :hints (("Goal" :induct (fn-mlh-empty-from r k fn-mlh))))

(defthm fn-mlh-empty-from-tag-at
  (implies (and (fn-mlh-empty-from p c fn-mlh) (natp c) (natp i) (<= c i) (< i *fn-mlh-page-slots*))
           (equal (fn-mlh-tag-at p i fn-mlh) 0))
  :hints (("Goal" :induct (fn-mlh-empty-from p c fn-mlh))))

; THE NEW PAGE receives the movers, in slot order, from C.
(defthm fn-mlh-pe-of-move-dest
  (implies (and (fn-mlhp fn-mlh) (fn-mlh-pgsp fn-mlh)
                (natp q) (< q (fn-mlh-pages fn-mlh)) (natp p) (< p (fn-mlh-pages fn-mlh))
                (not (equal p q)) (natp j) (natp c)
                (fn-mlh-empty-from p c fn-mlh)
                (<= (+ c (len (fn-mpxl-movers (fn-mlh-pe q j fn-mlh) n p))) *fn-mlh-page-slots*))
           (equal (fn-mlh-pe p c (fn-mlh-move q j c p n fn-mlh))
                  (fn-mpxl-movers (fn-mlh-pe q j fn-mlh) n p)))
  :hints (("Goal" :induct (fn-mlh-move q j c p n fn-mlh)
           :in-theory (e/d (fn-mlh-mover-at fn-mpxl-moverp fn-mlh-seq-at-is-seqw unsigned-byte-p)
                           (fn-mlh-pe fn-mlh-pgsp))
           :expand ((fn-mlh-pe q j fn-mlh)
                    (:free (x) (fn-mlh-pe p c x))))))

; After the move the new page is empty from C plus the movers.
(defthm fn-mlh-empty-from-of-move
  (implies (and (natp q) (natp p) (not (equal p q)) (natp j) (natp c)
                (fn-mlh-empty-from p c fn-mlh)
                (<= (+ c (len (fn-mpxl-movers (fn-mlh-pe q j fn-mlh) n p))) *fn-mlh-page-slots*))
           (fn-mlh-empty-from p (+ c (len (fn-mpxl-movers (fn-mlh-pe q j fn-mlh) n p)))
                              (fn-mlh-move q j c p n fn-mlh)))
  :hints (("Goal" :induct (fn-mlh-move q j c p n fn-mlh)
           :in-theory (e/d (fn-mlh-mover-at fn-mpxl-moverp) (fn-mlh-pe fn-mlh-empty-from))
           :expand ((fn-mlh-pe q j fn-mlh) (fn-mlh-empty-from p c fn-mlh)))))

; The same, its index written as the rewriter meets it.
(defthm fn-mlh-empty-from-of-move-at
  (implies (and (natp q) (natp p) (not (equal p q)) (natp j) (natp c)
                (fn-mlh-empty-from p c fn-mlh)
                (equal k (+ c (len (fn-mpxl-movers (fn-mlh-pe q j fn-mlh) n p))))
                (<= k *fn-mlh-page-slots*))
           (fn-mlh-empty-from p k (fn-mlh-move q j c p n fn-mlh)))
  :hints (("Goal" :use fn-mlh-empty-from-of-move
           :in-theory (disable fn-mlh-empty-from-of-move fn-mlh-pe fn-mlh-move fn-mlh-empty-from))))

; The entries below C of the new page are as they were.
(defthm fn-mlh-pe-upto-of-move
  (implies (and (natp q) (natp p) (not (equal p q)) (natp j) (natp c) (natp k) (<= k c)
                (<= k *fn-mlh-page-slots*))
           (equal (fn-mlh-pe-upto p k (fn-mlh-move q j c p n fn-mlh))
                  (fn-mlh-pe-upto p k fn-mlh)))
  :hints (("Goal" :induct (fn-mlh-pe-upto p k fn-mlh)
           :in-theory (e/d (fn-mlh-seq-at-is-seqw) (fn-mlh-move)))))

(defthm fn-mlh-pe-of-move-dest-whole
  (implies (and (fn-mlhp fn-mlh) (fn-mlh-pgsp fn-mlh)
                (natp q) (< q (fn-mlh-pages fn-mlh)) (natp p) (< p (fn-mlh-pages fn-mlh))
                (not (equal p q)) (natp j) (natp c)
                (fn-mlh-empty-from p c fn-mlh)
                (<= (+ c (len (fn-mpxl-movers (fn-mlh-pe q j fn-mlh) n p))) *fn-mlh-page-slots*))
           (equal (fn-mlh-pe p 0 (fn-mlh-move q j c p n fn-mlh))
                  (append (fn-mlh-pe-upto p c fn-mlh) (fn-mpxl-movers (fn-mlh-pe q j fn-mlh) n p))))
  :hints (("Goal" :use ((:instance fn-mlh-pe-upto-pe (j c) (fn-mlh (fn-mlh-move q j c p n fn-mlh))))
           :in-theory (disable fn-mlh-pe-upto-pe fn-mlh-pe fn-mlh-pe-upto fn-mlh-move))))

; --- the new page ---

; GROW: one fresh page after the last (Codex r42 F1): page NP's slot is
; taken in its table page, which is readied (64 empty slots) when NP opens
; one; the directory doubles only past its width, which the open reserves
; for the profile.  No pointer array is copied page by page.
(defun fn-mlh-grow (fn-mlh)
  (declare (xargs :stobjs fn-mlh :guard (fn-mlh-pgsp fn-mlh)))
  (let* ((np (fn-mlh-pages fn-mlh))
         (fn-mlh (fn-mlh-fresh-page np fn-mlh)))
    (update-fn-mlh-pages (+ 1 np) fn-mlh)))

(defthm fn-mlh-grow-shape
  (implies (and (fn-mlhp fn-mlh) (fn-mlh-pgsp fn-mlh))
           (and (fn-mlhp (fn-mlh-grow fn-mlh))
                (fn-mlh-pgsp (fn-mlh-grow fn-mlh))
                (equal (fn-mlh-pages (fn-mlh-grow fn-mlh)) (+ 1 (fn-mlh-pages fn-mlh)))
                (equal (fn-mlh-n (fn-mlh-grow fn-mlh)) (fn-mlh-n fn-mlh))
                (equal (fn-mlh-s (fn-mlh-grow fn-mlh)) (fn-mlh-s fn-mlh))
                (equal (fn-mlh-count (fn-mlh-grow fn-mlh)) (fn-mlh-count fn-mlh))
                (equal (fn-mlh-stuck (fn-mlh-grow fn-mlh)) (fn-mlh-stuck fn-mlh))
                (equal (fn-mlh-key-octets (fn-mlh-grow fn-mlh)) (fn-mlh-key-octets fn-mlh))))
  :hints (("Goal" :in-theory (enable fn-mlh-pgsp))))

; Every old slot reads as before; every slot of the new page is empty.
(defthm fn-mlh-accessors-of-grow
  (implies (and (fn-mlhp fn-mlh) (fn-mlh-pgsp fn-mlh) (natp r))
           (and (equal (fn-mlh-tag-at r i (fn-mlh-grow fn-mlh))
                       (if (equal r (fn-mlh-pages fn-mlh)) 0 (fn-mlh-tag-at r i fn-mlh)))
                (equal (fn-mlh-seqw r i (fn-mlh-grow fn-mlh))
                       (if (equal r (fn-mlh-pages fn-mlh)) 0 (fn-mlh-seqw r i fn-mlh)))))
  :hints (("Goal" :in-theory (enable fn-mlh-tag-at fn-mlh-seqw))))

(in-theory (disable fn-mlh-grow))

(defthm fn-mlh-pe-of-grow
  (implies (and (fn-mlhp fn-mlh) (fn-mlh-pgsp fn-mlh) (natp r) (< r (fn-mlh-pages fn-mlh)))
           (equal (fn-mlh-pe r i (fn-mlh-grow fn-mlh)) (fn-mlh-pe r i fn-mlh)))
  :hints (("Goal" :induct (fn-mlh-pe r i fn-mlh)
           :in-theory (enable fn-mlh-seq-at-is-seqw))))

(defthm fn-mlh-ovf-of-grow
  (implies (and (fn-mlhp fn-mlh) (fn-mlh-pgsp fn-mlh) (natp r))
           (equal (fn-mlh-ovf r (fn-mlh-grow fn-mlh))
                  (and (not (equal r (fn-mlh-pages fn-mlh))) (fn-mlh-ovf r fn-mlh))))
  :hints (("Goal" :in-theory (enable fn-mlh-ovf-is-seqw))))

(defthm fn-mlh-empty-from-of-grow
  (implies (and (fn-mlhp fn-mlh) (fn-mlh-pgsp fn-mlh) (equal p (fn-mlh-pages fn-mlh)))
           (fn-mlh-empty-from p c (fn-mlh-grow fn-mlh)))
  :hints (("Goal" :induct (fn-mlh-empty-from p c (fn-mlh-grow fn-mlh)))))

(defthm fn-mlh-pe-upto-0
  (equal (fn-mlh-pe-upto p 0 fn-mlh) nil))

; --- the split ---

; THE SPLIT; (mv taken fn-mlh).  M0 movers on page S, M1 on S + 1; refused,
; the table unchanged, when they exceed a page.  Taken: a fresh page N + S;
; the movers of S from its slot 0, then those of S + 1 after them; the root
; advances (S + 1, or N doubled and S = 0 at the round's end).
(defun fn-mlh-split (fn-mlh)
  (declare (xargs :stobjs fn-mlh :guard (fn-mlh-wfp fn-mlh)))
  (let ((np (fn-mlh-pages fn-mlh)) (n (fn-mlh-n fn-mlh)) (s (fn-mlh-s fn-mlh)))
    (if (zp np)
        (mv nil fn-mlh)
      (let* ((m0 (fn-mlh-count-movers s 0 n np fn-mlh))
             (m1 (if (< (+ 1 s) np) (fn-mlh-count-movers (+ 1 s) 0 n np fn-mlh) 0)))
        (if (< *fn-mpxl-cap* (+ m0 m1))
            (mv nil fn-mlh)
          (let* ((fn-mlh (fn-mlh-grow fn-mlh))
                 (fn-mlh (fn-mlh-move s 0 0 np n fn-mlh))
                 (fn-mlh (if (< (+ 1 s) np) (fn-mlh-move (+ 1 s) 0 m0 np n fn-mlh) fn-mlh))
                 (fn-mlh (if (equal (+ 1 s) n) (update-fn-mlh-n (* 2 n) fn-mlh) fn-mlh))
                 (fn-mlh (update-fn-mlh-s (if (equal (+ 1 s) n) 0 (+ 1 s)) fn-mlh)))
            (mv t fn-mlh)))))))

(defthm fn-mlh-pe-of-root-updates
  (and (equal (fn-mlh-pe r i (update-fn-mlh-n m fn-mlh)) (fn-mlh-pe r i fn-mlh))
       (equal (fn-mlh-pe r i (update-fn-mlh-s m fn-mlh)) (fn-mlh-pe r i fn-mlh))
       (equal (fn-mlh-pe r i (update-fn-mlh-count m fn-mlh)) (fn-mlh-pe r i fn-mlh))
       (equal (fn-mlh-pe r i (update-fn-mlh-stuck m fn-mlh)) (fn-mlh-pe r i fn-mlh)))
  :hints (("Goal" :induct (fn-mlh-pe r i fn-mlh) :in-theory (enable fn-mlh-seq-at-is-seqw))))

(defthm fn-mlh-ovf-of-root-updates
  (and (equal (fn-mlh-ovf r (update-fn-mlh-n m fn-mlh)) (fn-mlh-ovf r fn-mlh))
       (equal (fn-mlh-ovf r (update-fn-mlh-s m fn-mlh)) (fn-mlh-ovf r fn-mlh))
       (equal (fn-mlh-ovf r (update-fn-mlh-count m fn-mlh)) (fn-mlh-ovf r fn-mlh))
       (equal (fn-mlh-ovf r (update-fn-mlh-stuck m fn-mlh)) (fn-mlh-ovf r fn-mlh)))
  :hints (("Goal" :in-theory (enable fn-mlh-ovf-is-seqw))))

(local (defthm fn-mlh-true-listp-pe-upto
  (true-listp (fn-mlh-pe-upto p c fn-mlh))))

(defthm fn-mlh-pe-upto-when-empty-from
  (implies (and (fn-mlh-empty-from p c fn-mlh) (natp c) (<= c *fn-mlh-page-slots*))
           (equal (fn-mlh-pe-upto p c fn-mlh) (fn-mlh-pe p 0 fn-mlh)))
  :hints (("Goal" :use ((:instance fn-mlh-pe-upto-pe (j c)))
           :in-theory (disable fn-mlh-pe-upto-pe fn-mlh-pe fn-mlh-pe-upto))))

(local (defthm fn-mlh-len-movers-bound
  (<= (len (fn-mpxl-movers ents n p)) (len ents))
  :rule-classes :linear))

; THE PAGES AFTER THE SPLIT, page by page: S and S + 1 keep their stayers
; and their flags, the new page N + S holds the movers of S then of S + 1
; with its flag clear, every other page is as it was.
(defthm fn-mlh-split-page
  (implies (and (fn-mlhp fn-mlh) (fn-mlh-wfp fn-mlh) (posp (fn-mlh-pages fn-mlh))
                (mv-nth 0 (fn-mlh-split fn-mlh))
                (natp i) (<= i (fn-mlh-pages fn-mlh)))
           (let ((np (fn-mlh-pages fn-mlh)) (n (fn-mlh-n fn-mlh)) (s (fn-mlh-s fn-mlh))
                 (after (mv-nth 1 (fn-mlh-split fn-mlh))))
             (and (equal (fn-mlh-ovf i after)
                         (if (equal i np) nil (fn-mlh-ovf i fn-mlh)))
                  (equal (fn-mlh-pe i 0 after)
                         (cond ((equal i s) (fn-mpxl-stayers (fn-mlh-pe s 0 fn-mlh) n np))
                               ((and (equal i (+ 1 s)) (< i np))
                                (fn-mpxl-stayers (fn-mlh-pe i 0 fn-mlh) n np))
                               ((equal i np)
                                (append (fn-mpxl-movers (fn-mlh-pe s 0 fn-mlh) n np)
                                        (if (< (+ 1 s) np)
                                            (fn-mpxl-movers (fn-mlh-pe (+ 1 s) 0 fn-mlh) n np)
                                          nil)))
                               (t (fn-mlh-pe i 0 fn-mlh)))))))
  :hints (("Goal" :in-theory (e/d (fn-mlh-split) (fn-mlh-pe fn-mlh-pe-upto fn-mlh-move fn-mlh-ovf-is-seqw
                                                  fn-mlh-empty-from fn-mlh-count-movers))
           :do-not-induct t
           :cases ((< (+ 1 (fn-mlh-s fn-mlh)) (fn-mlh-pages fn-mlh))))))

(defthm fn-mlh-split-shape
  (implies (and (fn-mlhp fn-mlh) (fn-mlh-wfp fn-mlh))
           (let ((after (mv-nth 1 (fn-mlh-split fn-mlh))))
             (and (fn-mlhp after)
                  (fn-mlh-pgsp after)
                  (fn-mlh-wfp after)
                  (equal (fn-mlh-pages after)
                         (if (mv-nth 0 (fn-mlh-split fn-mlh)) (+ 1 (fn-mlh-pages fn-mlh)) (fn-mlh-pages fn-mlh)))
                  (equal (fn-mlh-n after)
                         (if (and (mv-nth 0 (fn-mlh-split fn-mlh)) (equal (+ 1 (fn-mlh-s fn-mlh)) (fn-mlh-n fn-mlh)))
                             (* 2 (fn-mlh-n fn-mlh))
                           (fn-mlh-n fn-mlh)))
                  (equal (fn-mlh-s after)
                         (if (mv-nth 0 (fn-mlh-split fn-mlh))
                             (if (equal (+ 1 (fn-mlh-s fn-mlh)) (fn-mlh-n fn-mlh)) 0 (+ 1 (fn-mlh-s fn-mlh)))
                           (fn-mlh-s fn-mlh)))
                  (equal (fn-mlh-count after) (fn-mlh-count fn-mlh))
                  (equal (fn-mlh-stuck after) (fn-mlh-stuck fn-mlh))
                  (equal (fn-mlh-key-octets after) (fn-mlh-key-octets fn-mlh)))))
  :hints (("Goal" :in-theory (e/d (fn-mlh-split) (fn-mlh-move fn-mlh-count-movers fn-mlh-count-movers-is-len))
           :do-not-induct t)))

(defthm fn-mlh-split-refused-unchanged
  (implies (not (mv-nth 0 (fn-mlh-split fn-mlh)))
           (equal (mv-nth 1 (fn-mlh-split fn-mlh)) fn-mlh))
  :hints (("Goal" :in-theory (e/d (fn-mlh-split) (fn-mlh-move fn-mlh-count-movers fn-mlh-count-movers-is-len)))))

; --- the split IS the logical split of the abstraction ---

; Two lists of the same length that agree at their first difference are
; equal (the first difference of equal lists is past both).
(local (defun fn-mlh-first-diff (a b)
  (if (and (consp a) (consp b) (equal (car a) (car b)))
      (+ 1 (fn-mlh-first-diff (cdr a) (cdr b)))
    0)))

(local (defthm fn-mlh-equal-by-first-diff
  (implies (and (true-listp a) (true-listp b) (equal (len a) (len b))
                (equal (nth (fn-mlh-first-diff a b) a) (nth (fn-mlh-first-diff a b) b)))
           (equal a b))
  :rule-classes nil
  :hints (("Goal" :induct (fn-mlh-first-diff a b) :in-theory (enable nth)))))

(local (defthm fn-mlh-first-diff-natp
  (natp (fn-mlh-first-diff a b))
  :rule-classes :type-prescription))

(local (defthm fn-mlh-abs-pages-true-listp
  (true-listp (fn-mlh-abs-pages p fn-mlh))))

(local (defthm fn-mlh-split-pages-true-listp
  (implies (fn-mpxl-pagesp pgs)
           (true-listp (fn-mpxl-split-pages pgs n s)))
  :hints (("Goal" :use fn-mpxl-split-pages-pagesp :in-theory (disable fn-mpxl-split-pages-pagesp)))))

(local (defthm fn-mlh-nth-is-page
  (implies (and (natp i) (< i (len pgs)))
           (equal (nth i pgs) (fn-mpxl-page i pgs)))
  :hints (("Goal" :in-theory (enable fn-mpxl-page)))))

(local (defthm fn-mlh-nth-beyond-len
  (implies (and (true-listp l) (natp i) (<= (len l) i))
           (equal (nth i l) nil))
  :hints (("Goal" :in-theory (enable nth)))))

(defthm fn-mlh-split-pages-is-split
  (implies (and (fn-mlhp fn-mlh) (fn-mlh-wfp fn-mlh) (posp (fn-mlh-pages fn-mlh))
                (mv-nth 0 (fn-mlh-split fn-mlh)))
           (equal (fn-mlh-abs-pages 0 (mv-nth 1 (fn-mlh-split fn-mlh)))
                  (fn-mpxl-split-pages (fn-mlh-abs-pages 0 fn-mlh) (fn-mlh-n fn-mlh) (fn-mlh-s fn-mlh))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-mlh-equal-by-first-diff
                            (a (fn-mlh-abs-pages 0 (mv-nth 1 (fn-mlh-split fn-mlh))))
                            (b (fn-mpxl-split-pages (fn-mlh-abs-pages 0 fn-mlh) (fn-mlh-n fn-mlh) (fn-mlh-s fn-mlh))))
                 (:instance fn-mlh-split-page
                            (i (fn-mlh-first-diff (fn-mlh-abs-pages 0 (mv-nth 1 (fn-mlh-split fn-mlh)))
                                                  (fn-mpxl-split-pages (fn-mlh-abs-pages 0 fn-mlh) (fn-mlh-n fn-mlh) (fn-mlh-s fn-mlh))))))
           :in-theory (disable fn-mlh-split-page fn-mlh-split fn-mlh-abs-pages fn-mpxl-split-pages fn-mlh-pe
                               fn-mlh-ovf-is-seqw))))

(local (in-theory (disable fn-mlh-nth-is-page)))

; The split is taken exactly when the logical split is.
(defthm fn-mlh-split-taken-iff
  (implies (and (fn-mlhp fn-mlh) (fn-mlh-wfp fn-mlh) (posp (fn-mlh-pages fn-mlh)))
           (iff (mv-nth 0 (fn-mlh-split fn-mlh))
                (mv-nth 0 (fn-mpxl-split (fn-mlh-abs fn-mlh)))))
  :hints (("Goal" :in-theory (e/d (fn-mlh-split fn-mpxl-split fn-mpxl-split-movers fn-mlh-abs)
                                  (fn-mlh-move fn-mlh-pe fn-mlh-abs-pages fn-mlh-grow))
           :do-not-induct t)))

; THE SPLIT REFINES THE LOGICAL SPLIT: the abstraction of the table after
; the split is the logical split of its abstraction, taken or refused.
(defthm fn-mlh-abs-of-split
  (implies (and (fn-mlhp fn-mlh) (fn-mlh-wfp fn-mlh) (posp (fn-mlh-pages fn-mlh)))
           (equal (fn-mlh-abs (mv-nth 1 (fn-mlh-split fn-mlh)))
                  (mv-nth 1 (fn-mpxl-split (fn-mlh-abs fn-mlh)))))
  :hints (("Goal" :cases ((mv-nth 0 (fn-mlh-split fn-mlh)))
           :in-theory (disable fn-mlh-split fn-mlh-abs-pages fn-mpxl-split-pages fn-mlh-split-taken-iff)
           :use fn-mlh-split-taken-iff)
          ("Subgoal 2" :in-theory (e/d (fn-mpxl-split-refused-unchanged)
                                       (fn-mlh-split fn-mlh-abs-pages fn-mpxl-split-pages fn-mlh-abs)))
          ("Subgoal 1" :in-theory (e/d (fn-mlh-abs fn-mpxl-split)
                                       (fn-mlh-split fn-mlh-abs-pages fn-mpxl-split-pages
                                        fn-mlh-split-taken-iff fn-mpxl-split-movers)))))

(defthm fn-mlh-split-no-pages
  (implies (zp (fn-mlh-pages fn-mlh))
           (not (mv-nth 0 (fn-mlh-split fn-mlh))))
  :hints (("Goal" :in-theory (enable fn-mlh-split))))

(in-theory (disable fn-mlh-split))

; Every candidate of every tag survives the split.
(defthm fn-mlh-split-keeps-candidate
  (implies (and (fn-mlhp fn-mlh) (fn-mlh-wfp fn-mlh) (posp tag)
                (member-equal q (fn-mlh-candidates tag fn-mlh)))
           (member-equal q (fn-mlh-candidates tag (mv-nth 1 (fn-mlh-split fn-mlh)))))
  :hints (("Goal" :cases ((posp (fn-mlh-pages fn-mlh)))
           :in-theory (disable fn-mpxl-split-keeps-candidate-always fn-mpxl-cands)
           :use ((:instance fn-mpxl-split-keeps-candidate-always (tab (fn-mlh-abs fn-mlh)))))))

(defthm fn-mlh-split-okp
  (implies (and (fn-mlhp fn-mlh) (fn-mlh-wfp fn-mlh) (fn-mlh-okp n fn-mlh))
           (fn-mlh-okp n (mv-nth 1 (fn-mlh-split fn-mlh))))
  :hints (("Goal" :cases ((posp (fn-mlh-pages fn-mlh)))
           :in-theory (e/d (fn-mlh-okp) (fn-mpxl-okp fn-mpxl-split-okp))
           :use ((:instance fn-mpxl-split-okp (tab (fn-mlh-abs fn-mlh)))))
          ("Subgoal 1" :cases ((mv-nth 0 (fn-mlh-split fn-mlh))))))

(defthm fn-mlh-faithful-from-of-split
  (implies (and (fn-mlhp fn-mlh) (fn-mlh-wfp fn-mlh)
                (fn-mlh-faithful-from i rows fn-mlh))
           (fn-mlh-faithful-from i rows (mv-nth 1 (fn-mlh-split fn-mlh))))
  :hints (("Goal" :induct (fn-mlh-faithful-from i rows fn-mlh)
           :in-theory (disable fn-mlh-candidates fn-mlh-candidates-is-cands fn-mpxl-cands
                               fn-mlh-abs-of-split))))

; KEYSTONE (the split): the table stays faithful to the rows, taken or
; refused -- by the refinement `fn-mlh-abs-of-split' and the logical
; book's `fn-mpxl-split-keeps-candidate-always' / `fn-mpxl-split-okp'.
(defthm fn-mlh-split-preserves-faithful
  (implies (and (fn-mlhp fn-mlh) (fn-mlh-wfp fn-mlh)
                (fn-mlh-faithful rows fn-mlh))
           (fn-mlh-faithful rows (mv-nth 1 (fn-mlh-split fn-mlh))))
  :hints (("Goal" :in-theory (disable fn-mlh-faithful-from fn-mlh-okp))))

; -----------------------------------------------------------------------------
; 8. THE ADD AND THE FOLD.  The add places the entry (the put), counts it,
; and -- when the count reaches half the round's slots (2 COUNT >= 1024 N)
; and no split was ever refused -- splits ONE page.  One add touches at
; most five data pages (home, its next, S, S + 1 and the new page: Codex
; r42 F1) and allocates one page plus at most 63 pointers of its table
; page; past the directory's reserved width, one add in 64 x 2^k pages
; doubles the directory (amortized; `fn-mlh-reserve' at open removes it
; within the profile).  The next-generation rebuild of books/msgid-pages-
; exec is gone.
; The splits of a round come one per add, N of them in N consecutive adds,
; so the load stays within [1/4, 1/2] (books/msgid-linear explains why the
; trigger is the round's half, not the table's).  A refused split sets
; STUCK: no further split is tried, and the table fills toward the named
; refusal `fn-mlh-saturatedp'.

; --- the table's scalars do not move its reader ---

(defthm fn-mlh-seq-at-of-scalar-updates
  (and (equal (fn-mlh-seq-at p j (update-fn-mlh-pages m fn-mlh)) (fn-mlh-seq-at p j fn-mlh))
       (equal (fn-mlh-seq-at p j (update-fn-mlh-n m fn-mlh)) (fn-mlh-seq-at p j fn-mlh))
       (equal (fn-mlh-seq-at p j (update-fn-mlh-s m fn-mlh)) (fn-mlh-seq-at p j fn-mlh))
       (equal (fn-mlh-seq-at p j (update-fn-mlh-count m fn-mlh)) (fn-mlh-seq-at p j fn-mlh))
       (equal (fn-mlh-seq-at p j (update-fn-mlh-stuck m fn-mlh)) (fn-mlh-seq-at p j fn-mlh))
       (equal (fn-mlh-seq-at p j (update-fn-mlh-keyi i v fn-mlh)) (fn-mlh-seq-at p j fn-mlh)))
  :hints (("Goal" :in-theory (enable fn-mlh-seq-at-is-seqw))))

(defthm fn-mlh-scan-of-count-stuck
  (and (equal (fn-mlh-scan tag p j acc (update-fn-mlh-count m fn-mlh)) (fn-mlh-scan tag p j acc fn-mlh))
       (equal (fn-mlh-scan tag p j acc (update-fn-mlh-stuck m fn-mlh)) (fn-mlh-scan tag p j acc fn-mlh))))

(defthm fn-mlh-candidates-of-count-stuck
  (and (equal (fn-mlh-candidates tag (update-fn-mlh-count m fn-mlh)) (fn-mlh-candidates tag fn-mlh))
       (equal (fn-mlh-candidates tag (update-fn-mlh-stuck m fn-mlh)) (fn-mlh-candidates tag fn-mlh)))
  :hints (("Goal" :in-theory (e/d (fn-mlh-candidates fn-mlh-ovf-is-seqw) (fn-mlh-scan)))))

(defthm fn-mlh-abs-pages-of-count-stuck
  (and (equal (fn-mlh-abs-pages p (update-fn-mlh-count m fn-mlh)) (fn-mlh-abs-pages p fn-mlh))
       (equal (fn-mlh-abs-pages p (update-fn-mlh-stuck m fn-mlh)) (fn-mlh-abs-pages p fn-mlh)))
  :hints (("Goal" :induct (fn-mlh-abs-pages p fn-mlh) :in-theory (disable fn-mlh-pe))))

(defthm fn-mlh-faithful-of-count-stuck
  (and (equal (fn-mlh-faithful-from i rows (update-fn-mlh-count m fn-mlh)) (fn-mlh-faithful-from i rows fn-mlh))
       (equal (fn-mlh-faithful-from i rows (update-fn-mlh-stuck m fn-mlh)) (fn-mlh-faithful-from i rows fn-mlh))
       (equal (fn-mlh-okp n (update-fn-mlh-count m fn-mlh)) (fn-mlh-okp n fn-mlh))
       (equal (fn-mlh-okp n (update-fn-mlh-stuck m fn-mlh)) (fn-mlh-okp n fn-mlh)))
  :hints (("Goal" :in-theory (e/d (fn-mlh-okp fn-mlh-abs) (fn-mlh-candidates fn-mlh-abs-pages)))
          ("Subgoal *1/2" :in-theory (disable fn-mlh-candidates))))

; --- the put keeps the table faithful ---

(defthm fn-mlh-ents-below-pe-of-write-slot
  (implies (and (fn-mpxl-ents-below (fn-mlh-pe r i fn-mlh) n) (natp n) (natp seq) (< seq n)
                (fn-mlhp fn-mlh) (< (+ 1 seq) *fn-mlh-tag-limit*)
                (natp p) (natp j) (< j *fn-mlh-page-slots*) (natp r))
           (fn-mpxl-ents-below (fn-mlh-pe r i (fn-mlh-write-slot p j tag seq fn-mlh)) n))
  :hints (("Goal" :induct (fn-mlh-pe r i fn-mlh)
           :in-theory (enable fn-mlh-seq-at-is-seqw))))

(defthm fn-mlh-pages-okp-of-write-slot
  (implies (and (fn-mpxl-pages-okp (fn-mlh-abs-pages k fn-mlh) n) (natp n) (natp seq) (< seq n)
                (fn-mlhp fn-mlh) (< (+ 1 seq) *fn-mlh-tag-limit*)
                (natp p) (natp j) (< j *fn-mlh-page-slots*))
           (fn-mpxl-pages-okp (fn-mlh-abs-pages k (fn-mlh-write-slot p j tag seq fn-mlh)) n))
  :hints (("Goal" :induct (fn-mlh-abs-pages k fn-mlh) :in-theory (disable fn-mlh-pe))))

(defthm fn-mlh-abs-pages-of-set-ovf-ents
  (implies (and (fn-mlhp fn-mlh) (natp p))
           (equal (fn-mpxl-pages-okp (fn-mlh-abs-pages k (fn-mlh-set-ovf p fn-mlh)) n)
                  (fn-mpxl-pages-okp (fn-mlh-abs-pages k fn-mlh) n)))
  :hints (("Goal" :induct (fn-mlh-abs-pages k fn-mlh) :in-theory (disable fn-mlh-pe))))

(defthm fn-mlh-pages-okp-mono
  (implies (and (fn-mpxl-pages-okp pgs n) (natp n) (natp n2) (<= n n2))
           (fn-mpxl-pages-okp pgs n2)))

(defthm fn-mlh-put-okp
  (implies (and (fn-mlhp fn-mlh) (fn-mlh-wfp fn-mlh) (fn-mlh-okp n fn-mlh)
                (natp tag) (< tag *fn-mlh-tag-limit*)
                (natp n) (natp seq) (< seq (+ 1 n)) (< (+ 1 seq) *fn-mlh-tag-limit*))
           (fn-mlh-okp (+ 1 n) (mv-nth 1 (fn-mlh-put tag seq fn-mlh))))
  :hints (("Goal" :in-theory (e/d (fn-mlh-okp fn-mlh-abs fn-mlh-put) (fn-mlh-abs-pages fn-mlh-pe fn-mpxl-addr-below))
           :use ((:instance fn-mpxl-addr-below (n (fn-mlh-n fn-mlh)) (s (fn-mlh-s fn-mlh)))))))

(local (defthm fn-mlh-nth-of-append-one
  (implies (natp i)
           (equal (nth i (append rows (list h)))
                  (if (< i (len rows)) (nth i rows) (if (equal i (len rows)) h nil))))
  :hints (("Goal" :in-theory (enable nth) :induct (nth i rows)))))

(defthm fn-mlh-faithful-from-beyond
  (implies (<= (len rows) (nfix i))
           (fn-mlh-faithful-from i rows fn-mlh)))

(defthm fn-mlh-faithful-from-append-last
  (implies (and (true-listp rows)
                (member-equal (len rows)
                              (fn-mlh-candidates (fn-mlh-tag (fn-record-msgid h) (fn-mlh-key-octets fn-mlh)) fn-mlh)))
           (fn-mlh-faithful-from (len rows) (append rows (list h)) fn-mlh))
  :hints (("Goal" :expand ((fn-mlh-faithful-from (len rows) (append rows (list h)) fn-mlh))
           :in-theory (disable fn-mlh-candidates fn-mlh-candidates-is-cands))))

(defthm fn-mlh-faithful-from-of-put-append
  (implies (and (fn-mlhp fn-mlh) (fn-mlh-wfp fn-mlh) (posp (fn-mlh-pages fn-mlh))
                (true-listp rows) (natp i)
                (fn-mlh-faithful-from i rows fn-mlh)
                (equal tag (fn-mlh-tag (fn-record-msgid h) (fn-mlh-key-octets fn-mlh)))
                (< (+ 1 (len rows)) *fn-mlh-tag-limit*)
                (mv-nth 0 (fn-mlh-put tag (len rows) fn-mlh)))
           (fn-mlh-faithful-from i (append rows (list h)) (mv-nth 1 (fn-mlh-put tag (len rows) fn-mlh))))
  :hints (("Goal" :induct (fn-mlh-faithful-from i rows fn-mlh)
           :in-theory (disable fn-mlh-candidates fn-mlh-candidates-is-cands fn-mlh-put-finds
                               fn-mlh-faithful-from-append-last))
          ("Subgoal *1/1" :cases ((equal i (len rows)))
           :use ((:instance fn-mlh-put-finds (seq (len rows)))
                 (:instance fn-mlh-faithful-from-append-last
                            (fn-mlh (mv-nth 1 (fn-mlh-put tag (len rows) fn-mlh))))))))

; The put of a row's entry at its sequence keeps the table faithful to the
; rows with that row appended.
(defthm fn-mlh-put-preserves-faithful
  (implies (and (fn-mlhp fn-mlh) (fn-mlh-wfp fn-mlh) (posp (fn-mlh-pages fn-mlh))
                (true-listp rows)
                (fn-mlh-faithful rows fn-mlh)
                (equal tag (fn-mlh-tag (fn-record-msgid h) (fn-mlh-key-octets fn-mlh)))
                (< (+ 1 (len rows)) *fn-mlh-tag-limit*)
                (mv-nth 0 (fn-mlh-put tag (len rows) fn-mlh)))
           (fn-mlh-faithful (append rows (list h)) (mv-nth 1 (fn-mlh-put tag (len rows) fn-mlh))))
  :hints (("Goal" :in-theory (disable fn-mlh-faithful-from fn-mlh-okp fn-mlh-candidates))))

; --- the first page ---

(defun fn-mlh-first-page (fn-mlh)
  (declare (xargs :stobjs fn-mlh :guard (fn-mlh-pgsp fn-mlh)))
  (let* ((fn-mlh (fn-mlh-grow fn-mlh))
         (fn-mlh (update-fn-mlh-n 1 fn-mlh)))
    (update-fn-mlh-s 0 fn-mlh)))

(defthm fn-mlh-first-page-shape
  (implies (and (fn-mlhp fn-mlh) (fn-mlh-pgsp fn-mlh) (zp (fn-mlh-pages fn-mlh)))
           (and (fn-mlhp (fn-mlh-first-page fn-mlh))
                (fn-mlh-wfp (fn-mlh-first-page fn-mlh))
                (equal (fn-mlh-pages (fn-mlh-first-page fn-mlh)) 1)
                (equal (fn-mlh-n (fn-mlh-first-page fn-mlh)) 1)
                (equal (fn-mlh-s (fn-mlh-first-page fn-mlh)) 0)
                (equal (fn-mlh-count (fn-mlh-first-page fn-mlh)) (fn-mlh-count fn-mlh))
                (equal (fn-mlh-stuck (fn-mlh-first-page fn-mlh)) (fn-mlh-stuck fn-mlh))
                (equal (fn-mlh-key-octets (fn-mlh-first-page fn-mlh)) (fn-mlh-key-octets fn-mlh)))))

; The first page is empty: no candidates, every row faithful only to none.
(defthm fn-mlh-first-page-empty
  (implies (and (fn-mlhp fn-mlh) (fn-mlh-pgsp fn-mlh) (zp (fn-mlh-pages fn-mlh)))
           (fn-mlh-empty-from 0 c (fn-mlh-first-page fn-mlh)))
  :hints (("Goal" :induct (fn-mlh-empty-from 0 c (fn-mlh-first-page fn-mlh)))))

(defthm fn-mlh-first-page-pe
  (implies (and (fn-mlhp fn-mlh) (fn-mlh-pgsp fn-mlh) (zp (fn-mlh-pages fn-mlh)))
           (equal (fn-mlh-pe 0 0 (fn-mlh-first-page fn-mlh)) nil)))

(defthm fn-mlh-first-page-okp
  (implies (and (fn-mlhp fn-mlh) (fn-mlh-pgsp fn-mlh) (zp (fn-mlh-pages fn-mlh)))
           (fn-mlh-okp n (fn-mlh-first-page fn-mlh)))
  :hints (("Goal" :in-theory (e/d (fn-mlh-okp fn-mlh-abs) (fn-mlh-first-page fn-mlh-pe))
           :expand ((fn-mlh-abs-pages 0 (fn-mlh-first-page fn-mlh))
                    (fn-mlh-abs-pages 1 (fn-mlh-first-page fn-mlh))))))

(defthm fn-mlh-addr-one-page
  (implies (integerp tag)
           (equal (fn-mpxl-addr tag 1 0) 0))
  :hints (("Goal" :in-theory (enable fn-mpxl-addr mod))))

(defthm fn-mlh-first-page-not-saturated
  (implies (and (fn-mlhp fn-mlh) (fn-mlh-pgsp fn-mlh) (zp (fn-mlh-pages fn-mlh)) (integerp tag))
           (not (fn-mlh-saturatedp tag (fn-mlh-first-page fn-mlh))))
  :hints (("Goal" :in-theory (e/d (fn-mlh-saturatedp) (fn-mlh-first-page))
           :expand ((fn-mlh-find-empty 0 0 (fn-mlh-first-page fn-mlh)))
           :use ((:instance fn-mlh-empty-from-tag-at (p 0) (c 0) (i 0) (fn-mlh (fn-mlh-first-page fn-mlh)))))))

(in-theory (disable fn-mlh-first-page))

; With no pages the table is faithful to no rows but the empty history, and
; never saturated.
(defthm fn-mlh-faithful-no-pages
  (implies (and (zp (fn-mlh-pages fn-mlh)) (fn-mlh-faithful rows fn-mlh))
           (equal (len rows) 0))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-mlh-faithful)
           :expand ((fn-mlh-faithful-from 0 rows fn-mlh)))))

(defthm fn-mlh-saturatedp-no-pages
  (implies (zp (fn-mlh-pages fn-mlh))
           (not (fn-mlh-saturatedp tag fn-mlh)))
  :hints (("Goal" :in-theory (enable fn-mlh-saturatedp))))

(defthm fn-mlh-wfp-of-count-stuck
  (and (equal (fn-mlh-wfp (update-fn-mlh-count m fn-mlh)) (fn-mlh-wfp fn-mlh))
       (equal (fn-mlh-wfp (update-fn-mlh-stuck m fn-mlh)) (fn-mlh-wfp fn-mlh))))

; --- THE ADD ---

(defthm fn-mlh-first-page-faithful
  (implies (and (fn-mlhp fn-mlh) (fn-mlh-pgsp fn-mlh) (zp (fn-mlh-pages fn-mlh))
                (equal (len rows) 0))
           (fn-mlh-faithful rows (fn-mlh-first-page fn-mlh)))
  :hints (("Goal" :in-theory (e/d (fn-mlh-faithful) (fn-mlh-okp)))))

(defthm fn-mlh-put-car-iff-not-saturated
  (implies (posp (fn-mlh-pages fn-mlh))
           (iff (car (fn-mlh-put tag seq fn-mlh))
                (not (fn-mlh-saturatedp tag fn-mlh))))
  :hints (("Goal" :use fn-mlh-put-places-iff-not-saturated
           :in-theory (disable fn-mlh-put-places-iff-not-saturated))))

;; THE SETTLE: one more entry counted, then -- at the round's half, never
;; after a refused split -- one split; a refused split sets STUCK.
(defun fn-mlh-settle (fn-mlh)
  (declare (xargs :stobjs fn-mlh :guard (fn-mlh-wfp fn-mlh)))
  (let ((fn-mlh (update-fn-mlh-count (+ 1 (fn-mlh-count fn-mlh)) fn-mlh)))
    (if (and (eql (fn-mlh-stuck fn-mlh) 0)
             (<= (* *fn-mlh-page-slots* (fn-mlh-n fn-mlh)) (* 2 (fn-mlh-count fn-mlh))))
        (mv-let (ok fn-mlh)
          (fn-mlh-split fn-mlh)
          (if ok fn-mlh (update-fn-mlh-stuck 1 fn-mlh)))
      fn-mlh)))

(defthm fn-mlh-settle-shape
  (implies (and (fn-mlhp fn-mlh) (fn-mlh-wfp fn-mlh))
           (and (fn-mlhp (fn-mlh-settle fn-mlh))
                (fn-mlh-wfp (fn-mlh-settle fn-mlh))
                (fn-mlh-pgsp (fn-mlh-settle fn-mlh))
                (equal (fn-mlh-key-octets (fn-mlh-settle fn-mlh)) (fn-mlh-key-octets fn-mlh))))
  :hints (("Goal" :in-theory (disable fn-mlh-wfp))))

(defthm fn-mlh-settle-preserves-faithful
  (implies (and (fn-mlhp fn-mlh) (fn-mlh-wfp fn-mlh) (fn-mlh-faithful rows fn-mlh))
           (fn-mlh-faithful rows (fn-mlh-settle fn-mlh)))
  :hints (("Goal" :in-theory (disable fn-mlh-wfp fn-mlh-faithful-from fn-mlh-okp))))

(in-theory (disable fn-mlh-settle))

; THE ADD; (mv :placed fn-mlh) or (mv :mpx-saturated fn-mlh), the table
; unchanged on a refusal.  One put, then the settle: at most one split.
(defun fn-mlh-add (tag seq fn-mlh)
  (declare (xargs :stobjs fn-mlh
                  :guard (and (posp tag) (< tag *fn-mlh-tag-limit*)
                              (natp seq) (< (+ 1 seq) *fn-mlh-tag-limit*)
                              (fn-mlh-wfp fn-mlh))))
  (let ((fn-mlh (if (zp (fn-mlh-pages fn-mlh)) (fn-mlh-first-page fn-mlh) fn-mlh)))
    (mv-let (placed fn-mlh)
      (fn-mlh-put tag seq fn-mlh)
      (if (not placed)
          (mv :mpx-saturated fn-mlh)
        (let ((fn-mlh (fn-mlh-settle fn-mlh)))
          (mv :placed fn-mlh))))))

(defthm fn-mlh-add-shape
  (implies (and (fn-mlhp fn-mlh) (fn-mlh-wfp fn-mlh)
                (natp tag) (< tag *fn-mlh-tag-limit*)
                (natp seq) (< (+ 1 seq) *fn-mlh-tag-limit*))
           (and (fn-mlhp (mv-nth 1 (fn-mlh-add tag seq fn-mlh)))
                (fn-mlh-wfp (mv-nth 1 (fn-mlh-add tag seq fn-mlh)))
                (fn-mlh-pgsp (mv-nth 1 (fn-mlh-add tag seq fn-mlh)))
                (equal (fn-mlh-key-octets (mv-nth 1 (fn-mlh-add tag seq fn-mlh))) (fn-mlh-key-octets fn-mlh))))
  :hints (("Goal" :in-theory (disable fn-mlh-put fn-mlh-wfp))))

; The add's outcome is the named refusal of the table as it is.
(defthm fn-mlh-add-places-iff-not-saturated
  (implies (and (fn-mlhp fn-mlh) (fn-mlh-pgsp fn-mlh) (natp tag))
           (iff (equal (mv-nth 0 (fn-mlh-add tag seq fn-mlh)) :placed)
                (not (fn-mlh-saturatedp tag fn-mlh))))
  :hints (("Goal" :in-theory (disable fn-mlh-put fn-mlh-split fn-mlh-put-places-iff-not-saturated)
           :cases ((zp (fn-mlh-pages fn-mlh)))
           :use (fn-mlh-put-places-iff-not-saturated
                 (:instance fn-mlh-put-places-iff-not-saturated (fn-mlh (fn-mlh-first-page fn-mlh)))))))

(defthm fn-mlh-add-saturated-keeps-the-table
  (implies (and (fn-mlhp fn-mlh) (fn-mlh-pgsp fn-mlh) (natp tag) (fn-mlh-saturatedp tag fn-mlh))
           (equal (mv-nth 1 (fn-mlh-add tag seq fn-mlh)) fn-mlh))
  :hints (("Goal" :in-theory (disable fn-mlh-put fn-mlh-split fn-mlh-put-places-iff-not-saturated)
           :cases ((zp (fn-mlh-pages fn-mlh)))
           :use (fn-mlh-put-places-iff-not-saturated))))

; KEYSTONE (the add): a placed row is a candidate of its tag and every
; other row stays one -- the table stays faithful to the rows with the row
; appended, through the put, the count and the split.
(defthm fn-mlh-add-preserves-faithful
  (implies (and (fn-mlhp fn-mlh) (fn-mlh-wfp fn-mlh)
                (true-listp rows)
                (fn-mlh-faithful rows fn-mlh)
                (equal tag (fn-mlh-tag (fn-record-msgid h) (fn-mlh-key-octets fn-mlh)))
                (< (+ 1 (len rows)) *fn-mlh-tag-limit*)
                (equal (mv-nth 0 (fn-mlh-add tag (len rows) fn-mlh)) :placed))
           (fn-mlh-faithful (append rows (list h)) (mv-nth 1 (fn-mlh-add tag (len rows) fn-mlh))))
  :hints (("Goal" :in-theory (disable fn-mlh-put fn-mlh-faithful fn-mlh-wfp fn-mlh-put-preserves-faithful
                                      fn-mlh-settle-preserves-faithful)
           :do-not-induct t
           :cases ((zp (fn-mlh-pages fn-mlh)))
           :use ((:instance fn-mlh-faithful-no-pages)
                 (:instance fn-mlh-put-preserves-faithful)
                 (:instance fn-mlh-put-preserves-faithful (fn-mlh (fn-mlh-first-page fn-mlh)))
                 (:instance fn-mlh-settle-preserves-faithful
                            (rows (append rows (list h)))
                            (fn-mlh (mv-nth 1 (fn-mlh-put tag (len rows) fn-mlh))))
                 (:instance fn-mlh-settle-preserves-faithful
                            (rows (append rows (list h)))
                            (fn-mlh (mv-nth 1 (fn-mlh-put tag (len rows) (fn-mlh-first-page fn-mlh)))))))))

; --- the clear and the key ---

; Empty the table: no pages (the page array released), the root, count and
; stuck reset, the key kept.
(defun fn-mlh-clear (fn-mlh)
  (declare (xargs :stobjs fn-mlh))
  (let* ((fn-mlh (update-fn-mlh-pages 0 fn-mlh))
         (fn-mlh (update-fn-mlh-n 0 fn-mlh))
         (fn-mlh (update-fn-mlh-s 0 fn-mlh))
         (fn-mlh (update-fn-mlh-count 0 fn-mlh))
         (fn-mlh (update-fn-mlh-stuck 0 fn-mlh))
         (fn-mlh (resize-fn-mlh-dir 0 fn-mlh)))
    fn-mlh))

(defthm fn-mlh-clear-shape
  (implies (fn-mlhp fn-mlh)
           (and (fn-mlhp (fn-mlh-clear fn-mlh))
                (fn-mlh-wfp (fn-mlh-clear fn-mlh))
                (fn-mlh-pgsp (fn-mlh-clear fn-mlh))
                (equal (fn-mlh-pages (fn-mlh-clear fn-mlh)) 0)
                (equal (fn-mlh-count (fn-mlh-clear fn-mlh)) 0)
                (equal (fn-mlh-stuck (fn-mlh-clear fn-mlh)) 0)
                (equal (fn-mlh-key-octets (fn-mlh-clear fn-mlh)) (fn-mlh-key-octets fn-mlh))))
  :hints (("Goal" :in-theory (enable fn-mlh-pgsp))))

(defthm fn-mlh-clear-root
  (and (equal (fn-mlh-n (fn-mlh-clear fn-mlh)) 0)
       (equal (fn-mlh-s (fn-mlh-clear fn-mlh)) 0)))

; Write KEY's octets (clamped, missing ones 0) from index I.
(defun fn-mlh-set-key-from (i key fn-mlh)
  (declare (xargs :stobjs fn-mlh :guard (natp i)
                  :measure (nfix (- *fn-mpxt-key-octets* (nfix i)))))
  (if (>= (nfix i) *fn-mpxt-key-octets*)
      fn-mlh
    (let ((fn-mlh (update-fn-mlh-keyi (nfix i) (fn-ns-octet (if (consp key) (car key) 0)) fn-mlh)))
      (fn-mlh-set-key-from (1+ (nfix i)) (if (consp key) (cdr key) nil) fn-mlh))))

(defthm fn-mlh-set-key-from-shape
  (implies (fn-mlhp fn-mlh)
           (fn-mlhp (fn-mlh-set-key-from i key fn-mlh)))
  :hints (("Goal" :induct (fn-mlh-set-key-from i key fn-mlh)
           :in-theory (enable unsigned-byte-p))))

(defthm fn-mlh-set-key-from-frame
  (and (equal (fn-mlh-pages (fn-mlh-set-key-from i key fn-mlh)) (fn-mlh-pages fn-mlh))
       (equal (fn-mlh-n (fn-mlh-set-key-from i key fn-mlh)) (fn-mlh-n fn-mlh))
       (equal (fn-mlh-s (fn-mlh-set-key-from i key fn-mlh)) (fn-mlh-s fn-mlh))
       (equal (fn-mlh-count (fn-mlh-set-key-from i key fn-mlh)) (fn-mlh-count fn-mlh))
       (equal (fn-mlh-stuck (fn-mlh-set-key-from i key fn-mlh)) (fn-mlh-stuck fn-mlh))
       (equal (fn-mlh-pgsp (fn-mlh-set-key-from i key fn-mlh)) (fn-mlh-pgsp fn-mlh)))
  :hints (("Goal" :induct (fn-mlh-set-key-from i key fn-mlh))))

; INSTALL the key into an emptied table (the open's step): the tags of the
; entries a table holds are its key's, so a key change empties it.
(defun fn-mlh-set-key (key fn-mlh)
  (declare (xargs :stobjs fn-mlh))
  (let ((fn-mlh (fn-mlh-clear fn-mlh)))
    (fn-mlh-set-key-from 0 key fn-mlh)))

(defthm fn-mlh-set-key-shape
  (implies (fn-mlhp fn-mlh)
           (and (fn-mlhp (fn-mlh-set-key key fn-mlh))
                (fn-mlh-wfp (fn-mlh-set-key key fn-mlh))
                (fn-mlh-pgsp (fn-mlh-set-key key fn-mlh))
                (equal (fn-mlh-pages (fn-mlh-set-key key fn-mlh)) 0)
                (equal (fn-mlh-count (fn-mlh-set-key key fn-mlh)) 0)
                (equal (fn-mlh-stuck (fn-mlh-set-key key fn-mlh)) 0)))
  :hints (("Goal" :in-theory (disable fn-mlh-clear))))

(defthm fn-mlh-candidates-no-pages-faithful-nil
  (implies (zp (fn-mlh-pages fn-mlh))
           (fn-mlh-faithful nil fn-mlh))
  :hints (("Goal" :in-theory (enable fn-mlh-faithful fn-mlh-okp))))

(in-theory (disable fn-mlh-clear fn-mlh-set-key))

; --- THE FOLD ---

; THE FOLD: the table the catalog holds is the fold of the add over its rows
; from the set-keyed empty table (books/catalog-logic's correspondence),
; the unplaced count its first value; a fold whose every step placed is
; faithful.  A row whose sequence would not leave room in the word is
; counted unplaced (books/msgid-pages-exec's bound on the sequence).  This
; logical fold reads row I by (nth i rows) under a (len rows) test, so
; EXECUTING it costs O(R^2) over R rows (measured 0.16 / 1.8 / 27.7 s at 8k /
; 32k / 131k rows); the executed rebuilds (fn-mlh-build-saturatedp,
; fn-mlh-build-health) run fn-mlh-build-tail below instead, a cursor down the
; rows, O(1) per row besides the add (fn-mlh-build-tail-is-build-from).
(defun fn-mlh-build-from (i u rows fn-mlh)
  (declare (xargs :stobjs fn-mlh :verify-guards nil
                  :guard (and (natp i) (natp u) (true-listp rows) (fn-mlh-wfp fn-mlh))
                  :measure (nfix (- (len rows) (nfix i)))))
  (if (>= (nfix i) (len rows))
      (mv u fn-mlh)
    (if (>= (+ 2 (nfix i)) *fn-mlh-tag-limit*)
        (fn-mlh-build-from (1+ (nfix i)) (1+ u) rows fn-mlh)
      (mv-let (r fn-mlh)
        (fn-mlh-add (fn-mlh-tag-of (fn-record-msgid (nth (nfix i) rows)) fn-mlh)
                    (nfix i) fn-mlh)
        (fn-mlh-build-from (1+ (nfix i)) (if (equal r :placed) u (1+ u)) rows fn-mlh)))))

(defun-nx fn-mlh-build (key rows)
  (mv-nth 1 (fn-mlh-build-from 0 0 rows (fn-mlh-set-key key (create-fn-mlh)))))

(defun-nx fn-mlh-build-unplaced (key rows)
  (mv-nth 0 (fn-mlh-build-from 0 0 rows (fn-mlh-set-key key (create-fn-mlh)))))

(defthm fn-mlh-build-from-shape
  (implies (and (fn-mlhp fn-mlh) (fn-mlh-wfp fn-mlh))
           (and (fn-mlhp (mv-nth 1 (fn-mlh-build-from i u rows fn-mlh)))
                (fn-mlh-wfp (mv-nth 1 (fn-mlh-build-from i u rows fn-mlh)))
                (equal (fn-mlh-key-octets (mv-nth 1 (fn-mlh-build-from i u rows fn-mlh)))
                       (fn-mlh-key-octets fn-mlh))))
  :hints (("Goal" :induct (fn-mlh-build-from i u rows fn-mlh)
           :in-theory (disable fn-mlh-add fn-mlh-wfp))))

(defthm fn-mlh-build-from-count
  (implies (natp u)
           (and (natp (mv-nth 0 (fn-mlh-build-from i u rows fn-mlh)))
                (<= u (mv-nth 0 (fn-mlh-build-from i u rows fn-mlh)))))
  :rule-classes ((:rewrite) (:linear :corollary (implies (natp u) (<= u (mv-nth 0 (fn-mlh-build-from i u rows fn-mlh))))))
  :hints (("Goal" :induct (fn-mlh-build-from i u rows fn-mlh)
           :in-theory (disable fn-mlh-add))))

(defthm fn-mlh-build-from-count-car
  (implies (natp u)
           (<= u (car (fn-mlh-build-from i u rows fn-mlh))))
  :rule-classes :linear
  :hints (("Goal" :use fn-mlh-build-from-count :in-theory (disable fn-mlh-build-from-count fn-mlh-build-from))))

(defthm fn-mlh-build-from-faithful
  (implies (and (fn-mlhp fn-mlh) (fn-mlh-wfp fn-mlh) (true-listp rows)
                (natp i) (<= i (len rows)) (natp u)
                (fn-mlh-faithful (fn-mpxt-prefix i rows) fn-mlh)
                (equal (mv-nth 0 (fn-mlh-build-from i u rows fn-mlh)) u))
           (fn-mlh-faithful rows (mv-nth 1 (fn-mlh-build-from i u rows fn-mlh))))
  :hints (("Goal" :induct (fn-mlh-build-from i u rows fn-mlh)
           :in-theory (disable fn-mlh-add fn-mlh-faithful fn-mpxt-prefix fn-mlh-add-preserves-faithful fn-mlh-wfp))
          ("Subgoal *1/3" :use ((:instance fn-mlh-add-preserves-faithful
                                           (rows (fn-mpxt-prefix i rows)) (h (nth i rows))
                                           (tag (fn-mlh-tag (fn-record-msgid (nth i rows)) (fn-mlh-key-octets fn-mlh))))))))

(defthm fn-mlh-build-from-past-the-limit
  (implies (and (natp u) (natp i) (< i (len rows))
                (<= *fn-mlh-tag-limit* (+ 1 (len rows))))
           (< u (mv-nth 0 (fn-mlh-build-from i u rows fn-mlh))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-mlh-build-from i u rows fn-mlh)
           :in-theory (disable fn-mlh-add))))

(defthm fn-mlh-create-is-a-table
  (fn-mlhp (create-fn-mlh))
  :hints (("Goal" :in-theory (enable fn-mlhp))))

(in-theory (disable create-fn-mlh (:e create-fn-mlh)))

(defthm fn-mlh-build-shape
  (and (fn-mlhp (fn-mlh-build key rows))
       (fn-mlh-wfp (fn-mlh-build key rows))
       (natp (fn-mlh-build-unplaced key rows))
       (equal (fn-mlh-key-octets (fn-mlh-build key rows))
              (fn-mlh-key-octets (fn-mlh-set-key key (create-fn-mlh)))))
  :hints (("Goal" :in-theory (disable fn-mlh-build-from fn-mlh-build-from-shape fn-mlh-wfp)
           :use ((:instance fn-mlh-build-from-shape (i 0) (u 0)
                            (fn-mlh (fn-mlh-set-key key (create-fn-mlh))))
                 (:instance fn-mlh-build-from-count (i 0) (u 0)
                            (fn-mlh (fn-mlh-set-key key (create-fn-mlh))))))))

(defthm fn-mlh-build-unplaced-zero-bound
  (implies (equal (fn-mlh-build-unplaced key rows) 0)
           (< (+ 1 (len rows)) *fn-mlh-tag-limit*))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-mlh-build-from)
           :use ((:instance fn-mlh-build-from-past-the-limit (i 0) (u 0)
                            (fn-mlh (fn-mlh-set-key key (create-fn-mlh))))))))

; KEYSTONE (the fold): a fold that placed every row is faithful to the rows.
(defthm fn-mlh-build-faithful
  (implies (and (true-listp rows)
                (equal (fn-mlh-build-unplaced key rows) 0))
           (fn-mlh-faithful rows (fn-mlh-build key rows)))
  :hints (("Goal" :in-theory (disable fn-mlh-build-from fn-mlh-faithful fn-mlh-build-from-faithful)
           :use ((:instance fn-mlh-build-from-faithful (i 0) (u 0)
                            (fn-mlh (fn-mlh-set-key key (create-fn-mlh))))))))

; The fold over one more row is one more (bounded) add: the catalog's commit.
(local (defthm fn-mlh-nth-of-append-at-end
  (implies (and (natp i) (equal i (len a)))
           (equal (nth i (append a (list h))) h))))
(local (defthm fn-mlh-len-of-append-one
  (equal (len (append a (list h))) (+ 1 (len a)))))

(local (defthm fn-mlh-build-from-append-base
  (equal (fn-mlh-build-from (len rows) u (append rows (list h)) fn-mlh)
         (if (< (+ 2 (len rows)) *fn-mlh-tag-limit*)
             (mv-let (r fn-mlh)
               (fn-mlh-add (fn-mlh-tag (fn-record-msgid h) (fn-mlh-key-octets fn-mlh))
                           (len rows) fn-mlh)
               (mv (if (equal r :placed) u (1+ u)) fn-mlh))
           (mv (1+ u) fn-mlh)))
  :hints (("Goal" :expand ((fn-mlh-build-from (len rows) u (append rows (list h)) fn-mlh)
                           (:free (u a) (fn-mlh-build-from (+ 1 (len rows)) u (append rows (list h)) a)))
           :in-theory (disable fn-mlh-add)))))

(defthm fn-mlh-build-from-append
  (implies (and (natp i) (<= i (len rows)))
           (equal (fn-mlh-build-from i u (append rows (list h)) fn-mlh)
                  (mv-let (u2 fn-mlh)
                    (fn-mlh-build-from i u rows fn-mlh)
                    (if (< (+ 2 (len rows)) *fn-mlh-tag-limit*)
                        (mv-let (r fn-mlh)
                          (fn-mlh-add (fn-mlh-tag (fn-record-msgid h) (fn-mlh-key-octets fn-mlh))
                                      (len rows) fn-mlh)
                          (mv (if (equal r :placed) u2 (1+ u2)) fn-mlh))
                      (mv (1+ u2) fn-mlh)))))
  :hints (("Goal" :induct (fn-mlh-build-from i u rows fn-mlh)
           :in-theory (disable fn-mlh-add))
          ("Subgoal *1/3" :expand ((fn-mlh-build-from i u (append rows (list h)) fn-mlh)))
          ("Subgoal *1/2" :expand ((fn-mlh-build-from i u (append rows (list h)) fn-mlh)))))

(defthm fn-mlh-build-append
  (and (equal (fn-mlh-build key (append rows (list h)))
              (if (< (+ 2 (len rows)) *fn-mlh-tag-limit*)
                  (mv-nth 1 (fn-mlh-add (fn-mlh-tag (fn-record-msgid h) (fn-mlh-key-octets (fn-mlh-build key rows)))
                                        (len rows) (fn-mlh-build key rows)))
                (fn-mlh-build key rows)))
       (equal (fn-mlh-build-unplaced key (append rows (list h)))
              (if (and (< (+ 2 (len rows)) *fn-mlh-tag-limit*)
                       (equal (mv-nth 0 (fn-mlh-add (fn-mlh-tag (fn-record-msgid h) (fn-mlh-key-octets (fn-mlh-build key rows)))
                                                    (len rows) (fn-mlh-build key rows)))
                              :placed))
                  (fn-mlh-build-unplaced key rows)
                (+ 1 (fn-mlh-build-unplaced key rows)))))
  :hints (("Goal" :in-theory (disable fn-mlh-build-from fn-mlh-add fn-mlh-set-key))))

(defthm fn-mlh-build-nil
  (and (equal (fn-mlh-build key nil) (fn-mlh-set-key key (create-fn-mlh)))
       (equal (fn-mlh-build-unplaced key nil) 0)))

; THE OUTCOME AT THE COMMIT: the fold over one more row places it exactly
; when the table is not saturated for its tag and the sequence space has
; room -- the served refusal asks exactly that of the table as it is.
(defthm fn-mlh-build-append-unplaced-iff
  (iff (equal (fn-mlh-build-unplaced key (append rows (list h)))
              (fn-mlh-build-unplaced key rows))
       (and (< (+ 2 (len rows)) *fn-mlh-tag-limit*)
            (not (fn-mlh-saturatedp (fn-mlh-tag (fn-record-msgid h) (fn-mlh-key-octets (fn-mlh-build key rows)))
                                    (fn-mlh-build key rows)))))
  :hints (("Goal" :in-theory (disable fn-mlh-build-from fn-mlh-add fn-mlh-set-key fn-mlh-saturatedp
                                      fn-mlh-build fn-mlh-build-unplaced fn-mlh-build-shape
                                      fn-mlh-add-places-iff-not-saturated)
           :do-not-induct t
           :use ((:instance fn-mlh-build-shape)
                 (:instance fn-mlh-add-places-iff-not-saturated
                            (tag (fn-mlh-tag (fn-record-msgid h) (fn-mlh-key-octets (fn-mlh-build key rows))))
                            (seq (len rows))
                            (fn-mlh (fn-mlh-build key rows)))))))

(in-theory (disable fn-mlh-build fn-mlh-build-unplaced))

; --- THE CLEARED TABLE IS CANONICAL (books/msgid-pages-exec 7h's shape) ---
; `fn-mlh-set-key' writes every one of the 32 key octets over a cleared
; table, so no trace of the table it was given remains; `fn-mlh-clear' is
; the set-key of the table's own key, the fold's base case.

(defun fn-mlh-keytail (i key)
  (declare (xargs :guard (natp i) :measure (nfix (- *fn-mpxt-key-octets* (nfix i)))))
  (if (>= (nfix i) *fn-mpxt-key-octets*)
      nil
    (cons (fn-ns-octet (if (consp key) (car key) 0))
          (fn-mlh-keytail (1+ (nfix i)) (if (consp key) (cdr key) nil)))))

(local (defthm fn-mlh-keyp-true-listp
  (implies (fn-mlh-keyp l) (true-listp l))))
(local (defthm fn-mlh-recognizer-facts
  (implies (fn-mlhp x)
           (and (true-listp x) (equal (len x) 7)
                (fn-mlh-keyp (nth 5 x)) (true-listp (nth 5 x)) (equal (len (nth 5 x)) 32)))
  :hints (("Goal" :in-theory (enable fn-mlhp)))))

(local (defthm fn-mlh-list-of-seven
  (implies (and (true-listp x) (equal (len x) 7))
           (equal (list (nth 0 x) (nth 1 x) (nth 2 x) (nth 3 x) (nth 4 x) (nth 5 x) (nth 6 x)) x))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable len nth)))))

(local (defthm fn-mlh-clear-nths
  (and (equal (nth 0 (fn-mlh-clear fn-mlh)) nil)
       (equal (nth 1 (fn-mlh-clear fn-mlh)) 0)
       (equal (nth 2 (fn-mlh-clear fn-mlh)) 0)
       (equal (nth 3 (fn-mlh-clear fn-mlh)) 0)
       (equal (nth 4 (fn-mlh-clear fn-mlh)) 0)
       (equal (nth 5 (fn-mlh-clear fn-mlh)) (nth 5 fn-mlh))
       (equal (nth 6 (fn-mlh-clear fn-mlh)) 0))
  :hints (("Goal" :in-theory (e/d (fn-mlh-clear update-fn-mlh-pages update-fn-mlh-n update-fn-mlh-s
                                   update-fn-mlh-count update-fn-mlh-stuck resize-fn-mlh-dir)
                                  (nth update-nth))))))

(defthm fn-mlh-clear-is-a-list
  (implies (fn-mlhp fn-mlh)
           (equal (fn-mlh-clear fn-mlh) (list nil 0 0 0 0 (nth *fn-mlh-keyi* fn-mlh) 0)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-mlh-list-of-seven (x (fn-mlh-clear fn-mlh)))
                        (:instance fn-mlh-recognizer-facts (x (fn-mlh-clear fn-mlh))))
           :in-theory (disable fn-mlh-recognizer-facts))))

(local (defthm fn-mlh-cdr-nthcdr
  (implies (natp i) (equal (cdr (nthcdr i l)) (nthcdr (+ 1 i) l)))))
(local (defthm fn-mlh-car-nthcdr
  (implies (natp i) (equal (car (nthcdr i l)) (nth i l)))))
(local (defthm fn-mlh-nthcdr-unfold
  (implies (and (natp i) (< i (len l)))
           (equal (cons (nth i l) (nthcdr (+ 1 i) l)) (nthcdr i l)))
  :hints (("Goal" :induct (nthcdr i l)))))
(local (defthm fn-mlh-consp-nthcdr
  (implies (natp i) (iff (consp (nthcdr i l)) (< i (len l))))
  :hints (("Goal" :induct (nthcdr i l) :in-theory (enable nthcdr)))))
(local (defthm fn-mlh-nthcdr-of-true-list-end
  (implies (and (true-listp l) (natp i) (<= (len l) i)) (equal (nthcdr i l) nil))))
(local (defthm fn-mlh-keyp-nth-octet
  (implies (and (fn-mlh-keyp l) (natp i) (< i (len l)))
           (equal (fn-ns-octet (nth i l)) (nth i l)))
  :hints (("Goal" :in-theory (enable nth)))))
(local (defthm fn-mlh-take-of-update-nth
  (implies (and (natp i) (< i (len l)))
           (equal (take (+ 1 i) (update-nth i v l)) (append (take i l) (list v))))
  :hints (("Goal" :induct (update-nth i v l) :in-theory (enable update-nth)))))
(local (defthm fn-mlh-take-of-len
  (implies (true-listp l) (equal (take (len l) l) l))))
(local (in-theory (disable nth nthcdr fn-mlh-keyp)))
(local (defthm fn-mlh-nthcdr-0
  (equal (nthcdr 0 l) l)
  :hints (("Goal" :in-theory (enable nthcdr)))))

(defthm fn-mlh-key-from-is-nthcdr
  (implies (and (fn-mlhp fn-mlh) (natp i))
           (equal (fn-mlh-key-from i fn-mlh) (nthcdr i (nth *fn-mlh-keyi* fn-mlh))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-mlh-key-from i fn-mlh)
           :in-theory (enable fn-mlh-keyi))))

(local (defthm fn-mlh-keytail-of-own-tail
  (implies (and (fn-mlh-keyp l) (equal (len l) *fn-mpxt-key-octets*) (natp i))
           (equal (fn-mlh-keytail i (nthcdr i l)) (nthcdr i l)))
  :hints (("Goal" :induct (fn-mlh-keytail i (nthcdr i l))))))

(local (defun fn-mlh-skf-ind (i key l)
  (declare (xargs :measure (nfix (- *fn-mpxt-key-octets* (nfix i)))))
  (if (>= (nfix i) *fn-mpxt-key-octets*)
      (list i key l)
    (fn-mlh-skf-ind (1+ (nfix i)) (if (consp key) (cdr key) nil)
                    (update-nth (nfix i) (fn-ns-octet (if (consp key) (car key) 0)) l)))))

(local (defthm fn-mlh-set-key-from-over-a-list
  (implies (and (true-listp l) (equal (len l) *fn-mpxt-key-octets*) (natp i) (<= i *fn-mpxt-key-octets*))
           (equal (fn-mlh-set-key-from i key (list nil 0 0 0 0 l 0))
                  (list nil 0 0 0 0 (append (take i l) (fn-mlh-keytail i key)) 0)))
  :hints (("Goal" :induct (fn-mlh-skf-ind i key l)
           :in-theory (enable update-fn-mlh-keyi))
          ("Subgoal *1/2" :expand ((fn-mlh-set-key-from i key (list nil 0 0 0 0 l 0))
                                   (fn-mlh-keytail i key)))
          ("Subgoal *1/1" :use fn-mlh-take-of-len))))

(defthm fn-mlh-set-key-is-a-list
  (implies (fn-mlhp fn-mlh)
           (equal (fn-mlh-set-key key fn-mlh)
                  (list nil 0 0 0 0 (fn-mlh-keytail 0 key) 0)))
  :hints (("Goal" :in-theory (e/d (fn-mlh-set-key) (fn-mlh-set-key-from fn-mlh-clear))
           :use ((:instance fn-mlh-clear-is-a-list)
                 (:instance fn-mlh-set-key-from-over-a-list (i 0) (l (nth 5 fn-mlh)))))))

(defthm fn-mlh-set-key-canonical
  (implies (fn-mlhp fn-mlh)
           (equal (fn-mlh-set-key key fn-mlh)
                  (fn-mlh-set-key key (create-fn-mlh))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-mlh-set-key))))

; CLEAR IS THE SET-KEY OF THE TABLE'S OWN KEY: the fold's base case.
(defthm fn-mlh-clear-is-build-nil
  (implies (fn-mlhp fn-mlh)
           (equal (fn-mlh-clear fn-mlh)
                  (fn-mlh-build (fn-mlh-key-octets fn-mlh) nil)))
  :hints (("Goal" :use ((:instance fn-mlh-clear-is-a-list)
                        (:instance fn-mlh-set-key-is-a-list (key (fn-mlh-key-octets fn-mlh)) (fn-mlh (create-fn-mlh)))
                        (:instance fn-mlh-key-from-is-nthcdr (i 0))
                        (:instance fn-mlh-keytail-of-own-tail (i 0) (l (nth 5 fn-mlh))))
           :in-theory (e/d (fn-mlh-key-octets fn-mlh-build-nil)
                           (fn-mlh-set-key fn-mlh-clear fn-mlh-key-from fn-mlh-set-key-is-a-list
                            fn-mlh-keytail-of-own-tail)))))

(defthm fn-mlh-create-is-build-nil
  (equal (fn-mlh-build (fn-mlh-key-octets (create-fn-mlh)) nil) (create-fn-mlh))
  :hints (("Goal" :use ((:instance fn-mlh-clear-is-build-nil (fn-mlh (create-fn-mlh)))
                        (:instance fn-mlh-clear-is-a-list (fn-mlh (create-fn-mlh))))
           :in-theory (e/d (create-fn-mlh (:e create-fn-mlh))
                           (fn-mlh-clear-is-build-nil fn-mlh-clear fn-mlh-set-key-is-a-list)))))

(local (defthm fn-mlh-keyp-of-mpxt-keyp
  (implies (fn-mpxt-keyp l) (fn-mlh-keyp l))
  :hints (("Goal" :in-theory (enable fn-mpxt-keyp fn-mlh-keyp)))))

; A 32-octet key written by the open reads back as itself.
(defthm fn-mlh-key-octets-of-set-key
  (implies (and (fn-mlhp fn-mlh) (fn-mpxt-keyp key) (equal (len key) *fn-mpxt-key-octets*))
           (equal (fn-mlh-key-octets (fn-mlh-set-key key fn-mlh)) key))
  :hints (("Goal" :use ((:instance fn-mlh-set-key-is-a-list)
                        (:instance fn-mlh-key-from-is-nthcdr (i 0) (fn-mlh (fn-mlh-set-key key fn-mlh)))
                        (:instance fn-mlh-keytail-of-own-tail (i 0) (l key)))
           :in-theory (e/d (fn-mlh-key-octets fn-mlhp)
                           (fn-mlh-set-key fn-mlh-key-from fn-mlh-set-key-is-a-list
                            fn-mlh-keytail-of-own-tail fn-mlh-recognizer-facts)))))

(in-theory (disable fn-mlh-keytail))

; --- the fold reads a row's Message-ID only ---

(local (defthm fn-mlh-nth-of-update-nth-msgid
  (implies (and (natp k) (< k (len rows)) (natp i)
                (equal (fn-record-msgid h) (fn-record-msgid (nth k rows))))
           (equal (fn-record-msgid (nth i (update-nth k h rows)))
                  (fn-record-msgid (nth i rows))))
  :hints (("Goal" :in-theory (enable nth update-nth)))))

(defthm fn-mlh-build-from-of-update-nth-same-msgid
  (implies (and (natp k) (< k (len rows))
                (equal (fn-record-msgid h) (fn-record-msgid (nth k rows))))
           (equal (fn-mlh-build-from i u (update-nth k h rows) fn-mlh)
                  (fn-mlh-build-from i u rows fn-mlh)))
  :hints (("Goal" :induct (fn-mlh-build-from i u rows fn-mlh)
           :in-theory (disable fn-mlh-add update-nth nth)
           :expand ((fn-mlh-build-from i u (update-nth k h rows) fn-mlh)))))

(defthm fn-mlh-build-of-update-nth-same-msgid
  (implies (and (natp k) (< k (len rows))
                (equal (fn-record-msgid h) (fn-record-msgid (nth k rows))))
           (and (equal (fn-mlh-build key (update-nth k h rows)) (fn-mlh-build key rows))
                (equal (fn-mlh-build-unplaced key (update-nth k h rows)) (fn-mlh-build-unplaced key rows))))
  :hints (("Goal" :in-theory (e/d (fn-mlh-build fn-mlh-build-unplaced)
                                  (fn-mlh-build-from fn-mlh-set-key fn-mlh-build-from-of-update-nth-same-msgid
                                   fn-mlh-set-key-is-a-list))
           :use ((:instance fn-mlh-build-from-of-update-nth-same-msgid (i 0) (u 0)
                            (fn-mlh (fn-mlh-set-key key (create-fn-mlh))))))))

; --- THE FOLD, EXECUTABLE (books/msgid-pages-exec 7j's shape) ---

(verify-guards fn-mlh-build-from
  :hints (("Goal" :in-theory (disable fn-mlh-add fn-mlh-wfp) :do-not-induct t)))

; The fold executed by a cursor: TAIL is (nthcdr i rows), so each step reads
; its row with CAR and moves with CDR instead of (nth i rows) under (len
; rows): O(1) per row besides the add, where the fold above is O(R^2) to
; execute.  Equal to the fold for every value (no hypothesis but I's type).
(defun fn-mlh-build-tail (i u tail fn-mlh)
  (declare (xargs :stobjs fn-mlh :verify-guards nil :measure (len tail)
                  :guard (and (natp i) (natp u) (true-listp tail) (fn-mlh-wfp fn-mlh))))
  (if (endp tail)
      (mv u fn-mlh)
    (if (>= (+ 2 (nfix i)) *fn-mlh-tag-limit*)
        (fn-mlh-build-tail (1+ (nfix i)) (1+ u) (cdr tail) fn-mlh)
      (mv-let (r fn-mlh)
        (fn-mlh-add (fn-mlh-tag (fn-record-msgid (car tail)) (fn-mlh-key-octets fn-mlh))
                    (nfix i) fn-mlh)
        (fn-mlh-build-tail (1+ (nfix i)) (if (equal r :placed) u (1+ u)) (cdr tail) fn-mlh)))))
(verify-guards fn-mlh-build-tail
  :hints (("Goal" :in-theory (disable fn-mlh-add fn-mlh-wfp) :do-not-induct t)))

(local (defthm fn-mlh-bt-cdr-nthcdr
  (implies (natp i) (equal (cdr (nthcdr i rows)) (nthcdr (+ 1 i) rows)))
  :hints (("Goal" :in-theory (enable nthcdr)))))
(local (defthm fn-mlh-bt-car-nthcdr
  (implies (natp i) (equal (car (nthcdr i rows)) (nth i rows)))
  :hints (("Goal" :in-theory (enable nthcdr nth)))))
(local (defthm fn-mlh-bt-consp-nthcdr
  (implies (natp i) (iff (consp (nthcdr i rows)) (< i (len rows))))
  :hints (("Goal" :in-theory (enable nthcdr)))))

; KEYSTONE (representation of the executed fold).
(defthm fn-mlh-build-tail-is-build-from
  (implies (natp i)
           (equal (fn-mlh-build-tail i u (nthcdr i rows) fn-mlh)
                  (fn-mlh-build-from i u rows fn-mlh)))
  :hints (("Goal" :induct (fn-mlh-build-from i u rows fn-mlh)
           :in-theory (disable fn-mlh-add nthcdr nth))))

(defthm fn-mlh-build-tail-from-zero-is-build-from
  (equal (fn-mlh-build-tail 0 u rows fn-mlh)
         (fn-mlh-build-from 0 u rows fn-mlh))
  :hints (("Goal" :use ((:instance fn-mlh-build-tail-is-build-from (i 0)))
           :in-theory (enable nthcdr))))

(defun fn-mlh-key-same-from (i key fn-mlh)
  (declare (xargs :stobjs fn-mlh :guard (natp i)
                  :measure (nfix (- *fn-mpxt-key-octets* (nfix i)))))
  (if (>= (nfix i) *fn-mpxt-key-octets*)
      (atom key)
    (and (consp key)
         (equal (car key) (fn-mlh-keyi (nfix i) fn-mlh))
         (fn-mlh-key-same-from (1+ (nfix i)) (cdr key) fn-mlh))))

(defthm fn-mlh-key-same-from-is-equal
  (implies (and (true-listp key) (natp i))
           (equal (fn-mlh-key-same-from i key fn-mlh)
                  (equal key (fn-mlh-key-from i fn-mlh))))
  :hints (("Goal" :induct (fn-mlh-key-same-from i key fn-mlh)
           :expand ((fn-mlh-key-from i fn-mlh)))))

(defun fn-mlh-key-samep (key fn-mlh)
  (declare (xargs :stobjs fn-mlh))
  (fn-mlh-key-same-from 0 key fn-mlh))

(defthm fn-mlh-key-samep-is-equal
  (implies (true-listp key)
           (equal (fn-mlh-key-samep key fn-mlh)
                  (equal key (fn-mlh-key-octets fn-mlh))))
  :hints (("Goal" :in-theory (enable fn-mlh-key-octets))))

(in-theory (disable fn-mlh-key-samep))

; The fold's outcome for one more row carrying MSGID, over a local table.
(defun fn-mlh-build-saturatedp (key msgid rows)
  (declare (xargs :guard (true-listp rows)
                  :guard-hints (("Goal" :in-theory (disable fn-mlh-build-from fn-mlh-saturatedp fn-mlh-set-key
                                                            fn-mlh-set-key-is-a-list)))))
  (with-local-stobj fn-mlh
    (mv-let (r fn-mlh)
      (let ((fn-mlh (fn-mlh-set-key key fn-mlh)))
        (mv-let (u fn-mlh)
          (mbe :logic (fn-mlh-build-from 0 0 rows fn-mlh)
               :exec (fn-mlh-build-tail 0 0 rows fn-mlh))
          (declare (ignore u))
          (mv (or (>= (+ 2 (len rows)) *fn-mlh-tag-limit*)
                  (fn-mlh-saturatedp (fn-mlh-tag-of msgid fn-mlh) fn-mlh))
              fn-mlh)))
      r)))

; The table's health over a local table: (pages count unplaced stuck).
(defun fn-mlh-build-health (key rows)
  (declare (xargs :guard (true-listp rows)
                  :guard-hints (("Goal" :in-theory (disable fn-mlh-build-from fn-mlh-set-key
                                                            fn-mlh-set-key-is-a-list)))))
  (with-local-stobj fn-mlh
    (mv-let (r fn-mlh)
      (let ((fn-mlh (fn-mlh-set-key key fn-mlh)))
        (mv-let (u fn-mlh)
          (mbe :logic (fn-mlh-build-from 0 0 rows fn-mlh)
               :exec (fn-mlh-build-tail 0 0 rows fn-mlh))
          (mv (list (fn-mlh-pages fn-mlh) (fn-mlh-count fn-mlh) u (fn-mlh-stuck fn-mlh))
              fn-mlh)))
      r)))

(defthm fn-mlh-build-saturatedp-is-the-build
  (equal (fn-mlh-build-saturatedp key msgid rows)
         (or (>= (+ 2 (len rows)) *fn-mlh-tag-limit*)
             (fn-mlh-saturatedp (fn-mlh-tag msgid (fn-mlh-key-octets (fn-mlh-build key rows)))
                                (fn-mlh-build key rows))))
  :hints (("Goal" :in-theory (e/d (fn-mlh-build) (fn-mlh-build-from fn-mlh-saturatedp fn-mlh-set-key
                                                  fn-mlh-set-key-is-a-list)))))

(defthm fn-mlh-build-health-is-the-build
  (equal (fn-mlh-build-health key rows)
         (list (fn-mlh-pages (fn-mlh-build key rows)) (fn-mlh-count (fn-mlh-build key rows))
               (fn-mlh-build-unplaced key rows) (fn-mlh-stuck (fn-mlh-build key rows))))
  :hints (("Goal" :in-theory (e/d (fn-mlh-build fn-mlh-build-unplaced)
                                  (fn-mlh-build-from fn-mlh-set-key fn-mlh-set-key-is-a-list)))))

; THE OUTCOME AT THE COMMIT, over the executable projection.
(defthm fn-mlh-build-saturatedp-is-the-outcome
  (implies (equal msgid (fn-record-msgid h))
           (iff (equal (fn-mlh-build-unplaced key (append rows (list h)))
                       (fn-mlh-build-unplaced key rows))
                (not (fn-mlh-build-saturatedp key msgid rows))))
  :hints (("Goal" :in-theory (disable fn-mlh-build-from fn-mlh-saturatedp fn-mlh-set-key
                                      fn-mlh-build-saturatedp fn-mlh-build-append))))

(in-theory (disable fn-mlh-build-saturatedp fn-mlh-build-health))
