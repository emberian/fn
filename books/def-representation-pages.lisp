; fn: the PERSISTED page image of `def-representation' (lane s-pck, 2026-10-07;
; Phase 2a of build/coordinator/STORAGE-PROGRAM-20261006.md).
;
; `def-representation ... :pages t' generates, per instance NAME,
;   NAME-pages-of      logical value -> the page store's CONTENTS (a list of
;                      pages, each 2048 u64 words: books/pagestore.lisp's
;                      `pgs-open' view),
;   NAME-of-pages      contents -> logical value,
;   NAME-append-dirty  the dirty alist (LPAGE . PAGE) that one append makes,
;   NAME-rowp, NAME-pool-pages-of-row
; and the theorems about them (round trip, locality against
; `pgs-apply-dirty', a bound with no term in the length of the value, the
; words being u64).  Every one is proved here ONCE, over a SCHEMA VARIABLE
; (`adt-tp-of-pages-of-pages-of' and the rest below); an instance's theorem is
; the library theorem at the instance's schema constant (the generator is
; books/def-representation.lisp, `rep-pages-events'), so no per-structure proof
; exists.  Instancing by the schema variable rather than by functional
; instantiation of an abstract constrained function: the codec is a function of
; the schema, so the schema variable IS the abstraction and the library theorem
; the common theorem.
;
; THE LAYOUT.  The contents is a TAPE: the words of the records in order, cut
; into pages of *pgs-page-words* words, the last page zero padded.  A record is
; its TAG word 1, then its fields in schema order:
;   a scalar field   one word, `adt-enc' of its value (a bool 0 or 1, an enum
;                    its index, a :nat or :u8/:u32/:u64 itself);
;   an octets field  one word (the octet count) then the octets, eight to a
;                    word, little-endian, the last word zero padded.
; The tag makes the tape self-delimiting: after the last record the words are
; zero padding, and the decoder stops at a word that is not the tag.  No count,
; fill or fence is stored, so an append rewrites the partial last page and adds
; the pages its words spill into, and NOTHING ELSE (`adt-tp-dirty'; bound
; `adt-tp-dirty-bound').  That is the whole content of "O(delta)": the dirty
; set is independent of how many records came before.  A :tree field is its
; postfix program's octets, as in the paged foundation.
;
; Scope, named.  (1) One tape is one structure.  The page store's contiguity
; rule (`pgs-lpages-ok': a dirty page number is at most the length reached so
; far; `pgs-apply-dirty' drops any other) forces pages in tape order, so two
; structures that both grow (the catalog rows and the msgid table) cannot each
; own a region of one store without a page directory in the root record; that
; directory is the next stage and is NOT in this book.  (2) Decoding is
; sequential, which is what adopting the pages at open needs; random access by
; row index wants an index over the tape (the root's).  (3) The words are u64
; (`adt-tp-pages-wordsp') only under the premise that no octet list has 2^64 or
; more octets (`adt-tp-seq-lens-ok'); the round trip and the locality need no
; such premise.  (4) The generator refuses, at expansion, a field that is not
; one word (a :nat bound or an :enum count of 2^64 or more).

(in-package "ACL2")
(include-book "proto/adt-lib")
(include-book "pagestore")
(local (include-book "arithmetic/top" :dir :system))
(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
(local (include-book "std/lists/append" :dir :system))

; -----------------------------------------------------------------------------
; 1. The tape: words cut into pages.

(defun adt-tp-take (n w)
  (declare (xargs :guard (natp n)))
  (if (or (zp n) (atom w)) nil (cons (car w) (adt-tp-take (1- n) (cdr w)))))

(defun adt-tp-zeros (n)
  (declare (xargs :guard (natp n)))
  (if (zp n) nil (cons 0 (adt-tp-zeros (1- n)))))

(defthm adt-tp-len-take
  (equal (len (adt-tp-take n w)) (min (nfix n) (len w))))

(defthm adt-tp-len-zeros
  (equal (len (adt-tp-zeros n)) (nfix n)))

(defthm adt-tp-len-nthcdr
  (equal (len (nthcdr n x)) (nfix (- (len x) (nfix n)))))

(defthm adt-tp-zeros-zero
  (equal (adt-tp-zeros 0) nil))

(defthm adt-tp-take-all
  (implies (and (<= (len w) (nfix n)) (true-listp w))
           (equal (adt-tp-take n w) w)))

(defthm adt-tp-append-take-nthcdr
  (implies (and (natp n) (<= n (len w)) (true-listp w))
           (equal (append (adt-tp-take n w) (nthcdr n w)) w)))

(in-theory (disable adt-tp-take adt-tp-zeros))

(defun adt-tp-page (w)
  ; The page the first words of W make: 2048 words, zero padded.
  (declare (xargs :guard t))
  (let ((tk (adt-tp-take *pgs-page-words* w)))
    (append tk (adt-tp-zeros (- *pgs-page-words* (len tk))))))

(defthm adt-tp-len-page
  (equal (len (adt-tp-page w)) *pgs-page-words*)
  :hints (("Goal" :in-theory (enable adt-tp-page))))

(defthm adt-tp-page-short
  (implies (and (<= (len w) *pgs-page-words*) (true-listp w))
           (equal (adt-tp-page w) (append w (adt-tp-zeros (- *pgs-page-words* (len w))))))
  :hints (("Goal" :in-theory (enable adt-tp-page))))

(defthm adt-tp-page-long
  (implies (and (<= *pgs-page-words* (len w)) (true-listp w))
           (equal (adt-tp-page w) (adt-tp-take *pgs-page-words* w)))
  :hints (("Goal" :in-theory (enable adt-tp-page))))

(in-theory (disable adt-tp-page))

(defun adt-tp-pages (w)
  (declare (xargs :guard (true-listp w) :measure (len w)))
  (if (atom w)
      nil
    (cons (adt-tp-page w) (adt-tp-pages (nthcdr *pgs-page-words* w)))))

(defun adt-tp-flat (pages)
  (declare (xargs :guard (true-list-listp pages)))
  (if (atom pages) nil (append (car pages) (adt-tp-flat (cdr pages)))))

(defun adt-tp-npages (n)
  ; The pages N words need.
  (declare (xargs :guard (natp n) :measure (nfix n)))
  (if (zp n) 0 (+ 1 (adt-tp-npages (nfix (- n *pgs-page-words*))))))

(defthm adt-tp-len-pages
  (equal (len (adt-tp-pages w)) (adt-tp-npages (len w)))
  :hints (("Goal" :induct (adt-tp-pages w))))

(defun adt-tp-pad (n)
  ; The zero words the last page of an N-word tape carries.
  (declare (xargs :guard (natp n) :measure (nfix n)))
  (if (zp n) 0
    (if (<= n *pgs-page-words*)
        (- *pgs-page-words* n)
      (adt-tp-pad (- n *pgs-page-words*)))))


(defthm adt-tp-nthcdr-short
  (implies (and (<= (len w) (nfix n)) (true-listp w))
           (equal (nthcdr n w) nil))
  :hints (("Goal" :induct (adt-tp-take n w) :in-theory (enable adt-tp-take))))
(defthm adt-tp-pad-long
  (implies (and (natp n) (< *pgs-page-words* n))
           (equal (adt-tp-pad n) (adt-tp-pad (- n *pgs-page-words*)))))
(defthm adt-tp-pad-short
  (implies (and (natp n) (<= n *pgs-page-words*))
           (equal (adt-tp-pad n) (if (zp n) 0 (- *pgs-page-words* n)))))
(in-theory (disable adt-tp-pad))


(defthm adt-tp-append-take-nthcdr-z
  (implies (and (natp n) (<= n (len w)) (true-listp w))
           (equal (append (adt-tp-take n w) (append (nthcdr n w) z)) (append w z)))
  :hints (("Goal" :use adt-tp-append-take-nthcdr :in-theory (disable adt-tp-append-take-nthcdr))))
(defthm adt-tp-flat-pages-step
  (implies (and (true-listp w) (< 2048 (len w)))
           (equal (adt-tp-flat (adt-tp-pages w))
                  (append (adt-tp-take 2048 w) (adt-tp-flat (adt-tp-pages (nthcdr 2048 w))))))
  :hints (("Goal" :expand ((adt-tp-pages w)) :do-not-induct t))
  :rule-classes nil)
(defthm adt-tp-flat-of-pages-short
  (implies (and (true-listp w) (<= (len w) 2048))
           (equal (adt-tp-flat (adt-tp-pages w))
                  (append w (adt-tp-zeros (adt-tp-pad (len w))))))
  :hints (("Goal" :expand ((adt-tp-pages w)))))
(defthm adt-tp-flat-of-pages-long
  (implies (and (true-listp w) (< 2048 (len w))
                (equal (adt-tp-flat (adt-tp-pages (nthcdr 2048 w)))
                       (append (nthcdr 2048 w) (adt-tp-zeros (adt-tp-pad (len (nthcdr 2048 w)))))))
           (equal (adt-tp-flat (adt-tp-pages w))
                  (append w (adt-tp-zeros (adt-tp-pad (len w))))))
  :hints (("Goal" :use (adt-tp-flat-pages-step
                        (:instance adt-tp-append-take-nthcdr (n 2048)))
           :in-theory (e/d (adt-tp-pad-long) (adt-tp-pages adt-tp-flat adt-tp-len-nthcdr))
           :do-not-induct t)))
(defthm adt-tp-flat-of-pages
  (implies (true-listp w)
           (equal (adt-tp-flat (adt-tp-pages w))
                  (append w (adt-tp-zeros (adt-tp-pad (len w))))))
  :hints (("Goal" :induct (adt-tp-pages w) :in-theory (disable (:definition adt-tp-pages)))
          ("Subgoal *1/2''" :cases ((< 2048 (len w))))))

; -----------------------------------------------------------------------------
; 2. Locality: an append of N words to a W-word tape rewrites the partial last
; page and adds the pages N spills into.

(defun adt-tp-number (k ps)
  ; The dirty alist of the pages PS from logical page K on.
  (declare (xargs :guard (natp k)))
  (if (atom ps) nil (cons (cons k (car ps)) (adt-tp-number (1+ k) (cdr ps)))))

(defun adt-tp-dirty (w n)
  ; The dirty pages of appending N to the tape W: nothing for no words, else
  ; the pages of the last (partial) page's words followed by N, numbered from
  ; that page.
  (declare (xargs :guard (and (true-listp w) (true-listp n))))
  (if (atom n)
      nil
    (let ((k0 (floor (len w) *pgs-page-words*)))
      (adt-tp-number k0 (adt-tp-pages (append (nthcdr (* *pgs-page-words* k0) w) n))))))

(defthm adt-tp-len-number
  (equal (len (adt-tp-number k ps)) (len ps)))

(defun adt-tp-number-ind (a b ps)
  (if (atom ps)
      (list a b)
    (adt-tp-number-ind (append a (list (car ps))) (cdr b) (cdr ps))))

(defthm adt-tp-update-nth-at-end
  (implies (and (true-listp a) (consp b))
           (equal (update-nth (len a) p (append a b))
                  (append a (cons p (cdr b)))))
  :hints (("Goal" :in-theory (enable update-nth))))

(defthm adt-tp-apply-dirty-number
  ; Dirty pages numbered from the end of A replace the (at most as many) pages after A.
  (implies (and (true-listp a) (true-listp b) (true-listp ps) (<= (len b) (len ps)))
           (equal (pgs-apply-dirty (append a b) (adt-tp-number (len a) ps))
                  (append a ps)))
  :hints (("Goal" :in-theory (enable pgs-apply-dirty)
           :induct (adt-tp-number-ind a b ps))))

(defthm adt-tp-pages-long
  (implies (and (true-listp w) (<= *pgs-page-words* (len w)))
           (equal (adt-tp-pages w)
                  (cons (adt-tp-take *pgs-page-words* w)
                        (adt-tp-pages (nthcdr *pgs-page-words* w)))))
  :hints (("Goal" :expand ((adt-tp-pages w)))))

(defthm adt-tp-take-of-append
  (implies (<= n (len a))
           (equal (adt-tp-take n (append a b)) (adt-tp-take n a)))
  :hints (("Goal" :in-theory (enable adt-tp-take))))

(defthm adt-tp-nthcdr-of-append
  (implies (and (natp n) (<= n (len a)) (true-listp a))
           (equal (nthcdr n (append a b)) (append (nthcdr n a) b))))

(defun adt-tp-ind-k (k w)
  (if (zp k) w (adt-tp-ind-k (1- k) (nthcdr *pgs-page-words* w))))

(defthm adt-tp-pages-of-append-aligned
  ; Appending after a whole number of pages leaves those pages alone.
  (implies (and (natp k) (true-listp w1) (true-listp z) (equal (len w1) (* k *pgs-page-words*)))
           (equal (adt-tp-pages (append w1 z))
                  (append (adt-tp-pages w1) (adt-tp-pages z))))
  :hints (("Goal" :induct (adt-tp-ind-k k w1))))

(defthm adt-tp-npages-small
  (implies (and (natp x) (< x *pgs-page-words*)) (<= (adt-tp-npages x) 1))
  :hints (("Goal" :in-theory (enable adt-tp-npages))))

(defthm adt-tp-npages-posp
  (implies (posp x) (<= 1 (adt-tp-npages x)))
  :hints (("Goal" :in-theory (enable adt-tp-npages))))

(defthm adt-tp-npages-of-multiple
  (implies (natp k)
           (equal (adt-tp-npages (* k *pgs-page-words*)) k))
  :hints (("Goal" :induct (adt-tp-ind-k k nil)
           :in-theory (enable adt-tp-npages))))

(defthm adt-tp-dirty-core
  (implies (and (true-listp w1) (true-listp t0) (consp n) (true-listp n)
                (natp k) (equal (len w1) (* k *pgs-page-words*))
                (< (len t0) *pgs-page-words*) (equal w (append w1 t0)))
           (equal (pgs-apply-dirty (adt-tp-pages w)
                                   (adt-tp-number k (adt-tp-pages (append t0 n))))
                  (adt-tp-pages (append w n))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance adt-tp-pages-of-append-aligned (z t0))
                 (:instance adt-tp-pages-of-append-aligned (z (append t0 n)))
                 (:instance adt-tp-apply-dirty-number
                            (a (adt-tp-pages w1)) (b (adt-tp-pages t0))
                            (ps (adt-tp-pages (append t0 n))))
                 (:instance adt-tp-npages-small (x (len t0)))
                 (:instance adt-tp-npages-posp (x (+ (len t0) (len n))))
                 (:instance adt-tp-npages-of-multiple)
                 (:instance adt-tp-len-pages (w w1)))
           :in-theory (disable adt-tp-pages-of-append-aligned adt-tp-apply-dirty-number adt-tp-pages-long adt-tp-page-short adt-tp-page-long (:executable-counterpart adt-tp-zeros) (:executable-counterpart adt-tp-take) (:executable-counterpart adt-tp-pages)))))

(defthm adt-tp-take-nthcdr-split
  (implies (and (true-listp w) (<= m (len w)) (natp m))
           (and (equal (append (take m w) (nthcdr m w)) w)
                (equal (len (take m w)) m)
                (true-listp (take m w))))
  :hints (("Goal" :in-theory (enable take))))

(defthm adt-tp-dirty-is-the-delta-k
  (implies (and (true-listp w) (true-listp n) (consp n) (natp k)
                (<= (* *pgs-page-words* k) (len w))
                (< (len w) (* *pgs-page-words* (+ 1 k))))
           (equal (pgs-apply-dirty (adt-tp-pages w)
                                   (adt-tp-number k (adt-tp-pages (append (nthcdr (* *pgs-page-words* k) w) n))))
                  (adt-tp-pages (append w n))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance adt-tp-take-nthcdr-split (m (* *pgs-page-words* k)))
                 (:instance adt-tp-dirty-core
                            (w1 (take (* *pgs-page-words* k) w))
                            (t0 (nthcdr (* *pgs-page-words* k) w))))
           :in-theory (disable adt-tp-dirty-core adt-tp-take-nthcdr-split adt-tp-pages-of-append-aligned))))

(defthm adt-tp-floor-bounds
  (implies (natp x)
           (and (natp (floor x *pgs-page-words*))
                (<= (* *pgs-page-words* (floor x *pgs-page-words*)) x)
                (< x (* *pgs-page-words* (+ 1 (floor x *pgs-page-words*))))))
  :hints (("Goal" :in-theory (disable floor))))

(defthm adt-tp-dirty-is-the-delta
  ; The pages of W with the dirty pages of the append applied are the pages of the append.
  (implies (and (true-listp w) (true-listp n))
           (equal (pgs-apply-dirty (adt-tp-pages w) (adt-tp-dirty w n))
                  (adt-tp-pages (append w n))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable adt-tp-dirty-is-the-delta-k adt-tp-floor-bounds)
           :use ((:instance adt-tp-dirty-is-the-delta-k (k (floor (len w) *pgs-page-words*)))
                 (:instance adt-tp-floor-bounds (x (len w)))))
          ("Subgoal 2" :in-theory (enable adt-tp-dirty))
          ("Subgoal 1" :in-theory (enable adt-tp-dirty))))

(defthm adt-tp-npages-le2
  (implies (and (natp x) (< x (* 2 *pgs-page-words*))) (<= (adt-tp-npages x) 2))
  :hints (("Goal" :in-theory (enable adt-tp-npages))))

(defthm adt-tp-npages-open
  (implies (and (natp n) (<= *pgs-page-words* n))
           (equal (adt-tp-npages n) (+ 1 (adt-tp-npages (- n *pgs-page-words*)))))
  :hints (("Goal" :expand ((adt-tp-npages n)))))

(defthm adt-tp-npages-subadd-small
  (implies (and (natp x) (natp y) (< x *pgs-page-words*) (< y *pgs-page-words*))
           (<= (adt-tp-npages (+ x y)) (+ 1 (adt-tp-npages y))))
  :hints (("Goal" :use ((:instance adt-tp-npages-le2 (x (+ x y)))
                        (:instance adt-tp-npages-small (x x))
                        (:instance adt-tp-npages-posp (x y)))
           :in-theory (disable adt-tp-npages-le2 adt-tp-npages-small adt-tp-npages-posp))))

(defun adt-tp-ind-y (y)
  (if (zp y) 0 (adt-tp-ind-y (nfix (- y *pgs-page-words*)))))

(defthm adt-tp-npages-subadd
  (implies (and (natp x) (natp y) (< x *pgs-page-words*))
           (<= (adt-tp-npages (+ x y)) (+ 1 (adt-tp-npages y))))
  :hints (("Goal" :induct (adt-tp-ind-y y)
           :in-theory (disable adt-tp-npages))))

(defthm adt-tp-dirty-bound
  ; No term in (len w): the pages the delta's words spill into, and the page it shares.
  (implies (and (true-listp w) (true-listp n))
           (<= (len (adt-tp-dirty w n)) (+ 1 (adt-tp-npages (len n)))))
  :hints (("Goal" :in-theory (e/d (adt-tp-dirty) (adt-tp-npages-subadd adt-tp-floor-bounds adt-tp-len-nthcdr))
           :use ((:instance adt-tp-floor-bounds (x (len w)))
                 (:instance adt-tp-npages-subadd
                            (x (- (len w) (* *pgs-page-words* (floor (len w) *pgs-page-words*))))
                            (y (len n)))))))

; -----------------------------------------------------------------------------
; 3. The record codec over a schema.

(defconst *adt-tp-w64* 18446744073709551616)

(defun adt-tp-kind-ok (k)
  ; Every value of kind K is one word.
  (declare (xargs :verify-guards nil :guard t))
  (and (adt-kindp k)
       (case (car k)
         (:nat (< (cadr k) *adt-tp-w64*))
         (:enum (< (len (cdr k)) *adt-tp-w64*))
         (otherwise t))))

(defun adt-tp-schema-ok (s)
  (declare (xargs :verify-guards nil :guard t))
  (if (atom s) (null s) (and (adt-tp-kind-ok (car s)) (adt-tp-schema-ok (cdr s)))))

; An octet list in words, eight to a word, little-endian, the last zero padded.
(defun adt-tp-wd (o k)
  (declare (xargs :verify-guards nil :guard t))
  (if (or (zp k) (atom o)) 0 (+ (nfix (car o)) (* 256 (adt-tp-wd (cdr o) (1- k))))))

(defun adt-tp-pack (o)
  (declare (xargs :verify-guards nil :guard t :measure (len o)))
  (if (atom o) nil (cons (adt-tp-wd o 8) (adt-tp-pack (nthcdr 8 o)))))

(defun adt-tp-unw (k w)
  ; The K octets of the word W, least significant first.
  (declare (xargs :verify-guards nil :guard t))
  (if (zp k) nil (cons (mod (nfix w) 256) (adt-tp-unw (1- k) (floor (nfix w) 256)))))

(defun adt-tp-npk (n)
  ; The words N octets take. Runtime callers supply an octet count (natural).
  (declare (xargs :guard (natp n) :measure (nfix n)))
  (if (zp n) 0 (+ 1 (adt-tp-npk (nfix (- n 8))))))

(defun adt-tp-unpack (n ws)
  (declare (xargs :verify-guards nil :guard t :measure (nfix n)))
  (if (zp n) nil
    (append (adt-tp-unw (min n 8) (car ws)) (adt-tp-unpack (nfix (- n 8)) (cdr ws)))))

; A record: the tag 1, then each field.
(defun adt-tp-fw (s rec)
  (declare (xargs :verify-guards nil :guard t))
  (cond ((atom s) nil)
        ((adt-octets-kind-p (car s))
         (cons (len (car rec)) (append (adt-tp-pack (car rec)) (adt-tp-fw (cdr s) (cdr rec)))))
        (t (cons (adt-enc (car s) (car rec)) (adt-tp-fw (cdr s) (cdr rec))))))

(defun adt-tp-rw (s rec)
  (declare (xargs :verify-guards nil :guard t))
  (cons 1 (adt-tp-fw s rec)))

(defun adt-tp-seq-words (s a)
  (declare (xargs :verify-guards nil :guard t))
  (if (atom a) nil (append (adt-tp-rw s (car a)) (adt-tp-seq-words s (cdr a)))))

(defun adt-tp-decf (s w)
  ; The record the words W start with.
  (declare (xargs :verify-guards nil :guard t))
  (cond ((atom s) nil)
        ((adt-octets-kind-p (car s))
         (cons (adt-tp-unpack (car w) (cdr w))
               (adt-tp-decf (cdr s) (nthcdr (adt-tp-npk (car w)) (cdr w)))))
        (t (cons (adt-dec (car s) (car w)) (adt-tp-decf (cdr s) (cdr w))))))

(defun adt-tp-restf (s w)
  ; The words after the record the words W start with.
  (declare (xargs :verify-guards nil :guard t))
  (cond ((atom s) w)
        ((adt-octets-kind-p (car s))
         (adt-tp-restf (cdr s) (nthcdr (adt-tp-npk (car w)) (cdr w))))
        (t (adt-tp-restf (cdr s) (cdr w)))))

(defthm adt-tp-len-restf
  (<= (len (adt-tp-restf s w)) (len w))
  :rule-classes :linear)

(defun adt-tp-dseq (s w)
  (declare (xargs :verify-guards nil :guard t :measure (len w)))
  (if (and (consp w) (equal (car w) 1))
      (cons (adt-tp-decf s (cdr w)) (adt-tp-dseq s (adt-tp-restf s (cdr w))))
    nil))

(in-theory (disable adt-tp-wd adt-tp-unw adt-tp-pack adt-tp-unpack adt-tp-npk))

(defun adt-tp-ind-uw (k o j)
  (if (or (zp k) (atom o)) (list k o j) (adt-tp-ind-uw (1- k) (cdr o) (1- j))))

(defthm adt-tp-unw-of-wd
  (implies (and (adt-octetsp o) (natp k) (natp j) (<= k j) (<= k (len o)))
           (equal (adt-tp-unw k (adt-tp-wd o j)) (adt-tp-take k o)))
  :hints (("Goal" :induct (adt-tp-ind-uw k o j)
           :in-theory (enable adt-tp-unw adt-tp-wd adt-tp-take))))

(defthm adt-tp-len-pack
  (equal (len (adt-tp-pack o)) (adt-tp-npk (len o)))
  :hints (("Goal" :induct (adt-tp-pack o)
           :in-theory (enable adt-tp-pack adt-tp-npk))))

(defthm adt-tp-true-listp-pack
  (true-listp (adt-tp-pack o))
  :hints (("Goal" :in-theory (enable adt-tp-pack))))

(defthm adt-tp-octetsp-nthcdr
  (implies (adt-octetsp o) (adt-octetsp (nthcdr n o))))

(defthm adt-tp-unpack-of-pack
  (implies (adt-octetsp o)
           (equal (adt-tp-unpack (len o) (append (adt-tp-pack o) r)) o))
  :hints (("Goal" :induct (adt-tp-pack o)
           :in-theory (enable adt-tp-pack adt-tp-unpack))))

(defthm adt-tp-nthcdr-of-pack
  (equal (nthcdr (adt-tp-npk (len o)) (append (adt-tp-pack o) x)) x)
  :hints (("Goal" :use ((:instance adt-tp-len-pack))
           :in-theory (disable adt-tp-len-pack))))

(defthm adt-tp-fields-roundtrip
  (implies (and (adt-tp-schema-ok s) (adt-rec-p s rec))
           (and (equal (adt-tp-decf s (append (adt-tp-fw s rec) r)) rec)
                (equal (adt-tp-restf s (append (adt-tp-fw s rec) r)) r)))
  :hints (("Goal" :induct (adt-tp-fw s rec)
           :in-theory (enable adt-dec-of-enc))))

(defthm adt-tp-true-listp-fw
  (true-listp (adt-tp-fw s rec)))

(defthm adt-tp-true-listp-rw
  (true-listp (adt-tp-rw s rec)))

(defthm adt-tp-true-listp-seq-words
  (true-listp (adt-tp-seq-words s a)))

(defthm adt-tp-seq-words-of-append
  (equal (adt-tp-seq-words s (append a b))
         (append (adt-tp-seq-words s a) (adt-tp-seq-words s b))))

(defthm adt-tp-seq-words-of-snoc
  (equal (adt-tp-seq-words s (append a (list x)))
         (append (adt-tp-seq-words s a) (adt-tp-rw s x))))

(defthm adt-tp-seq-roundtrip
  ; Reading a sequence's words, followed by anything that does not start a record.
  (implies (and (adt-tp-schema-ok s) (adt-seq-p s a)
                (or (atom tail) (not (equal (car tail) 1))))
           (equal (adt-tp-dseq s (append (adt-tp-seq-words s a) tail)) a))
  :hints (("Goal" :induct (adt-tp-seq-words s a))))

(defthm adt-tp-car-zeros
  (or (atom (adt-tp-zeros n)) (not (equal (car (adt-tp-zeros n)) 1)))
  :hints (("Goal" :in-theory (enable adt-tp-zeros))))

; The page image of a sequence, the sequence of a page image, and the dirty
; set of an append: the three the generator names.
(defun adt-tp-pages-of (s a)
  (declare (xargs :verify-guards nil :guard t))
  (adt-tp-pages (adt-tp-seq-words s a)))

(defun adt-tp-of-pages (s pages)
  (declare (xargs :verify-guards nil :guard t))
  (adt-tp-dseq s (adt-tp-flat pages)))

(defun adt-tp-append-dirty (s a x)
  (declare (xargs :verify-guards nil :guard t))
  (adt-tp-dirty (adt-tp-seq-words s a) (adt-tp-rw s x)))

(defun adt-tp-row-pages (s x)
  ; The pages one row's words take: the whole of an append's dirty set but the
  ; one page it may share with the rows before it.
  (declare (xargs :verify-guards nil :guard t))
  (adt-tp-npages (len (adt-tp-rw s x))))

(defthm adt-tp-of-pages-of-pages-of
  (implies (and (adt-tp-schema-ok s) (adt-seq-p s a))
           (equal (adt-tp-of-pages s (adt-tp-pages-of s a)) a))
  :hints (("Goal" :in-theory (disable adt-tp-seq-roundtrip adt-tp-car-zeros)
           :use ((:instance adt-tp-seq-roundtrip
                            (tail (adt-tp-zeros (adt-tp-pad (len (adt-tp-seq-words s a))))))
                 (:instance adt-tp-car-zeros (n (adt-tp-pad (len (adt-tp-seq-words s a)))))
                 (:instance adt-tp-flat-of-pages (w (adt-tp-seq-words s a)))))))

(defthm adt-tp-pages-of-append-is-apply-dirty
  (implies (and (adt-tp-schema-ok s) (adt-seq-p s a) (adt-rec-p s x))
           (equal (pgs-apply-dirty (adt-tp-pages-of s a) (adt-tp-append-dirty s a x))
                  (adt-tp-pages-of s (append a (list x)))))
  :hints (("Goal" :in-theory (disable adt-tp-dirty-is-the-delta)
           :use ((:instance adt-tp-dirty-is-the-delta
                            (w (adt-tp-seq-words s a)) (n (adt-tp-rw s x)))))))

(defthm adt-tp-append-dirty-bound
  (<= (len (adt-tp-append-dirty s a x)) (+ 1 (adt-tp-row-pages s x)))
  :hints (("Goal" :in-theory (disable adt-tp-dirty-bound)
           :use ((:instance adt-tp-dirty-bound (w (adt-tp-seq-words s a)) (n (adt-tp-rw s x)))))))

; -----------------------------------------------------------------------------
; 4. The words are u64 (the shape the page store's host fill returns).  The
; one premise is that no octet list has 2^64 octets or more.

(defun adt-tp-u64s (w)
  (declare (xargs :verify-guards nil :guard t))
  (if (atom w) (null w) (and (unsigned-byte-p 64 (car w)) (adt-tp-u64s (cdr w)))))

(defun adt-tp-rec-lens-ok (s rec)
  (declare (xargs :verify-guards nil :guard t))
  (cond ((atom s) t)
        ((adt-octets-kind-p (car s))
         (and (< (len (car rec)) *adt-tp-w64*) (adt-tp-rec-lens-ok (cdr s) (cdr rec))))
        (t (adt-tp-rec-lens-ok (cdr s) (cdr rec)))))

(defun adt-tp-seq-lens-ok (s a)
  (declare (xargs :verify-guards nil :guard t))
  (if (atom a) t (and (adt-tp-rec-lens-ok s (car a)) (adt-tp-seq-lens-ok s (cdr a)))))

(defthm adt-tp-wd-bound
  (implies (and (adt-octetsp o) (natp k))
           (< (adt-tp-wd o k) (expt 256 k)))
  :hints (("Goal" :induct (adt-tp-wd o k)
           :in-theory (enable adt-tp-wd expt))))

(defthm adt-tp-wd8-u64
  (implies (adt-octetsp o) (unsigned-byte-p 64 (adt-tp-wd o 8)))
  :hints (("Goal" :use ((:instance adt-tp-wd-bound (k 8)))
           :in-theory (e/d (unsigned-byte-p) (adt-tp-wd-bound)))))

(defthm adt-tp-u64s-pack
  (implies (adt-octetsp o) (adt-tp-u64s (adt-tp-pack o)))
  :hints (("Goal" :induct (adt-tp-pack o)
           :in-theory (enable adt-tp-pack))))

(defthm adt-tp-u64s-append
  (equal (adt-tp-u64s (append a b))
         (and (adt-tp-u64s (true-list-fix a)) (adt-tp-u64s b))))

(defthm adt-tp-index-below-len
  (implies (member-equal v l) (< (adt-index v l) (len l)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable adt-index))))

(defthm adt-tp-enc-u64
  (implies (and (adt-tp-kind-ok k) (not (adt-octets-kind-p k)) (adt-val-okp k v))
           (unsigned-byte-p 64 (adt-enc k v)))
  :hints (("Goal" :in-theory (enable adt-enc unsigned-byte-p))))

(defthm adt-tp-u64s-fw
  (implies (and (adt-tp-schema-ok s) (adt-rec-p s rec) (adt-tp-rec-lens-ok s rec))
           (adt-tp-u64s (adt-tp-fw s rec)))
  :hints (("Goal" :induct (adt-tp-fw s rec))))

(defthm adt-tp-u64s-seq-words
  (implies (and (adt-tp-schema-ok s) (adt-seq-p s a) (adt-tp-seq-lens-ok s a))
           (adt-tp-u64s (adt-tp-seq-words s a)))
  :hints (("Goal" :induct (adt-tp-seq-words s a))))

(defun adt-tp-pages-wordsp (ps)
  ; Every page is 2048 u64 words: the shape the page store's host fill returns.
  (declare (xargs :verify-guards nil :guard t))
  (if (atom ps)
      (null ps)
    (and (equal (len (car ps)) *pgs-page-words*) (adt-tp-u64s (car ps))
         (adt-tp-pages-wordsp (cdr ps)))))

(defthm adt-tp-u64s-take
  (implies (adt-tp-u64s w) (adt-tp-u64s (adt-tp-take n w)))
  :hints (("Goal" :in-theory (enable adt-tp-take))))

(defthm adt-tp-u64s-zeros
  (adt-tp-u64s (adt-tp-zeros n))
  :hints (("Goal" :in-theory (enable adt-tp-zeros))))

(defthm adt-tp-u64s-nthcdr
  (implies (adt-tp-u64s w) (adt-tp-u64s (nthcdr n w))))

(defthm adt-tp-u64s-page
  (implies (adt-tp-u64s w) (adt-tp-u64s (adt-tp-page w)))
  :hints (("Goal" :in-theory (enable adt-tp-page))))

(defthm adt-tp-pages-wordsp-pages
  (implies (adt-tp-u64s w) (adt-tp-pages-wordsp (adt-tp-pages w)))
  :hints (("Goal" :induct (adt-tp-pages w)
           :in-theory (disable adt-tp-len-page))
          ("Subgoal *1/2" :use ((:instance adt-tp-len-page)))))

(defthm adt-tp-pages-of-wordsp
  (implies (and (adt-tp-schema-ok s) (adt-seq-p s a) (adt-tp-seq-lens-ok s a))
           (adt-tp-pages-wordsp (adt-tp-pages-of s a))))

; -----------------------------------------------------------------------------
; 5. Appending a LIST of rows (a checkpoint's delta is many records).  The
; words of the delta are one append to the tape, so the dirty set is the same
; one `adt-tp-dirty' computes, and its bound is the pages the delta's own
; words take, plus the one page it shares with the tape before it.

(defun adt-tp-extend-dirty (s a xs)
  (declare (xargs :verify-guards nil :guard t))
  (adt-tp-dirty (adt-tp-seq-words s a) (adt-tp-seq-words s xs)))

(defun adt-tp-rows-pages (s xs)
  (declare (xargs :verify-guards nil :guard t))
  (adt-tp-npages (len (adt-tp-seq-words s xs))))

(defthm adt-tp-pages-of-extend-is-apply-dirty
  (implies (and (adt-tp-schema-ok s) (adt-seq-p s a) (adt-seq-p s xs))
           (equal (pgs-apply-dirty (adt-tp-pages-of s a) (adt-tp-extend-dirty s a xs))
                  (adt-tp-pages-of s (append a xs))))
  :hints (("Goal" :in-theory (disable adt-tp-dirty-is-the-delta)
           :use ((:instance adt-tp-dirty-is-the-delta
                            (w (adt-tp-seq-words s a)) (n (adt-tp-seq-words s xs)))))))

(defthm adt-tp-extend-dirty-bound
  (<= (len (adt-tp-extend-dirty s a xs)) (+ 1 (adt-tp-rows-pages s xs)))
  :hints (("Goal" :in-theory (disable adt-tp-dirty-bound)
           :use ((:instance adt-tp-dirty-bound (w (adt-tp-seq-words s a)) (n (adt-tp-seq-words s xs)))))))

; -----------------------------------------------------------------------------
; 5b. The dirty set from the tape's summary.  The host does not hold the tape's
; words: it holds their count and reads the last partial page from the store.
; `adt-tp-dirty-at' takes exactly those, and is the dirty set (the delta's words
; are the only input that grows).

(defun adt-tp-dirty-at (cnt tail n)
  ; CNT: the tape's word count; TAIL: the words of its last partial page.
  (declare (xargs :guard (and (natp cnt) (true-listp tail) (true-listp n))))
  (if (atom n) nil (adt-tp-number (floor cnt *pgs-page-words*) (adt-tp-pages (append tail n)))))

(defthm adt-tp-dirty-at-is-dirty
  (implies (true-listp w)
           (equal (adt-tp-dirty-at (len w) (nthcdr (* *pgs-page-words* (floor (len w) *pgs-page-words*)) w) n)
                  (adt-tp-dirty w n)))
  :hints (("Goal" :in-theory (enable adt-tp-dirty-at adt-tp-dirty))))

(defun adt-tp-extend-dirty-at (s cnt tail xs)
  (declare (xargs :verify-guards nil :guard t))
  (adt-tp-dirty-at cnt tail (adt-tp-seq-words s xs)))

(defthm adt-tp-extend-dirty-at-is-extend-dirty
  (equal (adt-tp-extend-dirty-at s (len (adt-tp-seq-words s a))
           (nthcdr (* *pgs-page-words* (floor (len (adt-tp-seq-words s a)) *pgs-page-words*))
                   (adt-tp-seq-words s a))
           xs)
         (adt-tp-extend-dirty s a xs))
  :hints (("Goal" :in-theory (e/d (adt-tp-extend-dirty-at adt-tp-extend-dirty)
                                  (adt-tp-dirty-at-is-dirty adt-tp-dirty-at adt-tp-dirty))
           :use ((:instance adt-tp-dirty-at-is-dirty (w (adt-tp-seq-words s a)) (n (adt-tp-seq-words s xs)))))))

(defthm adt-tp-nthcdr-nthcdr
  (implies (and (natp a) (natp b))
           (equal (nthcdr a (nthcdr b x)) (nthcdr (+ a b) x))))

(defthm adt-tp-nth-of-pages
  (implies (and (natp k) (true-listp w) (< (* *pgs-page-words* k) (len w)))
           (equal (nth k (adt-tp-pages w)) (adt-tp-page (nthcdr (* *pgs-page-words* k) w))))
  :hints (("Goal" :induct (adt-tp-ind-k k w) :in-theory (disable adt-tp-page))
          ("Subgoal *1/2" :expand ((adt-tp-pages w)))
          ("Subgoal *1/1" :expand ((adt-tp-pages w)))))

(defthm adt-tp-take-of-len
  (implies (true-listp a) (equal (adt-tp-take (len a) a) a))
  :hints (("Goal" :in-theory (enable adt-tp-take))))

(defthm adt-tp-len-nthcdr-x
  (equal (len (nthcdr n w)) (nfix (- (len w) (nfix n)))))

(defthm adt-tp-mod-is-len-minus
  (implies (and (natp l) (equal k (floor l *pgs-page-words*)))
           (equal (mod l *pgs-page-words*) (- l (* *pgs-page-words* k))))
  :hints (("Goal" :in-theory (enable mod))))

(defthm adt-tp-tail-is-page-prefix
  ; The host reads TAIL from page K of the store: the first (CNT mod 2048) words
  ; of page K = floor(CNT / 2048), when the tape ends inside it.
  (implies (and (true-listp w) (natp k) (equal k (floor (len w) *pgs-page-words*))
                (< (* *pgs-page-words* k) (len w)))
           (equal (nthcdr (* *pgs-page-words* k) w)
                  (adt-tp-take (mod (len w) *pgs-page-words*) (nth k (adt-tp-pages w)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable adt-tp-page-short adt-tp-take-of-append adt-tp-take-of-len adt-tp-nth-of-pages)
           :use ((:instance adt-tp-nth-of-pages)
                 (:instance adt-tp-mod-is-len-minus (l (len w)))
                 (:instance adt-tp-page-short (w (nthcdr (* *pgs-page-words* k) w)))
                 (:instance adt-tp-take-of-append (n (mod (len w) *pgs-page-words*))
                            (a (nthcdr (* *pgs-page-words* k) w))
                            (b (adt-tp-zeros (- *pgs-page-words* (len (nthcdr (* *pgs-page-words* k) w))))))
                 (:instance adt-tp-take-of-len (a (nthcdr (* *pgs-page-words* k) w)))))))

; -----------------------------------------------------------------------------
; 6. Setting a row in place.  A rewrite of the M words at offset R into page K0
; changes only the pages those words touch (`adt-tp-region-dirty-is-the-delta');
; a row replaced by one of the same width (the paged catalog's withdraw and
; redecide rewrite columns of a row, never its octets' length) is such a
; rewrite.  The set's dirty pages are the row's own and the one it may share:
; no term in the length of the sequence.

(defthm adt-tp-nthcdr-nthcdr
  (implies (and (natp a) (natp b))
           (equal (nthcdr a (nthcdr b x)) (nthcdr (+ a b) x))))

(defun adt-tp-ind-nth (k w)
  (if (zp k) w (adt-tp-ind-nth (1- k) (nthcdr *pgs-page-words* w))))

(defthm adt-tp-nthcdr-pages
  ; The pages after the first K are the pages of the words after the first 2048 K.
  (implies (and (natp k) (true-listp w))
           (equal (nthcdr k (adt-tp-pages w))
                  (adt-tp-pages (nthcdr (* *pgs-page-words* k) w))))
  :hints (("Goal" :induct (adt-tp-ind-nth k w))
          ("Subgoal *1/2" :expand ((adt-tp-pages w)))))

(defun adt-tp-ind-xy (x y)
  (declare (xargs :measure (nfix y)))
  (if (zp y) x (adt-tp-ind-xy (nfix (- x *pgs-page-words*)) (nfix (- y *pgs-page-words*)))))

(defthm adt-tp-npages-mono
  (implies (and (natp x) (natp y) (<= x y))
           (<= (adt-tp-npages x) (adt-tp-npages y)))
  :hints (("Goal" :induct (adt-tp-ind-xy x y)
           :in-theory (enable adt-tp-npages))))

(defun adt-tp-ind-k2 (k)
  (if (zp k) 0 (adt-tp-ind-k2 (1- k))))

(defthm adt-tp-npages-plus-multiple
  (implies (and (natp k) (natp y))
           (equal (adt-tp-npages (+ (* *pgs-page-words* k) y)) (+ k (adt-tp-npages y))))
  :hints (("Goal" :induct (adt-tp-ind-k2 k)
           :in-theory (enable adt-tp-npages))))

(defthm adt-tp-le-npages-times
  (implies (natp x) (<= x (* *pgs-page-words* (adt-tp-npages x))))
  :rule-classes :linear
  :hints (("Goal" :induct (adt-tp-npages x) :in-theory (enable adt-tp-npages))))

(defthm adt-tp-split3
  (implies (and (true-listp l) (natp a) (natp c) (<= (+ a c) (len l)))
           (equal (append (take a l) (append (take c (nthcdr a l)) (nthcdr (+ a c) l))) l))
  :hints (("Goal" :use ((:instance adt-tp-take-nthcdr-split (m a) (w l))
                        (:instance adt-tp-take-nthcdr-split (m c) (w (nthcdr a l)))
                        (:instance adt-tp-nthcdr-nthcdr (a c) (b a) (x l)))
           :in-theory (disable adt-tp-take-nthcdr-split adt-tp-nthcdr-nthcdr))))

(defthm adt-tp-take-of-append2
  (implies (and (natp n) (<= n (len a)))
           (equal (take n (append a b)) (take n a)))
  :hints (("Goal" :in-theory (enable take))))

(defthm adt-tp-take-of-append-len
  (implies (and (equal pw (append x y)) (equal (len x) k) (true-listp x))
           (equal (take k pw) x))
  :hints (("Goal" :use ((:instance adt-tp-take-of-append2 (n k) (a x) (b y))
                        (:instance adt-tp-take-nthcdr-split (m k) (w x)))
           :in-theory (disable adt-tp-take-of-append2 adt-tp-take-nthcdr-split))))

(defthm adt-tp-take-pages
  ; The first K pages are the pages of the first 2048 K words.
  (implies (and (natp k) (true-listp w) (<= (* *pgs-page-words* k) (len w)))
           (equal (take k (adt-tp-pages w))
                  (adt-tp-pages (take (* *pgs-page-words* k) w))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance adt-tp-take-nthcdr-split (m (* *pgs-page-words* k)) (w w))
                 (:instance adt-tp-pages-of-append-aligned
                            (w1 (take (* *pgs-page-words* k) w)) (z (nthcdr (* *pgs-page-words* k) w)))
                 (:instance adt-tp-npages-of-multiple)
                 (:instance adt-tp-len-pages (w (take (* *pgs-page-words* k) w)))
                 (:instance adt-tp-take-of-append-len (pw (adt-tp-pages w))
                            (x (adt-tp-pages (take (* *pgs-page-words* k) w)))
                            (y (adt-tp-pages (nthcdr (* *pgs-page-words* k) w)))))
           :in-theory (disable adt-tp-take-nthcdr-split adt-tp-pages-of-append-aligned adt-tp-npages-of-multiple
                               adt-tp-len-pages adt-tp-pages-long adt-tp-take-of-append-len))))

(defun adt-tp-region-ind (a b ps)
  (if (atom ps) (list a b) (adt-tp-region-ind (append a (list (car ps))) (cdr b) (cdr ps))))

(defthm adt-tp-apply-dirty-region
  ; The dirty pages numbered from the end of A, as many as B has, replace B and leave C.
  (implies (and (true-listp a) (true-listp b) (true-listp c) (true-listp ps)
                (equal (len b) (len ps)))
           (equal (pgs-apply-dirty (append a b c) (adt-tp-number (len a) ps))
                  (append a ps c)))
  :hints (("Goal" :in-theory (enable pgs-apply-dirty)
           :induct (adt-tp-region-ind a b ps))))

(defthm adt-tp-len-take2
  (implies (and (natp n) (<= n (len x))) (equal (len (take n x)) n))
  :hints (("Goal" :in-theory (enable take))))

(defthm adt-tp-true-listp-take2
  (true-listp (take n x))
  :hints (("Goal" :in-theory (enable take))))

(defthm adt-tp-region-lists
  ; Two page lists agreeing before page K and from page K+C on: the C dirty
  ; pages of the second, numbered from K, turn the first into the second.
  (implies (and (true-listp l) (true-listp l2) (natp k) (natp c)
                (<= (+ k c) (len l)) (<= (+ k c) (len l2))
                (equal (take k l) (take k l2))
                (equal (nthcdr (+ k c) l) (nthcdr (+ k c) l2)))
           (equal (pgs-apply-dirty l (adt-tp-number k (take c (nthcdr k l2)))) l2))
  :hints (("Goal" :do-not-induct t
           :use ((:instance adt-tp-split3 (l l) (a k) (c c))
                 (:instance adt-tp-split3 (l l2) (a k) (c c))
                 (:instance adt-tp-apply-dirty-region
                            (a (take k l)) (b (take c (nthcdr k l))) (c (nthcdr (+ k c) l))
                            (ps (take c (nthcdr k l2))))
                 (:instance adt-tp-len-take2 (n k) (x l))
                 (:instance adt-tp-len-take2 (n c) (x (nthcdr k l)))
                 (:instance adt-tp-len-take2 (n c) (x (nthcdr k l2))))
           :in-theory (disable adt-tp-split3 adt-tp-apply-dirty-region adt-tp-len-take2))))

(defthm adt-tp-nthcdr-append-len
  (implies (and (true-listp a) (natp j))
           (equal (nthcdr (+ (len a) j) (append a b)) (nthcdr j b))))

(defun adt-tp-region-dirty (w2 k0 r m)
  ; The dirty pages of rewriting M words that start R words into page K0 of
  ; the tape W2: the pages the region touches, numbered from K0.
  (declare (xargs :guard t :verify-guards nil))
  (adt-tp-number k0 (take (adt-tp-npages (+ r m)) (nthcdr k0 (adt-tp-pages w2)))))

(defthm adt-tp-after-region
  ; The words after the pages a region touches do not depend on the region.
  (implies (and (true-listp p) (true-listp wr) (natp k0) (natp r) (natp c)
                (equal (len p) (+ (* *pgs-page-words* k0) r))
                (<= (+ r (len wr)) (* *pgs-page-words* c)))
           (equal (nthcdr (* *pgs-page-words* (+ k0 c)) (append p (append wr q)))
                  (nthcdr (+ (* *pgs-page-words* c) (- (+ r (len wr)))) q)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance adt-tp-nthcdr-append-len (a p) (b (append wr q))
                            (j (+ (len wr) (+ (* *pgs-page-words* c) (- (+ r (len wr)))))))
                 (:instance adt-tp-nthcdr-append-len (a wr) (b q)
                            (j (+ (* *pgs-page-words* c) (- (+ r (len wr)))))))
           :in-theory (disable adt-tp-nthcdr-append-len))))

(defthm adt-tp-take-words-of-append
  ; The words before page K0 do not depend on what follows P.
  (implies (and (true-listp p) (natp k0) (<= (* *pgs-page-words* k0) (len p)))
           (equal (take (* *pgs-page-words* k0) (append p z)) (take (* *pgs-page-words* k0) p)))
  :hints (("Goal" :use ((:instance adt-tp-take-of-append2 (n (* *pgs-page-words* k0)) (a p) (b z)))
           :in-theory (disable adt-tp-take-of-append2))))

(defthm adt-tp-region-dirty-is-the-delta
  ; Rewriting the M words at offset 2048 K0 + R of a tape, by M other words: the
  ; dirty pages of the new tape, applied to the old pages, give the new pages.
  (implies (and (true-listp p) (true-listp wr) (true-listp wx) (true-listp q)
                (natp k0) (natp r) (< r *pgs-page-words*) (natp m)
                (equal (len p) (+ (* *pgs-page-words* k0) r))
                (equal (len wr) m) (equal (len wx) m))
           (equal (pgs-apply-dirty (adt-tp-pages (append p (append wr q)))
                                   (adt-tp-region-dirty (append p (append wx q)) k0 r m))
                  (adt-tp-pages (append p (append wx q)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (adt-tp-region-dirty)
                           (adt-tp-region-lists adt-tp-take-pages adt-tp-nthcdr-pages adt-tp-after-region
                            adt-tp-npages-mono adt-tp-npages-plus-multiple adt-tp-len-pages
                            adt-tp-pages-long adt-tp-take-words-of-append adt-tp-le-npages-times))
           :use ((:instance adt-tp-region-lists
                            (l (adt-tp-pages (append p (append wr q))))
                            (l2 (adt-tp-pages (append p (append wx q))))
                            (k k0) (c (adt-tp-npages (+ r m))))
                 (:instance adt-tp-take-pages (k k0) (w (append p (append wr q))))
                 (:instance adt-tp-take-pages (k k0) (w (append p (append wx q))))
                 (:instance adt-tp-take-words-of-append (z (append wr q)))
                 (:instance adt-tp-take-words-of-append (z (append wx q)))
                 (:instance adt-tp-nthcdr-pages (k (+ k0 (adt-tp-npages (+ r m)))) (w (append p (append wr q))))
                 (:instance adt-tp-nthcdr-pages (k (+ k0 (adt-tp-npages (+ r m)))) (w (append p (append wx q))))
                 (:instance adt-tp-after-region (c (adt-tp-npages (+ r m))) (q q))
                 (:instance adt-tp-after-region (c (adt-tp-npages (+ r m))) (wr wx) (q q))
                 (:instance adt-tp-le-npages-times (x (+ r m)))
                 (:instance adt-tp-len-pages (w (append p (append wr q))))
                 (:instance adt-tp-len-pages (w (append p (append wx q))))
                 (:instance adt-tp-npages-mono (x (+ (* *pgs-page-words* k0) r m))
                            (y (len (append p (append wr q)))))
                 (:instance adt-tp-npages-mono (x (+ (* *pgs-page-words* k0) r m))
                            (y (len (append p (append wx q)))))
                 (:instance adt-tp-npages-plus-multiple (k k0) (y (+ r m)))))))

; -----------------------------------------------------------------------------
; Setting a row in place (a same-width rewrite).

(defthm adt-tp-floor-mod
  (implies (natp x)
           (and (natp (floor x *pgs-page-words*)) (natp (mod x *pgs-page-words*))
                (< (mod x *pgs-page-words*) *pgs-page-words*)
                (equal x (+ (* *pgs-page-words* (floor x *pgs-page-words*)) (mod x *pgs-page-words*)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable floor mod))))

(defthm adt-tp-split-row
  (implies (and (true-listp a) (natp i) (< i (len a)))
           (and (equal a (append (take i a) (cons (nth i a) (nthcdr (+ 1 i) a))))
                (equal (update-nth i x a) (append (take i a) (cons x (nthcdr (+ 1 i) a))))
                (true-listp (take i a)) (true-listp (nthcdr (+ 1 i) a))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable take update-nth nth) :induct (take i a))))

(defun adt-tp-set-dirty (s a i x)
  ; The dirty pages of setting row I of A to X, when X has the width of the row it replaces.
  (declare (xargs :verify-guards nil :guard t))
  (let ((off (len (adt-tp-seq-words s (take i a)))))
    (adt-tp-region-dirty (adt-tp-seq-words s (update-nth i x a))
                         (floor off *pgs-page-words*) (mod off *pgs-page-words*)
                         (len (adt-tp-rw s x)))))

(defthm adt-tp-take-len-append
  (implies (true-listp a1) (equal (take (len a1) (append a1 y)) a1))
  :hints (("Goal" :in-theory (enable take))))

(defthm adt-tp-update-nth-len-append
  (implies (true-listp a1)
           (equal (update-nth (len a1) x (append a1 (cons r a2))) (append a1 (cons x a2))))
  :hints (("Goal" :in-theory (enable update-nth))))

(defthm adt-tp-seq-words-of-row-split
  (implies (and (true-listp a1))
           (equal (adt-tp-seq-words s (append a1 (cons r a2)))
                  (append (adt-tp-seq-words s a1)
                          (append (adt-tp-rw s r) (adt-tp-seq-words s a2)))))
  :hints (("Goal" :in-theory (enable adt-tp-seq-words))))

(defthm adt-tp-pages-of-set-split
  (implies (and (equal a (append a1 (cons r a2))) (equal i (len a1)) (true-listp a1)
                (adt-tp-schema-ok s) (adt-seq-p s a1) (adt-seq-p s a2)
                (adt-rec-p s r) (adt-rec-p s x)
                (equal (len (adt-tp-rw s x)) (len (adt-tp-rw s r))))
           (equal (pgs-apply-dirty (adt-tp-pages-of s a) (adt-tp-set-dirty s a i x))
                  (adt-tp-pages-of s (update-nth i x a))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (adt-tp-pages-of adt-tp-set-dirty)
                           (adt-tp-region-dirty-is-the-delta adt-tp-region-dirty))
           :use ((:instance adt-tp-floor-mod (x (len (adt-tp-seq-words s a1))))
                 (:instance adt-tp-region-dirty-is-the-delta
                            (p (adt-tp-seq-words s a1))
                            (wr (adt-tp-rw s r)) (wx (adt-tp-rw s x))
                            (q (adt-tp-seq-words s a2))
                            (k0 (floor (len (adt-tp-seq-words s a1)) *pgs-page-words*))
                            (r (mod (len (adt-tp-seq-words s a1)) *pgs-page-words*))
                            (m (len (adt-tp-rw s x))))))))

(defthm adt-tp-seq-p-true-listp
  (implies (adt-seq-p s a) (true-listp a))
  :rule-classes :forward-chaining)

(defthm adt-tp-seq-p-take
  (implies (and (adt-seq-p s a) (natp i) (<= i (len a))) (adt-seq-p s (take i a)))
  :hints (("Goal" :in-theory (enable take adt-seq-p) :induct (take i a))))

(defthm adt-tp-seq-p-nthcdr
  (implies (adt-seq-p s a) (adt-seq-p s (nthcdr i a)))
  :hints (("Goal" :in-theory (enable adt-seq-p nthcdr))))

(defthm adt-tp-rec-p-nth
  (implies (and (adt-seq-p s a) (natp i) (< i (len a))) (adt-rec-p s (nth i a)))
  :hints (("Goal" :in-theory (enable adt-seq-p nth))))

(defthm adt-tp-pages-of-set-is-apply-dirty
  (implies (and (adt-tp-schema-ok s) (adt-seq-p s a) (natp i) (< i (len a)) (adt-rec-p s x)
                (equal (len (adt-tp-rw s x)) (len (adt-tp-rw s (nth i a)))))
           (equal (pgs-apply-dirty (adt-tp-pages-of s a) (adt-tp-set-dirty s a i x))
                  (adt-tp-pages-of s (update-nth i x a))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable adt-tp-len-take2)
           :use ((:instance adt-tp-split-row (a a) (i i))
                 (:instance adt-tp-len-take2 (n i) (x a))
                 (:instance adt-tp-pages-of-set-split
                            (a1 (take i a)) (r (nth i a)) (a2 (nthcdr (+ 1 i) a)))))))

(defthm adt-tp-len-take-le
  (<= (len (take n x)) (nfix n))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable take))))

(defthm adt-tp-len-region-dirty
  (<= (len (adt-tp-region-dirty w2 k0 r m)) (adt-tp-npages (+ r m)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (adt-tp-region-dirty) (adt-tp-len-take-le))
           :use ((:instance adt-tp-len-take-le (n (adt-tp-npages (+ r m))) (x (nthcdr k0 (adt-tp-pages w2))))))))

(defthm adt-tp-set-dirty-bound
  ; The row's own pages and the one page it may share: no term in the length of the sequence.
  (<= (len (adt-tp-set-dirty s a i x)) (+ 1 (adt-tp-npages (len (adt-tp-rw s x)))))
  :hints (("Goal" :in-theory (e/d (adt-tp-set-dirty) (adt-tp-len-region-dirty adt-tp-npages-subadd))
           :use ((:instance adt-tp-len-region-dirty
                            (w2 (adt-tp-seq-words s (update-nth i x a)))
                            (k0 (floor (len (adt-tp-seq-words s (take i a))) *pgs-page-words*))
                            (r (mod (len (adt-tp-seq-words s (take i a))) *pgs-page-words*))
                            (m (len (adt-tp-rw s x))))
                 (:instance adt-tp-floor-mod (x (len (adt-tp-seq-words s (take i a)))))
                 (:instance adt-tp-npages-subadd
                            (x (mod (len (adt-tp-seq-words s (take i a))) *pgs-page-words*))
                            (y (len (adt-tp-rw s x))))))))

; -----------------------------------------------------------------------------
; Setting a row to a WIDER one (a row whose remainder tree grows: the paged
; catalog's withdraw of an escaped row).  The rows after row I shift, so the
; dirty set is the new tape's pages from the one row I starts in to its end:
; `adt-tp-set-dirty-widening'.  A row that does not narrow is the premise:
; `pgs-apply-dirty' replaces and appends pages and cannot drop one, so a
; narrower row that lost a page would not be reachable by any dirty set.

(defun adt-tp-widen-dirty (w k0)
  ; The pages of the tape W from page K0 to its end, numbered from K0.
  (declare (xargs :guard (natp k0) :verify-guards nil))
  (adt-tp-number k0 (nthcdr k0 (adt-tp-pages w))))

(defthm adt-tp-len-npages-ge-k
  (implies (and (natp k) (<= (* *pgs-page-words* k) n) (natp n))
           (<= k (adt-tp-npages n)))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance adt-tp-npages-mono (x (* *pgs-page-words* k)) (y n))
                        (:instance adt-tp-npages-of-multiple))
           :in-theory (disable adt-tp-npages-mono adt-tp-npages-of-multiple))))


(defthm adt-tp-widen-dirty-core
  (implies (and (true-listp wo) (true-listp wn) (natp k0)
                (<= (* *pgs-page-words* k0) (len wo))
                (<= (len wo) (len wn))
                (equal (take (* *pgs-page-words* k0) wo) (take (* *pgs-page-words* k0) wn)))
           (equal (pgs-apply-dirty (adt-tp-pages wo) (adt-tp-widen-dirty wn k0))
                  (adt-tp-pages wn)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (adt-tp-widen-dirty)
                           (adt-tp-apply-dirty-number adt-tp-take-pages adt-tp-len-pages adt-tp-npages-mono
                            adt-tp-take-nthcdr-split adt-tp-len-npages-ge-k adt-tp-pages))
           :use ((:instance adt-tp-apply-dirty-number
                            (a (take k0 (adt-tp-pages wo)))
                            (b (nthcdr k0 (adt-tp-pages wo)))
                            (ps (nthcdr k0 (adt-tp-pages wn))))
                 (:instance adt-tp-take-nthcdr-split (m k0) (w (adt-tp-pages wo)))
                 (:instance adt-tp-take-nthcdr-split (m k0) (w (adt-tp-pages wn)))
                 (:instance adt-tp-take-pages (k k0) (w wo))
                 (:instance adt-tp-take-pages (k k0) (w wn))
                 (:instance adt-tp-len-pages (w wo))
                 (:instance adt-tp-len-pages (w wn))
                 (:instance adt-tp-len-npages-ge-k (n (len wo)))
                 (:instance adt-tp-len-npages-ge-k (n (len wn)))
                 (:instance adt-tp-npages-mono (x (len wo)) (y (len wn)))))))

(defun adt-tp-set-dirty-widening (s a i x)
  ; The dirty pages of setting row I of A to X, whatever the width of X: the pages
  ; of the new tape from the one row I starts in to its end.
  (declare (xargs :verify-guards nil :guard t))
  (adt-tp-widen-dirty (adt-tp-seq-words s (update-nth i x a))
                      (floor (len (adt-tp-seq-words s (take i a))) *pgs-page-words*)))

(defthm adt-tp-seq-words-append
  (equal (adt-tp-seq-words s (append a b))
         (append (adt-tp-seq-words s a) (adt-tp-seq-words s b)))
  :hints (("Goal" :in-theory (enable adt-tp-seq-words))))


(defthm adt-tp-pages-of-set-widening-split
  (implies (and (equal a (append a1 (cons r a2))) (equal i (len a1)) (true-listp a1)
                (adt-tp-schema-ok s) (adt-seq-p s a1) (adt-seq-p s a2)
                (adt-rec-p s r) (adt-rec-p s x)
                (<= (len (adt-tp-rw s r)) (len (adt-tp-rw s x))))
           (equal (pgs-apply-dirty (adt-tp-pages-of s a) (adt-tp-set-dirty-widening s a i x))
                  (adt-tp-pages-of s (update-nth i x a))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (adt-tp-pages-of adt-tp-set-dirty-widening)
                           (adt-tp-widen-dirty-core adt-tp-take-words-of-append adt-tp-widen-dirty))
           :use ((:instance adt-tp-floor-mod (x (len (adt-tp-seq-words s a1))))
                 (:instance adt-tp-widen-dirty-core
                            (wo (append (adt-tp-seq-words s a1) (append (adt-tp-rw s r) (adt-tp-seq-words s a2))))
                            (wn (append (adt-tp-seq-words s a1) (append (adt-tp-rw s x) (adt-tp-seq-words s a2))))
                            (k0 (floor (len (adt-tp-seq-words s a1)) *pgs-page-words*)))
                 (:instance adt-tp-take-words-of-append
                            (p (adt-tp-seq-words s a1))
                            (k0 (floor (len (adt-tp-seq-words s a1)) *pgs-page-words*))
                            (z (append (adt-tp-rw s r) (adt-tp-seq-words s a2))))
                 (:instance adt-tp-take-words-of-append
                            (p (adt-tp-seq-words s a1))
                            (k0 (floor (len (adt-tp-seq-words s a1)) *pgs-page-words*))
                            (z (append (adt-tp-rw s x) (adt-tp-seq-words s a2))))))))

(defthm adt-tp-pages-of-set-widening-is-apply-dirty
  (implies (and (adt-tp-schema-ok s) (adt-seq-p s a) (natp i) (< i (len a)) (adt-rec-p s x)
                (<= (len (adt-tp-rw s (nth i a))) (len (adt-tp-rw s x))))
           (equal (pgs-apply-dirty (adt-tp-pages-of s a) (adt-tp-set-dirty-widening s a i x))
                  (adt-tp-pages-of s (update-nth i x a))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable adt-tp-len-take2)
           :use ((:instance adt-tp-split-row (a a) (i i))
                 (:instance adt-tp-len-take2 (n i) (x a))
                 (:instance adt-tp-pages-of-set-widening-split
                            (a1 (take i a)) (r (nth i a)) (a2 (nthcdr (+ 1 i) a)))))))

(defthm adt-tp-nthcdr-update-nth
  (implies (and (natp i) (< i (len a)))
           (equal (nthcdr i (update-nth i x a)) (cons x (nthcdr (+ 1 i) a))))
  :hints (("Goal" :in-theory (enable update-nth nthcdr) :induct (update-nth i x a))))

(defthm adt-tp-len-seq-words-update-nth
  (implies (and (natp i) (< i (len a)))
           (equal (len (adt-tp-seq-words s (update-nth i x a)))
                  (+ (len (adt-tp-seq-words s (take i a)))
                     (len (adt-tp-seq-words s (cons x (nthcdr (+ 1 i) a)))))))
  :hints (("Goal" :in-theory (enable take update-nth nthcdr adt-tp-seq-words) :induct (update-nth i x a))))

(defthm adt-tp-npages-tail-bound2
  (implies (and (natp o) (natp l) (equal n (+ o l)))
           (<= (adt-tp-npages (+ n (- (* *pgs-page-words* (floor o *pgs-page-words*)))))
               (+ 1 (adt-tp-npages l))))
  :rule-classes :linear
  :hints (("Goal" :do-not-induct t
           :in-theory (disable adt-tp-npages-subadd adt-tp-npages-plus-multiple floor)
           :use ((:instance adt-tp-floor-mod (x o))
                 (:instance adt-tp-npages-subadd (x (mod o *pgs-page-words*)) (y l))))))

(defthm adt-tp-set-dirty-widening-bound
  ; The new tape's pages from the row's own on: the row's pages, the rows after it, and the page it may share.
  (implies (and (natp i) (< i (len a)))
           (<= (len (adt-tp-set-dirty-widening s a i x))
               (+ 1 (adt-tp-npages (len (adt-tp-seq-words s (nthcdr i (update-nth i x a))))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (adt-tp-set-dirty-widening adt-tp-widen-dirty)
                           (adt-tp-npages-tail-bound2 adt-tp-len-seq-words-update-nth floor adt-tp-len-npages-ge-k))
           :use ((:instance adt-tp-len-seq-words-update-nth)
                 (:instance adt-tp-nthcdr-update-nth)
                 (:instance adt-tp-npages-tail-bound2
                            (o (len (adt-tp-seq-words s (take i a))))
                            (l (len (adt-tp-seq-words s (cons x (nthcdr (+ 1 i) a)))))
                            (n (len (adt-tp-seq-words s (update-nth i x a)))))))))
