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
  ; The words N octets take.
  (declare (xargs :verify-guards nil :guard t :measure (nfix n)))
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
