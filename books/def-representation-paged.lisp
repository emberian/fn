; fn: the PAGED foundation of `def-representation' (lane gate-b,
; 2026-10-01; stage 3 Gate B of
; planning/design-store-representation-2026-10-01.md; D27).
;
; The columnar foundation of books/proto/adt-lib.lisp keeps each column in
; one resizable array and the octets in one pool, and grows each by
; DOUBLING: the step that crosses a capacity allocates (and copies) as much
; as everything before it.  Here the same schema is kept in fixed PAGES:
; a row page holds R rows of every column (one typed array per column),
; a pool page Q octets.  Growth adds one row page (and, for a record's
; octets, the pool pages they need); no page is ever copied and no octet
; ever moves, so what one append allocates is bounded by one row page,
; its own octets and a pool page, whatever the count.  The page TABLES
; still double their pointers when full (O(N/R) words, an empty page
; header per slot), as books/payload-arena-paged.lisp's does.
;
; The abstraction is books/payload-arena-paged.lisp's, made generic over
; the schema: the pages of column CI concatenated (`adt-pg-col') are the
; library's column CI; the pool pages concatenated are its pool, and the
; FLAT VIEW `adt-pg-flat' of a paged image is a library image.  The paged
; correspondence `adt-pg-corr' is the library's `adt-corr' of the flat view
; with the page invariant `adt-pg-okp' (every page in use is a full page).
; Each paged operation is proved ONCE here against the flat view: a page
; write is the flat column's `update-nth', a page added is the flat column
; extended by a page of zeros (`adt-pg-flat-of-addrow'), and the growth
; itself keeps `adt-corr' (`adt-corr-of-grow-cols', `adt-corr-of-grow-pool':
; the library's correspondence reads a column below the count and the pool
; below the fill, nothing above).  With the room made first, the paged
; append, set, reads and clear are the library's operations on the flat
; view, so the library's adt-corr-* theorems carry over unchanged
; (adt-pg-corr-append, -set, -get, -count, -clear, -empty).
;
; The layout of a paged image (the logical image of the generated
; foundation NAME$C, books/proto/adt.lisp `adt-pg-foundation-events'):
;   0 the row page table   (each page the list of its P column arrays)
;   1 the pool page table  (each page the one-element list of its octets)
;   2 the count  3 the fill  4 pages in use  5 pool pages in use.

(in-package "ACL2")
(include-book "proto/adt-lib")
(include-book "proto/adt-load")
(local (include-book "arithmetic/top" :dir :system))
(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))

(local (in-theory (disable nth update-nth resize-list floor mod)))

; -----------------------------------------------------------------------------
; 1. A column of a page table: column CI of the first NP pages, in order.

(defun adt-pg-col (ci np rt)
  (declare (xargs :guard (and (natp ci) (natp np)) :verify-guards nil))
  (if (or (zp np) (atom rt))
      nil
    (append (nth ci (car rt)) (adt-pg-col ci (1- np) (cdr rt)))))

; Every page in use holds R entries in each of its first K columns.
(defun adt-pg-pagefullp (k r pg)
  (declare (xargs :guard (natp k) :verify-guards nil))
  (if (zp k)
      t
    (and (equal (len (nth (1- k) pg)) r)
         (adt-pg-pagefullp (1- k) r pg))))

(defun adt-pg-fullp (k r np rt)
  (declare (xargs :guard (and (natp k) (natp np)) :verify-guards nil))
  (if (zp np)
      t
    (and (consp rt)
         (adt-pg-pagefullp k r (car rt))
         (adt-pg-fullp k r (1- np) (cdr rt)))))

(local
 (defthm adt-pg-len-append
   (equal (len (append a b)) (+ (len a) (len b)))))

(local
 (defthm adt-pg-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

(local
 (defthm adt-pg-nth-append
   (equal (nth n (append a b))
          (if (< (nfix n) (len a)) (nth n a) (nth (- (nfix n) (len a)) b)))
   :hints (("Goal" :in-theory (enable nth)))))

(local
 (defthm adt-pg-update-nth-append
   (implies (natp n)
            (equal (update-nth n v (append a b))
                   (if (< n (len a))
                       (append (update-nth n v a) b)
                     (append a (update-nth (- n (len a)) v b)))))
   :hints (("Goal" :in-theory (enable update-nth)))))

(local
 (defthm adt-pg-len-update-nth-within
   (implies (< (nfix j) (len l))
            (equal (len (update-nth j v l)) (len l)))
   :hints (("Goal" :in-theory (enable update-nth)))))

(defthm adt-pg-pagefullp-nth
  (implies (and (adt-pg-pagefullp k r pg) (natp ci) (< ci (nfix k)))
           (equal (len (nth ci pg)) r)))

(defthm adt-pg-true-listp-col
  (true-listp (adt-pg-col ci np rt)))

(defthm adt-pg-len-col
  (implies (and (adt-pg-fullp k r np rt) (natp ci) (< ci (nfix k)) (natp np))
           (equal (len (adt-pg-col ci np rt)) (* r np))))

(defthm adt-pg-fullp-len
  (implies (and (adt-pg-fullp k r np rt) (natp np))
           (<= np (len rt)))
  :rule-classes :linear)

(local
 (defun adt-pg-two-induct (np rt kk)
   (if (or (zp np) (atom rt))
       (list np rt kk)
     (adt-pg-two-induct (1- np) (cdr rt) (1- kk)))))

(local
 (defthm adt-pg-kk-r
   (implies (and (natp r) (integerp kk) (< 0 kk)) (<= r (* kk r)))
   :rule-classes :linear))

; A read of the flat column at page KK, index J is that page's entry J.
(defthm adt-pg-nth-col
  (implies (and (adt-pg-fullp k r np rt) (natp np) (natp ci) (< ci (nfix k))
                (natp kk) (< kk np) (natp r) (natp j) (< j r))
           (equal (nth (+ j (* r kk)) (adt-pg-col ci np rt))
                  (nth j (nth ci (nth kk rt)))))
  :hints (("Goal" :induct (adt-pg-two-induct np rt kk)
           :in-theory (enable nth))))

; A write of page KK's column CI at J is the flat column's update at the same
; place; the other columns are unchanged.
(defun adt-pg-pw (kk ci j x rt)
  (declare (xargs :verify-guards nil))
  (update-nth kk (update-nth ci (update-nth j x (nth ci (nth kk rt))) (nth kk rt)) rt))

(defthm adt-pg-col-of-pw-same
  (implies (and (adt-pg-fullp k r np rt) (natp np) (natp ci) (< ci (nfix k))
                (natp kk) (< kk np) (natp r) (natp j) (< j r))
           (equal (adt-pg-col ci np (adt-pg-pw kk ci j x rt))
                  (update-nth (+ j (* r kk)) x (adt-pg-col ci np rt))))
  :hints (("Goal" :induct (adt-pg-two-induct np rt kk)
           :in-theory (enable nth update-nth))))

(defthm adt-pg-col-of-pw-other
  (implies (and (natp ci) (natp ci2) (not (equal ci ci2)) (natp kk) (< kk (len rt)))
           (equal (adt-pg-col ci2 np (adt-pg-pw kk ci j x rt))
                  (adt-pg-col ci2 np rt)))
  :hints (("Goal" :induct (adt-pg-two-induct np rt kk)
           :in-theory (enable nth update-nth adt-pg-pw))))

(defthm adt-pg-pagefullp-of-update-nth
  (implies (and (adt-pg-pagefullp k r pg) (natp ci) (equal (len v) (len (nth ci pg))))
           (adt-pg-pagefullp k r (update-nth ci v pg)))
  :hints (("Goal" :induct (adt-pg-pagefullp k r pg))))

(defthm adt-pg-fullp-of-update-nth
  (implies (and (adt-pg-fullp k r np rt) (natp np) (natp kk) (< kk np)
                (adt-pg-pagefullp k r pg))
           (adt-pg-fullp k r np (update-nth kk pg rt)))
  :hints (("Goal" :induct (adt-pg-two-induct np rt kk)
           :in-theory (enable update-nth))))

(defthm adt-pg-pagefullp-nth-page
  (implies (and (adt-pg-fullp k r np rt) (natp kk) (< kk (nfix np)))
           (adt-pg-pagefullp k r (nth kk rt)))
  :hints (("Goal" :induct (adt-pg-two-induct np rt kk)
           :in-theory (enable nth))))

(defthm adt-pg-fullp-of-pw
  (implies (and (adt-pg-fullp k r np rt) (natp np) (natp ci)
                (natp kk) (< kk np) (natp j) (< j (len (nth ci (nth kk rt)))))
           (adt-pg-fullp k r np (adt-pg-pw kk ci j x rt)))
  :hints (("Goal" :in-theory (enable adt-pg-pw))))

; The flat view reads only the first NP pages.
(defthm adt-pg-col-of-update-nth-above
  (implies (and (natp np) (natp kk) (<= np kk) (< kk (len rt)))
           (equal (adt-pg-col ci np (update-nth kk v rt))
                  (adt-pg-col ci np rt)))
  :hints (("Goal" :induct (adt-pg-two-induct np rt kk)
           :in-theory (enable update-nth))))

(defthm adt-pg-fullp-of-update-nth-above
  (implies (and (natp np) (natp kk) (<= np kk) (<= np (len rt)))
           (equal (adt-pg-fullp k r np (update-nth kk v rt))
                  (adt-pg-fullp k r np rt)))
  :hints (("Goal" :induct (adt-pg-two-induct np rt kk)
           :in-theory (enable update-nth))))

(local
 (defun adt-pg-resize-ind (np rt m)
   (if (or (zp np) (atom rt))
       (list rt m)
     (adt-pg-resize-ind (1- np) (cdr rt) (1- m)))))

(local
 (defthm adt-pg-resize-list-open
   (implies (posp n)
            (equal (resize-list l n d)
                   (cons (if (atom l) d (car l))
                         (resize-list (if (atom l) l (cdr l)) (1- n) d))))
   :hints (("Goal" :in-theory (enable resize-list)))))

(defthm adt-pg-col-of-resize-list
  (implies (and (natp np) (<= np (len rt)) (natp m) (<= np m))
           (equal (adt-pg-col ci np (resize-list rt m d))
                  (adt-pg-col ci np rt)))
  :hints (("Goal" :induct (adt-pg-resize-ind np rt m))))

(defthm adt-pg-fullp-of-resize-list
  (implies (and (natp np) (<= np (len rt)) (natp m) (<= np m))
           (equal (adt-pg-fullp k r np (resize-list rt m d))
                  (adt-pg-fullp k r np rt)))
  :hints (("Goal" :induct (adt-pg-resize-ind np rt m))))

(local (in-theory (disable adt-pg-resize-list-open)))

(defthm adt-pg-len-resize-list
  (equal (len (resize-list l n d)) (nfix n))
  :hints (("Goal" :in-theory (enable resize-list))))

; One page more: the flat column is the old one and the new page's entries.
(defthm adt-pg-col-snoc
  (implies (and (natp np) (< np (len rt)) (true-listp (nth ci (nth np rt))))
           (equal (adt-pg-col ci (1+ np) rt)
                  (append (adt-pg-col ci np rt) (nth ci (nth np rt)))))
  :hints (("Goal" :induct (adt-pg-col ci np rt) :in-theory (enable nth)
           :expand ((adt-pg-col ci 1 rt)))))

(defthm adt-pg-fullp-snoc
  (implies (and (natp np) (< np (len rt)))
           (equal (adt-pg-fullp k r (1+ np) rt)
                  (and (adt-pg-fullp k r np rt) (adt-pg-pagefullp k r (nth np rt)))))
  :hints (("Goal" :induct (adt-pg-col ci np rt) :in-theory (enable nth))))

(in-theory (disable adt-pg-col-snoc adt-pg-fullp-snoc adt-pg-pw))

; -----------------------------------------------------------------------------
; 2. The flat view of a paged image.

(defun adt-pg-cols (ci k np rt)
  (declare (xargs :guard (and (natp ci) (natp k) (natp np)) :verify-guards nil))
  (if (zp k)
      nil
    (cons (adt-pg-col ci np rt) (adt-pg-cols (1+ ci) (1- k) np rt))))

(defun adt-pg-flat (s c)
  (declare (xargs :verify-guards nil))
  (append (adt-pg-cols 0 (adt-ncols s) (nth 4 c) (nth 0 c))
          (list (adt-pg-col 0 (nth 5 c) (nth 1 c)) (nth 2 c) (nth 3 c))))

(defthm adt-pg-len-cols
  (equal (len (adt-pg-cols ci k np rt)) (nfix k)))

(local
 (defun adt-pg-nc-ind (m ci k)
   (if (or (zp k) (zp m)) (list m ci k) (adt-pg-nc-ind (1- m) (1+ ci) (1- k)))))

(defthm adt-pg-nth-cols
  (implies (and (natp m) (natp ci))
           (equal (nth m (adt-pg-cols ci k np rt))
                  (if (< m (nfix k)) (adt-pg-col (+ ci m) np rt) nil)))
  :hints (("Goal" :induct (adt-pg-nc-ind m ci k) :in-theory (enable nth)
           :expand ((adt-pg-cols ci k np rt)))))

(local
 (defthm adt-pg-update-nth-0-cons
   (equal (update-nth 0 v (cons a x)) (cons v x))
   :hints (("Goal" :in-theory (enable update-nth)))))

(local
 (defthm adt-pg-nth-list3
   (implies (and (integerp k) (<= 3 k)) (equal (nth k (list a b c)) nil))
   :hints (("Goal" :expand ((nth k (list a b c)) (nth (+ -1 k) (list b c))
                            (nth (+ -2 k) (list c)) (nth (+ -3 k) nil))))))

(defthm adt-pg-nth-flat
  (implies (natp m)
           (equal (nth m (adt-pg-flat s c))
                  (cond ((< m (adt-ncols s)) (adt-pg-col m (nth 4 c) (nth 0 c)))
                        ((equal m (adt-ncols s)) (adt-pg-col 0 (nth 5 c) (nth 1 c)))
                        ((equal m (+ 1 (adt-ncols s))) (nth 2 c))
                        ((equal m (+ 2 (adt-ncols s))) (nth 3 c))
                        (t nil))))
  :hints (("Goal" :cases ((< m (adt-ncols s)) (equal m (adt-ncols s))
                          (equal m (+ 1 (adt-ncols s))) (equal m (+ 2 (adt-ncols s)))))))

(defthm adt-pg-len-flat
  (equal (len (adt-pg-flat s c)) (+ 3 (adt-ncols s))))

(defthm adt-pg-true-listp-flat
  (true-listp (adt-pg-flat s c)))

; The flat view is a function of the tables, the counters and nothing else.
(defthm adt-pg-flat-of-update-np
  (implies (natp np)
           (equal (adt-pg-flat s (update-nth 4 np c))
                  (append (adt-pg-cols 0 (adt-ncols s) np (nth 0 c))
                          (list (adt-pg-col 0 (nth 5 c) (nth 1 c)) (nth 2 c) (nth 3 c))))))

(local
 (defthm adt-pg-cols-of-pw
   (implies (and (adt-pg-fullp k r np rt) (natp np) (natp ci) (< ci (nfix k)) (natp c0)
                 (natp kk) (< kk np) (natp r) (natp j) (< j r))
            (equal (adt-pg-cols c0 m np (adt-pg-pw kk ci j x rt))
                   (if (and (<= c0 ci) (< ci (+ c0 (nfix m))))
                       (update-nth (- ci c0) (update-nth (+ j (* r kk)) x (adt-pg-col ci np rt))
                                   (adt-pg-cols c0 m np rt))
                     (adt-pg-cols c0 m np rt))))
   :hints (("Goal" :induct (adt-pg-cols c0 m np rt) :in-theory (enable update-nth)))))

(local
 (defthm adt-pg-floor-mod
   (implies (and (natp n) (posp r))
            (and (natp (floor n r)) (natp (mod n r)) (< (mod n r) r)
                 (equal (+ (mod n r) (* r (floor n r))) n)))))

(local
 (defthm adt-pg-floor-below
   (implies (and (natp n) (posp r) (natp np) (< n (* r np)))
            (< (floor n r) np))
   :rule-classes :linear
   :hints (("Goal" :use adt-pg-floor-mod :in-theory (disable adt-pg-floor-mod)
            :nonlinearp t))))

; -----------------------------------------------------------------------------
; 3. The page invariant and the paged correspondence.  The row part (M
; columns of R rows a page) and the pool part (Q octets a page) are stated
; apart, so that every rule about a row operation binds its variables from
; the row invariant alone.

(defun adt-pg-rokp (m r c)
  (declare (xargs :verify-guards nil))
  (and (natp m) (posp r) (natp (nth 4 c)) (adt-pg-fullp m r (nth 4 c) (nth 0 c))))

(defun adt-pg-pokp (q c)
  (declare (xargs :verify-guards nil))
  (and (posp q) (natp (nth 5 c)) (adt-pg-fullp 1 q (nth 5 c) (nth 1 c))))

(defun adt-pg-okp (s r q c)
  (declare (xargs :verify-guards nil))
  (and (adt-pg-rokp (adt-ncols s) r c) (adt-pg-pokp q c)))

(defun adt-pg-corr (s r q c a)
  (declare (xargs :verify-guards nil))
  (and (adt-pg-okp s r q c)
       (adt-corr s (adt-pg-flat s c) a)))

(defthm adt-pg-rokp-fc
  (implies (adt-pg-rokp m r c) (and (natp m) (posp r) (natp (nth 4 c))))
  :rule-classes :forward-chaining)

(defthm adt-pg-pokp-fc
  (implies (adt-pg-pokp q c) (and (posp q) (natp (nth 5 c))))
  :rule-classes :forward-chaining)

; -----------------------------------------------------------------------------
; 4. The paged primitive operations (each instance's executables unfold to
; these, books/proto/adt.lisp), and their meaning on the flat view.

; Row N of column CI: page floor(N/R), entry N mod R.  Out of range (never,
; under the invariant) the write is nothing and the read 0.
(defun adt-pg-rput (ci n x r c)
  (declare (xargs :verify-guards nil))
  (let* ((rt (nth 0 c)) (k (floor n r)) (j (mod n r)))
    (if (< k (len rt))
        (update-nth 0 (update-nth k (if (< j (len (nth ci (nth k rt))))
                                        (update-nth ci (update-nth j x (nth ci (nth k rt))) (nth k rt))
                                      (nth k rt))
                                  rt)
                    c)
      c)))

(defun adt-pg-rget (ci n r c)
  (declare (xargs :verify-guards nil))
  (let* ((rt (nth 0 c)) (k (floor n r)) (j (mod n r)))
    (if (< k (len rt))
        (if (< j (len (nth ci (nth k rt)))) (nth j (nth ci (nth k rt))) 0)
      0)))

(defun adt-pg-pput (i b q c)
  (declare (xargs :verify-guards nil))
  (let* ((pt (nth 1 c)) (k (floor i q)) (j (mod i q)))
    (if (< k (len pt))
        (update-nth 1 (update-nth k (if (< j (len (nth 0 (nth k pt))))
                                        (update-nth 0 (update-nth j b (nth 0 (nth k pt))) (nth k pt))
                                      (nth k pt))
                                  pt)
                    c)
      c)))

(defun adt-pg-pget (i q c)
  (declare (xargs :verify-guards nil))
  (let* ((pt (nth 1 c)) (k (floor i q)) (j (mod i q)))
    (if (< k (len pt))
        (if (< j (len (nth 0 (nth k pt)))) (nth j (nth 0 (nth k pt))) 0)
      0)))

(local
 (defthm adt-pg-update-nth-nth-same
   (implies (and (natp k) (< k (len l)))
            (equal (update-nth k (nth k l) l) l))
   :hints (("Goal" :in-theory (enable nth update-nth)))))

(defthm adt-pg-nth-of-rput
  (implies (and (natp k) (not (equal k 0)))
           (equal (nth k (adt-pg-rput ci n x r c)) (nth k c))))

(defthm adt-pg-nth-of-pput
  (implies (and (natp k) (not (equal k 1)))
           (equal (nth k (adt-pg-pput i b q c)) (nth k c))))

(defthm adt-pg-pokp-of-rput
  (equal (adt-pg-pokp q (adt-pg-rput ci n x r c)) (adt-pg-pokp q c)))

(defthm adt-pg-rokp-of-pput
  (equal (adt-pg-rokp m r2 (adt-pg-pput i b q c)) (adt-pg-rokp m r2 c)))

(defthm adt-pg-flat-of-rput
  (implies (and (adt-pg-rokp (adt-ncols s) r c) (natp ci) (< ci (adt-ncols s))
                (natp n) (< n (* r (nth 4 c))))
           (equal (adt-pg-flat s (adt-pg-rput ci n x r c))
                  (update-nth ci (update-nth n x (nth ci (adt-pg-flat s c))) (adt-pg-flat s c))))
  :hints (("Goal" :in-theory (e/d (adt-pg-pw) (adt-pg-cols-of-pw adt-pg-floor-mod adt-pg-pagefullp-nth
                                               adt-pg-pagefullp-nth-page))
           :do-not-induct t
           :use ((:instance adt-pg-floor-mod)
                 (:instance adt-pg-floor-below (np (nth 4 c)))
                 (:instance adt-pg-pagefullp-nth (k (adt-ncols s)) (pg (nth (floor n r) (nth 0 c))))
                 (:instance adt-pg-pagefullp-nth-page (k (adt-ncols s)) (np (nth 4 c)) (rt (nth 0 c))
                            (kk (floor n r)))
                 (:instance adt-pg-cols-of-pw (k (adt-ncols s)) (np (nth 4 c)) (rt (nth 0 c))
                            (c0 0) (m (adt-ncols s)) (kk (floor n r)) (j (mod n r)))))))

(defthm adt-pg-rokp-of-rput
  (implies (and (adt-pg-rokp m r c) (natp ci) (< ci m)
                (natp n) (< n (* r (nth 4 c))))
           (adt-pg-rokp m r (adt-pg-rput ci n x r c)))
  :hints (("Goal" :in-theory (e/d (adt-pg-pw) (adt-pg-floor-mod adt-pg-fullp-of-pw adt-pg-pagefullp-nth
                                               adt-pg-pagefullp-nth-page))
           :do-not-induct t
           :use ((:instance adt-pg-floor-mod)
                 (:instance adt-pg-floor-below (np (nth 4 c)))
                 (:instance adt-pg-pagefullp-nth (k m) (pg (nth (floor n r) (nth 0 c))))
                 (:instance adt-pg-pagefullp-nth-page (k m) (np (nth 4 c)) (rt (nth 0 c))
                            (kk (floor n r)))
                 (:instance adt-pg-fullp-of-pw (k m) (np (nth 4 c)) (rt (nth 0 c))
                            (kk (floor n r)) (j (mod n r)))))))

(defthm adt-pg-rget-is-nth
  (implies (and (adt-pg-rokp m r c) (natp ci) (< ci m)
                (natp n) (< n (* r (nth 4 c))))
           (equal (adt-pg-rget ci n r c) (nth n (adt-pg-col ci (nth 4 c) (nth 0 c)))))
  :hints (("Goal" :in-theory (disable adt-pg-floor-mod adt-pg-nth-col adt-pg-pagefullp-nth
                                      adt-pg-pagefullp-nth-page)
           :do-not-induct t
           :use ((:instance adt-pg-floor-mod)
                 (:instance adt-pg-floor-below (np (nth 4 c)))
                 (:instance adt-pg-pagefullp-nth (k m) (pg (nth (floor n r) (nth 0 c))))
                 (:instance adt-pg-pagefullp-nth-page (k m) (np (nth 4 c)) (rt (nth 0 c))
                            (kk (floor n r)))
                 (:instance adt-pg-nth-col (k m) (np (nth 4 c)) (rt (nth 0 c))
                            (kk (floor n r)) (j (mod n r)))))))

(defthm adt-pg-flat-of-pput
  (implies (and (adt-pg-pokp q c) (natp i) (< i (* q (nth 5 c))))
           (equal (adt-pg-flat s (adt-pg-pput i b q c))
                  (update-nth (adt-ncols s) (update-nth i b (nth (adt-ncols s) (adt-pg-flat s c)))
                              (adt-pg-flat s c))))
  :hints (("Goal" :in-theory (e/d (adt-pg-pw) (adt-pg-floor-mod adt-pg-col-of-pw-same adt-pg-pagefullp-nth
                                               adt-pg-pagefullp-nth-page))
           :do-not-induct t
           :use ((:instance adt-pg-floor-mod (n i) (r q))
                 (:instance adt-pg-floor-below (n i) (r q) (np (nth 5 c)))
                 (:instance adt-pg-pagefullp-nth (k 1) (r q) (ci 0) (pg (nth (floor i q) (nth 1 c))))
                 (:instance adt-pg-pagefullp-nth-page (k 1) (r q) (np (nth 5 c)) (rt (nth 1 c))
                            (kk (floor i q)))
                 (:instance adt-pg-col-of-pw-same (k 1) (r q) (np (nth 5 c)) (rt (nth 1 c))
                            (ci 0) (x b) (kk (floor i q)) (j (mod i q)))))))

(defthm adt-pg-pool-of-pput
  (implies (and (adt-pg-pokp q c) (natp i) (< i (* q (nth 5 c))))
           (equal (adt-pg-col 0 (nth 5 c) (nth 1 (adt-pg-pput i b q c)))
                  (update-nth i b (adt-pg-col 0 (nth 5 c) (nth 1 c)))))
  :hints (("Goal" :in-theory (e/d (adt-pg-pw) (adt-pg-floor-mod adt-pg-col-of-pw-same adt-pg-pagefullp-nth
                                               adt-pg-pagefullp-nth-page))
           :do-not-induct t
           :use ((:instance adt-pg-floor-mod (n i) (r q))
                 (:instance adt-pg-floor-below (n i) (r q) (np (nth 5 c)))
                 (:instance adt-pg-pagefullp-nth (k 1) (r q) (ci 0) (pg (nth (floor i q) (nth 1 c))))
                 (:instance adt-pg-pagefullp-nth-page (k 1) (r q) (np (nth 5 c)) (rt (nth 1 c))
                            (kk (floor i q)))
                 (:instance adt-pg-col-of-pw-same (k 1) (r q) (np (nth 5 c)) (rt (nth 1 c))
                            (ci 0) (x b) (kk (floor i q)) (j (mod i q)))))))

(defthm adt-pg-pokp-of-pput
  (implies (and (adt-pg-pokp q c) (natp i) (< i (* q (nth 5 c))))
           (adt-pg-pokp q (adt-pg-pput i b q c)))
  :hints (("Goal" :in-theory (e/d (adt-pg-pw) (adt-pg-floor-mod adt-pg-fullp-of-pw adt-pg-pagefullp-nth
                                               adt-pg-pagefullp-nth-page))
           :do-not-induct t
           :use ((:instance adt-pg-floor-mod (n i) (r q))
                 (:instance adt-pg-floor-below (n i) (r q) (np (nth 5 c)))
                 (:instance adt-pg-pagefullp-nth (k 1) (r q) (ci 0) (pg (nth (floor i q) (nth 1 c))))
                 (:instance adt-pg-pagefullp-nth-page (k 1) (r q) (np (nth 5 c)) (rt (nth 1 c))
                            (kk (floor i q)))
                 (:instance adt-pg-fullp-of-pw (k 1) (r q) (np (nth 5 c)) (rt (nth 1 c))
                            (ci 0) (x b) (kk (floor i q)) (j (mod i q)))))))

(defthm adt-pg-pget-is-nth
  (implies (and (adt-pg-pokp q c) (natp i) (< i (* q (nth 5 c))))
           (equal (adt-pg-pget i q c) (nth i (adt-pg-col 0 (nth 5 c) (nth 1 c)))))
  :hints (("Goal" :in-theory (disable adt-pg-floor-mod adt-pg-nth-col adt-pg-pagefullp-nth
                                      adt-pg-pagefullp-nth-page)
           :do-not-induct t
           :use ((:instance adt-pg-floor-mod (n i) (r q))
                 (:instance adt-pg-floor-below (n i) (r q) (np (nth 5 c)))
                 (:instance adt-pg-pagefullp-nth (k 1) (r q) (ci 0) (pg (nth (floor i q) (nth 1 c))))
                 (:instance adt-pg-pagefullp-nth-page (k 1) (r q) (np (nth 5 c)) (rt (nth 1 c))
                            (kk (floor i q)))
                 (:instance adt-pg-nth-col (k 1) (r q) (np (nth 5 c)) (rt (nth 1 c)) (ci 0)
                            (kk (floor i q)) (j (mod i q)))))))

(defthm adt-pg-rokp-of-update
  (implies (and (natp k) (not (equal k 0)) (not (equal k 4)))
           (equal (adt-pg-rokp m r (update-nth k x c)) (adt-pg-rokp m r c))))

(defthm adt-pg-pokp-of-update
  (implies (and (natp k) (not (equal k 1)) (not (equal k 5)))
           (equal (adt-pg-pokp q (update-nth k x c)) (adt-pg-pokp q c))))

(defthm adt-pg-len-col-rokp
  (implies (and (adt-pg-rokp m r c) (natp ci) (< ci m))
           (equal (len (adt-pg-col ci (nth 4 c) (nth 0 c))) (* r (nth 4 c))))
  :hints (("Goal" :use ((:instance adt-pg-len-col (k m) (np (nth 4 c)) (rt (nth 0 c)))))))

(defthm adt-pg-len-col-pokp
  (implies (adt-pg-pokp q c)
           (equal (len (adt-pg-col 0 (nth 5 c) (nth 1 c))) (* q (nth 5 c))))
  :hints (("Goal" :use ((:instance adt-pg-len-col (k 1) (r q) (ci 0) (np (nth 5 c)) (rt (nth 1 c)))))))

(in-theory (disable adt-pg-rput adt-pg-rget adt-pg-pput adt-pg-pget adt-pg-flat adt-pg-rokp adt-pg-pokp))

; -----------------------------------------------------------------------------
; 5. Growth.  A page added is every column extended by a page of zeros (the
; pool by Q zeros); the library's correspondence reads a column below the
; count and the pool below the fill, so it survives any extension by typed
; entries (adt-corr-of-grow, adt-corr-of-grow-pool).

(defun adt-app-each (l z)
  (declare (xargs :verify-guards nil))
  (if (atom l) nil (cons (append (car l) z) (adt-app-each (cdr l) z))))

(defun adt-grow (p z c)
  (declare (xargs :verify-guards nil))
  (append (adt-app-each (take p c) z) (nthcdr p c)))

(defun adt-grow-pool (p z c)
  (declare (xargs :verify-guards nil))
  (update-nth p (append (nth p c) z) c))

(defthm adt-nth-of-grow-pool
  (implies (and (natp m) (natp p))
           (equal (nth m (adt-grow-pool p z c))
                  (if (equal m p) (append (nth p c) z) (nth m c)))))

(defthm adt-len-of-grow-pool
  (implies (and (natp p) (< p (len c)))
           (equal (len (adt-grow-pool p z c)) (len c)))
  :hints (("Goal" :in-theory (enable update-nth))))

(defthm adt-true-listp-of-grow-pool
  (implies (true-listp c) (true-listp (adt-grow-pool p z c)))
  :hints (("Goal" :in-theory (enable update-nth))))

(in-theory (disable adt-grow-pool))

(local
 (defthm adt-pg-nth-app-each
   (implies (and (natp m) (< m (len l)))
            (equal (nth m (adt-app-each l z)) (append (nth m l) z)))
   :hints (("Goal" :in-theory (enable nth)))))

(local
 (defthm adt-pg-len-app-each
   (equal (len (adt-app-each l z)) (len l))))

(local
 (defthm adt-pg-nth-take
   (implies (and (natp m) (< m (nfix p)))
            (equal (nth m (take p c)) (nth m c)))
   :hints (("Goal" :in-theory (enable nth)))))

(local
 (defthm adt-pg-nth-nthcdr
   (implies (and (natp m) (natp p))
            (equal (nth m (nthcdr p c)) (nth (+ p m) c)))
   :hints (("Goal" :in-theory (enable nth)))))

(local
 (defthm adt-pg-len-take
   (equal (len (take p c)) (nfix p))))

(defthm adt-nth-of-grow
  (implies (and (natp m) (natp p))
           (equal (nth m (adt-grow p z c))
                  (if (< m p) (append (nth m c) z) (nth m c)))))

(defthm adt-len-of-grow
  (implies (and (natp p) (<= p (len c)))
           (equal (len (adt-grow p z c)) (len c))))

(defthm adt-true-listp-of-grow
  (implies (true-listp c) (true-listp (adt-grow p z c))))

(in-theory (disable adt-grow))

; Zeros are an entry of every column type.
(defun adt-zerosp (z)
  (declare (xargs :guard t))
  (if (atom z) (null z) (and (equal (car z) 0) (adt-zerosp (cdr z)))))

(defthm adt-zerosp-of-resize-nil
  (adt-zerosp (resize-list nil n 0))
  :hints (("Goal" :in-theory (enable resize-list))))

(local
 (defthm adt-pg-all-elt-p-of-append-zeros
   (implies (and (adt-all-elt-p ct x) (adt-zerosp z) (adt-elt-p ct 0))
            (adt-all-elt-p ct (append x z)))))

(local
 (defthm adt-pg-elt-p-zero-nat
   (and (adt-elt-p '(:nat) 0) (adt-elt-p '(:ub 8) 0))
   :hints (("Goal" :in-theory (enable adt-elt-p)))))

(local
 (defthm adt-pg-nth-append-below
   (implies (and (natp i) (< i (len x)))
            (equal (nth i (append x z)) (nth i x)))))

(local
 (defthm adt-pg-scol-corr-of-append
   (implies (adt-scol-corr k col i v)
            (adt-scol-corr k (append col z) i v))))

(local
 (defthm adt-pg-ocol-corr-of-append
   (implies (adt-ocol-corr offs lens pool fl i v)
            (adt-ocol-corr (append offs z) (append lens z) pool fl i v))))

(local
 (defthm adt-pg-field-corr-of-grow
   (implies (and (adt-field-corr k ci p c v) (adt-kindp k) (adt-zerosp z)
                 (natp ci) (natp p) (<= (+ ci (adt-kind-width k)) p))
            (adt-field-corr k ci p (adt-grow p z c) v))
   :hints (("Goal" :in-theory (enable adt-field-corr)))))

(local
 (defthm adt-pg-fields-corr-of-grow
   (implies (and (adt-fields-corr s ci p c recs) (adt-schemap s) (adt-zerosp z)
                 (natp ci) (natp p) (<= (+ ci (adt-ncols s)) p))
            (adt-fields-corr s ci p (adt-grow p z c) recs))
   :hints (("Goal" :induct (adt-fields-corr s ci p c recs)
            :in-theory (enable adt-fields-corr)))))

(local
 (defthm adt-pg-cols-shape-of-grow
   (implies (and (adt-cols-shape s ci c) (adt-schemap s) (adt-zerosp z)
                 (natp ci) (natp p) (<= (+ ci (adt-ncols s)) p))
            (adt-cols-shape s ci (adt-grow p z c)))
   :hints (("Goal" :induct (adt-cols-shape s ci c)
            :in-theory (enable adt-cols-shape)))))

(defthm adt-corr-of-grow
  (implies (and (adt-corr s c a) (adt-zerosp z))
           (adt-corr s (adt-grow (adt-ncols s) z c) a))
  :hints (("Goal" :in-theory (enable adt-corr adt-shape-p adt-fill-okp))))

(local
 (defun adt-pg-dec (n) (if (zp n) n (adt-pg-dec (1- n)))))

(local
 (defthm adt-pg-prefix-eq-append
   (implies (and (natp n) (<= n (len p)))
            (adt-prefix-eq p (append p z) n))
   :hints (("Goal" :induct (adt-pg-dec n) :in-theory (enable adt-prefix-eq)))))

(local
 (defthm adt-pg-field-corr-of-grow-pool
   (implies (and (adt-field-corr k ci p c v) (adt-fill-okp p c)
                 (natp ci) (natp p) (<= (+ ci (adt-kind-width k)) p))
            (adt-field-corr k ci p (adt-grow-pool p z c) v))
   :hints (("Goal" :in-theory (e/d (adt-field-corr adt-fill-okp) (adt-ocol-corr-of-pool))
            :use ((:instance adt-ocol-corr-of-pool
                             (offs (nth ci c)) (lens (nth (+ 1 ci) c)) (pool (nth p c))
                             (fl (nth (+ 2 p) c)) (pool2 (append (nth p c) z))
                             (fl2 (nth (+ 2 p) c)) (i 0)))))))

(local
 (defthm adt-pg-fields-corr-of-grow-pool
   (implies (and (adt-fields-corr s ci p c recs) (adt-fill-okp p c)
                 (natp ci) (natp p) (<= (+ ci (adt-ncols s)) p))
            (adt-fields-corr s ci p (adt-grow-pool p z c) recs))
   :hints (("Goal" :induct (adt-fields-corr s ci p c recs)
            :in-theory (e/d (adt-fields-corr) (adt-fill-okp))))))

(local
 (defthm adt-pg-cols-shape-of-update-above
   (implies (and (natp ci) (natp k) (<= (+ ci (adt-ncols s)) k))
            (equal (adt-cols-shape s ci (update-nth k v c))
                   (adt-cols-shape s ci c)))
   :hints (("Goal" :induct (adt-cols-shape s ci c)
            :in-theory (enable adt-cols-shape adt-ncols)))))

(defthm adt-corr-of-grow-pool
  (implies (and (adt-corr s c a) (adt-zerosp z))
           (adt-corr s (adt-grow-pool (adt-ncols s) z c) a))
  :hints (("Goal" :in-theory (e/d (adt-corr adt-shape-p) (adt-pg-fields-corr-of-grow-pool))
           :use ((:instance adt-pg-fields-corr-of-grow-pool (ci 0) (p (adt-ncols s)) (recs a))))
          ("Subgoal 1" :in-theory (enable adt-fill-okp))))

; -----------------------------------------------------------------------------
; 6. Adding a page, and the rooms an append or a set makes first.

; A page made ready: each of its M columns emptied and resized to R zeros.
(defun adt-pg-fresh (ci m r pg)
  (declare (xargs :verify-guards nil))
  (if (zp m)
      pg
    (adt-pg-fresh (1+ ci) (1- m) r (update-nth ci (resize-list (resize-list (nth ci pg) 0 0) r 0) pg))))

; Page NP of the row table made ready (the table doubling its pointers when
; it has no spare slot; D is the page stobj's creator).
(defun adt-pg-addrow (m r d c)
  (declare (xargs :verify-guards nil))
  (let* ((k (nth 4 c))
         (c (if (< k (len (nth 0 c))) c (update-nth 0 (resize-list (nth 0 c) (max 8 (* 2 k)) d) c)))
         (c (update-nth 0 (update-nth k (adt-pg-fresh 0 m r (nth k (nth 0 c))) (nth 0 c)) c)))
    (update-nth 4 (+ 1 k) c)))

(defun adt-pg-addpool (q d c)
  (declare (xargs :verify-guards nil))
  (let* ((k (nth 5 c))
         (c (if (< k (len (nth 1 c))) c (update-nth 1 (resize-list (nth 1 c) (max 8 (* 2 k)) d) c)))
         (c (update-nth 1 (update-nth k (adt-pg-fresh 0 1 q (nth k (nth 1 c))) (nth 1 c)) c)))
    (update-nth 5 (+ 1 k) c)))

(defun adt-pg-rowroom (m r d c)
  (declare (xargs :verify-guards nil))
  (if (< (nth 2 c) (* r (nth 4 c))) c (adt-pg-addrow m r d c)))

(defun adt-pg-poolroom (q d need c)
  (declare (xargs :verify-guards nil
                  :measure (nfix (- (nfix need) (* (nfix q) (nfix (nth 5 c)))))
                  :hints (("Goal" :in-theory (enable nth update-nth)))))
  (if (and (posp q) (natp (nth 5 c)) (natp need) (< (* q (nth 5 c)) need))
      (adt-pg-poolroom q d need (adt-pg-addpool q d c))
    c))

(local
 (defthm adt-pg-resize-list-0
   (equal (resize-list x 0 d) nil)
   :hints (("Goal" :in-theory (enable resize-list)))))

(local
 (defthm adt-pg-nth-fresh
   (implies (and (natp ci) (natp cj))
            (equal (nth cj (adt-pg-fresh ci m r pg))
                   (if (and (<= ci cj) (< cj (+ ci (nfix m))))
                       (resize-list nil r 0)
                     (nth cj pg))))
   :hints (("Goal" :induct (adt-pg-fresh ci m r pg)))))

(local
 (defthm adt-pg-pagefullp-fresh
   (implies (and (natp r) (natp kk) (<= kk (nfix m)))
            (adt-pg-pagefullp kk r (adt-pg-fresh 0 m r pg)))
   :hints (("Goal" :induct (adt-pg-dec kk)))))

(local
 (defthm adt-pg-col-snoc-fresh
   (implies (and (natp np) (< np (len rt)) (natp ci) (< ci (nfix m)))
            (equal (adt-pg-col ci (+ 1 np) (update-nth np (adt-pg-fresh 0 m r pg) rt))
                   (append (adt-pg-col ci np rt) (resize-list nil r 0))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (adt-pg-col-snoc) (adt-pg-col adt-pg-fresh))))))

(local
 (defthm adt-pg-cols-snoc-fresh
   (implies (and (natp np) (< np (len rt)) (natp c0) (<= (+ c0 (nfix kk)) (nfix m)))
            (equal (adt-pg-cols c0 kk (+ 1 np) (update-nth np (adt-pg-fresh 0 m r pg) rt))
                   (adt-app-each (adt-pg-cols c0 kk np rt) (resize-list nil r 0))))
   :hints (("Goal" :induct (adt-pg-cols c0 kk np rt)
            :in-theory (disable adt-pg-col adt-pg-fresh)))))

(local
 (defthm adt-pg-cols-of-resize-list
   (implies (and (natp np) (<= np (len rt)) (natp mm) (<= np mm))
            (equal (adt-pg-cols c0 kk np (resize-list rt mm d))
                   (adt-pg-cols c0 kk np rt)))))

(local
 (defthm adt-pg-take-of-append
   (implies (and (true-listp a) (equal n (len a)))
            (equal (take n (append a b)) a))))

(local
 (defthm adt-pg-nthcdr-of-append
   (implies (equal n (len a))
            (equal (nthcdr n (append a b)) b))))

(local
 (defthm adt-pg-true-listp-cols
   (true-listp (adt-pg-cols ci k np rt))))

(defthm adt-pg-nth-of-addrow
  (implies (and (natp k) (not (equal k 0)) (not (equal k 4)))
           (equal (nth k (adt-pg-addrow m r d c)) (nth k c))))

(defthm adt-pg-nth-of-addpool
  (implies (and (natp k) (not (equal k 1)) (not (equal k 5)))
           (equal (nth k (adt-pg-addpool q d c)) (nth k c))))

(defthm adt-pg-np-of-addrow
  (equal (nth 4 (adt-pg-addrow m r d c)) (+ 1 (nth 4 c))))

(defthm adt-pg-nq-of-addpool
  (equal (nth 5 (adt-pg-addpool q d c)) (+ 1 (nth 5 c))))

(defthm adt-pg-flat-of-addrow
  (implies (and (adt-pg-rokp m r c) (equal m (adt-ncols s)))
           (equal (adt-pg-flat s (adt-pg-addrow m r d c))
                  (adt-grow (adt-ncols s) (resize-list nil r 0) (adt-pg-flat s c))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (adt-pg-flat adt-pg-rokp adt-grow)
                           (adt-pg-fresh adt-ncols adt-pg-cols adt-pg-col)))))

(defthm adt-pg-rokp-of-addrow
  (implies (adt-pg-rokp m r c)
           (adt-pg-rokp m r (adt-pg-addrow m r d c)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (adt-pg-rokp adt-pg-fullp-snoc) (adt-pg-fresh adt-pg-cols adt-pg-col)))))

(defthm adt-pg-pokp-of-addrow
  (equal (adt-pg-pokp q (adt-pg-addrow m r d c)) (adt-pg-pokp q c))
  :hints (("Goal" :in-theory (enable adt-pg-pokp))))

(defthm adt-pg-flat-of-addpool
  (implies (adt-pg-pokp q c)
           (equal (adt-pg-flat s (adt-pg-addpool q d c))
                  (adt-grow-pool (adt-ncols s) (resize-list nil q 0) (adt-pg-flat s c))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (adt-pg-flat adt-pg-pokp adt-grow-pool)
                           (adt-pg-fresh adt-ncols adt-pg-cols adt-pg-col)))))

(defthm adt-pg-pokp-of-addpool
  (implies (adt-pg-pokp q c)
           (adt-pg-pokp q (adt-pg-addpool q d c)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (adt-pg-pokp adt-pg-fullp-snoc) (adt-pg-fresh adt-pg-cols adt-pg-col)))))

(defthm adt-pg-rokp-of-addpool
  (equal (adt-pg-rokp m r (adt-pg-addpool q d c)) (adt-pg-rokp m r c))
  :hints (("Goal" :in-theory (enable adt-pg-rokp))))

(in-theory (disable adt-pg-addrow adt-pg-addpool))

; The count is within the first column (a schema has a field).
(defthm adt-pg-ncols-pos
  (implies (consp s) (< 0 (adt-ncols s)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable adt-ncols adt-kind-width))))

(defthm adt-corr-count-bound
  (implies (and (adt-corr s c a) (consp s))
           (<= (len a) (len (nth 0 c))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable adt-corr adt-fields-corr adt-field-corr)
           :cases ((consp a)))
          ("Subgoal 1" :use ((:instance adt-scol-corr-get-0 (k (car s)) (col (nth 0 c))
                                        (v (adt-cars a)) (m (1- (len a))))
                             (:instance adt-ocol-corr-get-0 (offs (nth 0 c)) (lens (nth 1 c))
                                        (pool (nth (adt-ncols s) c))
                                        (fl (nth (+ 2 (adt-ncols s)) c))
                                        (v (adt-cars a)) (m (1- (len a))))))))

(defthm adt-pg-corr-count-bound
  (implies (and (adt-pg-corr s r q c a) (consp s))
           (<= (len a) (* r (nth 4 c))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (adt-pg-corr) (adt-ncols))
           :do-not-induct t
           :use ((:instance adt-corr-count-bound (c (adt-pg-flat s c)))))))

(defthm adt-pg-corr-count
  (implies (adt-pg-corr s r q c a)
           (equal (nth 2 c) (len a)))
  :hints (("Goal" :in-theory (enable adt-pg-corr adt-corr adt-pg-flat))))

(defthm adt-pg-rowroom-meaning
  (implies (and (adt-pg-corr s r q c a) (consp s) (equal m (adt-ncols s)))
           (let ((c2 (adt-pg-rowroom m r d c)))
             (and (adt-pg-corr s r q c2 a)
                  (< (nth 2 c2) (* r (nth 4 c2)))
                  (equal (nth 1 c2) (nth 1 c))
                  (equal (nth 2 c2) (nth 2 c))
                  (equal (nth 3 c2) (nth 3 c))
                  (equal (nth 5 c2) (nth 5 c)))))
  :hints (("Goal" :in-theory (e/d (adt-pg-corr adt-pg-rowroom) (adt-pg-corr-count-bound adt-pg-corr-count))
           :use (adt-pg-corr-count-bound adt-pg-corr-count))))

(defthm adt-pg-poolroom-meaning
  (implies (adt-pg-corr s r q c a)
           (let ((c2 (adt-pg-poolroom q d need c)))
             (and (adt-pg-corr s r q c2 a)
                  (implies (natp need) (<= need (* q (nth 5 c2))))
                  (natp (nth 5 c2))
                  (equal (nth 0 c2) (nth 0 c))
                  (equal (nth 2 c2) (nth 2 c))
                  (equal (nth 3 c2) (nth 3 c))
                  (equal (nth 4 c2) (nth 4 c)))))
  :hints (("Goal" :induct (adt-pg-poolroom q d need c)
           :in-theory (enable adt-pg-corr))))

(in-theory (disable adt-pg-rowroom adt-pg-poolroom))

; -----------------------------------------------------------------------------
; 7. The pool's write and read loops.

(defun adt-pg-poolw (i bytes q c)
  (declare (xargs :verify-guards nil))
  (if (atom bytes)
      c
    (adt-pg-poolw (1+ i) (cdr bytes) q (adt-pg-pput i (car bytes) q c))))

(defun adt-pg-poolr (off n acc q c)
  (declare (xargs :verify-guards nil))
  (if (zp n)
      acc
    (adt-pg-poolr off (1- n) (cons (adt-pg-pget (+ off (1- n)) q c) acc) q c)))

(local
 (defthm adt-pg-update-nth-update-nth-same
   (equal (update-nth n x (update-nth n y l)) (update-nth n x l))
   :hints (("Goal" :in-theory (enable update-nth)))))

(local
 (defthm adt-pg-len-pool-writes
   (implies (and (natp i) (<= (+ i (len bytes)) (len pool)))
            (equal (len (adt-pool-writes pool i bytes)) (len pool)))))

(local
 (defthm adt-pg-poolw-steps
   (implies (and (adt-pg-pokp q c) (natp i) (<= (+ i (len bytes)) (* q (nth 5 c))))
            (let ((c2 (adt-pg-poolw i bytes q c)))
              (and (equal (adt-pg-col 0 (nth 5 c) (nth 1 c2))
                          (adt-pool-writes (adt-pg-col 0 (nth 5 c) (nth 1 c)) i bytes))
                   (adt-pg-pokp q c2)
                   (equal (nth 5 c2) (nth 5 c)))))
   :hints (("Goal" :induct (adt-pg-poolw i bytes q c)
            :in-theory (disable adt-pg-col)))))

(defthm adt-pg-nth-of-poolw
  (implies (and (natp k) (not (equal k 1)))
           (equal (nth k (adt-pg-poolw i bytes q c)) (nth k c))))

(defthm adt-pg-rokp-of-poolw
  (equal (adt-pg-rokp m r (adt-pg-poolw i bytes q c)) (adt-pg-rokp m r c))
  :hints (("Goal" :in-theory (enable adt-pg-rokp))))

(defthm adt-pg-pokp-of-poolw
  (implies (and (adt-pg-pokp q c) (natp i) (<= (+ i (len bytes)) (* q (nth 5 c))))
           (adt-pg-pokp q (adt-pg-poolw i bytes q c))))

(defthm adt-pg-flat-of-poolw
  (implies (and (adt-pg-pokp q c) (natp i) (<= (+ i (len bytes)) (* q (nth 5 c))))
           (equal (adt-pg-flat s (adt-pg-poolw i bytes q c))
                  (update-nth (adt-ncols s)
                              (adt-pool-writes (nth (adt-ncols s) (adt-pg-flat s c)) i bytes)
                              (adt-pg-flat s c))))
  :hints (("Goal" :in-theory (e/d (adt-pg-flat) (adt-pg-col adt-pg-cols adt-pg-poolw-steps))
           :do-not-induct t
           :use adt-pg-poolw-steps)))

(defthm adt-pg-poolr-meaning
  (implies (and (adt-pg-pokp q c) (natp off) (natp n) (<= (+ off n) (* q (nth 5 c))))
           (equal (adt-pg-poolr off n acc q c)
                  (adt-poolr 0 off n acc (list (adt-pg-col 0 (nth 5 c) (nth 1 c))))))
  :hints (("Goal" :induct (adt-pg-poolr off n acc q c)
           :in-theory (e/d (adt-poolr) (adt-poolr-is-slice)))))

(in-theory (disable adt-pg-poolw adt-pg-poolr))

; -----------------------------------------------------------------------------
; 8. One field of one row, and a record's fields, with the room made.

(defun adt-pg-put-field (k ci n v r q c)
  (declare (xargs :verify-guards nil))
  (if (adt-octets-kind-p k)
      (let* ((o (nth 3 c))
             (c (adt-pg-poolw o v q c))
             (c (update-nth 3 (+ o (len v)) c))
             (c (adt-pg-rput ci n o r c)))
        (adt-pg-rput (+ 1 ci) n (len v) r c))
    (adt-pg-rput ci n (adt-enc k v) r c)))

(defun adt-pg-get-field (k ci i r q c)
  (declare (xargs :verify-guards nil))
  (if (adt-octets-kind-p k)
      (adt-pg-poolr (adt-pg-rget ci i r c) (adt-pg-rget (+ 1 ci) i r c) nil q c)
    (adt-dec k (adt-pg-rget ci i r c))))

(defun adt-pg-append-fields (s ci n rec r q c)
  (declare (xargs :verify-guards nil))
  (if (atom s)
      c
    (adt-pg-append-fields (cdr s) (+ (adt-kind-width (car s)) ci) n (cdr rec) r q
                          (adt-pg-put-field (car s) ci n (car rec) r q c))))

(defun adt-pg-set-fields (s j ci i v r q c)
  (declare (xargs :verify-guards nil))
  (if (atom s)
      c
    (if (zp j)
        (adt-pg-put-field (car s) ci i v r q c)
      (adt-pg-set-fields (cdr s) (1- j) (+ (adt-kind-width (car s)) ci) i v r q c))))

(defun adt-pg-get-fields (s j ci i r q c)
  (declare (xargs :verify-guards nil))
  (if (atom s)
      nil
    (if (zp j)
        (adt-pg-get-field (car s) ci i r q c)
      (adt-pg-get-fields (cdr s) (1- j) (+ (adt-kind-width (car s)) ci) i r q c))))

(defthm adt-pg-len-nth-flat
  (and (implies (and (adt-pg-rokp (adt-ncols s) r c) (natp ci) (< ci (adt-ncols s)))
                (equal (len (nth ci (adt-pg-flat s c))) (* r (nth 4 c))))
       (implies (adt-pg-pokp q c)
                (equal (len (nth (adt-ncols s) (adt-pg-flat s c))) (* q (nth 5 c))))
       (equal (nth (+ 2 (adt-ncols s)) (adt-pg-flat s c)) (nth 3 c))
       (equal (nth (+ 1 (adt-ncols s)) (adt-pg-flat s c)) (nth 2 c)))
  :hints (("Goal" :in-theory (enable adt-pg-flat))))

(defthm adt-pg-flat-of-update-fill
  (equal (adt-pg-flat s (update-nth 3 x c))
         (update-nth (+ 2 (adt-ncols s)) x (adt-pg-flat s c)))
  :hints (("Goal" :in-theory (enable adt-pg-flat))))

(defthm adt-pg-flat-of-update-count
  (equal (adt-pg-flat s (update-nth 2 x c))
         (update-nth (+ 1 (adt-ncols s)) x (adt-pg-flat s c)))
  :hints (("Goal" :in-theory (enable adt-pg-flat))))

(local
 (defthm adt-pg-col-put-in-room
   (implies (and (natp n) (< n (len col)))
            (equal (adt-col-put col n x) (update-nth n x col)))
   :hints (("Goal" :in-theory (enable adt-col-put adt-col-room)))))

(local
 (defthm adt-pg-pool-room-in-room
   (implies (<= need (len (nth p c)))
            (equal (adt-pool-room p need c) c))
   :hints (("Goal" :in-theory (enable adt-pool-room)))))

(local
 (defthm adt-pg-update-nth-of-nth-same
   (implies (and (natp k) (< k (len l)))
            (equal (update-nth k (nth k l) l) l))
   :hints (("Goal" :in-theory (enable nth update-nth)))))

(defthm adt-pg-put-field-meaning
  (implies (and (adt-pg-rokp (adt-ncols s0) r c) (adt-pg-pokp q c) (natp ci) (<= (+ ci (adt-kind-width k)) (adt-ncols s0))
                (natp n) (< n (* r (nth 4 c))) (natp (nth 3 c))
                (or (not (adt-octets-kind-p k))
                    (<= (+ (nth 3 c) (len v)) (* q (nth 5 c)))))
           (let ((c2 (adt-pg-put-field k ci n v r q c)))
             (and (equal (adt-pg-flat s0 c2)
                         (adt-put-field k ci (adt-ncols s0) n v (adt-pg-flat s0 c)))
                  (adt-pg-rokp (adt-ncols s0) r c2)
                  (adt-pg-pokp q c2)
                  (equal (nth 2 c2) (nth 2 c))
                  (equal (nth 4 c2) (nth 4 c))
                  (equal (nth 5 c2) (nth 5 c))
                  (equal (nth 3 c2) (+ (nth 3 c) (if (adt-octets-kind-p k) (len v) 0))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (adt-put-field adt-pool-push adt-kind-width)
                           (adt-pg-col adt-pg-cols adt-pg-nth-flat)))))

(defthm adt-pg-append-fields-meaning
  (implies (and (adt-pg-rokp (adt-ncols s0) r c) (adt-pg-pokp q c) (natp ci) (<= (+ ci (adt-ncols s)) (adt-ncols s0))
                (natp n) (< n (* r (nth 4 c))) (natp (nth 3 c))
                (<= (+ (nth 3 c) (adt-rec-load s rec)) (* q (nth 5 c))))
           (let ((c2 (adt-pg-append-fields s ci n rec r q c)))
             (and (equal (adt-pg-flat s0 c2)
                         (adt-append-fields s ci (adt-ncols s0) n rec (adt-pg-flat s0 c)))
                  (adt-pg-rokp (adt-ncols s0) r c2)
                  (adt-pg-pokp q c2)
                  (equal (nth 2 c2) (nth 2 c))
                  (equal (nth 4 c2) (nth 4 c))
                  (equal (nth 5 c2) (nth 5 c))
                  (equal (nth 3 c2) (+ (nth 3 c) (adt-rec-load s rec))))))
  :hints (("Goal" :induct (adt-pg-append-fields s ci n rec r q c)
           :in-theory (e/d (adt-append-fields adt-ncols adt-rec-load) (adt-put-field adt-pg-put-field)))))

(defthm adt-pg-set-fields-meaning
  (implies (and (adt-pg-rokp (adt-ncols s0) r c) (adt-pg-pokp q c) (natp ci) (<= (+ ci (adt-ncols s)) (adt-ncols s0))
                (natp i) (< i (* r (nth 4 c))) (natp (nth 3 c))
                (or (not (adt-octets-kind-p (nth j s)))
                    (<= (+ (nth 3 c) (len v)) (* q (nth 5 c)))))
           (let ((c2 (adt-pg-set-fields s j ci i v r q c)))
             (and (equal (adt-pg-flat s0 c2)
                         (adt-set-fields s j ci (adt-ncols s0) i v (adt-pg-flat s0 c)))
                  (adt-pg-rokp (adt-ncols s0) r c2)
                  (adt-pg-pokp q c2)
                  (equal (nth 2 c2) (nth 2 c))
                  (equal (nth 4 c2) (nth 4 c))
                  (equal (nth 5 c2) (nth 5 c)))))
  :hints (("Goal" :induct (adt-pg-set-fields s j ci i v r q c)
           :in-theory (e/d (adt-set-fields adt-ncols nth) (adt-put-field adt-pg-put-field)))))

(in-theory (disable adt-pg-put-field adt-pg-append-fields adt-pg-set-fields))

(local
 (defthm adt-pg-get-field-meaning
   (implies (and (adt-pg-rokp (adt-ncols s0) r c) (adt-pg-pokp q c)
                 (natp ci) (<= (+ ci (adt-kind-width k)) (adt-ncols s0))
                 (natp i) (< i (* r (nth 4 c)))
                 (if (adt-octets-kind-p k)
                     (and (adt-all-elt-p '(:nat) (nth ci (adt-pg-flat s0 c)))
                          (adt-all-elt-p '(:nat) (nth (+ 1 ci) (adt-pg-flat s0 c))))
                   t)
                 (adt-get-field-okp k ci (adt-ncols s0) i (adt-pg-flat s0 c)))
            (equal (adt-pg-get-field k ci i r q c)
                   (adt-get-field k ci (adt-ncols s0) i (adt-pg-flat s0 c))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (adt-get-field adt-get-field-okp adt-kind-width)
                            (adt-pg-col adt-pg-cols))))))

(local
 (defthm adt-pg-get-fields-meaning
   (implies (and (adt-pg-rokp (adt-ncols s0) r c) (adt-pg-pokp q c)
                 (natp ci) (<= (+ ci (adt-ncols s)) (adt-ncols s0))
                 (natp i) (< i (* r (nth 4 c)))
                 (adt-cols-shape s ci (adt-pg-flat s0 c))
                 (adt-get-fields-okp s j ci (adt-ncols s0) i (adt-pg-flat s0 c)))
            (equal (adt-pg-get-fields s j ci i r q c)
                   (adt-get-fields s j ci (adt-ncols s0) i (adt-pg-flat s0 c))))
   :hints (("Goal" :induct (adt-pg-get-fields s j ci i r q c)
            :in-theory (e/d (adt-get-fields adt-get-fields-okp adt-cols-shape adt-ncols)
                            (adt-pg-get-field adt-get-field adt-get-field-okp))))))

(in-theory (disable adt-pg-get-field adt-pg-get-fields))

; -----------------------------------------------------------------------------
; 9. The sequence: append, set, get, count, clear, and the creator's image.
; Each is the library's operation on the flat view after the room is made,
; so the library's adt-corr-* theorems are its correspondence theorems.

; The roomed image an append writes into, then the append into it.
(defun adt-pg-append-room (s rec r q d dp c)
  (declare (xargs :verify-guards nil))
  (let ((c (adt-pg-rowroom (adt-ncols s) r d c)))
    (adt-pg-poolroom q dp (+ (nth 3 c) (adt-rec-load s rec)) c)))

(defun adt-pg-append-at (s rec r q c)
  (declare (xargs :verify-guards nil))
  (let ((n (nth 2 c)))
    (update-nth 2 (+ 1 n) (adt-pg-append-fields s 0 n rec r q c))))

(defun adt-pg-append-c (s rec r q d dp c)
  (declare (xargs :verify-guards nil))
  (adt-pg-append-at s rec r q (adt-pg-append-room s rec r q d dp c)))

(defun adt-pg-set-c (s j i v r q dp c)
  (declare (xargs :verify-guards nil))
  (let ((c (if (adt-octets-kind-p (nth j s))
               (adt-pg-poolroom q dp (+ (nth 3 c) (len v)) c)
             c)))
    (adt-pg-set-fields s j 0 i v r q c)))

(defun adt-pg-get-c (s j i r q c)
  (declare (xargs :verify-guards nil))
  (adt-pg-get-fields s j 0 i r q c))

(defun adt-pg-clear-c (c)
  (declare (xargs :verify-guards nil))
  (update-nth 5 0 (update-nth 4 0 (update-nth 3 0 (update-nth 2 0 (update-nth 1 nil (update-nth 0 nil c)))))))

(defthm adt-pg-corr-fill-natp
  (implies (adt-pg-corr s r q c a) (natp (nth 3 c)))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("Goal" :in-theory (enable adt-pg-corr adt-corr adt-fill-okp adt-shape-p))))

(defthm adt-pg-rec-load-natp
  (natp (adt-rec-load s rec))
  :rule-classes :type-prescription)


(defthm adt-pg-append-room-meaning
  (implies (and (adt-pg-corr s r q c a) (consp s))
           (let ((c2 (adt-pg-append-room s rec r q d dp c)))
             (and (adt-pg-corr s r q c2 a)
                  (< (nth 2 c2) (* r (nth 4 c2)))
                  (<= (+ (nth 3 c2) (adt-rec-load s rec)) (* q (nth 5 c2)))
                  (equal (nth 2 c2) (nth 2 c))
                  (equal (nth 3 c2) (nth 3 c)))))
  :hints (("Goal" :in-theory (disable adt-pg-corr adt-pg-rowroom-meaning adt-pg-poolroom-meaning)
           :do-not-induct t
           :use ((:instance adt-pg-rowroom-meaning (m (adt-ncols s)))
                 (:instance adt-pg-poolroom-meaning (c (adt-pg-rowroom (adt-ncols s) r d c)) (d dp)
                            (need (+ (nth 3 c) (adt-rec-load s rec))))))))

(defthm adt-pg-append-at-meaning
  (implies (and (adt-pg-rokp (adt-ncols s) r c) (adt-pg-pokp q c)
                (natp (nth 2 c)) (natp (nth 3 c))
                (< (nth 2 c) (* r (nth 4 c)))
                (<= (+ (nth 3 c) (adt-rec-load s rec)) (* q (nth 5 c))))
           (let ((c3 (adt-pg-append-at s rec r q c)))
             (and (equal (adt-pg-flat s c3) (adt-append-c s rec (adt-pg-flat s c)))
                  (adt-pg-rokp (adt-ncols s) r c3)
                  (adt-pg-pokp q c3)
                  (equal (nth 3 c3) (+ (nth 3 c) (adt-rec-load s rec))))))
  :hints (("Goal" :in-theory (e/d (adt-append-c) (adt-append-fields)))))

(defthm adt-pg-append-c-is-room-then-append
  (implies (and (adt-pg-corr s r q c a) (consp s))
           (equal (adt-pg-flat s (adt-pg-append-c s rec r q d dp c))
                  (adt-append-c s rec (adt-pg-flat s (adt-pg-append-room s rec r q d dp c)))))
  :hints (("Goal" :in-theory (e/d (adt-pg-corr adt-pg-okp)
                                  (adt-pg-append-room-meaning adt-pg-append-at-meaning adt-append-c
                                   adt-pg-append-room adt-pg-append-at))
           :do-not-induct t
           :use (adt-pg-append-room-meaning adt-pg-corr-count adt-pg-corr-fill-natp
                 (:instance adt-pg-append-at-meaning (c (adt-pg-append-room s rec r q d dp c)))))))

(defthm adt-pg-corr-append
  (implies (and (adt-pg-corr s r q c a) (consp s) (adt-rec-p s rec))
           (adt-pg-corr s r q (adt-pg-append-c s rec r q d dp c) (append a (list rec))))
  :hints (("Goal" :in-theory (e/d (adt-pg-corr adt-pg-okp)
                                  (adt-pg-append-room-meaning adt-pg-append-at-meaning adt-append-c
                                   adt-pg-append-room adt-pg-append-at adt-corr-append))
           :do-not-induct t
           :use (adt-pg-append-room-meaning adt-pg-corr-count adt-pg-corr-fill-natp
                 (:instance adt-pg-append-at-meaning (c (adt-pg-append-room s rec r q d dp c)))
                 (:instance adt-corr-append (c (adt-pg-flat s (adt-pg-append-room s rec r q d dp c))))))))

(defun adt-pg-set-room (s j v q dp c)
  (declare (xargs :verify-guards nil))
  (if (adt-octets-kind-p (nth j s))
      (adt-pg-poolroom q dp (+ (nth 3 c) (len v)) c)
    c))

(defthm adt-pg-set-c-is-room-then-set
  (equal (adt-pg-set-c s j i v r q dp c)
         (adt-pg-set-fields s j 0 i v r q (adt-pg-set-room s j v q dp c)))
  :hints (("Goal" :in-theory (enable adt-pg-set-c))))

(defthm adt-pg-set-room-meaning
  (implies (adt-pg-corr s r q c a)
           (let ((c2 (adt-pg-set-room s j v q dp c)))
             (and (adt-pg-corr s r q c2 a)
                  (or (not (adt-octets-kind-p (nth j s)))
                      (<= (+ (nth 3 c2) (len v)) (* q (nth 5 c2))))
                  (equal (nth 2 c2) (nth 2 c))
                  (equal (nth 3 c2) (nth 3 c))
                  (equal (nth 4 c2) (nth 4 c)))))
  :hints (("Goal" :in-theory (disable adt-pg-corr adt-pg-poolroom-meaning)
           :use ((:instance adt-pg-poolroom-meaning (d dp) (need (+ (nth 3 c) (len v))))))))

(defthm adt-pg-corr-set
  (implies (and (adt-pg-corr s r q c a) (consp s) (natp j) (< j (len s)) (natp i) (< i (len a))
                (adt-val-okp (nth j s) v))
           (adt-pg-corr s r q (adt-pg-set-c s j i v r q dp c) (adt-set-a j i v a)))
  :hints (("Goal" :in-theory (e/d (adt-pg-corr adt-pg-okp adt-set-c)
                                  (adt-set-fields adt-pg-set-room adt-pg-set-room-meaning
                                   adt-pg-set-fields-meaning adt-corr-set adt-pg-corr-count-bound))
           :do-not-induct t
           :use (adt-pg-set-room-meaning
                 (:instance adt-pg-corr-count-bound (c (adt-pg-set-room s j v q dp c)))
                 (:instance adt-pg-corr-fill-natp (c (adt-pg-set-room s j v q dp c)))
                 (:instance adt-pg-set-fields-meaning (s0 s) (ci 0) (c (adt-pg-set-room s j v q dp c)))
                 (:instance adt-corr-set (c (adt-pg-flat s (adt-pg-set-room s j v q dp c))))))))

(defthm adt-pg-corr-get
  (implies (and (adt-pg-corr s r q c a) (consp s) (natp j) (< j (len s)) (natp i) (< i (len a)))
           (equal (adt-pg-get-c s j i r q c) (nth j (nth i a))))
  :hints (("Goal" :in-theory (e/d (adt-pg-corr adt-pg-okp adt-get-c adt-get-okp adt-pg-get-c adt-shape-p)
                                  (adt-corr-get adt-corr-shape adt-pg-get-fields-meaning
                                   adt-pg-corr-count-bound))
           :do-not-induct t
           :use (adt-pg-corr-count-bound
                 (:instance adt-corr-get (c (adt-pg-flat s c)))
                 (:instance adt-corr-shape (c (adt-pg-flat s c)))
                 (:instance adt-pg-get-fields-meaning (s0 s) (ci 0))))))

(local
 (defthm adt-pg-cols-of-none
   (equal (adt-pg-cols ci k 0 rt) (adt-nils k))))

(defthm adt-pg-flat-of-empty
  (implies (and (equal (nth 4 c) 0) (equal (nth 5 c) 0) (equal (nth 2 c) 0) (equal (nth 3 c) 0))
           (equal (adt-pg-flat s c) (adt-empty-c s)))
  :hints (("Goal" :in-theory (enable adt-pg-flat adt-empty-c))))

(defthm adt-pg-corr-empty
  (implies (and (adt-schemap s) (posp r) (posp q)
                (equal (nth 4 c) 0) (equal (nth 5 c) 0) (equal (nth 2 c) 0) (equal (nth 3 c) 0))
           (adt-pg-corr s r q c nil))
  :hints (("Goal" :in-theory (enable adt-pg-corr adt-pg-okp adt-pg-rokp adt-pg-pokp))))

(defthm adt-pg-corr-clear
  (implies (and (adt-schemap s) (posp r) (posp q))
           (adt-pg-corr s r q (adt-pg-clear-c c) nil)))

; A write-once instance's pool: its fill is the live records' octets after
; every writing operation (books/proto/adt-load.lisp, on the flat view).
(defthm adt-pg-fill-is-load-of-append
  (implies (and (adt-pg-corr s r q c a) (consp s) (adt-fill-is-load s (adt-pg-flat s c) a))
           (adt-fill-is-load s (adt-pg-flat s (adt-pg-append-c s rec r q d dp c)) (append a (list rec))))
  :hints (("Goal" :in-theory (e/d (adt-pg-corr adt-pg-okp adt-fill-is-load)
                                  (adt-pg-append-room-meaning adt-pg-append-at-meaning adt-append-c
                                   adt-pg-append-room adt-pg-append-at adt-fill-is-load-of-append-c))
           :do-not-induct t
           :use (adt-pg-append-room-meaning adt-pg-corr-count adt-pg-corr-fill-natp
                 (:instance adt-pg-append-at-meaning (c (adt-pg-append-room s rec r q d dp c)))
                 (:instance adt-fill-is-load-of-append-c
                            (c (adt-pg-flat s (adt-pg-append-room s rec r q d dp c))))))))

(defthm adt-pg-fill-is-load-of-set
  (implies (and (adt-pg-corr s r q c a) (consp s) (natp j) (< j (len s))
                (not (adt-octets-kind-p (nth j s)))
                (natp i) (< i (len a))
                (adt-fill-is-load s (adt-pg-flat s c) a))
           (adt-fill-is-load s (adt-pg-flat s (adt-pg-set-c s j i v r q dp c)) (adt-set-a j i v a)))
  :hints (("Goal" :in-theory (e/d (adt-pg-corr adt-pg-okp adt-set-c adt-fill-is-load)
                                  (adt-set-fields adt-pg-set-room adt-pg-set-room-meaning
                                   adt-pg-set-fields-meaning adt-fill-is-load-of-set-c
                                   adt-pg-corr-count-bound))
           :do-not-induct t
           :use (adt-pg-set-room-meaning
                 (:instance adt-pg-corr-count-bound (c (adt-pg-set-room s j v q dp c)))
                 (:instance adt-pg-corr-fill-natp (c (adt-pg-set-room s j v q dp c)))
                 (:instance adt-pg-set-fields-meaning (s0 s) (ci 0) (c (adt-pg-set-room s j v q dp c)))
                 (:instance adt-fill-is-load-of-set-c (c (adt-pg-flat s (adt-pg-set-room s j v q dp c))))))))

(defthm adt-pg-fill-is-load-of-empty
  (implies (and (equal (nth 4 c) 0) (equal (nth 5 c) 0) (equal (nth 2 c) 0) (equal (nth 3 c) 0))
           (adt-fill-is-load s (adt-pg-flat s c) nil)))

(in-theory (disable adt-pg-append-c adt-pg-set-c adt-pg-get-c adt-pg-clear-c adt-pg-append-room adt-pg-append-at
                    adt-pg-set-room
                    adt-pg-corr))
