; fn: the catalog's (group . number)-keyed tables as DENSE PER-GROUP RUNS
; (stage 4 of planning/design-store-representation-2026-10-01.md, lane
; stage-4, 2026-10-01).
;
; WHAT IT REPLACES.  Three `(hash-table equal)' fields of the paged catalog
; are keyed by a membership (group . number): the numbers table (number ->
; the row's sequence, the old foundation's position 3) and the two live
; links (books/catalog-live-links.lisp: NEXT and PREV).  An `equal' table of
; N entries rehashes into fresh vectors of 2N when it fills: measured on the
; paged catalog's commit at 131,071 rows of two groups, the numbers table's
; doubling allocated 10.1 MB and the links' 20.2 MB in one commit
; (build/s4/m0.lisp, hbox, guards on), Theta(N) in one scheduling step (D27).
;
; THE REPRESENTATION.  A group's numbers are dense from 1 to its high by
; construction (a commit's number is one past the high, never reused:
; `fn-cat-group-next-is-high'), so the membership (g . n) is a CELL, not a
; key: page (g . floor((n-1)/256)) holds 256 memberships x 3 lanes of u64
; words (lane 0 numbers, 1 NEXT, 2 PREV), word = value + 1, 0 = unbound;
; 8 octets a membership per lane.  A page is found through the page table
; ((g . page index) -> page id: one entry per 256 memberships) and carries
; its OWNER key, so a stale or foreign page id never reads as a hit (no
; injectivity invariant is needed).  A put allocates at most one page
; (6 KiB); the page table and the page array still double, at N/256
; entries (a pointer and an empty page header each): the step's worst
; allocation is O(N/256) words, not O(N) records.
;
; THE ESCAPE.  What a cell cannot carry -- a key that is not (g . posint), a
; value that is not a natural below 2^64 - 1 -- goes to the escape table,
; keyed (lane . key).  The composed catalog puts only sequences and live
; numbers there (naturals) under (group . posint) keys, so the escape is
; empty on every reachable state; it exists so that the logical side can be
; the hash tables' own (total over every key and value).
;
; THE LOGICAL SIDE is exactly three stobj hash tables: get = (cdr
; (hons-assoc-equal k al)), put = (cons (cons k v) al), rem =
; hons-remove-assoc, clear = nil -- the definitions `defstobj' gives the
; fields this replaces, so every catalog theorem over those fields reads
; the same alist (books/catalog-paged.lisp's view puts lane 0 at the old
; numbers position).  The correspondence is extensional: for every lane and
; key the concrete read is the alist's lookup (fn-dm-agree).
;
; GEN: def-representation -- the generator's shape is a sequence of
; records; a keyed map with pages is not yet one of its kinds.

(in-package "ACL2")

(local (include-book "arithmetic-5/top" :dir :system))
(local (in-theory (disable nth update-nth resize-list floor mod)))

(defconst *fn-dm-run* 256)
(defconst *fn-dm-page-words* 768)
(defconst *fn-dm-word-sent* (1- (expt 2 64)))

; One page: its owner key and its 3 x 256 words (empty until it is used).
(defstobj fn-dpg
  (fn-dpg-own :type t :initially nil)
  (fn-dpg-w :type (array (unsigned-byte 64) (0)) :initially 0 :resizable t)
  :inline t)

(defstobj fn-dmap$c
  (fn-dmap$c-pt :type (hash-table equal))
  (fn-dmap$c-pg :type (array fn-dpg (0)) :resizable t)
  (fn-dmap$c-np :type (integer 0 *) :initially 0)
  (fn-dmap$c-esc :type (hash-table equal))
  :inline t)

; -----------------------------------------------------------------------------
; 1. Addressing.

; A membership a cell can hold: (g . n), n a positive integer.
(defun fn-dm-keyp (k)
  (declare (xargs :guard t))
  (and (consp k) (posp (cdr k))))

(defun fn-dm-pkey (k)
  (declare (xargs :guard (fn-dm-keyp k)))
  (cons (car k) (floor (1- (cdr k)) *fn-dm-run*)))

(defun fn-dm-slot (lane k)
  (declare (xargs :guard (and (natp lane) (fn-dm-keyp k))))
  (+ (* lane *fn-dm-run*) (mod (1- (cdr k)) *fn-dm-run*)))

(defun fn-dm-lanep (lane)
  (declare (xargs :guard t))
  (and (natp lane) (< lane 3)))

(defthm fn-dm-slot-bound
  (implies (and (fn-dm-lanep lane) (fn-dm-keyp k))
           (and (natp (fn-dm-slot lane k))
                (< (fn-dm-slot lane k) *fn-dm-page-words*)))
  :rule-classes ((:rewrite)
                 (:linear :corollary (implies (and (fn-dm-lanep lane) (fn-dm-keyp k))
                                              (< (fn-dm-slot lane k) *fn-dm-page-words*)))
                 (:type-prescription :corollary (implies (and (fn-dm-lanep lane) (fn-dm-keyp k))
                                                         (natp (fn-dm-slot lane k)))))
  :hints (("Goal" :in-theory (enable mod))))

(in-theory (disable fn-dm-slot fn-dm-pkey))

; A value a cell can hold.
(defun fn-dm-smallp (v)
  (declare (xargs :guard t))
  (and (natp v) (< v *fn-dm-word-sent*)))

; -----------------------------------------------------------------------------
; 2. The concrete reads.

; The live page id of a page key: bound, below the pages in use and the
; array, and owned by that key; nil otherwise.
(defun fn-dmap$c-pid (pk fn-dmap$c)
  (declare (xargs :stobjs fn-dmap$c))
  (let ((pid (fn-dmap$c-pt-get pk fn-dmap$c)))
    (if (and (natp pid)
             (< pid (fn-dmap$c-np fn-dmap$c))
             (< pid (fn-dmap$c-pg-length fn-dmap$c))
             (stobj-let ((fn-dpg (fn-dmap$c-pgi pid fn-dmap$c)))
                        (own)
                        (and (equal (fn-dpg-own fn-dpg) pk)
                             (equal (fn-dpg-w-length fn-dpg) *fn-dm-page-words*))
                        own))
        pid
      nil)))

;; What the guards need, stated once; the recognizers stay closed below.
(defthm fn-dm-pgp-nth
  (implies (and (fn-dmap$c-pgp l) (natp i) (< i (len l)))
           (fn-dpgp (nth i l)))
  :hints (("Goal" :in-theory (enable nth fn-dmap$c-pgp))))

(defthm fn-dm-cp-fields
  (implies (fn-dmap$cp c)
           (and (fn-dmap$c-pgp (nth *fn-dmap$c-pgi* c))
                (true-listp (nth *fn-dmap$c-pgi* c))
                (integerp (nth *fn-dmap$c-np* c))
                (<= 0 (nth *fn-dmap$c-np* c))))
  :rule-classes ((:rewrite) (:forward-chaining))
  :hints (("Goal" :in-theory (enable fn-dmap$cp fn-dmap$c-npp))))

(defthm fn-dm-len-resize-list
  (equal (len (resize-list l n d)) (nfix n))
  :hints (("Goal" :in-theory (enable resize-list))))

(defthm fn-dm-pgp-true-listp
  (implies (fn-dmap$c-pgp l) (true-listp l))
  :hints (("Goal" :in-theory (enable fn-dmap$c-pgp))))

(defthm fn-dm-wp-nth
  (implies (and (fn-dpg-wp l) (natp i) (< i (len l)))
           (unsigned-byte-p 64 (nth i l)))
  :hints (("Goal" :in-theory (enable fn-dpg-wp nth))))

(defthm fn-dm-dpg-word
  (implies (and (fn-dpgp p) (natp i) (< i (len (nth *fn-dpg-wi* p))))
           (unsigned-byte-p 64 (nth i (nth *fn-dpg-wi* p))))
  :hints (("Goal" :in-theory (enable fn-dpgp))))

(defthm fn-dm-pid-type
  (let ((pid (fn-dmap$c-pid pk c)))
    (implies pid
             (and (natp pid)
                  (< pid (len (nth *fn-dmap$c-pgi* c)))
                  (< pid (nth *fn-dmap$c-np* c))
                  (equal (nth 0 (nth pid (nth *fn-dmap$c-pgi* c))) pk)
                  (equal (len (nth 1 (nth pid (nth *fn-dmap$c-pgi* c)))) *fn-dm-page-words*))))
  :hints (("Goal" :in-theory (enable fn-dmap$c-pid))))

(defthm fn-dm-pid-natp
  (or (null (fn-dmap$c-pid pk c)) (natp (fn-dmap$c-pid pk c)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn-dmap$c-pid))))

(in-theory (disable fn-dmap$c-pid fn-dmap$cp))

(defthm fn-dm-lanep-fc
  (implies (fn-dm-lanep lane) (and (natp lane) (< lane 3)))
  :rule-classes :forward-chaining)

(defthm fn-dm-keyp-fc
  (implies (fn-dm-keyp k) (and (consp k) (posp (cdr k))))
  :rule-classes :forward-chaining)

(in-theory (disable fn-dm-lanep fn-dm-keyp))

; The word of a membership (0: no cell).
(defun fn-dmap$c-word (lane k fn-dmap$c)
  (declare (xargs :stobjs fn-dmap$c :guard (fn-dm-lanep lane)))
  (if (fn-dm-keyp k)
      (let ((pid (fn-dmap$c-pid (fn-dm-pkey k) fn-dmap$c)))
        (if (natp pid)
            (stobj-let ((fn-dpg (fn-dmap$c-pgi pid fn-dmap$c)))
                       (w)
                       (if (< (fn-dm-slot lane k) (fn-dpg-w-length fn-dpg))
                           (fn-dpg-wi (fn-dm-slot lane k) fn-dpg)
                         0)
                       w)
          0))
    0))

(defthm fn-dm-word-natp
  (implies (and (fn-dmap$cp c) (fn-dm-lanep lane))
           (natp (fn-dmap$c-word lane k c)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (e/d (fn-dmap$c-word) (fn-dpgp fn-dm-dpg-word fn-dm-pgp-nth))
                  :use ((:instance fn-dm-pgp-nth (l (nth *fn-dmap$c-pgi* c)) (i (fn-dmap$c-pid (fn-dm-pkey k) c)))
                        (:instance fn-dm-dpg-word
                                   (p (nth (fn-dmap$c-pid (fn-dm-pkey k) c) (nth *fn-dmap$c-pgi* c)))
                                   (i (fn-dm-slot lane k)))))))

(defun fn-dmap$c-get (lane k fn-dmap$c)
  (declare (xargs :stobjs fn-dmap$c :guard (fn-dm-lanep lane)))
  (let ((w (fn-dmap$c-word lane k fn-dmap$c)))
    (if (zp w)
        (fn-dmap$c-esc-get (cons lane k) fn-dmap$c)
      (1- w))))

; -----------------------------------------------------------------------------
; 3. The concrete writes.

; Write word W at the membership's cell of live page PID.
(defun fn-dmap$c-write (pid lane k w fn-dmap$c)
  (declare (xargs :stobjs fn-dmap$c
                  :guard (and (natp pid) (< pid (fn-dmap$c-pg-length fn-dmap$c))
                              (fn-dm-lanep lane) (fn-dm-keyp k)
                              (unsigned-byte-p 64 w))))
  (stobj-let ((fn-dpg (fn-dmap$c-pgi pid fn-dmap$c)))
             (fn-dpg)
             (if (< (fn-dm-slot lane k) (fn-dpg-w-length fn-dpg))
                 (update-fn-dpg-wi (fn-dm-slot lane k) w fn-dpg)
               fn-dpg)
             fn-dmap$c))

; A fresh page for page key PK at id np: room in the array (doubling: N/256
; pointers), the page's words zeroed, its owner set, the table bound.
(defun fn-dmap$c-alloc (pk fn-dmap$c)
  (declare (xargs :stobjs fn-dmap$c))
  (let* ((pid (fn-dmap$c-np fn-dmap$c))
         (fn-dmap$c (if (< pid (fn-dmap$c-pg-length fn-dmap$c))
                        fn-dmap$c
                      (resize-fn-dmap$c-pg (+ 4 (* 2 pid)) fn-dmap$c)))
         (fn-dmap$c (stobj-let ((fn-dpg (fn-dmap$c-pgi pid fn-dmap$c)))
                               (fn-dpg)
                               (let* ((fn-dpg (resize-fn-dpg-w 0 fn-dpg))
                                      (fn-dpg (resize-fn-dpg-w *fn-dm-page-words* fn-dpg)))
                                 (update-fn-dpg-own pk fn-dpg))
                               fn-dmap$c))
         (fn-dmap$c (fn-dmap$c-pt-put pk pid fn-dmap$c))
         (fn-dmap$c (update-fn-dmap$c-np (+ 1 pid) fn-dmap$c)))
    (mv pid fn-dmap$c)))

(defun fn-dmap$c-put (lane k v fn-dmap$c)
  (declare (xargs :stobjs fn-dmap$c :guard (fn-dm-lanep lane)))
  (if (fn-dm-keyp k)
      (let ((pid (fn-dmap$c-pid (fn-dm-pkey k) fn-dmap$c)))
        (if (fn-dm-smallp v)
            (if (natp pid)
                (fn-dmap$c-write pid lane k (+ 1 v) fn-dmap$c)
              (mv-let (pid fn-dmap$c)
                (fn-dmap$c-alloc (fn-dm-pkey k) fn-dmap$c)
                (fn-dmap$c-write pid lane k (+ 1 v) fn-dmap$c)))
          (let ((fn-dmap$c (if (natp pid) (fn-dmap$c-write pid lane k 0 fn-dmap$c) fn-dmap$c)))
            (fn-dmap$c-esc-put (cons lane k) v fn-dmap$c))))
    (fn-dmap$c-esc-put (cons lane k) v fn-dmap$c)))

(defun fn-dmap$c-rem (lane k fn-dmap$c)
  (declare (xargs :stobjs fn-dmap$c :guard (fn-dm-lanep lane)))
  (let* ((pid (and (fn-dm-keyp k) (fn-dmap$c-pid (fn-dm-pkey k) fn-dmap$c)))
         (fn-dmap$c (if (natp pid) (fn-dmap$c-write pid lane k 0 fn-dmap$c) fn-dmap$c)))
    (fn-dmap$c-esc-rem (cons lane k) fn-dmap$c)))

; The clear keeps the page array (its pages are reused, zeroed at
; allocation) and forgets the table, the count and the escape.
(defun fn-dmap$c-clear (fn-dmap$c)
  (declare (xargs :stobjs fn-dmap$c))
  (let* ((fn-dmap$c (fn-dmap$c-pt-clear fn-dmap$c))
         (fn-dmap$c (update-fn-dmap$c-np 0 fn-dmap$c)))
    (fn-dmap$c-esc-clear fn-dmap$c)))

; -----------------------------------------------------------------------------
; 4. The concrete facts: every write changes exactly its own cell.

(defthm fn-dm-digits
  (implies (and (natp a1) (natp a2) (natp m1) (natp m2) (< m1 256) (< m2 256))
           (equal (equal (+ m1 (* 256 a1)) (+ m2 (* 256 a2)))
                  (and (equal a1 a2) (equal m1 m2))))
  :hints (("Goal" :cases ((< a1 a2) (< a2 a1)))))
(defthm fn-dm-floor-mod-equal
  (implies (and (natp x) (natp y) (equal (floor x 256) (floor y 256))
                (equal (mod x 256) (mod y 256)))
           (equal x y))
  :rule-classes nil
  :hints (("Goal" :use ((:instance floor-mod-elim (x x) (y 256))
                        (:instance floor-mod-elim (x y) (y 256)))
                  :in-theory (disable floor-mod-elim))))
(defthm fn-dm-slot-inj
  (implies (and (fn-dm-lanep l1) (fn-dm-lanep l2) (fn-dm-keyp k1) (fn-dm-keyp k2)
                (equal (fn-dm-pkey k1) (fn-dm-pkey k2)))
           (equal (equal (fn-dm-slot l1 k1) (fn-dm-slot l2 k2))
                  (and (equal l1 l2) (equal k1 k2))))
  :hints (("Goal" :in-theory (e/d (fn-dm-slot fn-dm-pkey fn-dm-lanep fn-dm-keyp) (floor mod))
                  :use ((:instance fn-dm-floor-mod-equal (x (+ -1 (cdr k1))) (y (+ -1 (cdr k2))))
                        (:instance fn-dm-digits (a1 l1) (a2 l2) (m1 (mod (+ -1 (cdr k1)) 256))
                                   (m2 (mod (+ -1 (cdr k2)) 256)))))))

(defthm fn-dm-write-fields
  (and (equal (nth *fn-dmap$c-pt-get* (fn-dmap$c-write pid lane k w c)) (nth *fn-dmap$c-pt-get* c))
       (equal (nth *fn-dmap$c-np* (fn-dmap$c-write pid lane k w c)) (nth *fn-dmap$c-np* c))
       (equal (nth *fn-dmap$c-esc-get* (fn-dmap$c-write pid lane k w c)) (nth *fn-dmap$c-esc-get* c)))
  :hints (("Goal" :in-theory (enable fn-dmap$c-write))))
(defthm fn-dm-write-pages
  (implies (and (natp pid) (< pid (len (nth *fn-dmap$c-pgi* c))))
           (equal (nth *fn-dmap$c-pgi* (fn-dmap$c-write pid lane k w c))
                  (update-nth pid
                              (let ((p (nth pid (nth *fn-dmap$c-pgi* c))))
                                (if (< (fn-dm-slot lane k) (len (nth 1 p)))
                                    (update-nth 1 (update-nth (fn-dm-slot lane k) w (nth 1 p)) p)
                                  p))
                              (nth *fn-dmap$c-pgi* c))))
  :hints (("Goal" :in-theory (enable fn-dmap$c-write))))
(in-theory (disable fn-dmap$c-write))
(defthm fn-dm-len-update-nth
  (implies (< (nfix i) (len l)) (equal (len (update-nth i v l)) (len l)))
  :hints (("Goal" :in-theory (enable update-nth))))
(defthm fn-dm-nth-update-nth
  (equal (nth i (update-nth j v l))
         (if (equal (nfix i) (nfix j)) v (nth i l)))
  :hints (("Goal" :in-theory (enable nth update-nth))))
(defthm fn-dm-pid-of-write
  (implies (and (natp pid) (< pid (len (nth *fn-dmap$c-pgi* c))))
           (equal (fn-dmap$c-pid pk (fn-dmap$c-write pid lane k w c))
                  (fn-dmap$c-pid pk c)))
  :hints (("Goal" :in-theory (enable fn-dmap$c-pid))))

(defthm fn-dm-pid-own
  (implies (and (fn-dmap$c-pid pk1 c) (equal (fn-dmap$c-pid pk1 c) (fn-dmap$c-pid pk2 c)))
           (equal (equal pk1 pk2) t))
  :hints (("Goal" :use ((:instance fn-dm-pid-type (pk pk1)) (:instance fn-dm-pid-type (pk pk2)))
                  :in-theory (disable fn-dm-pid-type))))
(defthm fn-dm-word-of-write
  (implies (and (fn-dm-lanep lane) (fn-dm-keyp k) (fn-dm-lanep l2)
                (equal pid (fn-dmap$c-pid (fn-dm-pkey k) c)) pid)
           (equal (fn-dmap$c-word l2 k2 (fn-dmap$c-write pid lane k w c))
                  (if (and (equal l2 lane) (equal k2 k))
                      w
                    (fn-dmap$c-word l2 k2 c))))
  :hints (("Goal" :in-theory (enable fn-dmap$c-word)
                  :cases ((and (fn-dm-keyp k2)
                               (equal (fn-dmap$c-pid (fn-dm-pkey k2) c) (fn-dmap$c-pid (fn-dm-pkey k) c)))))))

(defun fn-dm-rl-ind (i l n)
  (if (or (zp n) (zp i)) (list i l n)
    (fn-dm-rl-ind (1- i) (if (atom l) l (cdr l)) (1- n))))
(defthm fn-dm-resize-list-open
  (implies (posp n)
           (equal (resize-list l n d)
                  (cons (if (atom l) d (car l))
                        (resize-list (if (atom l) l (cdr l)) (1- n) d))))
  :hints (("Goal" :in-theory (enable resize-list))))
(defthm fn-dm-resize-list-zp
  (implies (zp n) (equal (resize-list l n d) nil))
  :hints (("Goal" :in-theory (enable resize-list))))
(defthm fn-dm-nth-resize-list
  (implies (natp i)
           (equal (nth i (resize-list l n d))
                  (if (< i (nfix n)) (if (< i (len l)) (nth i l) d) nil)))
  :hints (("Goal" :induct (fn-dm-rl-ind i l n) :in-theory (enable nth))))
(in-theory (disable fn-dm-resize-list-open))
(defthm fn-dm-resize-list-0
  (equal (resize-list l 0 d) nil)
  :hints (("Goal" :in-theory (enable resize-list))))
(defthm fn-dm-alloc-fields
  (and (equal (mv-nth 0 (fn-dmap$c-alloc pk c)) (nth *fn-dmap$c-np* c))
       (equal (nth *fn-dmap$c-pt-get* (mv-nth 1 (fn-dmap$c-alloc pk c)))
              (cons (cons pk (nth *fn-dmap$c-np* c)) (nth *fn-dmap$c-pt-get* c)))
       (equal (nth *fn-dmap$c-np* (mv-nth 1 (fn-dmap$c-alloc pk c))) (+ 1 (nth *fn-dmap$c-np* c)))
       (equal (nth *fn-dmap$c-esc-get* (mv-nth 1 (fn-dmap$c-alloc pk c))) (nth *fn-dmap$c-esc-get* c)))
  :hints (("Goal" :in-theory (enable fn-dmap$c-alloc))))
(defthm fn-dm-pid-of-alloc
  (implies (and (fn-dmap$cp c) (not (fn-dmap$c-pid pk c)))
           (equal (fn-dmap$c-pid pk2 (mv-nth 1 (fn-dmap$c-alloc pk c)))
                  (if (equal pk2 pk) (nth *fn-dmap$c-np* c) (fn-dmap$c-pid pk2 c))))
  :hints (("Goal" :in-theory (enable fn-dmap$c-pid fn-dmap$c-alloc))))
(defthm fn-dm-page-of-alloc-other
  (implies (and (fn-dmap$cp c) (natp i) (< i (len (nth *fn-dmap$c-pgi* c)))
                (not (equal i (nth *fn-dmap$c-np* c))))
           (equal (nth i (nth *fn-dmap$c-pgi* (mv-nth 1 (fn-dmap$c-alloc pk c))))
                  (nth i (nth *fn-dmap$c-pgi* c))))
  :hints (("Goal" :in-theory (enable fn-dmap$c-alloc))))
(defun fn-dm-zerosp (l)
  (declare (xargs :guard t))
  (if (consp l) (and (equal (car l) 0) (fn-dm-zerosp (cdr l))) t))
(defthm fn-dm-nth-of-zeros
  (implies (and (fn-dm-zerosp l) (natp j) (< j (len l)))
           (equal (nth j l) 0))
  :hints (("Goal" :in-theory (enable nth))))
(defthm fn-dm-page-of-alloc-fresh
  (implies (and (fn-dmap$cp c) (natp j) (< j *fn-dm-page-words*))
           (equal (nth j (nth 1 (nth (nth *fn-dmap$c-np* c)
                                     (nth *fn-dmap$c-pgi* (mv-nth 1 (fn-dmap$c-alloc pk c))))))
                  0))
  :hints (("Goal" :in-theory (enable fn-dmap$c-alloc))))
(in-theory (disable fn-dmap$c-alloc))
(defthm fn-dm-pid-linear
  (implies (fn-dmap$c-pid pk c)
           (and (< (fn-dmap$c-pid pk c) (len (nth *fn-dmap$c-pgi* c)))
                (< (fn-dmap$c-pid pk c) (nth *fn-dmap$c-np* c))))
  :rule-classes :linear
  :hints (("Goal" :use fn-dm-pid-type :in-theory (disable fn-dm-pid-type))))
(defthm fn-dm-word-of-alloc
  (implies (and (fn-dmap$cp c) (not (fn-dmap$c-pid pk c)) (fn-dm-lanep l2))
           (equal (fn-dmap$c-word l2 k2 (mv-nth 1 (fn-dmap$c-alloc pk c)))
                  (fn-dmap$c-word l2 k2 c)))
  :hints (("Goal" :in-theory (enable fn-dmap$c-word)
                  :cases ((and (fn-dm-keyp k2) (equal (fn-dm-pkey k2) pk))))))

(defthm fn-dm-pgp-update-nth
  (implies (and (fn-dmap$c-pgp l) (fn-dpgp p) (natp i) (< i (len l)))
           (fn-dmap$c-pgp (update-nth i p l)))
  :hints (("Goal" :in-theory (enable fn-dmap$c-pgp update-nth))))
(defthm fn-dm-pgp-resize-list
  (implies (and (fn-dmap$c-pgp l) (fn-dpgp d))
           (fn-dmap$c-pgp (resize-list l n d)))
  :hints (("Goal" :induct (resize-list l n d)
                  :in-theory (enable fn-dmap$c-pgp fn-dm-resize-list-open (:induction resize-list)))))
(defthm fn-dm-wp-update-nth
  (implies (and (fn-dpg-wp l) (natp i) (< i (len l)) (unsigned-byte-p 64 w))
           (fn-dpg-wp (update-nth i w l)))
  :hints (("Goal" :in-theory (enable fn-dpg-wp update-nth))))
(defthm fn-dm-dpgp-update-w
  (implies (and (fn-dpgp p) (fn-dpg-wp w)) (fn-dpgp (update-nth 1 w p)))
  :hints (("Goal" :in-theory (enable fn-dpgp))))
(defthm fn-dm-dpgp-update-own
  (implies (fn-dpgp p) (fn-dpgp (update-nth 0 x p)))
  :hints (("Goal" :in-theory (enable fn-dpgp))))
(defthm fn-dm-dpgp-fields
  (implies (fn-dpgp p) (fn-dpg-wp (nth 1 p)))
  :hints (("Goal" :in-theory (enable fn-dpgp))))
(defthm fn-dm-cp-of-update
  (implies (fn-dmap$cp c)
           (and (fn-dmap$cp (update-nth *fn-dmap$c-pt-get* x c))
                (fn-dmap$cp (update-nth *fn-dmap$c-esc-get* x c))
                (implies (natp n) (fn-dmap$cp (update-nth *fn-dmap$c-np* n c)))
                (implies (fn-dmap$c-pgp l) (fn-dmap$cp (update-nth *fn-dmap$c-pgi* l c)))))
  :hints (("Goal" :in-theory (enable fn-dmap$cp fn-dmap$c-npp))))
(defthm fn-dm-cp-of-write
  (implies (and (fn-dmap$cp c) (natp pid) (< pid (len (nth *fn-dmap$c-pgi* c)))
                (unsigned-byte-p 64 w) (fn-dm-lanep lane) (fn-dm-keyp k))
           (fn-dmap$cp (fn-dmap$c-write pid lane k w c)))
  :hints (("Goal" :in-theory (e/d (fn-dmap$c-write) (fn-dmap$c-pgp)))))
(defthm fn-dm-cp-of-alloc
  (implies (fn-dmap$cp c)
           (fn-dmap$cp (mv-nth 1 (fn-dmap$c-alloc pk c))))
  :hints (("Goal" :in-theory (enable fn-dmap$c-alloc fn-dmap$cp))))
(defthm fn-dm-alloc-room
  (implies (fn-dmap$cp c)
           (< (nth *fn-dmap$c-np* c)
              (len (nth *fn-dmap$c-pgi* (mv-nth 1 (fn-dmap$c-alloc pk c))))))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable fn-dmap$c-alloc))))
(defthm fn-dm-cp-of-put
  (implies (and (fn-dmap$cp c) (fn-dm-lanep lane))
           (fn-dmap$cp (fn-dmap$c-put lane k v c)))
  :hints (("Goal" :in-theory (enable fn-dmap$c-put))))
(defthm fn-dm-cp-of-rem
  (implies (and (fn-dmap$cp c) (fn-dm-lanep lane))
           (fn-dmap$cp (fn-dmap$c-rem lane k c)))
  :hints (("Goal" :in-theory (enable fn-dmap$c-rem))))
(defthm fn-dm-cp-of-clear
  (implies (fn-dmap$cp c)
           (fn-dmap$cp (fn-dmap$c-clear c)))
  :hints (("Goal" :in-theory (enable fn-dmap$c-clear fn-dmap$cp))))

(defthm fn-dm-word-of-esc
  (equal (fn-dmap$c-word l k (update-nth *fn-dmap$c-esc-get* x c))
         (fn-dmap$c-word l k c))
  :hints (("Goal" :in-theory (enable fn-dmap$c-word fn-dmap$c-pid))))
(defthm fn-dm-word-no-page
  (implies (not (and (fn-dm-keyp k) (fn-dmap$c-pid (fn-dm-pkey k) c)))
           (equal (fn-dmap$c-word lane k c) 0))
  :hints (("Goal" :in-theory (enable fn-dmap$c-word))))
(defthm fn-dm-get-of-put
  (implies (and (fn-dmap$cp c) (fn-dm-lanep lane) (fn-dm-lanep l2))
           (equal (fn-dmap$c-get l2 k2 (fn-dmap$c-put lane k v c))
                  (if (and (equal l2 lane) (equal k2 k)) v (fn-dmap$c-get l2 k2 c))))
  :hints (("Goal" :in-theory (enable fn-dmap$c-put fn-dmap$c-get fn-dm-smallp))))
(defthm fn-dm-assoc-of-remove-assoc
  (equal (hons-assoc-equal k2 (hons-remove-assoc k al))
         (if (equal k2 k) nil (hons-assoc-equal k2 al))))
(defthm fn-dm-get-of-rem
  (implies (and (fn-dmap$cp c) (fn-dm-lanep lane) (fn-dm-lanep l2))
           (equal (fn-dmap$c-get l2 k2 (fn-dmap$c-rem lane k c))
                  (if (and (equal l2 lane) (equal k2 k)) nil (fn-dmap$c-get l2 k2 c))))
  :hints (("Goal" :in-theory (enable fn-dmap$c-rem fn-dmap$c-get))))
(defthm fn-dm-get-of-clear
  (equal (fn-dmap$c-get l2 k2 (fn-dmap$c-clear c)) nil)
  :hints (("Goal" :in-theory (enable fn-dmap$c-clear fn-dmap$c-get fn-dmap$c-word fn-dmap$c-pid))))


; -----------------------------------------------------------------------------
; 5. The logical side: three stobj hash tables, and the abstract stobj.

(defun fn-dmap$ap (a)
  (declare (xargs :guard t))
  (and (true-listp a) (equal (len a) 3)))

(defun create-fn-dmap$a ()
  (declare (xargs :guard t))
  (list nil nil nil))

(defun fn-dmap$a-get (lane k a)
  (declare (xargs :guard (and (fn-dmap$ap a) (fn-dm-lanep lane))))
  (cdr (hons-assoc-equal k (nth lane a))))

(defun fn-dmap$a-put (lane k v a)
  (declare (xargs :guard (and (fn-dmap$ap a) (fn-dm-lanep lane))))
  (update-nth lane (cons (cons k v) (nth lane a)) a))

(defun fn-dmap$a-rem (lane k a)
  (declare (xargs :guard (and (fn-dmap$ap a) (fn-dm-lanep lane))))
  (update-nth lane (hons-remove-assoc k (nth lane a)) a))

(defun fn-dmap$a-clear (a)
  (declare (xargs :guard (fn-dmap$ap a)) (ignore a))
  (list nil nil nil))

(defun-sk fn-dm-agree (c a)
  (forall (lane k)
          (implies (fn-dm-lanep lane)
                   (equal (fn-dmap$c-get lane k c) (fn-dmap$a-get lane k a)))))

(defun-nx fn-dmap$corr (fn-dmap$c a)
  (and (fn-dmap$cp fn-dmap$c) (fn-dmap$ap a) (fn-dm-agree fn-dmap$c a)))

(defthm fn-dm-agree-of-put
  (implies (and (fn-dmap$cp c) (fn-dm-lanep lane) (fn-dm-agree c a))
           (fn-dm-agree (fn-dmap$c-put lane k v c) (fn-dmap$a-put lane k v a)))
  :hints (("Goal" :expand ((fn-dm-agree (fn-dmap$c-put lane k v c) (fn-dmap$a-put lane k v a)))
                  :use ((:instance fn-dm-agree-necc
                                   (lane (mv-nth 0 (fn-dm-agree-witness (fn-dmap$c-put lane k v c)
                                                                        (fn-dmap$a-put lane k v a))))
                                   (k (mv-nth 1 (fn-dm-agree-witness (fn-dmap$c-put lane k v c)
                                                                     (fn-dmap$a-put lane k v a))))))
                  :in-theory (e/d (fn-dm-lanep) (fn-dm-agree-necc fn-dmap$c-get fn-dmap$c-put)))))

(defthm fn-dm-agree-of-rem
  (implies (and (fn-dmap$cp c) (fn-dm-lanep lane) (fn-dm-agree c a))
           (fn-dm-agree (fn-dmap$c-rem lane k c) (fn-dmap$a-rem lane k a)))
  :hints (("Goal" :expand ((fn-dm-agree (fn-dmap$c-rem lane k c) (fn-dmap$a-rem lane k a)))
                  :use ((:instance fn-dm-agree-necc
                                   (lane (mv-nth 0 (fn-dm-agree-witness (fn-dmap$c-rem lane k c)
                                                                        (fn-dmap$a-rem lane k a))))
                                   (k (mv-nth 1 (fn-dm-agree-witness (fn-dmap$c-rem lane k c)
                                                                     (fn-dmap$a-rem lane k a))))))
                  :in-theory (e/d (fn-dm-lanep) (fn-dm-agree-necc fn-dmap$c-get fn-dmap$c-rem)))))

(defthm fn-dm-nth-of-nils
  (equal (nth i '(nil nil nil)) nil)
  :hints (("Goal" :in-theory (enable nth))))

(defthm fn-dm-get-of-create
  (equal (fn-dmap$c-get l k (create-fn-dmap$c)) nil)
  :hints (("Goal" :in-theory (enable fn-dmap$c-get fn-dmap$c-word fn-dmap$c-pid))))

(defthm fn-dm-agree-of-clear
  (fn-dm-agree (fn-dmap$c-clear c) (fn-dmap$a-clear a))
  :hints (("Goal" :in-theory (disable fn-dmap$c-clear fn-dmap$c-get))))

(defthm fn-dm-agree-of-create
  (fn-dm-agree (create-fn-dmap$c) (create-fn-dmap$a))
  :hints (("Goal" :in-theory (disable create-fn-dmap$c fn-dmap$c-get))))

; The obligations defabsstobj states (defabsstobj-missing-events lists
; exactly these nine).
(defthm fn-dm-cp-of-create
  (fn-dmap$cp (create-fn-dmap$c))
  :hints (("Goal" :in-theory (enable fn-dmap$cp))))

(defthm create-fn-dmap{correspondence}
  (fn-dmap$corr (create-fn-dmap$c) (create-fn-dmap$a))
  :hints (("Goal" :use fn-dm-agree-of-create
                  :in-theory (disable create-fn-dmap$c fn-dm-agree fn-dm-agree-of-create))))

(defthm create-fn-dmap{preserved}
  (fn-dmap$ap (create-fn-dmap$a)))

(defthm fn-dmap-get{correspondence}
  (implies (and (fn-dmap$corr fn-dmap$c fn-dmap) (fn-dmap$ap fn-dmap) (fn-dm-lanep lane))
           (equal (fn-dmap$c-get lane k fn-dmap$c) (fn-dmap$a-get lane k fn-dmap)))
  :hints (("Goal" :use ((:instance fn-dm-agree-necc (c fn-dmap$c) (a fn-dmap)))
                  :in-theory (disable fn-dm-agree-necc fn-dmap$c-get fn-dmap$a-get))))

(defthm fn-dmap-put{preserved}
  (implies (and (fn-dmap$ap fn-dmap) (fn-dm-lanep lane))
           (fn-dmap$ap (fn-dmap$a-put lane k v fn-dmap)))
  :hints (("Goal" :in-theory (enable fn-dm-lanep))))

(defthm fn-dmap-put{correspondence}
  (implies (and (fn-dmap$corr fn-dmap$c fn-dmap) (fn-dmap$ap fn-dmap) (fn-dm-lanep lane))
           (fn-dmap$corr (fn-dmap$c-put lane k v fn-dmap$c) (fn-dmap$a-put lane k v fn-dmap)))
  :hints (("Goal" :use fn-dmap-put{preserved}
                  :in-theory (disable fn-dmap$c-put fn-dmap$a-put fn-dm-agree fn-dmap-put{preserved}))))

(defthm fn-dmap-rem{preserved}
  (implies (and (fn-dmap$ap fn-dmap) (fn-dm-lanep lane))
           (fn-dmap$ap (fn-dmap$a-rem lane k fn-dmap)))
  :hints (("Goal" :in-theory (enable fn-dm-lanep))))

(defthm fn-dmap-rem{correspondence}
  (implies (and (fn-dmap$corr fn-dmap$c fn-dmap) (fn-dmap$ap fn-dmap) (fn-dm-lanep lane))
           (fn-dmap$corr (fn-dmap$c-rem lane k fn-dmap$c) (fn-dmap$a-rem lane k fn-dmap)))
  :hints (("Goal" :use fn-dmap-rem{preserved}
                  :in-theory (disable fn-dmap$c-rem fn-dmap$a-rem fn-dm-agree fn-dmap-rem{preserved}))))

(defthm fn-dmap-clear{preserved}
  (implies (fn-dmap$ap fn-dmap)
           (fn-dmap$ap (fn-dmap$a-clear fn-dmap))))

(defthm fn-dmap-clear{correspondence}
  (implies (and (fn-dmap$corr fn-dmap$c fn-dmap) (fn-dmap$ap fn-dmap))
           (fn-dmap$corr (fn-dmap$c-clear fn-dmap$c) (fn-dmap$a-clear fn-dmap)))
  :hints (("Goal" :use fn-dmap-clear{preserved}
                  :in-theory (disable fn-dmap$c-clear fn-dmap$a-clear fn-dm-agree fn-dmap-clear{preserved}))))

(defabsstobj fn-dmap
  :foundation fn-dmap$c
  :recognizer (fn-dmapp :logic fn-dmap$ap :exec fn-dmap$cp)
  :creator (create-fn-dmap :logic create-fn-dmap$a :exec create-fn-dmap$c)
  :corr-fn fn-dmap$corr
  :exports ((fn-dmap-get :logic fn-dmap$a-get :exec fn-dmap$c-get)
            (fn-dmap-put :logic fn-dmap$a-put :exec fn-dmap$c-put :protect t)
            (fn-dmap-rem :logic fn-dmap$a-rem :exec fn-dmap$c-rem :protect t)
            (fn-dmap-clear :logic fn-dmap$a-clear :exec fn-dmap$c-clear :protect t)))
