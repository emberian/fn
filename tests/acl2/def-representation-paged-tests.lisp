; Teeth for the paged foundation's library keystones
; (books/def-representation-paged.lisp, -tree.lisp, -lib.lisp): Codex r37
; Q5, r40 F3, r47 F1/F4.  Each witness is a ground theorem: the library's
; functions on constant images, evaluated by the prover.  A POSITIVE
; witness asserts the theorem's complete antecedent and conclusion at its
; literal statement on a reachable image (one an export sequence makes:
; create, reserve, append); a HYPOTHESIS-REMOVAL witness asserts every
; retained hypothesis, the failure of the omitted one, and the failure of
; the conclusion, labelled with how its image is built.
;
; Images: schema ((:u64) (:octets)), three physical columns; R = 256 rows
; and Q = 16,384 octets a page; D and DP the page stobjs' creators.

(in-package "ACL2")
(include-book "../../books/def-representation")
(include-book "../../books/def-representation-tree")

(defconst *pt-s* '((:u64) (:octets)))
(defconst *pt-d* '(nil nil nil))
(defconst *pt-dp* '(nil))
(defconst *pt-c0* '(nil nil 0 0 0 0))
(defconst *pt-rec1* '(1 (9 9 9)))
(defconst *pt-rec2* '(2 (5 6)))
(defconst *pt-tree* '("fn.x" 3 -4 #\a (5 6 7) nil . :k))

(defmacro pt-append (rec c)
  `(adt-pg-append-c *pt-s* ,rec *adt-pg-rows* *adt-pg-octets* *pt-d* *pt-dp* ,c))

; -----------------------------------------------------------------------------
; 1. adt-pg-append-step-bound (r47 F1/F2): below the reservation an append
;    grows no directory; it adds one row page at most and pool pages for
;    its load L only.

; Positive: create, reserve 1,000 rows and 1,000 octets, append one record;
; the next append's load is 2 = L.
(defthm pt-step-bound-positive
  (let ((s *pt-s*) (r *adt-pg-rows*) (q *adt-pg-octets*) (d *pt-d*) (dp *pt-dp*)
        (c (pt-append *pt-rec1* (adt-pg-reserve-c 1000 1000 *adt-pg-rows* *adt-pg-octets* *pt-c0*)))
        (a (list *pt-rec1*)) (rec *pt-rec2*) (l 2))
    (and (adt-pg-corr s r q c a) (consp s)
         (< (nth 2 c) (* r *adt-pg-tpages* (len (nth 0 c))))
         (<= (+ (nth 3 c) (adt-rec-load s rec)) (* q *adt-pg-tpages* (len (nth 1 c))))
         (<= (adt-rec-load s rec) l)
         (let ((c2 (adt-pg-append-c s rec r q d dp c)))
           (and (equal (len (nth 0 c2)) (len (nth 0 c)))
                (equal (len (nth 1 c2)) (len (nth 1 c)))
                (<= (nth 4 c2) (+ 1 (nth 4 c)))
                (<= (* q (nth 5 c2)) (+ (* q (nth 5 c)) l (- q 1)))))))
  :rule-classes nil)

; Removal of the row reservation.  Image: the empty image with only its
; pool directory reserved (the library's adt-pg-dreserve; an export's
; reserve widens both), which corresponds to the empty sequence.  The first
; page's directory is made *adt-pg-dir-reserve* slots wide: it grows.
(defthm pt-step-bound-row-removal
  (let ((s *pt-s*) (r *adt-pg-rows*) (q *adt-pg-octets*) (d *pt-d*) (dp *pt-dp*)
        (c (adt-pg-dreserve 1 1 *pt-c0*)) (a nil) (rec *pt-rec2*) (l 2))
    (and (adt-pg-corr s r q c a) (consp s)
         (not (< (nth 2 c) (* r *adt-pg-tpages* (len (nth 0 c)))))
         (<= (+ (nth 3 c) (adt-rec-load s rec)) (* q *adt-pg-tpages* (len (nth 1 c))))
         (<= (adt-rec-load s rec) l)
         (let ((c2 (adt-pg-append-c s rec r q d dp c)))
           (not (and (equal (len (nth 0 c2)) (len (nth 0 c)))
                     (equal (len (nth 1 c2)) (len (nth 1 c)))
                     (<= (nth 4 c2) (+ 1 (nth 4 c)))
                     (<= (* q (nth 5 c2)) (+ (* q (nth 5 c)) l (- q 1))))))))
  :rule-classes nil)

; Removal of the pool reservation (image: only the row directory reserved).
(defthm pt-step-bound-pool-removal
  (let ((s *pt-s*) (r *adt-pg-rows*) (q *adt-pg-octets*) (d *pt-d*) (dp *pt-dp*)
        (c (adt-pg-dreserve 0 1 *pt-c0*)) (a nil) (rec *pt-rec2*) (l 2))
    (and (adt-pg-corr s r q c a) (consp s)
         (< (nth 2 c) (* r *adt-pg-tpages* (len (nth 0 c))))
         (not (<= (+ (nth 3 c) (adt-rec-load s rec)) (* q *adt-pg-tpages* (len (nth 1 c)))))
         (<= (adt-rec-load s rec) l)
         (let ((c2 (adt-pg-append-c s rec r q d dp c)))
           (not (and (equal (len (nth 0 c2)) (len (nth 0 c)))
                     (equal (len (nth 1 c2)) (len (nth 1 c)))
                     (<= (nth 4 c2) (+ 1 (nth 4 c)))
                     (<= (* q (nth 5 c2)) (+ (* q (nth 5 c)) l (- q 1))))))))
  :rule-classes nil)

; Removal of the load bound (reachable image: create, reserve; L = 0 under
; a load of 2): the first pool page is Q octets, more than L + Q - 1.
(defthm pt-step-bound-load-removal
  (let ((s *pt-s*) (r *adt-pg-rows*) (q *adt-pg-octets*) (d *pt-d*) (dp *pt-dp*)
        (c (adt-pg-reserve-c 1000 1000 *adt-pg-rows* *adt-pg-octets* *pt-c0*))
        (a nil) (rec *pt-rec2*) (l 0))
    (and (adt-pg-corr s r q c a) (consp s)
         (< (nth 2 c) (* r *adt-pg-tpages* (len (nth 0 c))))
         (<= (+ (nth 3 c) (adt-rec-load s rec)) (* q *adt-pg-tpages* (len (nth 1 c))))
         (not (<= (adt-rec-load s rec) l))
         (let ((c2 (adt-pg-append-c s rec r q d dp c)))
           (not (and (equal (len (nth 0 c2)) (len (nth 0 c)))
                     (equal (len (nth 1 c2)) (len (nth 1 c)))
                     (<= (nth 4 c2) (+ 1 (nth 4 c)))
                     (<= (* q (nth 5 c2)) (+ (* q (nth 5 c)) l (- q 1))))))))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; 2. The reservation: adt-pg-corr-reserve, adt-pg-reserve-capacity.

(defthm pt-corr-reserve-positive
  (let ((s *pt-s*) (r *adt-pg-rows*) (q *adt-pg-octets*)
        (c (pt-append *pt-rec1* *pt-c0*)) (a (list *pt-rec1*))
        (rows 5000000) (octets 2000000) (r2 *adt-pg-rows*) (q2 *adt-pg-octets*))
    (and (adt-pg-corr s r q c a)
         (adt-pg-corr s r q (adt-pg-reserve-c rows octets r2 q2 c) a)
         (equal (adt-pg-flat s (adt-pg-reserve-c rows octets r2 q2 c)) (adt-pg-flat s c))
         ; the reservation widened the row directory (5,000,000 rows: 306 slots)
         (< (len (nth 0 c)) (len (nth 0 (adt-pg-reserve-c rows octets r2 q2 c))))))
  :rule-classes nil)

; Removal of the correspondence (corrupted state: the empty image against a
; one-record sequence): the reserved image corresponds to it no more.
(defthm pt-corr-reserve-removal
  (let ((s *pt-s*) (r *adt-pg-rows*) (q *adt-pg-octets*)
        (c *pt-c0*) (a (list *pt-rec1*))
        (rows 70000) (octets 2000000) (r2 *adt-pg-rows*) (q2 *adt-pg-octets*))
    (and (not (adt-pg-corr s r q c a))
         (not (and (adt-pg-corr s r q (adt-pg-reserve-c rows octets r2 q2 c) a)
                   (equal (adt-pg-flat s (adt-pg-reserve-c rows octets r2 q2 c)) (adt-pg-flat s c))))))
  :rule-classes nil)

(defthm pt-reserve-capacity-positive
  (let ((rows 70000) (octets 2000000) (r *adt-pg-rows*) (q *adt-pg-octets*)
        (c (pt-append *pt-rec1* *pt-c0*)))
    (and (natp rows) (natp octets) (posp r) (posp q)
         (let ((c2 (adt-pg-reserve-c rows octets r q c)))
           (and (< rows (* r *adt-pg-tpages* (len (nth 0 c2))))
                (< octets (* q *adt-pg-tpages* (len (nth 1 c2))))
                (<= (len (nth 0 c)) (len (nth 0 c2)))
                (<= (len (nth 1 c)) (len (nth 1 c2)))))))
  :rule-classes nil)

; Removal of (posp r), the rest retained (r = 0: no row fits a page).
(defthm pt-reserve-capacity-r-removal
  (let ((rows 70000) (octets 2000000) (r 0) (q *adt-pg-octets*)
        (c (pt-append *pt-rec1* *pt-c0*)))
    (and (natp rows) (natp octets) (not (posp r)) (posp q)
         (not (let ((c2 (adt-pg-reserve-c rows octets r q c)))
                (and (< rows (* r *adt-pg-tpages* (len (nth 0 c2))))
                     (< octets (* q *adt-pg-tpages* (len (nth 1 c2))))
                     (<= (len (nth 0 c)) (len (nth 0 c2)))
                     (<= (len (nth 1 c)) (len (nth 1 c2))))))))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; 3. The two-level view (r47 F4): put and get are the one-level ones of the
;    view, the directory invariant kept; a page added; the page bounds.

(defthm pt-view-of-rput-positive
  (let ((c (pt-append *pt-rec1* *pt-c0*)) (ci 0) (n 0) (x 42) (r *adt-pg-rows*))
    (and (adt-pg-dokp *adt-pg-tpages* (nth 4 c) (nth 0 c)) (natp (nth 4 c))
         (natp n) (posp r) (< n (* r (nth 4 c)))
         (equal (adt-pg-view (adt-pg-rput ci n x r c)) (adt-pg1-rput ci n x r (adt-pg-view c)))
         (adt-pg-dokp *adt-pg-tpages* (nth 4 c) (nth 0 (adt-pg-rput ci n x r c)))
         (not (equal (adt-pg-rput ci n x r c) c))))
  :rule-classes nil)

(defthm pt-view-of-rget-positive
  (let ((c (pt-append *pt-rec1* *pt-c0*)) (ci 0) (n 0) (r *adt-pg-rows*))
    (and (adt-pg-dokp *adt-pg-tpages* (nth 4 c) (nth 0 c)) (natp (nth 4 c))
         (natp n) (posp r) (< n (* r (nth 4 c)))
         (equal (adt-pg-rget ci n r c) (adt-pg1-rget ci n r (adt-pg-view c)))
         (equal (adt-pg-rget ci n r c) 1)))
  :rule-classes nil)

(defthm pt-view-of-pput-positive
  (let ((c (pt-append *pt-rec1* *pt-c0*)) (i 1) (b 7) (q *adt-pg-octets*))
    (and (adt-pg-dokp *adt-pg-tpages* (nth 5 c) (nth 1 c)) (natp (nth 5 c))
         (natp i) (posp q) (< i (* q (nth 5 c)))
         (equal (adt-pg-view (adt-pg-pput i b q c)) (adt-pg1-pput i b q (adt-pg-view c)))
         (adt-pg-dokp *adt-pg-tpages* (nth 5 c) (nth 1 (adt-pg-pput i b q c)))
         (not (equal (adt-pg-pput i b q c) c))))
  :rule-classes nil)

(defthm pt-view-of-pget-positive
  (let ((c (pt-append *pt-rec1* *pt-c0*)) (i 1) (q *adt-pg-octets*))
    (and (adt-pg-dokp *adt-pg-tpages* (nth 5 c) (nth 1 c)) (natp (nth 5 c))
         (natp i) (posp q) (< i (* q (nth 5 c)))
         (equal (adt-pg-pget i q c) (adt-pg1-pget i q (adt-pg-view c)))
         (equal (adt-pg-pget i q c) 9)))
  :rule-classes nil)

(defthm pt-dadd-meaning-positive
  (let ((m 3) (r *adt-pg-rows*) (d *pt-d*) (k 0) (dir nil))
    (and (adt-pg-dokp *adt-pg-tpages* k dir) (natp k)
         (let ((dir2 (adt-pg-dadd m r d k dir)) (g (adt-pg-dgrown d k dir)))
           (and (adt-pg-dokp *adt-pg-tpages* (+ 1 k) dir2)
                (equal (adt-pg-dflat *adt-pg-tpages* (+ 1 k) dir2)
                       (update-nth k (adt-pg-fresh 0 m r (nth k g)) g))
                (equal (len dir2) *adt-pg-dir-reserve*)))))
  :rule-classes nil)

(defthm pt-addrow-tab-positive
  (let ((m 3) (r *adt-pg-rows*) (d *pt-d*) (c (pt-append *pt-rec1* *pt-c0*)))
    (and (adt-pg-dokp *adt-pg-tpages* (nth 4 c) (nth 0 c)) (natp (nth 4 c))
         (let ((c2 (adt-pg-addrow m r d c)) (g (adt-pg-dgrown d (nth 4 c) (nth 0 c))))
           (and (adt-pg-dokp *adt-pg-tpages* (+ 1 (nth 4 c)) (nth 0 c2))
                (equal (adt-pg-rtab c2) (update-nth (nth 4 c) (adt-pg-fresh 0 m r (nth (nth 4 c) g)) g))
                (equal (adt-pg-ptab c2) (adt-pg-ptab c))))))
  :rule-classes nil)

(defthm pt-addpool-tab-positive
  (let ((q *adt-pg-octets*) (d *pt-dp*) (c (pt-append *pt-rec1* *pt-c0*)))
    (and (adt-pg-dokp *adt-pg-tpages* (nth 5 c) (nth 1 c)) (natp (nth 5 c))
         (let ((c2 (adt-pg-addpool q d c)) (g (adt-pg-dgrown d (nth 5 c) (nth 1 c))))
           (and (adt-pg-dokp *adt-pg-tpages* (+ 1 (nth 5 c)) (nth 1 c2))
                (equal (adt-pg-ptab c2) (update-nth (nth 5 c) (adt-pg-fresh 0 1 q (nth (nth 5 c) g)) g))
                (equal (adt-pg-rtab c2) (adt-pg-rtab c))))))
  :rule-classes nil)

; Two pages asked for (20,000 octets): exactly two added, within the bound.
(defthm pt-poolroom-pages-bound-positive
  (let ((q *adt-pg-octets*) (d *pt-dp*) (c *pt-c0*) (need 20000))
    (and (posp q) (natp (nth 5 c)) (natp need)
         (<= (* q (nth 5 (adt-pg-poolroom q d need c)))
             (max (* q (nth 5 c)) (+ need (- q 1))))
         (equal (nth 5 (adt-pg-poolroom q d need c)) 2)))
  :rule-classes nil)

(defthm pt-append-pages-bound-positive
  (let ((s *pt-s*) (r *adt-pg-rows*) (q *adt-pg-octets*) (d *pt-d*) (dp *pt-dp*)
        (c *pt-c0*) (a nil) (rec *pt-rec1*))
    (and (adt-pg-corr s r q c a) (consp s)
         (let ((c2 (adt-pg-append-c s rec r q d dp c)))
           (and (<= (nth 4 c2) (+ 1 (nth 4 c)))
                (<= (* q (nth 5 c2)) (+ (* q (nth 5 c)) (adt-rec-load s rec) (- q 1)))
                (equal (nth 4 c2) 1) (equal (nth 5 c2) 1)))))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; 4. Codex r37 Q5: the sequence's correspondence and fill-is-load keystones,
;    positive on reachable images (create; one append).

(defthm pt-corr-of-grow-positive
  (let ((s *pt-s*) (c (adt-pg-flat *pt-s* (pt-append *pt-rec1* *pt-c0*))) (a (list *pt-rec1*))
        (z '(0 0)))
    (and (adt-corr s c a) (adt-zerosp z)
         (adt-corr s (adt-grow (adt-ncols s) z c) a)))
  :rule-classes nil)

(defthm pt-corr-of-grow-pool-positive
  (let ((s *pt-s*) (c (adt-pg-flat *pt-s* (pt-append *pt-rec1* *pt-c0*))) (a (list *pt-rec1*))
        (z '(0 0)))
    (and (adt-corr s c a) (adt-zerosp z)
         (adt-corr s (adt-grow-pool (adt-ncols s) z c) a)))
  :rule-classes nil)

(defthm pt-corr-append-positive
  (let ((s *pt-s*) (r *adt-pg-rows*) (q *adt-pg-octets*) (d *pt-d*) (dp *pt-dp*)
        (c (pt-append *pt-rec1* *pt-c0*)) (a (list *pt-rec1*)) (rec *pt-rec2*))
    (and (adt-pg-corr s r q c a) (consp s) (adt-rec-p s rec)
         (adt-pg-corr s r q (adt-pg-append-c s rec r q d dp c) (append a (list rec)))))
  :rule-classes nil)

(defthm pt-corr-set-positive
  (let ((s *pt-s*) (r *adt-pg-rows*) (q *adt-pg-octets*) (dp *pt-dp*)
        (c (pt-append *pt-rec1* *pt-c0*)) (a (list *pt-rec1*)) (j 1) (i 0) (v '(4 4)))
    (and (adt-pg-corr s r q c a) (consp s) (natp j) (< j (len s)) (natp i) (< i (len a))
         (adt-val-okp (nth j s) v)
         (adt-pg-corr s r q (adt-pg-set-c s j i v r q dp c) (adt-set-a j i v a))))
  :rule-classes nil)

(defthm pt-corr-get-positive
  (let ((s *pt-s*) (r *adt-pg-rows*) (q *adt-pg-octets*)
        (c (pt-append *pt-rec1* *pt-c0*)) (a (list *pt-rec1*)) (j 1) (i 0))
    (and (adt-pg-corr s r q c a) (consp s) (natp j) (< j (len s)) (natp i) (< i (len a))
         (equal (adt-pg-get-c s j i r q c) (nth j (nth i a)))
         (equal (adt-pg-get-c s j i r q c) '(9 9 9))))
  :rule-classes nil)

(defthm pt-corr-count-positive
  (let ((s *pt-s*) (r *adt-pg-rows*) (q *adt-pg-octets*)
        (c (pt-append *pt-rec1* *pt-c0*)) (a (list *pt-rec1*)))
    (and (adt-pg-corr s r q c a)
         (equal (nth 2 c) (len a))))
  :rule-classes nil)

(defthm pt-corr-empty-positive
  (let ((s *pt-s*) (r *adt-pg-rows*) (q *adt-pg-octets*) (c *pt-c0*))
    (and (adt-schemap s) (posp r) (posp q)
         (equal (nth 4 c) 0) (equal (nth 5 c) 0) (equal (nth 2 c) 0) (equal (nth 3 c) 0)
         (adt-pg-corr s r q c nil)))
  :rule-classes nil)

(defthm pt-corr-clear-positive
  (let ((s *pt-s*) (r *adt-pg-rows*) (q *adt-pg-octets*) (c (pt-append *pt-rec1* *pt-c0*)))
    (and (adt-schemap s) (posp r) (posp q)
         (adt-pg-corr s r q (adt-pg-clear-c c) nil)))
  :rule-classes nil)

(defthm pt-fill-is-load-of-append-positive
  (let ((s *pt-s*) (r *adt-pg-rows*) (q *adt-pg-octets*) (d *pt-d*) (dp *pt-dp*)
        (c (pt-append *pt-rec1* *pt-c0*)) (a (list *pt-rec1*)) (rec *pt-rec2*))
    (and (adt-pg-corr s r q c a) (consp s) (adt-fill-is-load s (adt-pg-flat s c) a)
         (adt-fill-is-load s (adt-pg-flat s (adt-pg-append-c s rec r q d dp c)) (append a (list rec)))))
  :rule-classes nil)

(defthm pt-fill-is-load-of-set-positive
  (let ((s *pt-s*) (r *adt-pg-rows*) (q *adt-pg-octets*) (dp *pt-dp*)
        (c (pt-append *pt-rec1* *pt-c0*)) (a (list *pt-rec1*)) (j 0) (i 0) (v 77))
    (and (adt-pg-corr s r q c a) (consp s) (natp j) (< j (len s))
         (not (adt-octets-kind-p (nth j s)))
         (natp i) (< i (len a))
         (adt-fill-is-load s (adt-pg-flat s c) a)
         (adt-fill-is-load s (adt-pg-flat s (adt-pg-set-c s j i v r q dp c)) (adt-set-a j i v a))))
  :rule-classes nil)

(defthm pt-fill-is-load-of-empty-positive
  (let ((s *pt-s*) (c *pt-c0*))
    (and (equal (nth 4 c) 0) (equal (nth 5 c) 0) (equal (nth 2 c) 0) (equal (nth 3 c) 0)
         (adt-fill-is-load s (adt-pg-flat s c) nil)))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; 5. The tree keystones (r37 Q5/Q6, r40 F3) and the scalar set (lib).

(defthm pt-cputs-is-poolw-positive
  (let ((q *adt-pg-octets*) (c (pt-append *pt-rec1* *pt-c0*)) (bytes '(1 2 3)))
    (and (adt-pg-pokp q c) (natp (nth 3 c)) (adt-octetsp bytes)
         (<= (+ (nth 3 c) (len bytes)) (* q (nth 5 c)))
         (equal (adt-pg-cputs bytes q c)
                (update-nth 3 (+ (nth 3 c) (len bytes)) (adt-pg-poolw (nth 3 c) bytes q c)))))
  :rule-classes nil)

(defthm pt-put-tree-is-put-field-positive
  (let ((ci 1) (n 0) (x *pt-tree*) (r *adt-pg-rows*) (q *adt-pg-octets*)
        (c (pt-append *pt-rec1* *pt-c0*)))
    (and (adt-pg-pokp q c) (natp (nth 3 c)) (fn-sccb-treep x)
         (<= (+ (nth 3 c) (len (fn-scc-program x))) (* q (nth 5 c)))
         (equal (adt-pg-put-tree ci n x r q c)
                (adt-pg-put-field '(:octets) ci n (fn-scc-program x) r q c))))
  :rule-classes nil)

(defthm pt-append-fields-t-is-append-fields-positive
  (let ((s0 *pt-s*) (s *pt-s*) (mask '(nil t)) (ci 0) (n 1) (rec (list 2 *pt-tree*))
        (r *adt-pg-rows*) (q *adt-pg-octets*)
        (c (pt-append *pt-rec1* *pt-c0*)))
    (and (adt-pg-rokp (adt-ncols s0) r c) (adt-pg-pokp q c)
         (natp ci) (<= (+ ci (adt-ncols s)) (adt-ncols s0))
         (natp n) (< n (* r (nth 4 c))) (natp (nth 3 c))
         (adt-pg-tmask-kinds-okp s mask) (adt-pg-tmask-okp mask rec)
         (<= (+ (nth 3 c) (adt-rec-load s (adt-pg-tmask-enc mask rec))) (* q (nth 5 c)))
         (equal (adt-pg-append-fields-t s mask ci n rec r q c)
                (adt-pg-append-fields s ci n (adt-pg-tmask-enc mask rec) r q c))))
  :rule-classes nil)

(defthm pt-append-t-c-is-append-c-positive
  (let ((s *pt-s*) (r *adt-pg-rows*) (q *adt-pg-octets*) (d *pt-d*) (dp *pt-dp*)
        (c (pt-append *pt-rec1* *pt-c0*)) (a (list *pt-rec1*))
        (mask '(nil t)) (rec (list 2 *pt-tree*)))
    (and (adt-pg-corr s r q c a) (consp s)
         (adt-pg-tmask-kinds-okp s mask) (adt-pg-tmask-okp mask rec)
         (equal (adt-pg-append-t-c s mask rec r q d dp c)
                (adt-pg-append-c s (adt-pg-tmask-enc mask rec) r q d dp c))))
  :rule-classes nil)

(defthm pt-corr-set-scalar-positive
  (let ((s '((:u64))) (r *adt-pg-rows*) (q *adt-pg-octets*) (dp *pt-dp*)
        (c (adt-pg-append-c '((:u64)) '(4) *adt-pg-rows* *adt-pg-octets* '(nil) *pt-dp* *pt-c0*))
        (a '(4)) (i 0) (v 11))
    (and (adt-pg-corr s r q c (adt-wrap1 a)) (equal (len s) 1)
         (natp i) (< i (len a)) (adt-val-okp (car s) v)
         (adt-pg-corr s r q (adt-pg-set-c s 0 i v r q dp c) (update-nth i (list v) (adt-wrap1 a)))))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; 6. A generated instance's reservation, executed (r47 F1): NAME$C-RESERVE
;    widens the row directory once (5,000,000 rows: 306 slots of 64 pages of
;    256 rows) and the pool's (2,000,000 octets: 2 slots of 64 pages of
;    16 KiB), and 1,000 appends leave both so; with no reservation the
;    first append makes each *adt-pg-dir-reserve* = 256 slots.  The abstract export
;    is the identity (PT-INS-RESERVE-IS-IDENTITY, generated).

(def-representation pt-ins (a :u64) (m :octets))

(defun pt-ins-fill (i n pt-ins$c)
  (declare (xargs :stobjs pt-ins$c :verify-guards nil :measure (nfix (- (nfix n) (nfix i)))))
  (if (< (nfix i) (nfix n))
      (let ((pt-ins$c (pt-ins$c-append (list i '(1 2 3)) pt-ins$c)))
        (pt-ins-fill (+ 1 (nfix i)) n pt-ins$c))
    pt-ins$c))

(defun pt-ins-run (pt-ins$c)
  (declare (xargs :stobjs pt-ins$c :verify-guards nil))
  (let* ((pt-ins$c (pt-ins$c-clear pt-ins$c))
         (pt-ins$c (pt-ins$c-append (list 0 '(1)) pt-ins$c))
         (unreserved (pt-ins$c-rows-length pt-ins$c))
         (pt-ins$c (pt-ins$c-clear pt-ins$c))
         (pt-ins$c (pt-ins$c-reserve 5000000 2000000 pt-ins$c))
         (r0 (pt-ins$c-rows-length pt-ins$c))
         (p0 (pt-ins$c-ppages-length pt-ins$c))
         (pt-ins$c (pt-ins-fill 0 1000 pt-ins$c)))
    (mv (list unreserved r0 p0 (pt-ins$c-rows-length pt-ins$c) (pt-ins$c-ppages-length pt-ins$c)
              (pt-ins$c-count pt-ins$c))
        pt-ins$c)))

(defun pt-ins-run-ok ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj pt-ins$c
    (mv-let (got pt-ins$c) (pt-ins-run pt-ins$c)
      (equal got '(256 306 2 306 2 1000)))))

(assert-event (pt-ins-run-ok))
