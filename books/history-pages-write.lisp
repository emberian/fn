; fn: the history's writer, its model: the appended history's image words
; are the old ones with six blocks replaced (lane arena-store-3,
; 2026-09-28).  Prefix fn-hp-.
;
; An append of one event EV to H changes the image's words in six blocks:
; the header's words 6-17 (N, R and the region table: the lengths change,
; the starts do not while no region changes its cap), one cell at the end of
; each of the four columns, and the padded tree at the end of the pool
; (`fn-hp-blocks').  Proved over octets (`fn-hp-rep', a block replacement)
; and carried to words (`fn-hp-pack8-rep'), region by region
; (`fn-hp-wbody-blocks').  books/history-pages-write-exec.lisp is the stobj
; writer; books/history-pages-write-keys.lisp its keystone.
(in-package "ACL2")
(include-book "history-pages-read")
(local (include-book "arithmetic/top" :dir :system))

; -----------------------------------------------------------------------------
; A. Replacing a block, in octets and in words.

(defun fn-hp-rep (b o x)
  ; B with X in place of its octets (or words) [O, O + |X|)
  (declare (xargs :guard (and (true-listp b) (natp o) (true-listp x))))
  (append (take o b) x (nthcdr (+ (nfix o) (len x)) b)))

(local
 (defun fn-hp-pa-ind (k x)
   (if (zp k) (list k x) (fn-hp-pa-ind (1- k) (nthcdr 8 x)))))

(local (defthm fn-hp-append-len0 (implies (equal (len x) 0) (equal (append x y) y))))

(defthm fn-hp-pack8-append
  (implies (and (natp k1) (natp k2) (equal (len x) (* 8 k1)))
           (equal (fn-hp-pack8 (+ k1 k2) (append x y))
                  (append (fn-hp-pack8 k1 x) (fn-hp-pack8 k2 y))))
  :hints (("Goal" :induct (fn-hp-pa-ind k1 x) :expand ((fn-hp-pack8 (+ k1 k2) (append x y)) (fn-hp-pack8 k1 x)))))
(local
 (defun fn-hp-pt-ind (k m b)
   (if (zp k) (list k m b) (fn-hp-pt-ind (1- k) (- m 8) (nthcdr 8 b)))))

(local
 (defun fn-hp-nt-ind (a m b)
   (if (zp a) (list a m b) (fn-hp-nt-ind (1- a) (1- m) (cdr b)))))

(defthm fn-hp-nthcdr-of-take
  (implies (and (natp a) (natp m) (<= a m))
           (equal (nthcdr a (take m b)) (take (- m a) (nthcdr a b))))
  :hints (("Goal" :induct (fn-hp-nt-ind a m b) :in-theory (enable take nthcdr))))

(defthm fn-hp-pack8-take
  (implies (and (natp k) (natp m) (<= (* 8 k) m))
           (equal (fn-hp-pack8 k (take m b)) (fn-hp-pack8 k b)))
  :hints (("Goal" :induct (fn-hp-pt-ind k m b) :expand ((fn-hp-pack8 k (take m b)) (fn-hp-pack8 k b))
           :in-theory (enable take nthcdr))))

(local
 (defthm fn-hp-len-take-x
   (equal (len (take n b)) (nfix n))))

(defthm fn-hp-pack8-rep
  (implies (and (natp m) (natp j) (natp k) (equal (len x) (* 8 k))
                (<= (+ j k) m) (<= (* 8 m) (len b)))
           (equal (fn-hp-pack8 m (fn-hp-rep b (* 8 j) x))
                  (fn-hp-rep (fn-hp-pack8 m b) j (fn-hp-pack8 k x))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-pack8-append (k1 j) (k2 (- m j)) (x (take (* 8 j) b))
                            (y (append x (nthcdr (+ (* 8 j) (len x)) b))))
                 (:instance fn-hp-pack8-append (k1 k) (k2 (- m (+ j k))) (x x)
                            (y (nthcdr (+ (* 8 j) (len x)) b))))
           :in-theory (disable fn-hp-pack8-append))))
(local
 (defun fn-hp-zeros-ind2 (m z)
   (if (or (zp m) (zp z)) (list m z) (fn-hp-zeros-ind2 (1- m) (1- z)))))

(defthm fn-hp-nthcdr-of-zeros
  (implies (and (natp m) (<= m (nfix z)))
           (equal (nthcdr m (adt-zeros z)) (adt-zeros (- (nfix z) m))))
  :hints (("Goal" :in-theory (enable nthcdr) :induct (fn-hp-zeros-ind2 m z))))

(defthm fn-hp-pad-of-append
  (implies (and (true-listp r) (true-listp d)
                (equal (adt-cap (+ (len r) (len d))) (adt-cap (len r))))
           (equal (adt-pad (append r d)) (fn-hp-rep (adt-pad r) (len r) d)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance adt-cap-covers (u (+ (len r) (len d)))))
           :in-theory (e/d (adt-pad) (adt-cap adt-cap-covers)))))
(defthm fn-hp-take-past-prefix
  (implies (and (natp j) (true-listp p))
           (equal (take (+ (len p) j) (append p z)) (append p (take j z))))
  :hints (("Goal" :in-theory (enable take) :induct (len p))))

(defthm fn-hp-nthcdr-past-prefix
  (implies (natp j)
           (equal (nthcdr (+ (len p) j) (append p z)) (nthcdr j z)))
  :hints (("Goal" :in-theory (enable nthcdr) :induct (len p))))

(defthm fn-hp-rep-middle
  (implies (and (natp j) (true-listp p) (true-listp x) (<= (+ j (len b)) (len x)))
           (equal (fn-hp-rep (append p x y) (+ (len p) j) b)
                  (append p (fn-hp-rep x j b) y)))
  :hints (("Goal" :do-not-induct t :in-theory (enable fn-hp-rep)
           :use ((:instance fn-hp-take-past-prefix (z (append x y)))
                 (:instance fn-hp-nthcdr-past-prefix (j (+ j (len b))) (z (append x y)))))))

(defthm fn-hp-len-rep
  (implies (and (natp o) (<= (+ o (len x)) (len b)))
           (equal (len (fn-hp-rep b o x)) (len b))))

(defthm fn-hp-true-listp-rep
  (implies (true-listp b) (true-listp (fn-hp-rep b o x))))

(in-theory (disable fn-hp-rep))

; A region's words: its padded octets, packed.
(defun fn-hp-wpad (r)
  (declare (xargs :verify-guards nil))
  (fn-hp-pack8 (* 2048 (adt-cap (len r))) (adt-pad r)))

(defun fn-hp-wbody (regs)
  (declare (xargs :verify-guards nil))
  (if (atom regs) nil (append (fn-hp-wpad (car regs)) (fn-hp-wbody (cdr regs)))))

(defun fn-hp-caps-sum (regs)
  (declare (xargs :guard (true-list-listp regs)))
  (if (atom regs) 0 (+ (adt-cap (len (car regs))) (fn-hp-caps-sum (cdr regs)))))

(defthm fn-hp-pack8-body
  (equal (fn-hp-pack8 (* 2048 (fn-hp-caps-sum regs)) (adt-body regs))
         (fn-hp-wbody regs))
  :hints (("Goal" :induct (fn-hp-wbody regs) :in-theory (disable adt-cap adt-pad fn-hp-pack8))
          ("Subgoal *1/2" :use ((:instance fn-hp-pack8-append (k1 (* 2048 (adt-cap (len (car regs)))))
                                           (k2 (* 2048 (fn-hp-caps-sum (cdr regs))))
                                           (x (adt-pad (car regs))) (y (adt-body (cdr regs))))))))
(defthm fn-hp-len-wpad
  (equal (len (fn-hp-wpad r)) (* 2048 (adt-cap (len r)))))

(defthm fn-hp-true-listp-wpad (true-listp (fn-hp-wpad r)))

(defthm fn-hp-true-listp-pack8 (true-listp (fn-hp-pack8 n b)))

(defthm fn-hp-wpad-of-append
  (implies (and (true-listp r) (true-listp d)
                (equal (mod (len r) 8) 0) (equal (mod (len d) 8) 0)
                (equal (adt-cap (+ (len r) (len d))) (adt-cap (len r))))
           (equal (fn-hp-wpad (append r d))
                  (fn-hp-rep (fn-hp-wpad r) (floor (len r) 8) (fn-hp-pack8 (floor (len d) 8) d))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-pad-of-append)
                 (:instance adt-cap-covers (u (+ (len r) (len d))))
                 (:instance fn-hp-floor-8-exact (x (len r)))
                 (:instance fn-hp-floor-8-exact (x (len d)))
                 (:instance fn-hp-pack8-rep (m (* 2048 (adt-cap (len r)))) (b (adt-pad r))
                            (j (floor (len r) 8)) (k (floor (len d) 8)) (x d)))
           :in-theory (disable fn-hp-pad-of-append adt-cap-covers fn-hp-pack8-rep adt-cap adt-pad
                               fn-hp-floor-8-exact floor mod fn-hp-pack8))))
(in-theory (disable fn-hp-wpad))

(defun fn-hp-wreps (w blocks)
  ; W with each block (J . WORDS) in place, in order
  (declare (xargs :guard (and (true-listp w) (alistp blocks))))
  (if (atom blocks) w
    (fn-hp-wreps (fn-hp-rep w (nfix (car (car blocks))) (true-list-fix (cdr (car blocks)))) (cdr blocks))))

(defun fn-hp-body-blocks (regs ds base)
  ; the blocks an in-place growth of REGS by DS writes, the body from page BASE
  (declare (xargs :verify-guards nil))
  (if (atom regs) nil
    (cons (cons (+ (* 2048 (nfix base)) (floor (len (car regs)) 8))
                (fn-hp-pack8 (floor (len (car ds)) 8) (car ds)))
          (fn-hp-body-blocks (cdr regs) (cdr ds) (+ (nfix base) (adt-cap (len (car regs))))))))

(defun fn-hp-deltas-ok (regs ds)
  ; every region and delta word-aligned, and no region's cap changes
  (declare (xargs :verify-guards nil))
  (if (atom regs) t
    (and (consp ds) (true-listp (car regs)) (true-listp (car ds))
         (equal (mod (len (car regs)) 8) 0) (equal (mod (len (car ds)) 8) 0)
         (equal (adt-cap (+ (len (car regs)) (len (car ds)))) (adt-cap (len (car regs))))
         (fn-hp-deltas-ok (cdr regs) (cdr ds)))))

(local
 (defun fn-hp-bb-ind (regs ds base p)
   (declare (xargs :verify-guards nil))
   (if (atom regs) (list ds base p)
     (fn-hp-bb-ind (cdr regs) (cdr ds) (+ (nfix base) (adt-cap (len (car regs))))
                   (append p (fn-hp-wpad (append (car regs) (car ds))))))))

(local (defthm fn-hp-append-assoc (equal (append (append a b) c) (append a (append b c)))))

(defthm fn-hp-wbody-blocks
  (implies (and (true-listp p) (natp base) (equal (len p) (* 2048 base)) (fn-hp-deltas-ok regs ds))
           (equal (fn-hp-wreps (append p (fn-hp-wbody regs)) (fn-hp-body-blocks regs ds base))
                  (append p (fn-hp-wbody (fn-hp-zapp regs ds)))))
  :hints (("Goal" :induct (fn-hp-bb-ind regs ds base p) :in-theory (disable adt-cap floor mod fn-hp-pack8))
          ("Subgoal *1/2" :use ((:instance fn-hp-rep-middle (j (floor (len (car regs)) 8)) (x (fn-hp-wpad (car regs)))
                                           (y (fn-hp-wbody (cdr regs)))
                                           (b (fn-hp-pack8 (floor (len (car ds)) 8) (car ds))))
                                (:instance adt-cap-covers (u (+ (len (car regs)) (len (car ds)))))
                                (:instance fn-hp-floor-8-exact (x (len (car regs))))
                                (:instance fn-hp-floor-8-exact (x (len (car ds))))))))
; -----------------------------------------------------------------------------
; B. The regions of the appended history: each region grows by its delta.

(local
 (defthm fn-hp-w-rows-cells-of-append
   (implies (natp pos)
            (equal (adt-rows-cells s (append a b) pos)
                   (append (adt-rows-cells s a pos)
                           (adt-rows-cells s b (+ pos (len (adt-rows-pool s a)))))))
   :hints (("Goal" :induct (adt-rows-cells s a pos) :in-theory (disable adt-row-cells adt-row-pool)))))

(local
 (defthm fn-hp-w-rows-pool-of-append
   (equal (adt-rows-pool s (append a b)) (append (adt-rows-pool s a) (adt-rows-pool s b)))
   :hints (("Goal" :in-theory (disable adt-row-pool)))))

(local (defthm fn-hp-w-cars-of-append (equal (adt-cars (append x y)) (append (adt-cars x) (adt-cars y)))))
(local (defthm fn-hp-w-cdrs-of-append (equal (adt-cdrs (append x y)) (append (adt-cdrs x) (adt-cdrs y)))))

(local
 (defthm fn-hp-w-transpose-of-append
   (equal (adt-transpose m (append x y))
          (fn-hp-zapp (adt-transpose m x) (adt-transpose m y)))))

(local
 (defthm fn-hp-w-le-list-of-append
   (equal (adt-le-list w (append x y)) (append (adt-le-list w x) (adt-le-list w y)))))

(local
 (defthm fn-hp-w-col-regs-of-zapp
   (implies (equal (len c1) (len ws))
            (equal (adt-col-regs ws (fn-hp-zapp c1 c2))
                   (fn-hp-zapp (adt-col-regs ws c1) (adt-col-regs ws c2))))))

(local
 (defthm fn-hp-w-zapp-snoc
   (implies (equal (len x) (len y))
            (equal (fn-hp-zapp (append x (list p)) (append y (list q)))
                   (append (fn-hp-zapp x y) (list (append p q)))))))

(defun fn-hp-ds (ev salt off)
  ; the regions' deltas when EV is appended with its pool entry at OFF
  (declare (xargs :verify-guards nil))
  (list (adt-le 8 (fn-hp-mkey ev salt)) (adt-le 8 (len (fn-scc-encode ev)))
        (adt-le 8 off) (adt-le 8 (len (fn-hp-pe ev))) (fn-hp-pe ev)))

(local
 (defthm fn-hp-w-row-cells-of-row
   (equal (adt-row-cells *fn-hp-schema* (fn-hp-row ev salt) pos)
          (cons (fn-hp-cells-of ev salt pos) (+ (nfix pos) (len (fn-hp-pe ev)))))
   :hints (("Goal" :in-theory (e/d (adt-enc fn-hp-pe) (fn-scc-encode fn-scc-program fn-hp-mkey fn-hp-pad8))))))

(local
 (defthm fn-hp-w-row-pool-of-row
   (equal (adt-row-pool *fn-hp-schema* (fn-hp-row ev salt)) (fn-hp-pe ev))
   :hints (("Goal" :in-theory (e/d (fn-hp-pe) (fn-scc-encode fn-hp-mkey))))))

(local
 (defthm fn-hp-w-cells-of-is
   (equal (fn-hp-cells-of ev salt pos)
          (list (fn-hp-mkey ev salt) (len (fn-scc-encode ev)) (nfix pos) (len (fn-hp-pe ev))))
   :hints (("Goal" :in-theory (e/d (fn-hp-pe) (fn-scc-encode fn-hp-mkey fn-hp-pad8))))))

(defthm fn-hp-regs-of-append1
  (equal (fn-hp-regs (append h (list ev)) salt)
         (fn-hp-zapp (fn-hp-regs h salt) (fn-hp-ds ev salt (fn-hp-pes-len h))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (adt-regs) (fn-hp-row fn-hp-mkey fn-scc-encode fn-hp-pe fn-hp-rows-pool-is-pes fn-hp-pad8 fn-scc-program
                                                 adt-row-cells adt-row-pool))
           :use ((:instance fn-hp-rows-pool-is-pes)))))
; -----------------------------------------------------------------------------
; C. The header: N and the lengths change, the rest does not.

(defun fn-hp-hmeta (n r starts lens)
  ; the header's octets 48 on: N, R, then the (start, length) pairs
  (declare (xargs :verify-guards nil))
  (append (adt-le 8 n) (adt-le 8 r) (adt-meta starts lens)))

(defthm fn-hp-len-meta
  (equal (len (adt-meta starts lens)) (* 16 (len starts))))

(local
 (defthm fn-hp-rep-whole
   (implies (and (true-listp m) (true-listp m2) (equal (len m2) (len m)))
            (equal (fn-hp-rep m 0 m2) m2))
   :hints (("Goal" :in-theory (enable fn-hp-rep)))))

(defthm fn-hp-header-of-meta
  (implies (and (equal (len regs2) (len regs))
                (<= (+ 64 (* 16 (len regs))) *adt-page*)
                (equal (adt-starts regs2 1) (adt-starts regs 1)))
           (equal (adt-header s n2 regs2)
                  (fn-hp-rep (adt-header s n regs) 48
                             (fn-hp-hmeta n2 (len regs) (adt-starts regs 1) (adt-lens regs2)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-rep-middle (p (append (adt-hdr-const) (adt-schema-digest s))) (j 0)
                            (x (fn-hp-hmeta n (len regs) (adt-starts regs 1) (adt-lens regs)))
                            (y (adt-zeros (- *adt-page* (+ 64 (* 16 (len regs))))))
                            (b (fn-hp-hmeta n2 (len regs) (adt-starts regs 1) (adt-lens regs2)))))
           :in-theory (e/d (adt-header adt-header-content) (fn-hp-rep-middle adt-starts adt-lens)))))

(defun fn-hp-u64-listp (xs)
  (declare (xargs :guard t))
  (if (atom xs) (null xs) (and (unsigned-byte-p 64 (car xs)) (fn-hp-u64-listp (cdr xs)))))

(defun fn-hp-meta-words (starts lens)
  (declare (xargs :guard (and (true-listp starts) (true-listp lens))))
  (if (atom starts) nil
    (list* (car starts) (car lens) (fn-hp-meta-words (cdr starts) (cdr lens)))))

(defthm fn-hp-pack8-le
  (implies (and (natp k) (unsigned-byte-p 64 x))
           (equal (fn-hp-pack8 (+ 1 k) (append (adt-le 8 x) rest))
                  (cons x (fn-hp-pack8 k rest))))
  :hints (("Goal" :expand ((fn-hp-pack8 (+ 1 k) (append (adt-le 8 x) rest)))
           :use ((:instance adt-unle-le (w 8)))
           :in-theory (disable adt-unle-le adt-le adt-unle))))

(defthm fn-hp-pack8-le2
  (implies (and (posp c) (unsigned-byte-p 64 x))
           (equal (fn-hp-pack8 c (append (adt-le 8 x) rest))
                  (cons x (fn-hp-pack8 (1- c) rest))))
  :hints (("Goal" :use ((:instance fn-hp-pack8-le (k (1- c)))) :in-theory (disable fn-hp-pack8-le adt-le fn-hp-pack8))))

(defthm fn-hp-pack8-meta
  (implies (and (fn-hp-u64-listp starts) (fn-hp-u64-listp lens) (equal (len lens) (len starts)))
           (equal (fn-hp-pack8 (* 2 (len starts)) (adt-meta starts lens))
                  (fn-hp-meta-words starts lens)))
  :hints (("Goal" :induct (fn-hp-meta-words starts lens) :in-theory (disable adt-le fn-hp-pack8-le))
          ("Subgoal *1/1" :expand ((fn-hp-pack8 0 nil)))))

(defthm fn-hp-pack8-hmeta
  (implies (and (unsigned-byte-p 64 n) (unsigned-byte-p 64 r)
                (fn-hp-u64-listp starts) (fn-hp-u64-listp lens) (equal (len lens) (len starts)))
           (equal (fn-hp-pack8 (+ 2 (* 2 (len starts))) (fn-hp-hmeta n r starts lens))
                  (list* n r (fn-hp-meta-words starts lens))))
  :hints (("Goal" :do-not-induct t :use ((:instance fn-hp-pack8-meta)) :in-theory (disable fn-hp-pack8-le adt-le fn-hp-pack8 fn-hp-pack8-meta))))
; -----------------------------------------------------------------------------
; D. The appended history's words are the old words with six blocks replaced.

(defthm fn-hp-end-is-caps-sum
  (implies (natp s) (equal (adt-end regs s) (+ s (fn-hp-caps-sum regs))))
  :hints (("Goal" :induct (adt-end regs s) :in-theory (disable adt-cap))))

(defthm fn-hp-len-regs-5
  (equal (len (fn-hp-regs h salt)) 5)
  :hints (("Goal" :in-theory (enable adt-regs))))

(defthm fn-hp-len-header-5
  (implies (equal (len regs) 5) (equal (len (adt-header s n regs)) 16384))
  :hints (("Goal" :in-theory (enable adt-header))))

(defthmd fn-hp-npages-is-caps-sum
  (equal (fn-hp-npages h salt) (+ 1 (fn-hp-caps-sum (fn-hp-regs h salt))))
  :hints (("Goal" :in-theory (e/d (fn-hp-npages) (fn-hp-regs adt-end-is-end-l fn-hp-npages-is-end-l fn-hp-lens)))))

(defthm fn-hp-iw-split
  (equal (fn-hp-iw h salt)
         (append (fn-hp-pack8 2048 (adt-header *fn-hp-schema* (len h) (fn-hp-regs h salt)))
                 (fn-hp-wbody (fn-hp-regs h salt))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-pack8-append (k1 2048) (k2 (* 2048 (fn-hp-caps-sum (fn-hp-regs h salt))))
                            (x (adt-header *fn-hp-schema* (len h) (fn-hp-regs h salt)))
                            (y (adt-body (fn-hp-regs h salt))))
                 (:instance fn-hp-npages-is-caps-sum))
           :in-theory (e/d (fn-hp-iw fn-hp-image)
                           (fn-hp-pack8-append fn-hp-pack8 adt-header adt-body fn-hp-regs adt-regs fn-hp-rows
                            fn-hp-npages)))
          ("Goal'" :in-theory (e/d (adt-ser fn-hp-regs) (fn-hp-pack8-append fn-hp-pack8 adt-header adt-body adt-regs fn-hp-rows fn-hp-npages)))))
(defthm fn-hp-starts-of-zapp
  (implies (fn-hp-deltas-ok regs ds)
           (equal (adt-starts (fn-hp-zapp regs ds) s) (adt-starts regs s)))
  :hints (("Goal" :induct (fn-hp-body-blocks regs ds s) :in-theory (disable adt-cap))))

(defthm fn-hp-len-zapp (equal (len (fn-hp-zapp regs ds)) (len regs)))

(defthm fn-hp-caps-sum-of-zapp
  (implies (fn-hp-deltas-ok regs ds)
           (equal (fn-hp-caps-sum (fn-hp-zapp regs ds)) (fn-hp-caps-sum regs)))
  :hints (("Goal" :in-theory (disable adt-cap))))

(defun fn-hp-hb (n2 starts lens2)
  ; the header's words 6-17 after an append: N, R, the (start, length) pairs
  (declare (xargs :guard (and (true-listp starts) (true-listp lens2))))
  (list* n2 5 (fn-hp-meta-words starts lens2)))

(defun fn-hp-blocks (h ev salt)
  ; the blocks the append of EV to H writes: the header's words 6-17, then
  ; per region its delta at its end
  (declare (xargs :verify-guards nil))
  (let ((regs (fn-hp-regs h salt)) (ds (fn-hp-ds ev salt (fn-hp-pes-len h))))
    (cons (cons 6 (fn-hp-hb (+ 1 (len h)) (adt-starts regs 1) (adt-lens (fn-hp-zapp regs ds))))
          (fn-hp-body-blocks regs ds 1))))

(defthm fn-hp-len-meta-words
  (equal (len (fn-hp-meta-words starts lens)) (* 2 (len starts))))

(defthm fn-hp-len-hmeta
  (equal (len (fn-hp-hmeta n r starts lens)) (+ 16 (* 16 (len starts)))))

(defthm fn-hp-header-words-of-append1
  (implies (and (fn-hp-deltas-ok (fn-hp-regs h salt) (fn-hp-ds ev salt (fn-hp-pes-len h)))
                (unsigned-byte-p 64 (+ 1 (len h)))
                (fn-hp-u64-listp (adt-starts (fn-hp-regs h salt) 1))
                (fn-hp-u64-listp (adt-lens (fn-hp-zapp (fn-hp-regs h salt) (fn-hp-ds ev salt (fn-hp-pes-len h))))))
           (equal (fn-hp-pack8 2048 (adt-header *fn-hp-schema* (+ 1 (len h)) (fn-hp-regs (append h (list ev)) salt)))
                  (fn-hp-rep (fn-hp-pack8 2048 (adt-header *fn-hp-schema* (len h) (fn-hp-regs h salt)))
                             6 (fn-hp-hb (+ 1 (len h)) (adt-starts (fn-hp-regs h salt) 1)
                                         (adt-lens (fn-hp-zapp (fn-hp-regs h salt) (fn-hp-ds ev salt (fn-hp-pes-len h))))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-header-of-meta (s *fn-hp-schema*) (n (len h)) (n2 (+ 1 (len h)))
                            (regs (fn-hp-regs h salt))
                            (regs2 (fn-hp-zapp (fn-hp-regs h salt) (fn-hp-ds ev salt (fn-hp-pes-len h)))))
                 (:instance fn-hp-pack8-rep (m 2048) (j 6) (k 12)
                            (b (adt-header *fn-hp-schema* (len h) (fn-hp-regs h salt)))
                            (x (fn-hp-hmeta (+ 1 (len h)) 5 (adt-starts (fn-hp-regs h salt) 1)
                                            (adt-lens (fn-hp-zapp (fn-hp-regs h salt) (fn-hp-ds ev salt (fn-hp-pes-len h)))))))
                 (:instance fn-hp-pack8-hmeta (n (+ 1 (len h))) (r 5) (starts (adt-starts (fn-hp-regs h salt) 1))
                            (lens (adt-lens (fn-hp-zapp (fn-hp-regs h salt) (fn-hp-ds ev salt (fn-hp-pes-len h)))))))
           :in-theory (disable fn-hp-header-of-meta fn-hp-pack8-rep fn-hp-pack8-hmeta fn-hp-regs fn-hp-ds adt-header
                               fn-hp-zapp fn-hp-pack8 adt-starts adt-lens fn-hp-hmeta fn-hp-deltas-ok adt-starts-is-starts-l))))
(defthm fn-hp-rep-front
  (implies (and (natp j) (true-listp x) (<= (+ j (len b)) (len x)))
           (equal (fn-hp-rep (append x y) j b) (append (fn-hp-rep x j b) y)))
  :hints (("Goal" :use ((:instance fn-hp-rep-middle (p nil))) :in-theory (disable fn-hp-rep-middle))))

(defthm fn-hp-len-pack8-2048 (equal (len (fn-hp-pack8 2048 b)) 2048))

(defthm fn-hp-true-listp-hb (true-listp (fn-hp-hb n2 starts lens2)))

(defthm fn-hp-len-hb
  (equal (len (fn-hp-hb n2 starts lens2)) (+ 2 (* 2 (len starts)))))

; The model theorem (the append's words): the appended history's image words
; are the old image words with the six blocks of `fn-hp-blocks' in place,
; when no region's cap changes and the header's new fields are u64.  The
; host-called writer's keystone is `fn-hp-x-append-refines'
; (books/history-pages-write-keys.lisp).
(defthm fn-hp-iw-of-append1
  (implies (and (fn-hp-deltas-ok (fn-hp-regs h salt) (fn-hp-ds ev salt (fn-hp-pes-len h)))
                (unsigned-byte-p 64 (+ 1 (len h)))
                (fn-hp-u64-listp (adt-starts (fn-hp-regs h salt) 1))
                (fn-hp-u64-listp (adt-lens (fn-hp-zapp (fn-hp-regs h salt) (fn-hp-ds ev salt (fn-hp-pes-len h))))))
           (equal (fn-hp-iw (append h (list ev)) salt)
                  (fn-hp-wreps (fn-hp-iw h salt) (fn-hp-blocks h ev salt))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-iw-split (h (append h (list ev))))
                 (:instance fn-hp-iw-split)
                 (:instance fn-hp-header-words-of-append1)
                 (:instance fn-hp-wbody-blocks (base 1) (regs (fn-hp-regs h salt))
                            (ds (fn-hp-ds ev salt (fn-hp-pes-len h)))
                            (p (fn-hp-rep (fn-hp-pack8 2048 (adt-header *fn-hp-schema* (len h) (fn-hp-regs h salt)))
                                          6 (fn-hp-hb (+ 1 (len h)) (adt-starts (fn-hp-regs h salt) 1)
                                                      (adt-lens (fn-hp-zapp (fn-hp-regs h salt)
                                                                            (fn-hp-ds ev salt (fn-hp-pes-len h))))))))
                 (:instance fn-hp-rep-front (j 6)
                            (x (fn-hp-pack8 2048 (adt-header *fn-hp-schema* (len h) (fn-hp-regs h salt))))
                            (y (fn-hp-wbody (fn-hp-regs h salt)))
                            (b (fn-hp-hb (+ 1 (len h)) (adt-starts (fn-hp-regs h salt) 1)
                                         (adt-lens (fn-hp-zapp (fn-hp-regs h salt)
                                                               (fn-hp-ds ev salt (fn-hp-pes-len h))))))))
           :in-theory (e/d (fn-hp-blocks)
                           (fn-hp-iw-split fn-hp-header-words-of-append1 fn-hp-wbody-blocks fn-hp-rep-front
                            fn-hp-iw fn-hp-regs fn-hp-ds adt-header fn-hp-zapp fn-hp-pack8 adt-starts adt-lens
                            fn-hp-hb fn-hp-deltas-ok adt-starts-is-starts-l fn-hp-body-blocks fn-hp-wbody
                            fn-hp-regs-of-append1)))
          ("Goal'" :use ((:instance fn-hp-regs-of-append1)))))
; -----------------------------------------------------------------------------
; E. Agreement on a range of words survives a block replacement.

(local
 (defthm fn-hp-nth-append-w
   (implies (natp k)
            (equal (nth k (append a b)) (if (< k (len a)) (nth k a) (nth (- k (len a)) b))))
   :hints (("Goal" :in-theory (enable nth) :induct (nth k a)))))

(local
 (defthm fn-hp-nth-take-w
   (implies (and (natp k) (natp j) (< k j))
            (equal (nth k (take j x)) (nth k x)))
   :hints (("Goal" :in-theory (enable nth take)))))

(local
 (defthm fn-hp-nth-nthcdr-w
   (implies (and (natp k) (natp m))
            (equal (nth k (nthcdr m x)) (nth (+ k m) x)))
   :hints (("Goal" :in-theory (enable nth nthcdr)))))

(defthm fn-hp-nth-rep
  (implies (and (natp j) (natp k))
           (equal (nth k (fn-hp-rep x j b))
                  (if (and (<= j k) (< k (+ j (len b)))) (nth (- k j) b) (nth k x))))
  :hints (("Goal" :in-theory (e/d (fn-hp-rep) (nth take nthcdr)))))
(defun fn-hp-agree (a n x y)
  ; X and Y agree on words A .. A+N-1
  (declare (xargs :guard (and (natp a) (natp n) (true-listp x) (true-listp y)) :measure (nfix n)))
  (if (zp n) t (and (equal (nth a x) (nth a y)) (fn-hp-agree (+ 1 (nfix a)) (1- n) x y))))

(local
 (defthm fn-hp-take-nthcdr-open
   (implies (and (natp a) (posp n))
            (equal (take n (nthcdr a x)) (cons (nth a x) (take (1- n) (nthcdr (+ 1 a) x)))))
   :hints (("Goal" :in-theory (enable take nthcdr nth)))))

(defthm fn-hp-agree-is-take
  (implies (natp a)
           (equal (fn-hp-agree a n x y)
                  (equal (take n (nthcdr a x)) (take n (nthcdr a y)))))
  :hints (("Goal" :induct (fn-hp-agree a n x y) :in-theory (disable nth nthcdr take))
          ("Subgoal *1/1" :in-theory (enable take))))

(in-theory (disable fn-hp-agree-is-take))
(local (in-theory (disable fn-hp-take-nthcdr-open)))

(defthm fn-hp-agree-of-rep
  (implies (and (fn-hp-agree a n x y) (natp a) (natp j))
           (fn-hp-agree a n (fn-hp-rep x j b) (fn-hp-rep y j b)))
  :hints (("Goal" :induct (fn-hp-agree a n x y))))

(local
 (defun fn-hp-wreps2-ind (x y bs)
   (if (atom bs) (list x y)
     (fn-hp-wreps2-ind (fn-hp-rep x (nfix (car (car bs))) (true-list-fix (cdr (car bs))))
                       (fn-hp-rep y (nfix (car (car bs))) (true-list-fix (cdr (car bs)))) (cdr bs)))))

(defthm fn-hp-agree-of-wreps
  (implies (and (fn-hp-agree a n x y) (natp a))
           (fn-hp-agree a n (fn-hp-wreps x bs) (fn-hp-wreps y bs)))
  :hints (("Goal" :induct (fn-hp-wreps2-ind x y bs) :in-theory (disable fn-hp-agree fn-hp-rep))))
