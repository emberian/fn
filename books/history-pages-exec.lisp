; fn: the history's FNADTSN2 image read through the page store's words
; (lane arena-store-2, 2026-09-28).  Prefix fn-hp-.
(in-package "ACL2")
(include-book "history-pages")
(include-book "history-pages-words")
(include-book "pagestore-exec")
(local (include-book "arithmetic/top" :dir :system))

;; The tau system is off in this book (lane tau-pass, tools/tau_cost.py).
;; Its work is proof time no prover step counts (docs/proof-style.md
;; 9.1); planning/evidence/tau-cost-*.json has this book's figures.
(local (in-theory (disable (tau-system))))

; -----------------------------------------------------------------------------
; A. What the image holds at a row: its cells and its pool entry.

(local
 (defun fn-hp-tr-ind (r m rows)
   (if (or (zp r) (zp m)) (list r m rows) (fn-hp-tr-ind (1- r) (1- m) (adt-cdrs rows)))))

(local
 (defthm fn-hp-nth-cars
   (equal (nth i (adt-cars rows)) (if (< (nfix i) (len rows)) (car (nth i rows)) nil))
   :hints (("Goal" :in-theory (enable nth)))))

(local
 (defthm fn-hp-nth-cdrs
   (equal (nth i (adt-cdrs rows)) (if (< (nfix i) (len rows)) (cdr (nth i rows)) nil))
   :hints (("Goal" :in-theory (enable nth)))))

(defthm fn-hp-nth-nth-transpose
  (implies (and (natp r) (< r (nfix m)) (natp i) (< i (len rows)))
           (equal (nth i (nth r (adt-transpose m rows))) (nth r (nth i rows))))
  :hints (("Goal" :induct (fn-hp-tr-ind r m rows) :in-theory (enable nth)
           :expand ((adt-transpose m rows)))))

(defun fn-hp-cells-of (ev salt pos)
  ; the cells of EV's row when its pool entry starts at POS
  (declare (xargs :verify-guards nil))
  (list (fn-hp-mkey ev salt) (len (fn-scc-encode ev)) (nfix pos)
        (len (fn-hp-pad8 (fn-scc-encode ev)))))

(local
 (defthm fn-hp-row-cells-of-row
   (equal (adt-row-cells *fn-hp-schema* (fn-hp-row ev salt) pos)
          (cons (fn-hp-cells-of ev salt pos) (+ (nfix pos) (len (fn-hp-pad8 (fn-scc-encode ev))))))
   :hints (("Goal" :in-theory (e/d (adt-enc) (fn-scc-encode fn-scc-program fn-hp-mkey fn-hp-pad8))))))

(local
 (defun fn-hp-ci-ind (i h pos salt)
   (if (or (zp i) (atom h)) (list i h pos salt)
     (fn-hp-ci-ind (1- i) (cdr h) (+ pos (len (fn-hp-pad8 (fn-scc-encode (car h))))) salt))))

(defthm fn-hp-nth-rows-cells
  (implies (and (natp i) (< i (len h)) (natp pos))
           (equal (nth i (adt-rows-cells *fn-hp-schema* (fn-hp-rows h salt) pos))
                  (fn-hp-cells-of (nth i h) salt (+ pos (fn-hp-enc-len (take i h))))))
  :hints (("Goal" :induct (fn-hp-ci-ind i h pos salt)
           :in-theory (e/d (nth take) (fn-hp-cells-of fn-hp-row adt-row-cells fn-scc-encode fn-scc-program
                                       fn-hp-pad8 fn-hp-mkey)))))

; Pool entries, abstracted: EV's entry is its padded tree.
(defun fn-hp-pe (ev)
  (declare (xargs :verify-guards nil))
  (fn-hp-pad8 (fn-scc-encode ev)))

(defun fn-hp-pes (h)
  (declare (xargs :verify-guards nil))
  (if (atom h) nil (append (fn-hp-pe (car h)) (fn-hp-pes (cdr h)))))

(defun fn-hp-pes-len (h)
  (declare (xargs :verify-guards nil))
  (if (atom h) 0 (+ (len (fn-hp-pe (car h))) (fn-hp-pes-len (cdr h)))))

(local
 (defthm fn-hp-row-pool-of-row-x
   (equal (adt-row-pool *fn-hp-schema* (fn-hp-row ev salt)) (fn-hp-pad8 (fn-scc-encode ev)))
   :hints (("Goal" :in-theory (disable fn-scc-encode fn-hp-mkey)))))

(defthm fn-hp-rows-pool-is-pes
  (equal (adt-rows-pool *fn-hp-schema* (fn-hp-rows h salt)) (fn-hp-pes h))
  :hints (("Goal" :in-theory (disable fn-hp-row fn-scc-encode fn-hp-pad8 adt-row-pool))))

(defthm fn-hp-enc-len-is-pes-len
  (equal (fn-hp-enc-len h) (fn-hp-pes-len h)))

(in-theory (disable fn-hp-pe))

(local
 (defthm fn-hp-true-listp-pe (true-listp (fn-hp-pe ev))
   :hints (("Goal" :in-theory (enable fn-hp-pe fn-hp-pad8)))))

(local
 (defun fn-hp-pi-ind (i h)
   (if (or (zp i) (atom h)) (list i h) (fn-hp-pi-ind (1- i) (cdr h)))))

(defthm fn-hp-pes-entry
  (implies (and (natp i) (< i (len h)))
           (equal (take (len (fn-hp-pe (nth i h))) (nthcdr (fn-hp-pes-len (take i h)) (fn-hp-pes h)))
                  (fn-hp-pe (nth i h))))
  :hints (("Goal" :induct (fn-hp-pi-ind i h) :in-theory (enable nth take))))

(defthm fn-hp-len-pes (equal (len (fn-hp-pes h)) (fn-hp-pes-len h)))

(defthm fn-hp-pes-len-take-bound
  (implies (and (natp i) (< i (len h)))
           (<= (+ (fn-hp-pes-len (take i h)) (len (fn-hp-pe (nth i h)))) (fn-hp-pes-len h)))
  :hints (("Goal" :induct (fn-hp-pi-ind i h) :in-theory (enable nth take)))
  :rule-classes :linear)

; Reading a column cell and a pool entry out of the octets.
(local
 (defun fn-hp-r-ind (r ws starts useds)
   (if (zp r) (list r ws starts useds) (fn-hp-r-ind (1- r) (cdr ws) (cdr starts) (cdr useds)))))

(defthm fn-hp-nth-dec-cols
  (implies (and (natp r) (< r (len ws)))
           (equal (nth r (adt-dec-cols ws n starts useds b))
                  (adt-unle-list (nfix (nth r ws)) n
                                 (take (nfix (nth r useds)) (nthcdr (* *adt-page* (nfix (nth r starts))) b)))))
  :hints (("Goal" :induct (fn-hp-r-ind r ws starts useds) :expand ((adt-dec-cols ws n starts useds b))
           :in-theory (e/d (nth) (adt-dec-cols adt-unle-list take nthcdr)))))

(local
 (defun fn-hp-ul-ind (i n x)
   (if (or (zp i) (zp n)) (list i n x) (fn-hp-ul-ind (1- i) (1- n) (nthcdr 8 x)))))

(defthm fn-hp-nth-unle-list-8
  (implies (and (natp i) (< i (nfix n)))
           (equal (nth i (adt-unle-list 8 n x)) (adt-unle 8 (nthcdr (* 8 i) x))))
  :hints (("Goal" :induct (fn-hp-ul-ind i n x) :in-theory (e/d (nth) (adt-unle))
           :expand ((adt-unle-list 8 n x)))))

(local
 (defun fn-hp-u-ind (w u y)
   (if (zp w) (list w u y) (fn-hp-u-ind (1- w) (1- u) (cdr y)))))

(defthm fn-hp-unle-take
  (implies (and (natp w) (<= w (nfix u)))
           (equal (adt-unle w (take u y)) (adt-unle w y)))
  :hints (("Goal" :induct (fn-hp-u-ind w u y) :in-theory (enable take))))

(defthm fn-hp-nth-col-sizes
  (implies (and (adt-col-sizes-ok ws n useds) (natp r) (< r (len ws)))
           (equal (nth r useds) (* (nfix (nth r ws)) (nfix n))))
  :hints (("Goal" :induct (fn-hp-r-ind r ws starts useds) :in-theory (enable nth))))

(local
 (defthm fn-hp-nthcdr-take-x
   (implies (and (natp m) (natp l) (<= m l))
            (equal (nthcdr m (take l y)) (take (- l m) (nthcdr m y))))
   :hints (("Goal" :in-theory (enable take nthcdr)))))

(defun fn-hp-okp (h salt)
  ; the history's image exists and is addressable
  (declare (xargs :verify-guards nil))
  (and (fn-hp-events-okp h) (< (len h) *adt-u64-limit*)
       (< (len (fn-hp-image h salt)) *adt-u64-limit*)))

(defun fn-hp-lens (h salt) (declare (xargs :verify-guards nil)) (adt-lens (fn-hp-regs h salt)))
(defun fn-hp-starts (h salt) (declare (xargs :verify-guards nil)) (adt-starts-l (fn-hp-lens h salt) 1))

(defthm fn-hp-ser-okp
  (implies (fn-hp-okp h salt) (adt-ser-okp *fn-hp-schema* (fn-hp-rows h salt)))
  :hints (("Goal" :in-theory (enable adt-ser-okp))))

(defthm fn-hp-dec-cols-cell
  (implies (and (natp r) (< r (len ws)) (equal (nth r ws) 8) (natp n) (natp i) (< i n)
                (equal (nth r useds) (* 8 n)) (natp (nth r starts)))
           (equal (nth i (nth r (adt-dec-cols ws n starts useds b)))
                  (adt-unle 8 (nthcdr (+ (* *adt-page* (nth r starts)) (* 8 i)) b))))
  :hints (("Goal" :do-not-induct t :in-theory (disable adt-unle adt-unle-list adt-dec-cols))))

(local
 (defthm fn-hp-natp-nth-starts-l
   (implies (and (nat-listp lens) (natp s) (natp r) (< r (len lens)))
            (natp (nth r (adt-starts-l lens s))))
   :hints (("Goal" :in-theory (enable nth)))))

(local (defthm fn-hp-nth-8888 (implies (and (natp r) (< r 4)) (equal (nth r '(8 8 8 8)) 8))
  :hints (("Goal" :cases ((equal r 0) (equal r 1) (equal r 2))))))

; Cell I of column R (the MKEY, tree-length, offset and length columns).
(defthm fn-hp-col-octets
  (implies (and (fn-hp-okp h salt) (natp r) (< r 4) (natp i) (< i (len h)))
           (equal (adt-unle 8 (nthcdr (+ (* 16384 (nth r (fn-hp-starts h salt))) (* 8 i))
                                      (fn-hp-image h salt)))
                  (nth r (fn-hp-cells-of (nth i h) salt (fn-hp-pes-len (take i h))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance adt-ser-columns (s *fn-hp-schema*) (a (fn-hp-rows h salt)))
                 (:instance fn-hp-ser-okp)
                 (:instance fn-hp-nth-col-sizes (ws '(8 8 8 8)) (n (len h))
                            (useds (adt-lens (adt-regs *fn-hp-schema* (fn-hp-rows h salt)))))
                 (:instance fn-hp-dec-cols-cell (ws '(8 8 8 8)) (n (len h))
                            (starts (adt-starts-l (adt-lens (adt-regs *fn-hp-schema* (fn-hp-rows h salt))) 1))
                            (useds (adt-lens (adt-regs *fn-hp-schema* (fn-hp-rows h salt))))
                            (b (adt-ser *fn-hp-schema* (fn-hp-rows h salt))))
                 (:instance fn-hp-nth-nth-transpose (m 4) (rows (adt-rows-cells *fn-hp-schema* (fn-hp-rows h salt) 0)))
                 (:instance fn-hp-nth-rows-cells (pos 0))
                 (:instance fn-hp-natp-nth-starts-l (lens (adt-lens (adt-regs *fn-hp-schema* (fn-hp-rows h salt)))) (s 1)))
           :in-theory (e/d (fn-hp-enc-len-is-pes-len)
                           (adt-ser-columns fn-hp-ser-okp adt-ser adt-regs adt-starts-l adt-lens fn-hp-nth-col-sizes
                            fn-hp-dec-cols-cell fn-hp-nth-nth-transpose fn-hp-nth-rows-cells fn-hp-natp-nth-starts-l
                            adt-dec-cols adt-transpose adt-rows-cells fn-hp-cells-of adt-nth-lens
                            fn-hp-okp fn-hp-rows adt-ser-okp adt-col-sizes-ok adt-unle adt-unle-list)))))

(local
 (defun fn-hp-tt-ind (n l y)
   (if (or (zp n) (zp l)) (list n l y) (fn-hp-tt-ind (1- n) (1- l) (cdr y)))))

(local
 (defthm fn-hp-take-take-below
   (implies (and (natp n) (natp l) (<= n l))
            (equal (take n (take l y)) (take n y)))
   :hints (("Goal" :in-theory (enable take) :induct (fn-hp-tt-ind n l y)))))

(local
 (defthm fn-hp-take-nthcdr-of-take
   (implies (and (natp off) (natp n) (natp l) (<= (+ off n) l))
            (equal (take n (nthcdr off (take l y))) (take n (nthcdr off y))))
   :hints (("Goal" :in-theory (disable fn-hp-nthcdr-take-x) :use ((:instance fn-hp-nthcdr-take-x (m off)))))))

(defthm fn-hp-natp-start-4
  (implies (fn-hp-okp h salt) (natp (nth 4 (fn-hp-starts h salt))))
  :hints (("Goal" :use ((:instance fn-hp-natp-nth-starts-l (r 4) (s 1) (lens (fn-hp-lens h salt))))
           :in-theory (disable fn-hp-natp-nth-starts-l adt-starts-l adt-regs fn-hp-rows)))
  :rule-classes :type-prescription)

; Event I's pool entry.
(defthm fn-hp-pool-octets
  (implies (and (fn-hp-okp h salt) (natp i) (< i (len h)))
           (equal (take (len (fn-hp-pe (nth i h)))
                        (nthcdr (+ (* 16384 (nth 4 (fn-hp-starts h salt))) (fn-hp-pes-len (take i h)))
                                (fn-hp-image h salt)))
                  (fn-hp-pe (nth i h))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance adt-ser-pool (s *fn-hp-schema*) (a (fn-hp-rows h salt)))
                 (:instance fn-hp-ser-okp)
                 (:instance fn-hp-pes-entry)
                 (:instance fn-hp-natp-start-4)
                 (:instance fn-hp-nthcdr-nthcdr (m (fn-hp-pes-len (take i h)))
                            (n (* 16384 (nth 4 (fn-hp-starts h salt)))) (b (fn-hp-image h salt)))
                 (:instance fn-hp-take-nthcdr-of-take (off (fn-hp-pes-len (take i h))) (n (len (fn-hp-pe (nth i h))))
                            (l (fn-hp-pes-len h))
                            (y (nthcdr (* 16384 (nth 4 (fn-hp-starts h salt))) (fn-hp-image h salt)))))
           :in-theory (e/d () (adt-ser-pool fn-hp-ser-okp fn-hp-pes-entry fn-hp-take-nthcdr-of-take adt-ser adt-regs
                                           fn-hp-nthcdr-nthcdr fn-hp-natp-start-4
                                           adt-starts-l adt-lens fn-hp-okp fn-hp-rows adt-ser-okp fn-hp-pes fn-hp-pes-len)))))

(local
 (defun fn-hp-rl-ind (r lens start)
   (if (or (zp r) (atom lens)) (list r lens start)
     (fn-hp-rl-ind (1- r) (cdr lens) (+ (nfix start) (adt-cap (nfix (car lens))))))))

(defthm fn-hp-region-within-end
  (implies (and (nat-listp lens) (natp start) (natp r) (< r (len lens)))
           (<= (+ (* *adt-page* (nth r (adt-starts-l lens start))) (nth r lens))
               (* *adt-page* (adt-end-l lens start))))
  :hints (("Goal" :induct (fn-hp-rl-ind r lens start) :in-theory (e/d (nth) (adt-cap)))
          ("Subgoal *1/2" :use ((:instance adt-cap-covers (u (car lens)))
                                (:instance adt-end-l-lower (lens (cdr lens)) (start (+ start (adt-cap (car lens)))))))
          ("Subgoal *1/1" :use ((:instance adt-cap-covers (u (car lens)))
                                (:instance adt-end-l-lower (lens (cdr lens)) (start (+ start (adt-cap (car lens))))))))
  :rule-classes :linear)

; The header: its region table.
(local
 (defun fn-hp-rm-ind (r k b)
   (if (or (zp r) (zp k)) (list r k b) (fn-hp-rm-ind (1- r) (1- k) (nthcdr 16 b)))))

(defthm fn-hp-nth-read-meta
  (implies (and (natp r) (< r (nfix k)))
           (and (equal (nth r (car (adt-read-meta k b))) (adt-unle 8 (nthcdr (* 16 r) b)))
                (equal (nth r (cdr (adt-read-meta k b))) (adt-unle 8 (nthcdr (+ 8 (* 16 r)) b)))))
  :hints (("Goal" :induct (fn-hp-rm-ind r k b) :in-theory (e/d (nth) (adt-unle))
           :expand ((adt-read-meta k b)))))

(defthm fn-hp-unle-via-take
  (implies (and (natp k) (natp m) (<= (+ k 8) m))
           (equal (adt-unle 8 (nthcdr k (take m x))) (adt-unle 8 (nthcdr k x))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-nthcdr-take-x (m k) (l m) (y x))
                 (:instance fn-hp-unle-take (w 8) (u (- m k)) (y (nthcdr k x))))
           :in-theory (disable adt-unle fn-hp-nthcdr-take-x fn-hp-unle-take))))

(defthm fn-hp-header-meta-octets
  (implies (and (fn-hp-okp h salt) (natp r) (< r 5))
           (and (equal (adt-unle 8 (nthcdr (+ 64 (* 16 r)) (fn-hp-image h salt))) (nth r (fn-hp-starts h salt)))
                (equal (adt-unle 8 (nthcdr (+ 72 (* 16 r)) (fn-hp-image h salt))) (nth r (fn-hp-lens h salt)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance adt-ser-header-reads (s *fn-hp-schema*) (a (fn-hp-rows h salt)))
                 (:instance fn-hp-ser-okp)
                 (:instance fn-hp-nth-read-meta (k 5) (b (nthcdr 64 (adt-ser *fn-hp-schema* (fn-hp-rows h salt))))))
           :in-theory (disable adt-ser-header-reads fn-hp-ser-okp fn-hp-nth-read-meta adt-ser adt-regs adt-starts-l adt-lens
                               adt-read-meta adt-unle fn-hp-okp fn-hp-rows adt-ser-okp))))

(defconst *fn-hp-magic-word* (adt-unle 8 *adt-magic*))

(defconst *fn-hp-schema-words* (fn-hp-pack8 4 (adt-schema-digest *fn-hp-schema*)))

(defthm fn-hp-header-fixed-octets
  (implies (fn-hp-okp h salt)
           (let ((b (fn-hp-image h salt)))
             (and (equal (adt-unle 8 b) *fn-hp-magic-word*)
                  (equal (adt-unle 8 (nthcdr 8 b)) *adt-version*)
                  (equal (adt-unle 8 (nthcdr 144 b)) (fn-hp-npages h salt))
                  (equal (list (adt-unle 8 (nthcdr 16 b)) (adt-unle 8 (nthcdr 24 b))
                               (adt-unle 8 (nthcdr 32 b)) (adt-unle 8 (nthcdr 40 b)))
                         *fn-hp-schema-words*)
                  (equal (adt-unle 8 (nthcdr 48 b)) (len h))
                  (equal (adt-unle 8 (nthcdr 56 b)) 5))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance adt-ser-header-reads (s *fn-hp-schema*) (a (fn-hp-rows h salt)))
                 (:instance fn-hp-ser-okp)
                 (:instance fn-hp-unle-take (w 8) (u 8) (y (adt-ser *fn-hp-schema* (fn-hp-rows h salt))))
                 (:instance fn-hp-unle-via-take (k 0) (m 32) (x (nthcdr 16 (adt-ser *fn-hp-schema* (fn-hp-rows h salt)))))
                 (:instance fn-hp-unle-via-take (k 8) (m 32) (x (nthcdr 16 (adt-ser *fn-hp-schema* (fn-hp-rows h salt)))))
                 (:instance fn-hp-unle-via-take (k 16) (m 32) (x (nthcdr 16 (adt-ser *fn-hp-schema* (fn-hp-rows h salt)))))
                 (:instance fn-hp-unle-via-take (k 24) (m 32) (x (nthcdr 16 (adt-ser *fn-hp-schema* (fn-hp-rows h salt))))))
           :in-theory (e/d (fn-hp-npages fn-hp-regs)
                           (adt-ser-header-reads fn-hp-ser-okp fn-hp-unle-take fn-hp-unle-via-take adt-ser adt-regs
                            adt-starts-l adt-lens adt-read-meta adt-unle fn-hp-okp fn-hp-rows adt-ser-okp
                            adt-schema-digest)))))

; -----------------------------------------------------------------------------
; B. The image as words, and the open's header check over them.

(defun fn-hp-iw (h salt)
  ; the image as the page store's words
  (declare (xargs :verify-guards nil))
  (fn-hp-pack8 (* 2048 (fn-hp-npages h salt)) (fn-hp-image h salt)))

(defthm fn-hp-npages-posp
  (posp (fn-hp-npages h salt))
  :hints (("Goal" :in-theory (disable adt-regs adt-cap)))
  :rule-classes :type-prescription)

(defthm fn-hp-iw-word
  (implies (and (natp j) (< j (* 2048 (fn-hp-npages h salt))))
           (equal (nth j (fn-hp-iw h salt)) (adt-unle 8 (nthcdr (* 8 j) (fn-hp-image h salt)))))
  :hints (("Goal" :in-theory (disable fn-hp-npages fn-hp-image))))

(defun fn-hp-w-header (w npages)
  ; the open's header check over the image's words W, the page store
  ; holding NPAGES logical pages: (:ok N LENS STARTS) or (:refused REASON).
  ; FNADTSN2: the regions may lie anywhere the header says
  ; (`adt-placement-ok' against word 18, the image's page count).
  (declare (xargs :guard (true-listp w) :verify-guards nil))
  (let ((n (nth 6 w))
        (lens (list (nth 9 w) (nth 11 w) (nth 13 w) (nth 15 w) (nth 17 w)))
        (starts (list (nth 8 w) (nth 10 w) (nth 12 w) (nth 14 w) (nth 16 w)))
        (np (nth 18 w)))
    (cond ((not (equal (nth 0 w) *fn-hp-magic-word*)) (list :refused :magic))
          ((not (equal (nth 1 w) *adt-version*)) (list :refused :version))
          ((not (equal (list (nth 2 w) (nth 3 w) (nth 4 w) (nth 5 w)) *fn-hp-schema-words*))
           (list :refused :schema))
          ((not (equal (nth 7 w) 5)) (list :refused :regions))
          ((not (and (natp n) (nat-listp lens) (natp np))) (list :refused :fields))
          ((not (adt-placement-ok starts lens np)) (list :refused :placement))
          ((not (and (equal (nth 0 lens) (* 8 n)) (equal (nth 1 lens) (* 8 n))
                     (equal (nth 2 lens) (* 8 n)) (equal (nth 3 lens) (* 8 n))))
           (list :refused :column-size))
          ((not (equal np npages)) (list :refused :length))
          (t (list :ok n lens starts)))))

(defthm fn-hp-len-lens
  (equal (len (fn-hp-lens h salt)) 5)
  :hints (("Goal" :in-theory (disable adt-regs fn-hp-rows))))

(local
 (defthm fn-hp-list5
   (implies (and (true-listp x) (equal (len x) 5))
            (equal (list (nth 0 x) (nth 1 x) (nth 2 x) (nth 3 x) (nth 4 x)) x))
   :hints (("Goal" :in-theory (e/d (nth) (len true-listp))
            :expand ((len x) (len (cdr x)) (len (cddr x)) (len (cdddr x)) (len (cddddr x)) (len (cdr (cddddr x)))
                     (true-listp x) (true-listp (cdr x)) (true-listp (cddr x)) (true-listp (cdddr x))
                     (true-listp (cddddr x)) (true-listp (cdr (cddddr x))))))))

(defthm fn-hp-lens-col-sizes
  (implies (and (fn-hp-okp h salt) (natp r) (< r 4))
           (equal (nth r (fn-hp-lens h salt)) (* 8 (len h))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance adt-ser-columns (s *fn-hp-schema*) (a (fn-hp-rows h salt)))
                 (:instance fn-hp-ser-okp)
                 (:instance fn-hp-nth-col-sizes (ws '(8 8 8 8)) (n (len h))
                            (useds (adt-lens (adt-regs *fn-hp-schema* (fn-hp-rows h salt))))))
           :in-theory (disable adt-ser-columns fn-hp-ser-okp fn-hp-nth-col-sizes adt-ser adt-regs adt-lens
                               adt-dec-cols adt-transpose adt-rows-cells fn-hp-okp fn-hp-rows adt-ser-okp
                               adt-col-sizes-ok adt-nth-lens))))

(defthm fn-hp-len-starts-l
  (equal (len (adt-starts-l lens s)) (len lens)))

(defthm fn-hp-true-listp-starts-l
  (true-listp (adt-starts-l lens s)))

(defthm fn-hp-len-starts
  (equal (len (fn-hp-starts h salt)) 5)
  :hints (("Goal" :in-theory (disable fn-hp-lens))))

(defthm fn-hp-true-listp-lens
  (true-listp (fn-hp-lens h salt)))

(defthmd fn-hp-starts-is
  (equal (fn-hp-starts h salt) (adt-starts-l (fn-hp-lens h salt) 1)))

(defthmd fn-hp-lens-is
  (equal (fn-hp-lens h salt) (adt-lens (adt-regs *fn-hp-schema* (fn-hp-rows h salt)))))


(defthm fn-hp-placement-ok-of-image
  (adt-placement-ok (fn-hp-starts h salt) (fn-hp-lens h salt) (fn-hp-npages h salt))
  :hints (("Goal" :use ((:instance adt-placement-ok-of-starts-l (lens (fn-hp-lens h salt)) (s 1)))
           :in-theory (e/d (fn-hp-starts fn-hp-npages fn-hp-lens fn-hp-regs)
                           (adt-placement-ok-of-starts-l adt-placement-ok adt-regs fn-hp-rows adt-starts-l adt-end-l
                            adt-lens)))))

; The open's header check accepts the image and answers its N and regions.
(defthm fn-hp-w-header-of-image
  (implies (fn-hp-okp h salt)
           (equal (fn-hp-w-header (fn-hp-iw h salt) (fn-hp-npages h salt))
                  (list :ok (len h) (fn-hp-lens h salt) (fn-hp-starts h salt))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-header-fixed-octets)
                 (:instance fn-hp-placement-ok-of-image)
                 (:instance fn-hp-header-meta-octets (r 0)) (:instance fn-hp-header-meta-octets (r 1))
                 (:instance fn-hp-header-meta-octets (r 2)) (:instance fn-hp-header-meta-octets (r 3))
                 (:instance fn-hp-header-meta-octets (r 4))
                 (:instance fn-hp-lens-col-sizes (r 0)) (:instance fn-hp-lens-col-sizes (r 1))
                 (:instance fn-hp-lens-col-sizes (r 2)) (:instance fn-hp-lens-col-sizes (r 3))
                 (:instance fn-hp-list5 (x (fn-hp-lens h salt)))
                 (:instance fn-hp-list5 (x (fn-hp-starts h salt))) (:instance fn-hp-len-starts) (:instance fn-hp-len-lens) (:instance fn-hp-starts-is) (:instance fn-hp-lens-is))
           :in-theory (e/d (fn-hp-npages fn-hp-regs)
                           (fn-hp-header-fixed-octets fn-hp-header-meta-octets fn-hp-lens-col-sizes fn-hp-list5
                            fn-hp-iw fn-hp-image fn-hp-okp adt-unle adt-regs fn-hp-rows adt-starts-l adt-end-l
                            adt-lens fn-hp-lens fn-hp-starts adt-placement-ok fn-hp-placement-ok-of-image)))))

