; fn: the history's FNADTSN1 image read through the page store's words
; (lane arena-store-2, 2026-09-28).  Prefix fn-hp-.
(in-package "ACL2")
(include-book "history-pages")
(include-book "history-pages-words")
(include-book "pagestore-exec")
(local (include-book "arithmetic/top" :dir :system))

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
                  (equal (adt-unle 8 (nthcdr 8 b)) 1)
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
           :in-theory (disable adt-ser-header-reads fn-hp-ser-okp fn-hp-unle-take fn-hp-unle-via-take adt-ser adt-regs
                               adt-starts-l adt-lens adt-read-meta adt-unle fn-hp-okp fn-hp-rows adt-ser-okp
                               adt-schema-digest))))

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
  ; holding NPAGES logical pages: (:ok N LENS STARTS) or (:refused REASON)
  (declare (xargs :guard (true-listp w) :verify-guards nil))
  (let ((n (nth 6 w))
        (lens (list (nth 9 w) (nth 11 w) (nth 13 w) (nth 15 w) (nth 17 w)))
        (starts (list (nth 8 w) (nth 10 w) (nth 12 w) (nth 14 w) (nth 16 w))))
    (cond ((not (equal (nth 0 w) *fn-hp-magic-word*)) (list :refused :magic))
          ((not (equal (nth 1 w) 1)) (list :refused :version))
          ((not (equal (list (nth 2 w) (nth 3 w) (nth 4 w) (nth 5 w)) *fn-hp-schema-words*))
           (list :refused :schema))
          ((not (equal (nth 7 w) 5)) (list :refused :regions))
          ((not (and (natp n) (nat-listp lens))) (list :refused :fields))
          ((not (equal starts (adt-starts-l lens 1))) (list :refused :placement))
          ((not (and (equal (nth 0 lens) (* 8 n)) (equal (nth 1 lens) (* 8 n))
                     (equal (nth 2 lens) (* 8 n)) (equal (nth 3 lens) (* 8 n))))
           (list :refused :column-size))
          ((not (equal (adt-end-l lens 1) npages)) (list :refused :length))
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


; The open's header check accepts the image and answers its N and regions.
(defthm fn-hp-w-header-of-image
  (implies (fn-hp-okp h salt)
           (equal (fn-hp-w-header (fn-hp-iw h salt) (fn-hp-npages h salt))
                  (list :ok (len h) (fn-hp-lens h salt) (fn-hp-starts h salt))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-header-fixed-octets)
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
                            adt-lens fn-hp-lens fn-hp-starts)))))

; -----------------------------------------------------------------------------
; C. The row reader over the words: the event at SEQ.

(defthm fn-hp-evp-nth
  (implies (and (fn-hp-events-okp h) (natp i) (< i (len h)))
           (fn-hp-evp (nth i h)))
  :hints (("Goal" :in-theory (e/d (nth) (fn-hp-evp)))))

(defthm fn-hp-len-pad8
  (equal (len (fn-hp-pad8 x)) (+ (len x) (fn-hp-pad8-count (len x))))
  :hints (("Goal" :in-theory (enable fn-hp-pad8))))

(defthm fn-hp-pe-mod-8
  (equal (mod (len (fn-hp-pe ev)) 8) 0)
  :hints (("Goal" :in-theory (e/d (fn-hp-pe) (mod))
           :use ((:instance fn-hp-pad-to-8 (n (len (fn-scc-encode ev))))))))

(defthm fn-hp-pes-len-mod-8
  (equal (mod (fn-hp-pes-len h) 8) 0)
  :hints (("Goal" :in-theory (disable fn-hp-pe-mod-8 mod) :induct (fn-hp-pes-len h))
          ("Subgoal *1/2" :use ((:instance fn-hp-pe-mod-8 (ev (car h)))
                                (:instance fn-hp-mod-8-sum (x (len (fn-hp-pe (car h)))) (y (fn-hp-pes-len (cdr h))))))))

(defthm fn-hp-lens-4
  (equal (nth 4 (fn-hp-lens h salt)) (fn-hp-pes-len h))
  :hints (("Goal" :in-theory (e/d (adt-regs) (fn-hp-rows)))))

(defthm fn-hp-take-of-pe
  (implies (fn-hp-evp ev)
           (equal (take (len (fn-scc-encode ev)) (fn-hp-pe ev)) (fn-scc-encode ev)))
  :hints (("Goal" :in-theory (e/d (fn-hp-pe fn-hp-pad8) (fn-scc-encode)))))

(defthm fn-hp-len-enc-le-pe
  (<= (len (fn-scc-encode ev)) (len (fn-hp-pe ev)))
  :hints (("Goal" :in-theory (e/d (fn-hp-pe fn-hp-pad8) (fn-scc-encode))))
  :rule-classes :linear)

(defthm fn-hp-pe-is-pad8
  (equal (fn-hp-pad8 (fn-scc-encode ev)) (fn-hp-pe ev))
  :hints (("Goal" :in-theory (enable fn-hp-pe))))

(defthm fn-hp-decode-enc
  (implies (fn-hp-evp ev)
           (equal (fn-scc-decode-tree (fn-scc-encode ev)) (list :ok ev)))
  :hints (("Goal" :use ((:instance fn-scc-decode-tree-of-encode (x ev)))
           :in-theory (disable fn-scc-decode-tree-of-encode fn-scc-decode-tree fn-scc-encode))))

(defun fn-hp-w-at (seq w salt n lens starts)
  ; the event at SEQ read from the image's words W, given the header's N,
  ; LENS and STARTS: (:ok EV) or (:refused REASON)
  (declare (xargs :verify-guards nil))
  (let* ((mkey (nth (+ (* 2048 (nth 0 starts)) seq) w))
         (tl (nth (+ (* 2048 (nth 1 starts)) seq) w))
         (off (nth (+ (* 2048 (nth 2 starts)) seq) w))
         (plen (nth (+ (* 2048 (nth 3 starts)) seq) w)))
    (cond ((not (and (natp seq) (< seq (nfix n)))) (list :refused :seq))
          ((not (and (natp off) (natp plen) (natp tl) (equal (mod off 8) 0) (equal (mod plen 8) 0)
                     (<= tl plen) (<= (+ off plen) (nfix (nth 4 lens)))))
           (list :refused :cells))
          (t (let ((bytes (pgs-words-le-octets
                           (take (floor plen 8) (nthcdr (+ (* 2048 (nth 4 starts)) (floor off 8)) w)))))
               (if (not (equal bytes (fn-hp-pad8 (take tl bytes))))
                   (list :refused :padding)
                 (let ((d (fn-scc-decode-tree (take tl bytes))))
                   (cond ((not (eq (car d) :ok)) (list :refused :tree))
                         ((not (equal mkey (fn-hp-mkey (cadr d) salt))) (list :refused :mkey))
                         (t d)))))))))

(local
 (defthm fn-hp-octetsp-meta
   (adt-octetsp (adt-meta starts lens))
   :hints (("Goal" :in-theory (enable adt-meta)))))

(defthm fn-hp-octetsp-header
  (adt-octetsp (adt-header *fn-hp-schema* n regs))
  :hints (("Goal" :in-theory (e/d (adt-header adt-header-content adt-hdr-const (:executable-counterpart adt-hdr-const))
                                  (adt-zeros adt-le)))))

(local
 (defthm fn-hp-octetsp-col-regs
   (adt-all-octetsp (adt-col-regs ws cols))
   :hints (("Goal" :in-theory (enable adt-all-octetsp)))))

(local
 (defthm fn-hp-all-octetsp-append
   (implies (and (adt-all-octetsp x) (adt-all-octetsp y)) (adt-all-octetsp (append x y)))
   :hints (("Goal" :in-theory (enable adt-all-octetsp)))))


(local
 (defthm fn-hp-octetsp-of-scc-octets-x
   (implies (fn-scc-octet-listp x) (adt-octetsp x))))

(defthm fn-hp-octetsp-pe
  (implies (fn-hp-evp ev) (adt-octetsp (fn-hp-pe ev)))
  :hints (("Goal" :in-theory (e/d (fn-hp-pe) (fn-scc-program)))))

(defthm fn-hp-octetsp-pes
  (implies (fn-hp-events-okp h) (adt-octetsp (fn-hp-pes h)))
  :hints (("Goal" :in-theory (disable fn-hp-evp))))

(defthm fn-hp-octetsp-image
  (implies (fn-hp-events-okp h) (adt-octetsp (fn-hp-image h salt)))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (adt-ser adt-regs adt-all-octetsp) (adt-ser-is-header-body adt-header fn-hp-rows)))))

(defthm fn-hp-len-image
  (equal (len (fn-hp-image h salt)) (* 16384 (fn-hp-npages h salt)))
  :hints (("Goal" :in-theory (disable adt-ser adt-regs fn-hp-rows adt-end-is-end-l))))

(defthm fn-hp-npages-is-end-l
  (equal (fn-hp-npages h salt) (adt-end-l (fn-hp-lens h salt) 1))
  :hints (("Goal" :in-theory (disable adt-regs fn-hp-rows))))

(defthm fn-hp-nat-listp-lens
  (nat-listp (fn-hp-lens h salt)))

(defthm fn-hp-iw-cell
  (implies (and (fn-hp-okp h salt) (natp r) (< r 4) (natp i) (< i (len h)))
           (equal (nth (+ (* 2048 (nth r (fn-hp-starts h salt))) i) (fn-hp-iw h salt))
                  (nth r (fn-hp-cells-of (nth i h) salt (fn-hp-pes-len (take i h))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-iw-word (j (+ (* 2048 (nth r (fn-hp-starts h salt))) i)))
                 (:instance fn-hp-col-octets)
                 (:instance fn-hp-region-within-end (lens (fn-hp-lens h salt)) (start 1))
                 (:instance fn-hp-lens-col-sizes)
                 (:instance fn-hp-natp-nth-starts-l (lens (fn-hp-lens h salt)) (s 1))
                 (:instance fn-hp-starts-is))
           :in-theory (disable fn-hp-iw-word fn-hp-col-octets fn-hp-region-within-end fn-hp-lens-col-sizes
                               fn-hp-natp-nth-starts-l fn-hp-iw fn-hp-image fn-hp-okp fn-hp-cells-of
                               fn-hp-starts fn-hp-lens fn-hp-npages adt-unle adt-starts-l adt-end-l))))

(defthm fn-hp-octetsp-nthcdr-x
  (implies (adt-octetsp b) (adt-octetsp (nthcdr n b)))
  :hints (("Goal" :in-theory (enable nthcdr))))
(defthm fn-hp-words-slice
  (implies (and (natp e) (adt-octetsp b) (equal (len b) (* 16384 e)) (natp s) (natp o) (natp p)
                (equal (mod o 8) 0) (equal (mod p 8) 0) (<= (+ (* 16384 s) o p) (* 16384 e)))
           (equal (pgs-words-le-octets (take (floor p 8) (nthcdr (+ (* 2048 s) (floor o 8)) (fn-hp-pack8 (* 2048 e) b))))
                  (take p (nthcdr (+ (* 16384 s) o) b))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-floor-8-exact (x o)) (:instance fn-hp-floor-8-exact (x p))
                 (:instance fn-hp-nthcdr-pack8 (m (+ (* 2048 s) (floor o 8))) (n (* 2048 e)))
                 (:instance fn-hp-take-pack8 (m (floor p 8)) (n (- (* 2048 e) (+ (* 2048 s) (floor o 8))))
                            (b (nthcdr (* 8 (+ (* 2048 s) (floor o 8))) b)))
                 (:instance fn-hp-words-le-octets-of-pack8 (n (floor p 8)) (b (nthcdr (* 8 (+ (* 2048 s) (floor o 8))) b))))
           :in-theory (disable floor mod fn-hp-floor-8-exact fn-hp-nthcdr-pack8 fn-hp-take-pack8
                               fn-hp-words-le-octets-of-pack8 pgs-words-le-octets fn-hp-pack8))))

(defthm fn-hp-okp-events
  (implies (fn-hp-okp h salt) (fn-hp-events-okp h))
  :rule-classes :forward-chaining)

(defthm fn-hp-iw-pool
  (implies (and (fn-hp-okp h salt) (natp i) (< i (len h)))
           (equal (pgs-words-le-octets
                   (take (floor (len (fn-hp-pe (nth i h))) 8)
                         (nthcdr (+ (* 2048 (nth 4 (fn-hp-starts h salt))) (floor (fn-hp-pes-len (take i h)) 8))
                                 (fn-hp-iw h salt))))
                  (fn-hp-pe (nth i h))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-pool-octets) (:instance fn-hp-octetsp-image)
                 (:instance fn-hp-region-within-end (lens (fn-hp-lens h salt)) (start 1) (r 4))
                 (:instance fn-hp-pes-len-take-bound)
                 (:instance fn-hp-natp-start-4)
                 (:instance fn-hp-starts-is)
                 (:instance fn-hp-words-slice (e (fn-hp-npages h salt)) (b (fn-hp-image h salt))
                            (s (nth 4 (fn-hp-starts h salt))) (o (fn-hp-pes-len (take i h)))
                            (p (len (fn-hp-pe (nth i h))))))
           :in-theory (disable fn-hp-pool-octets fn-hp-region-within-end fn-hp-pes-len-take-bound fn-hp-natp-start-4
                               fn-hp-words-slice floor mod
                               fn-hp-image fn-hp-okp fn-hp-starts fn-hp-lens fn-hp-npages adt-starts-l adt-end-l
                               fn-hp-pes-len pgs-words-le-octets fn-hp-pack8))))

(defthmd fn-hp-cells-of-is
  (equal (fn-hp-cells-of ev salt pos)
         (list (fn-hp-mkey ev salt) (len (fn-scc-encode ev)) (nfix pos) (len (fn-hp-pe ev))))
  :hints (("Goal" :in-theory (e/d (fn-hp-pe) (fn-scc-encode fn-hp-len-pad8)))))

(defthm fn-hp-w-at-when
  (implies (and (natp seq) (< seq (nfix n))
                (equal (nth (+ (* 2048 (nth 0 starts)) seq) w) k)
                (equal (nth (+ (* 2048 (nth 1 starts)) seq) w) tl)
                (equal (nth (+ (* 2048 (nth 2 starts)) seq) w) off)
                (equal (nth (+ (* 2048 (nth 3 starts)) seq) w) plen)
                (natp off) (natp plen) (natp tl) (equal (mod off 8) 0) (equal (mod plen 8) 0)
                (<= tl plen) (<= (+ off plen) (nfix (nth 4 lens)))
                (equal (pgs-words-le-octets (take (floor plen 8) (nthcdr (+ (* 2048 (nth 4 starts)) (floor off 8)) w)))
                       bytes)
                (equal bytes (fn-hp-pad8 (take tl bytes)))
                (equal (fn-scc-decode-tree (take tl bytes)) (list :ok ev))
                (equal k (fn-hp-mkey ev salt)))
           (equal (fn-hp-w-at seq w salt n lens starts) (list :ok ev)))
  :hints (("Goal" :in-theory (disable fn-hp-mkey fn-scc-decode-tree pgs-words-le-octets floor mod take nthcdr nth))))

(defthmd fn-hp-pe-def
  (equal (fn-hp-pe ev) (fn-hp-pad8 (fn-scc-encode ev)))
  :hints (("Goal" :in-theory (enable fn-hp-pe))))

(defthm fn-hp-w-at-of-image
  (implies (and (fn-hp-okp h salt) (natp seq) (< seq (len h)))
           (equal (fn-hp-w-at seq (fn-hp-iw h salt) salt (len h) (fn-hp-lens h salt) (fn-hp-starts h salt))
                  (list :ok (nth seq h))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-w-at-when (w (fn-hp-iw h salt)) (n (len h)) (lens (fn-hp-lens h salt))
                            (starts (fn-hp-starts h salt)) (ev (nth seq h))
                            (k (fn-hp-mkey (nth seq h) salt)) (tl (len (fn-scc-encode (nth seq h))))
                            (off (fn-hp-pes-len (take seq h))) (plen (len (fn-hp-pe (nth seq h))))
                            (bytes (fn-hp-pe (nth seq h))))
                 (:instance fn-hp-iw-cell (r 0) (i seq)) (:instance fn-hp-iw-cell (r 1) (i seq))
                 (:instance fn-hp-iw-cell (r 2) (i seq)) (:instance fn-hp-iw-cell (r 3) (i seq))
                 (:instance fn-hp-cells-of-is (ev (nth seq h)) (pos (fn-hp-pes-len (take seq h))))
                 (:instance fn-hp-iw-pool (i seq))
                 (:instance fn-hp-evp-nth (i seq))
                 (:instance fn-hp-pes-len-take-bound (i seq))
                 (:instance fn-hp-pes-len-mod-8 (h (take seq h)))
                 (:instance fn-hp-pe-mod-8 (ev (nth seq h)))
                 (:instance fn-hp-take-of-pe (ev (nth seq h)))
                 (:instance fn-hp-pe-def (ev (nth seq h)))
                 (:instance fn-hp-decode-enc (ev (nth seq h)))
                 (:instance fn-hp-len-enc-le-pe (ev (nth seq h))))
           :in-theory (theory 'minimal-theory))
          ("Goal'" :in-theory (e/d (fn-hp-lens-4) (fn-hp-w-at fn-hp-iw fn-hp-image fn-hp-okp fn-hp-starts fn-hp-lens
                                   fn-hp-npages fn-hp-pes-len fn-hp-pe fn-scc-encode fn-scc-decode-tree fn-hp-evp
                                   pgs-words-le-octets floor mod fn-hp-mkey fn-hp-cells-of fn-hp-len-pad8 fn-scc-program adt-len-region-below-body adt-body
                                   fn-hp-pad8-count fn-hp-pe-is-pad8 fn-hp-pad8 nth take nthcdr fn-hp-events-okp)))))

(defun fn-hp-x-ready (p pgs-mem)
  ; :ok when logical page P is resident and verified; otherwise what the
  ; host serves before it asks again, in `pgs-x-read''s shapes:
  ; (:need-table T PHYS), (:need-page P PHYS) (fill the page from PHYS and
  ; call `pgs-x-open-page' with :eager, which verifies it against its table
  ; entry), or :out-of-range.  Reads the stobj; changes nothing.
  (declare (xargs :stobjs pgs-mem :guard (natp p)))
  (let ((tp (floor p 341)))
    (cond ((not (and (< p (pgs-v-length pgs-mem))
                     (<= (* 2048 (+ 1 p)) (pgs-w-length pgs-mem))
                     (< tp (pgs-tv-length pgs-mem))))
           :out-of-range)
          ((not (equal (pgs-tvi tp pgs-mem) 2))
           (list :need-table tp (first (pgs-x-get-entry 1 *pgs-x-dir-base* tp pgs-mem))))
          ((not (equal (pgs-vi p pgs-mem) 2))
           (list :need-page p (first (pgs-x-get-entry 2 0 p pgs-mem))))
          (t :ok))))

(defthm fn-hp-x-ready-ok
  (implies (equal (fn-hp-x-ready p pgs-mem) :ok)
           (and (< p (pgs-v-length pgs-mem))
                (<= (* 2048 (+ 1 p)) (pgs-w-length pgs-mem))
                (equal (pgs-vi p pgs-mem) 2)))
  :rule-classes :forward-chaining)

(defun fn-hp-x-ready-range (p hi pgs-mem)
  ; :ok when every page in [P, HI) is ready, else the first one's verdict
  (declare (xargs :stobjs pgs-mem :guard (and (natp p) (natp hi))
                  :measure (nfix (- (nfix hi) (nfix p)))))
  (if (mbe :logic (zp (- (nfix hi) (nfix p))) :exec (<= hi p))
      :ok
    (let ((v (fn-hp-x-ready p pgs-mem)))
      (if (eq v :ok) (fn-hp-x-ready-range (+ 1 (nfix p)) hi pgs-mem) v))))

(defun fn-hp-x-words (i k pgs-mem)
  ; words I .. I+K-1 of the image, as a list
  (declare (xargs :stobjs pgs-mem
                  :guard (and (natp i) (natp k) (<= (+ i k) (pgs-w-length pgs-mem)))))
  (if (zp k) nil (cons (pgs-wi i pgs-mem) (fn-hp-x-words (+ 1 i) (1- k) pgs-mem))))

(defthm fn-hp-x-words-is-take
  (implies (natp i)
           (equal (fn-hp-x-words i k pgs-mem) (take k (nthcdr i (nth *pgs-wi* pgs-mem)))))
  :hints (("Goal" :in-theory (enable pgs-wi take nthcdr) :induct (fn-hp-x-words i k pgs-mem))))

; The open's header check as the host calls it.
(verify-guards fn-hp-w-header)

(defun fn-hp-x-header (npages pgs-mem)
  ; The open's header check, as the host calls it: (mv VERDICT RESULT).
  ; VERDICT :ok and RESULT (:ok N LENS STARTS) or (:refused REASON) once
  ; page 0 is ready; else VERDICT is what the host serves first.
  (declare (xargs :stobjs pgs-mem :guard (natp npages)))
  (let ((v (fn-hp-x-ready 0 pgs-mem)))
    (if (eq v :ok)
        (mv :ok (fn-hp-w-header (fn-hp-x-words 0 18 pgs-mem) npages))
      (mv v nil))))

(local
 (defthm fn-hp-nth-take-below
   (implies (and (natp j) (natp k) (< j k))
            (equal (nth j (take k w)) (nth j w)))
   :hints (("Goal" :in-theory (enable nth take)))))

(defthm fn-hp-w-header-take-18
  (equal (fn-hp-w-header (take 18 w) npages) (fn-hp-w-header w npages))
  :hints (("Goal" :in-theory (disable take adt-starts-l adt-end-l))))

(local
 (defthm fn-hp-take-18-of-take-2048
   (equal (take 18 (take 2048 w)) (take 18 w))
   :hints (("Goal" :in-theory (enable take)))))

; KEYSTONE (the open's header, m2): when page 0 of the page store's image
; holds page 0 of the history's image and the store holds the image's page
; count, the header check the host calls answers the history's N and
; regions; no row page is read.
(defthm fn-hp-x-header-of-image
  (implies (and (fn-hp-okp h salt)
                (equal (take 2048 (nth *pgs-wi* pgs-mem)) (take 2048 (fn-hp-iw h salt)))
                (equal npages (fn-hp-npages h salt))
                (equal (mv-nth 0 (fn-hp-x-header npages pgs-mem)) :ok))
           (equal (mv-nth 1 (fn-hp-x-header npages pgs-mem))
                  (list :ok (len h) (fn-hp-lens h salt) (fn-hp-starts h salt))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-w-header-of-image)
                 (:instance fn-hp-w-header-take-18 (w (nth *pgs-wi* pgs-mem)) (npages (fn-hp-npages h salt)))
                 (:instance fn-hp-w-header-take-18 (w (fn-hp-iw h salt)) (npages (fn-hp-npages h salt)))
                 (:instance fn-hp-take-18-of-take-2048 (w (nth *pgs-wi* pgs-mem)))
                 (:instance fn-hp-take-18-of-take-2048 (w (fn-hp-iw h salt))))
           :in-theory (disable fn-hp-w-header-of-image fn-hp-w-header-take-18 fn-hp-take-18-of-take-2048
                               fn-hp-w-header fn-hp-iw fn-hp-okp fn-hp-npages fn-hp-lens fn-hp-starts take))))

(local
 (defthm fn-hp-octetp-sha-byte
   (fn-scc-octetp (fn-sha256-byte x))
   :hints (("Goal" :in-theory (enable fn-sha256-byte fn-scc-octetp)))))
(local
 (defthm fn-hp-scc-octets-of-word
   (fn-scc-octet-listp (pgs-word-le-octets w))
   :hints (("Goal" :in-theory (disable fn-sha256-byte ash)))))
(local
 (defthm fn-hp-scc-octet-listp-append
   (implies (and (fn-scc-octet-listp x) (fn-scc-octet-listp y)) (fn-scc-octet-listp (append x y)))))
(defthm fn-hp-scc-octets-of-words
  (fn-scc-octet-listp (pgs-words-le-octets ws))
  :hints (("Goal" :in-theory (disable pgs-word-le-octets))))

(defun fn-hp-at-core (seq n lens salt mkey tl off plen pw)
  ; the decision of the row read, given the row's four cells and PW, the
  ; words of its pool entry
  (declare (xargs :guard (and (true-listp lens) (true-listp pw))))
  (cond ((not (and (natp seq) (< seq (nfix n)))) (list :refused :seq))
        ((not (and (natp off) (natp plen) (natp tl) (equal (mod off 8) 0) (equal (mod plen 8) 0)
                   (<= tl plen) (<= (+ off plen) (nfix (nth 4 lens)))))
         (list :refused :cells))
        (t (let ((bytes (pgs-words-le-octets pw)))
             (if (not (and (<= tl (len bytes)) (equal bytes (fn-hp-pad8 (take tl bytes)))))
                 (list :refused :padding)
               (let ((d (fn-scc-decode-tree (take tl bytes))))
                 (cond ((not (eq (car d) :ok)) (list :refused :tree))
                       ((not (equal mkey (fn-hp-mkey (cadr d) salt))) (list :refused :mkey))
                       (t d))))))))

(defthm fn-hp-at-core-when
  (implies (and (natp seq) (< seq (nfix n))
                (natp off) (natp plen) (natp tl) (equal (mod off 8) 0) (equal (mod plen 8) 0)
                (<= tl plen) (<= (+ off plen) (nfix (nth 4 lens)))
                (equal (pgs-words-le-octets pw) bytes)
                (<= tl (len bytes))
                (equal bytes (fn-hp-pad8 (take tl bytes)))
                (equal (fn-scc-decode-tree (take tl bytes)) (list :ok ev))
                (equal mkey (fn-hp-mkey ev salt)))
           (equal (fn-hp-at-core seq n lens salt mkey tl off plen pw) (list :ok ev)))
  :hints (("Goal" :in-theory (disable fn-hp-mkey fn-scc-decode-tree pgs-words-le-octets mod take nth))))

(defun fn-hp-cell-word (r seq w starts)
  ; cell SEQ of column R, as the reader finds it in the words W
  (declare (xargs :verify-guards nil))
  (nth (+ (* 2048 (nth r starts)) seq) w))

(defun fn-hp-pool-words (seq w starts)
  ; the words of row SEQ's pool entry, as the reader finds them in W
  (declare (xargs :verify-guards nil))
  (let ((off (fn-hp-cell-word 2 seq w starts)) (plen (fn-hp-cell-word 3 seq w starts)))
    (take (floor plen 8) (nthcdr (+ (* 2048 (nth 4 starts)) (floor off 8)) w))))

(defun fn-hp-w-row (seq w salt n lens starts)
  ; the row read over the words W: the core over what W holds at the row
  (declare (xargs :verify-guards nil))
  (fn-hp-at-core seq n lens salt
                 (fn-hp-cell-word 0 seq w starts) (fn-hp-cell-word 1 seq w starts)
                 (fn-hp-cell-word 2 seq w starts) (fn-hp-cell-word 3 seq w starts)
                 (fn-hp-pool-words seq w starts)))

(defthm fn-hp-len-pe-bound
  (<= (len (fn-scc-encode ev)) (len (fn-hp-pe ev)))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn-hp-len-enc-le-pe)))))

(defthm fn-hp-w-row-of-image
  (implies (and (fn-hp-okp h salt) (natp seq) (< seq (len h)))
           (equal (fn-hp-w-row seq (fn-hp-iw h salt) salt (len h) (fn-hp-lens h salt) (fn-hp-starts h salt))
                  (list :ok (nth seq h))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-at-core-when (n (len h)) (lens (fn-hp-lens h salt)) (ev (nth seq h))
                            (mkey (fn-hp-mkey (nth seq h) salt)) (tl (len (fn-scc-encode (nth seq h))))
                            (off (fn-hp-pes-len (take seq h))) (plen (len (fn-hp-pe (nth seq h))))
                            (pw (take (floor (len (fn-hp-pe (nth seq h))) 8)
                                      (nthcdr (+ (* 2048 (nth 4 (fn-hp-starts h salt))) (floor (fn-hp-pes-len (take seq h)) 8))
                                              (fn-hp-iw h salt))))
                            (bytes (fn-hp-pe (nth seq h))))
                 (:instance fn-hp-iw-cell (r 0) (i seq)) (:instance fn-hp-iw-cell (r 1) (i seq))
                 (:instance fn-hp-iw-cell (r 2) (i seq)) (:instance fn-hp-iw-cell (r 3) (i seq))
                 (:instance fn-hp-cells-of-is (ev (nth seq h)) (pos (fn-hp-pes-len (take seq h))))
                 (:instance fn-hp-iw-pool (i seq))
                 (:instance fn-hp-evp-nth (i seq))
                 (:instance fn-hp-pes-len-take-bound (i seq))
                 (:instance fn-hp-pes-len-mod-8 (h (take seq h)))
                 (:instance fn-hp-pe-mod-8 (ev (nth seq h)))
                 (:instance fn-hp-take-of-pe (ev (nth seq h)))
                 (:instance fn-hp-pe-def (ev (nth seq h)))
                 (:instance fn-hp-decode-enc (ev (nth seq h)))
                 (:instance fn-hp-len-enc-le-pe (ev (nth seq h))))
           :in-theory (theory 'minimal-theory))
          ("Goal'" :in-theory (e/d (fn-hp-lens-4 fn-hp-w-row fn-hp-cell-word fn-hp-pool-words)
                                   (fn-hp-at-core fn-hp-iw fn-hp-image fn-hp-okp fn-hp-starts fn-hp-lens
                                   fn-hp-npages fn-hp-pes-len fn-hp-pe fn-scc-encode fn-scc-decode-tree fn-hp-evp
                                   pgs-words-le-octets floor mod fn-hp-mkey fn-hp-cells-of fn-hp-len-pad8 fn-scc-program
                                   adt-len-region-below-body adt-body
                                   fn-hp-pad8-count fn-hp-pe-is-pad8 fn-hp-pad8 nth take nthcdr fn-hp-events-okp)))))

; -----------------------------------------------------------------------------
; D. The reads as the host calls them: need-verdicts, never a fill.

(defun fn-hp-starts-okp (starts)
  (declare (xargs :guard t))
  (and (nat-listp starts) (equal (len starts) 5)))

(defun fn-hp-x-cell (r seq starts pgs-mem)
  ; cell SEQ of column R: (mv VERDICT WORD); VERDICT :ok once its page is
  ; ready, else what the host serves first
  (declare (xargs :stobjs pgs-mem
                  :guard (and (natp r) (< r 5) (natp seq) (fn-hp-starts-okp starts))))
  (let* ((i (+ (* 2048 (nfix (nth r starts))) seq))
         (v (fn-hp-x-ready (floor i 2048) pgs-mem)))
    (cond ((not (eq v :ok)) (mv v 0))
          ((not (< i (pgs-w-length pgs-mem))) (mv :out-of-range 0))
          (t (mv :ok (pgs-wi i pgs-mem))))))


(defthm fn-hp-x-cell-natp
  (implies (and (pgs-memp pgs-mem) (natp seq)) (natp (mv-nth 1 (fn-hp-x-cell r seq starts pgs-mem))))
  :rule-classes :type-prescription)


(defthm fn-hp-starts-okp-true-listp
  (implies (fn-hp-starts-okp s) (true-listp s))
  :rule-classes :forward-chaining)


(defthm fn-hp-x-ready-range-ok
  (implies (and (equal (fn-hp-x-ready-range p hi pgs-mem) :ok) (natp p) (natp hi) (< p hi))
           (<= (* 2048 hi) (pgs-w-length pgs-mem)))
  :hints (("Goal" :induct (fn-hp-x-ready-range p hi pgs-mem)))
  :rule-classes nil)

(defun fn-hp-pool-lo (off starts)
  ; the first word of the pool entry at octet OFFSET OFF
  (declare (xargs :guard (and (natp off) (fn-hp-starts-okp starts))))
  (+ (* 2048 (nfix (nth 4 starts))) (floor (nfix off) 8)))

(defun fn-hp-x-pool-ready (lo k pgs-mem)
  ; every page of words LO .. LO+K-1 ready (K > 0)
  (declare (xargs :stobjs pgs-mem :guard (and (natp lo) (natp k))))
  (fn-hp-x-ready-range (floor lo 2048) (+ 1 (floor (+ lo k -1) 2048)) pgs-mem))

(defthm fn-hp-x-pool-ready-bound
  (implies (and (equal (fn-hp-x-pool-ready lo k pgs-mem) :ok) (natp lo) (posp k))
           (<= (+ lo k) (pgs-w-length pgs-mem)))
  :hints (("Goal" :in-theory (disable floor)
           :use ((:instance fn-hp-x-ready-range-ok (p (floor lo 2048)) (hi (+ 1 (floor (+ lo k -1) 2048))))
                 (:instance fn-hp-page-start-below-word (w lo))
                 (:instance fn-hp-word-below-next-page (w (+ lo k -1)))
                 (:instance fn-hp-page-start-below-word (w (+ lo k -1)))
                 (:instance fn-hp-word-below-next-page (w lo))))))

(defun fn-hp-x-at (seq salt n lens starts pgs-mem)
  ; The event at SEQ, as the host calls it: (mv VERDICT RESULT).  VERDICT
  ; :ok and RESULT (:ok EV) or (:refused REASON) once every page the row
  ; touches is ready (its four cells' pages and its pool entry's pages);
  ; else VERDICT is what the host serves (a fill, then it asks again).
  ; N, LENS, STARTS: the open's header answer.  Changes nothing.
  (declare (xargs :stobjs pgs-mem
                  :guard (and (natp seq) (natp n) (true-listp lens) (fn-hp-starts-okp starts))
                  :guard-hints (("Goal" :in-theory (disable fn-hp-x-cell fn-hp-x-ready fn-hp-x-pool-ready
                                                            fn-hp-at-core floor mod fn-hp-starts-okp nth)))))
  (if (not (< seq n))
      (mv :ok (list :refused :seq))
    (mv-let (v0 mkey) (fn-hp-x-cell 0 seq starts pgs-mem)
      (mv-let (v1 tl) (fn-hp-x-cell 1 seq starts pgs-mem)
        (mv-let (v2 off) (fn-hp-x-cell 2 seq starts pgs-mem)
          (mv-let (v3 plen) (fn-hp-x-cell 3 seq starts pgs-mem)
            (cond ((not (eq v0 :ok)) (mv v0 nil))
                  ((not (eq v1 :ok)) (mv v1 nil))
                  ((not (eq v2 :ok)) (mv v2 nil))
                  ((not (eq v3 :ok)) (mv v3 nil))
                  ((not (and (equal (mod off 8) 0) (equal (mod plen 8) 0) (<= tl plen)
                             (<= (+ off plen) (nfix (nth 4 lens))) (< 0 plen)))
                   (mv :ok (fn-hp-at-core seq n lens salt mkey tl off plen nil)))
                  (t
                   (let* ((lo (fn-hp-pool-lo off starts))
                          (k (floor plen 8))
                          (v (fn-hp-x-pool-ready lo k pgs-mem)))
                     (cond ((not (eq v :ok)) (mv v nil))
                           ((not (<= (+ lo k) (pgs-w-length pgs-mem))) (mv :out-of-range nil))
                           (t (mv :ok (fn-hp-at-core seq n lens salt mkey tl off plen
                                                     (fn-hp-x-words lo k pgs-mem))))))))))))))


; The read against the verified pages.

(defun-nx fn-hp-vhold (p np pgs-mem iw)
  ; every VERIFIED page P..NP-1 of the store holds the image's words IW there
  (declare (xargs :measure (nfix (- (nfix np) (nfix p)))))
  (if (zp (- (nfix np) (nfix p)))
      t
    (and (implies (equal (pgs-vi p pgs-mem) 2)
                  (equal (take 2048 (nthcdr (* 2048 (nfix p)) (nth *pgs-wi* pgs-mem)))
                         (take 2048 (nthcdr (* 2048 (nfix p)) iw))))
         (fn-hp-vhold (+ 1 (nfix p)) np pgs-mem iw))))

(local
 (defthm fn-hp-nth-of-take-nthcdr
   (implies (and (natp a) (natp j) (< j k) (natp k))
            (equal (nth j (take k (nthcdr a x))) (nth (+ a j) x)))
   :hints (("Goal" :in-theory (enable nth take nthcdr)))))

(defthm fn-hp-vhold-page
  (implies (and (fn-hp-vhold p np pgs-mem iw) (natp p) (natp q) (<= p q) (< q (nfix np))
                (equal (pgs-vi q pgs-mem) 2))
           (equal (take 2048 (nthcdr (* 2048 q) (nth *pgs-wi* pgs-mem)))
                  (take 2048 (nthcdr (* 2048 q) iw))))
  :hints (("Goal" :induct (fn-hp-vhold p np pgs-mem iw) :in-theory (disable take nthcdr))))

(defthm fn-hp-vhold-word
  (implies (and (fn-hp-vhold p np pgs-mem iw) (natp p) (natp q) (<= p q) (< q (nfix np))
                (equal (pgs-vi q pgs-mem) 2) (natp j) (< j 2048))
           (equal (nth (+ (* 2048 q) j) (nth *pgs-wi* pgs-mem)) (nth (+ (* 2048 q) j) iw)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-vhold-page)
                 (:instance fn-hp-nth-of-take-nthcdr (a (* 2048 q)) (k 2048) (x (nth *pgs-wi* pgs-mem)))
                 (:instance fn-hp-nth-of-take-nthcdr (a (* 2048 q)) (k 2048) (x iw)))
           :in-theory (disable fn-hp-vhold-page fn-hp-nth-of-take-nthcdr fn-hp-vhold take nthcdr))))
(defthm fn-hp-vhold-index
  (implies (and (fn-hp-vhold 0 np pgs-mem iw) (natp i) (< (floor i 2048) (nfix np))
                (equal (pgs-vi (floor i 2048) pgs-mem) 2))
           (equal (nth i (nth *pgs-wi* pgs-mem)) (nth i iw)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-vhold-word (p 0) (q (floor i 2048)) (j (mod i 2048))))
           :in-theory (disable fn-hp-vhold-word fn-hp-vhold))))

(defthm fn-hp-x-ready-range-each
  (implies (and (equal (fn-hp-x-ready-range p hi pgs-mem) :ok) (natp p) (natp q) (<= p q) (< q (nfix hi)))
           (equal (fn-hp-x-ready q pgs-mem) :ok))
  :hints (("Goal" :induct (fn-hp-x-ready-range p hi pgs-mem) :in-theory (disable fn-hp-x-ready))))
(defthm fn-hp-floor-in-pages
  (implies (and (natp i) (natp p) (natp h) (<= (* 2048 p) i) (< i (* 2048 h)))
           (and (<= p (floor i 2048)) (< (floor i 2048) h)))
  :hints (("Goal" :use ((:instance fn-hp-word-below-next-page (w i))
                        (:instance fn-hp-page-start-below-word (w i)))
           :in-theory (disable floor)))
  :rule-classes nil)

(defthm fn-hp-x-words-from-ready
  (implies (and (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem iw) (natp lo) (natp k) (natp p) (natp h)
                (equal (fn-hp-x-ready-range p h pgs-mem) :ok)
                (<= (* 2048 p) lo) (<= (+ lo k) (* 2048 h)))
           (equal (fn-hp-x-words lo k pgs-mem) (take k (nthcdr lo iw))))
  :hints (("Goal" :induct (fn-hp-x-words lo k pgs-mem)
           :in-theory (e/d (take nthcdr) (fn-hp-x-ready fn-hp-x-ready-range fn-hp-vhold floor)))
          ("Subgoal *1/2" :use ((:instance fn-hp-floor-in-pages (i lo))
                                (:instance fn-hp-x-ready-range-each (q (floor lo 2048)))
                                (:instance fn-hp-x-ready-ok (p (floor lo 2048)))
                                (:instance fn-hp-vhold-index (i lo) (np (pgs-v-length pgs-mem)))))))
(defthm fn-hp-x-cell-from-ready
  (implies (and (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem iw) (natp seq)
                (equal (mv-nth 0 (fn-hp-x-cell r seq starts pgs-mem)) :ok))
           (equal (mv-nth 1 (fn-hp-x-cell r seq starts pgs-mem))
                  (nth (+ (* 2048 (nfix (nth r starts))) seq) iw)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-x-ready-ok (p (floor (+ (* 2048 (nfix (nth r starts))) seq) 2048)))
                 (:instance fn-hp-vhold-index (i (+ (* 2048 (nfix (nth r starts))) seq)) (np (pgs-v-length pgs-mem))))
           :in-theory (e/d (pgs-wi) (fn-hp-x-ready fn-hp-vhold fn-hp-x-ready-ok fn-hp-vhold-index floor)))))

(defthm fn-hp-x-words-from-pool-ready
  (implies (and (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem iw) (natp lo) (posp k)
                (equal (fn-hp-x-pool-ready lo k pgs-mem) :ok))
           (equal (fn-hp-x-words lo k pgs-mem) (take k (nthcdr lo iw))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-x-words-from-ready (p (floor lo 2048)) (h (+ 1 (floor (+ lo k -1) 2048))))
                 (:instance fn-hp-page-start-below-word (w lo))
                 (:instance fn-hp-word-below-next-page (w (+ lo k -1))))
           :in-theory (disable fn-hp-x-words-from-ready fn-hp-x-words fn-hp-x-ready-range fn-hp-vhold floor))))

(defthm fn-hp-x-at-ok-cells
  (implies (and (natp seq) (natp n) (< seq n)
                (equal (mv-nth 0 (fn-hp-x-at seq salt n lens starts pgs-mem)) :ok))
           (and (equal (mv-nth 0 (fn-hp-x-cell 0 seq starts pgs-mem)) :ok)
                (equal (mv-nth 0 (fn-hp-x-cell 1 seq starts pgs-mem)) :ok)
                (equal (mv-nth 0 (fn-hp-x-cell 2 seq starts pgs-mem)) :ok)
                (equal (mv-nth 0 (fn-hp-x-cell 3 seq starts pgs-mem)) :ok)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-hp-x-cell fn-hp-x-pool-ready fn-hp-x-words fn-hp-at-core fn-hp-pool-lo floor mod mv-nth))))

(defthm fn-hp-x-at-ok-pool
  (implies (and (natp seq) (natp n) (< seq n)
                (equal (mv-nth 0 (fn-hp-x-at seq salt n lens starts pgs-mem)) :ok)
                (equal off (mv-nth 1 (fn-hp-x-cell 2 seq starts pgs-mem)))
                (equal plen (mv-nth 1 (fn-hp-x-cell 3 seq starts pgs-mem)))
                (equal (mod off 8) 0) (equal (mod plen 8) 0)
                (<= (mv-nth 1 (fn-hp-x-cell 1 seq starts pgs-mem)) plen)
                (<= (+ off plen) (nfix (nth 4 lens))) (< 0 plen))
           (and (equal (fn-hp-x-pool-ready (fn-hp-pool-lo off starts) (floor plen 8) pgs-mem) :ok)
                (equal (mv-nth 1 (fn-hp-x-at seq salt n lens starts pgs-mem))
                       (fn-hp-at-core seq n lens salt
                                      (mv-nth 1 (fn-hp-x-cell 0 seq starts pgs-mem))
                                      (mv-nth 1 (fn-hp-x-cell 1 seq starts pgs-mem)) off plen
                                      (fn-hp-x-words (fn-hp-pool-lo off starts) (floor plen 8) pgs-mem)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-hp-x-cell fn-hp-x-pool-ready fn-hp-x-words fn-hp-at-core fn-hp-pool-lo floor mod))))

(defthm fn-hp-x-at-ok-nopool
  (implies (and (natp seq) (natp n) (< seq n)
                (equal (mv-nth 0 (fn-hp-x-at seq salt n lens starts pgs-mem)) :ok)
                (not (and (equal (mod (mv-nth 1 (fn-hp-x-cell 2 seq starts pgs-mem)) 8) 0)
                          (equal (mod (mv-nth 1 (fn-hp-x-cell 3 seq starts pgs-mem)) 8) 0)
                          (<= (mv-nth 1 (fn-hp-x-cell 1 seq starts pgs-mem)) (mv-nth 1 (fn-hp-x-cell 3 seq starts pgs-mem)))
                          (<= (+ (mv-nth 1 (fn-hp-x-cell 2 seq starts pgs-mem)) (mv-nth 1 (fn-hp-x-cell 3 seq starts pgs-mem)))
                              (nfix (nth 4 lens)))
                          (< 0 (mv-nth 1 (fn-hp-x-cell 3 seq starts pgs-mem))))))
           (equal (mv-nth 1 (fn-hp-x-at seq salt n lens starts pgs-mem))
                  (fn-hp-at-core seq n lens salt
                                 (mv-nth 1 (fn-hp-x-cell 0 seq starts pgs-mem))
                                 (mv-nth 1 (fn-hp-x-cell 1 seq starts pgs-mem))
                                 (mv-nth 1 (fn-hp-x-cell 2 seq starts pgs-mem))
                                 (mv-nth 1 (fn-hp-x-cell 3 seq starts pgs-mem)) nil)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-hp-x-cell fn-hp-x-pool-ready fn-hp-x-words fn-hp-at-core fn-hp-pool-lo floor mod))))

(defthm fn-hp-consp-program
  (consp (fn-scc-program x))
  :hints (("Goal" :in-theory (enable fn-scc-program fn-scc-atom-octets))))

(defthm fn-hp-len-pe-pos
  (< 0 (len (fn-hp-pe ev)))
  :hints (("Goal" :in-theory (enable fn-hp-pe fn-hp-pad8)))
  :rule-classes :linear)

(local
 (defthm fn-hp-natp-nth-nat-listp
   (implies (and (nat-listp l) (natp r) (< r (len l))) (natp (nth r l)))
   :hints (("Goal" :in-theory (enable nth)))))

(defthm fn-hp-nfix-nth-starts
  (implies (and (fn-hp-starts-okp starts) (natp r) (< r 5)) (equal (nfix (nth r starts)) (nth r starts)))
  :hints (("Goal" :use ((:instance fn-hp-natp-nth-nat-listp (l starts))) :in-theory (disable fn-hp-natp-nth-nat-listp))))

(local
 (defthm fn-hp-nat-listp-starts-l
   (implies (natp s) (nat-listp (adt-starts-l lens s)))))

(defthm fn-hp-starts-okp-of-starts
  (fn-hp-starts-okp (fn-hp-starts h salt))
  :hints (("Goal" :in-theory (disable fn-hp-lens adt-starts-l))))

(defthm fn-hp-floor-pe-posp
  (posp (floor (len (fn-hp-pe ev)) 8))
  :hints (("Goal" :use ((:instance fn-hp-floor-8-exact (x (len (fn-hp-pe ev))))
                        (:instance fn-hp-pe-mod-8) (:instance fn-hp-len-pe-pos))
           :in-theory (disable fn-hp-floor-8-exact fn-hp-pe-mod-8 fn-hp-len-pe-pos floor mod)))
  :rule-classes :type-prescription)

(defthm fn-hp-pes-len-natp (natp (fn-hp-pes-len h)) :rule-classes :type-prescription)

(defthm fn-hp-x-cell-of-image
  (implies (and (fn-hp-okp h salt) (natp seq) (< seq (len h)) (natp r) (< r 4)
                (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-iw h salt))
                (equal (mv-nth 0 (fn-hp-x-cell r seq (fn-hp-starts h salt) pgs-mem)) :ok))
           (equal (mv-nth 1 (fn-hp-x-cell r seq (fn-hp-starts h salt) pgs-mem))
                  (nth r (fn-hp-cells-of (nth seq h) salt (fn-hp-pes-len (take seq h))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-x-cell-from-ready (starts (fn-hp-starts h salt)) (iw (fn-hp-iw h salt)))
                 (:instance fn-hp-nfix-nth-starts (starts (fn-hp-starts h salt)))
                 (:instance fn-hp-iw-cell (i seq)))
           :in-theory (disable fn-hp-x-cell-from-ready fn-hp-nfix-nth-starts fn-hp-iw-cell fn-hp-x-cell
                               fn-hp-iw fn-hp-okp fn-hp-starts fn-hp-vhold fn-hp-cells-of))))


(defthm fn-hp-x-cells-of-image
  (implies (and (fn-hp-okp h salt) (natp seq) (< seq (len h)) (pgs-memp pgs-mem)
                (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-iw h salt))
                (equal (mv-nth 0 (fn-hp-x-at seq salt (len h) lens (fn-hp-starts h salt) pgs-mem)) :ok))
           (and (equal (mv-nth 1 (fn-hp-x-cell 0 seq (fn-hp-starts h salt) pgs-mem)) (fn-hp-mkey (nth seq h) salt))
                (equal (mv-nth 1 (fn-hp-x-cell 1 seq (fn-hp-starts h salt) pgs-mem)) (len (fn-scc-encode (nth seq h))))
                (equal (mv-nth 1 (fn-hp-x-cell 2 seq (fn-hp-starts h salt) pgs-mem)) (fn-hp-pes-len (take seq h)))
                (equal (mv-nth 1 (fn-hp-x-cell 3 seq (fn-hp-starts h salt) pgs-mem)) (len (fn-hp-pe (nth seq h))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-x-at-ok-cells (n (len h)) (starts (fn-hp-starts h salt)))
                 (:instance fn-hp-x-cell-of-image (r 0)) (:instance fn-hp-x-cell-of-image (r 1))
                 (:instance fn-hp-x-cell-of-image (r 2)) (:instance fn-hp-x-cell-of-image (r 3))
                 (:instance fn-hp-cells-of-is (ev (nth seq h)) (pos (fn-hp-pes-len (take seq h)))))
           :in-theory (union-theories '(car-cons cdr-cons nth-0-cons nth-add1 natp zp (:e zp) (:e natp) (:e <) (:e nth)
                                         (:e len) nth len (:e car) (:e cdr) (:t len) fn-hp-pes-len-natp nfix (:e nfix))
                                      (theory 'minimal-theory)))))

(defthm fn-hp-floor-8-natp (implies (natp x) (natp (floor x 8))) :rule-classes :type-prescription)

(defthm fn-hp-floor-8-nonneg (implies (natp x) (<= 0 (floor x 8))) :rule-classes :linear)

; KEYSTONE (the row read, m2): whenever the read the host calls answers
; (VERDICT :ok), its answer is the history's event at SEQ -- over ANY page
; store state whose VERIFIED pages hold the image's words.  A page not yet
; verified is never read: the read answers a need-verdict instead, and the
; host's fill + `pgs-x-open-page' check is where a page becomes verified.
(defthm fn-hp-x-at-is-nth
  (implies (and (fn-hp-okp h salt) (natp seq) (< seq (len h)) (pgs-memp pgs-mem)
                (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-iw h salt))
                (equal (mv-nth 0 (fn-hp-x-at seq salt (len h) (fn-hp-lens h salt) (fn-hp-starts h salt) pgs-mem)) :ok))
           (equal (mv-nth 1 (fn-hp-x-at seq salt (len h) (fn-hp-lens h salt) (fn-hp-starts h salt) pgs-mem))
                  (list :ok (nth seq h))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-x-cells-of-image (lens (fn-hp-lens h salt)))
                 (:instance fn-hp-x-at-ok-pool (n (len h)) (lens (fn-hp-lens h salt)) (starts (fn-hp-starts h salt))
                            (off (fn-hp-pes-len (take seq h))) (plen (len (fn-hp-pe (nth seq h)))))
                 (:instance fn-hp-x-words-from-pool-ready (iw (fn-hp-iw h salt))
                            (lo (+ (* 2048 (nth 4 (fn-hp-starts h salt))) (floor (fn-hp-pes-len (take seq h)) 8)))
                            (k (floor (len (fn-hp-pe (nth seq h))) 8)))
                 (:instance fn-hp-nfix-nth-starts (r 4) (starts (fn-hp-starts h salt)))
                 (:instance fn-hp-starts-okp-of-starts)
                 (:instance fn-hp-at-core-when (n (len h)) (lens (fn-hp-lens h salt)) (ev (nth seq h))
                            (mkey (fn-hp-mkey (nth seq h) salt)) (tl (len (fn-scc-encode (nth seq h))))
                            (off (fn-hp-pes-len (take seq h))) (plen (len (fn-hp-pe (nth seq h))))
                            (pw (take (floor (len (fn-hp-pe (nth seq h))) 8)
                                      (nthcdr (+ (* 2048 (nth 4 (fn-hp-starts h salt))) (floor (fn-hp-pes-len (take seq h)) 8))
                                              (fn-hp-iw h salt))))
                            (bytes (fn-hp-pe (nth seq h))))
                 (:instance fn-hp-iw-pool (i seq))
                 (:instance fn-hp-evp-nth (i seq))
                 (:instance fn-hp-take-of-pe (ev (nth seq h)))
                 (:instance fn-hp-pe-def (ev (nth seq h)))
                 (:instance fn-hp-decode-enc (ev (nth seq h)))
                 (:instance fn-hp-lens-4)
                 (:instance fn-hp-pes-len-take-bound (i seq))
                 (:instance fn-hp-pes-len-mod-8 (h (take seq h)))
                 (:instance fn-hp-pe-mod-8 (ev (nth seq h)))
                 (:instance fn-hp-len-pe-pos (ev (nth seq h)))
                 (:instance fn-hp-floor-pe-posp (ev (nth seq h)))
                 (:instance fn-hp-len-enc-le-pe (ev (nth seq h))))
           :in-theory (union-theories '(fn-hp-pool-lo nfix natp posp fn-hp-pes-len-natp (:t len) (:e <) (:e natp)
                                        (:t floor) fn-hp-okp-events fn-hp-floor-8-natp fn-hp-floor-8-nonneg)
                                      (theory 'minimal-theory)))))
