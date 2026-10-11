; fn: the runtime contract's executable state, part one: the concrete object
; (arrays and one octet array), the abstraction to the contract's list state,
; and both sides of every export.  books/runtime-contract-pool.lisp proves the
; abstract stobj's obligations from these and admits `fn-rtc-st'.
;
; `fn-rtc-st' is the layer state of books/runtime-contract.lisp as one
; single-threaded object: its LOGICAL value is the list state
; (config slots pool uses mstates next-op) the contract's definitions and
; keystones are about, and its EXECUTABLE is arrays: the slot table and the
; machine states one cell per slot, each buffer's (generation owner fill) one
; cell per buffer, and every buffer's octets in ONE (unsigned-byte 8) array,
; buffer h at cells [base(h), base(h) + cap(h)): the home buffers of capf
; octets first, then the pool's npool buffers of capl octets
; (`fn-rtc-buf-base', `fn-rtc-buf-cap'), so the array holds
; nhome*capf + npool*capl octets, the memory model's connection term.  No
; buffer's bytes are ever a list at run time; a worker's input lands in the
; array in place.
;
; Every export's :logic is the contract's own state operation (fn-rtc-slot,
; fn-rtc-with-slot, fn-rtc-with-buffer of the buffer's fields, fn-rtc-issue,
; fn-rtc-release-all, fn-rtc-view ...), so a function written over the
; exports IS, logically, the contract's function over the list state; the
; executable layer (books/runtime-contract-exec.lisp) proves that equality
; once and the keystones follow.

(in-package "ACL2")
(include-book "runtime-contract")
(local (include-book "arithmetic-5/top" :dir :system))

; -----------------------------------------------------------------------------
; The concrete stobj.

(defstobj fn-rtc-st$c
  (fn-rtc-c-cfg :type t :initially (2 0 0 0 0 0 0))
  (fn-rtc-c-slots :type (array t (2)) :initially nil :resizable t)
  (fn-rtc-c-ms :type (array t (2)) :initially nil :resizable t)
  (fn-rtc-c-meta :type (array t (0)) :initially nil :resizable t)
  (fn-rtc-c-bytes :type (array (unsigned-byte 8) (0)) :initially 0 :resizable t)
  (fn-rtc-c-uses :type t :initially nil)
  (fn-rtc-c-nop :type (integer 0 *) :initially 0)
  :inline t)

; -----------------------------------------------------------------------------
; The array layout: buffer h's first cell, and the array's length.  Buffer
; h + 1 starts where buffer h ends (`fn-rtc-buf-base-of-succ'), so the
; buffers' regions are disjoint and in order.

(defun fn-rtc-buf-base (h cfg)
  (declare (xargs :guard t))
  (let ((h (nfix h)) (nh (fn-rtc-nhome cfg)))
    (if (< h nh)
        (* h (fn-rtc-capf cfg))
      (+ (* nh (fn-rtc-capf cfg)) (* (- h nh) (fn-rtc-capl cfg))))))

(defun fn-rtc-octets-total (cfg)
  (declare (xargs :guard t))
  (+ (* (fn-rtc-nhome cfg) (fn-rtc-capf cfg)) (* (fn-rtc-npool cfg) (fn-rtc-capl cfg))))

(local (in-theory (disable fn-rtc-nhome fn-rtc-capf fn-rtc-capl fn-rtc-npool fn-rtc-nbufs)))

(defthm fn-rtc-buf-base-natp
  (natp (fn-rtc-buf-base h cfg))
  :rule-classes :type-prescription
  :hints (("Goal" :nonlinearp t)))

(defthm fn-rtc-buf-base-of-succ
  (implies (natp h)
           (equal (fn-rtc-buf-base (+ 1 h) cfg)
                  (+ (fn-rtc-buf-base h cfg) (fn-rtc-buf-cap h cfg)))))

(local (defun fn-rtc-buf-ind (j h)
  (declare (xargs :measure (nfix (- (nfix h) (nfix j)))))
  (if (and (natp j) (natp h) (< (+ 1 j) h)) (fn-rtc-buf-ind (+ 1 j) h) (list j h))))

(defthm fn-rtc-buf-base-monotone
  (implies (and (natp j) (natp h) (< j h))
           (<= (+ (fn-rtc-buf-base j cfg) (fn-rtc-buf-cap j cfg)) (fn-rtc-buf-base h cfg)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :induct (fn-rtc-buf-ind j h)
           :in-theory (disable fn-rtc-buf-base fn-rtc-buf-cap))
          ("Subgoal *1/1" :use ((:instance fn-rtc-buf-base-of-succ (h j))))
          ("Subgoal *1/2" :use ((:instance fn-rtc-buf-base-of-succ (h (+ 1 j)))))))

(defthm fn-rtc-buf-base-of-nbufs
  (implies (fn-rtc-configp cfg)
           (equal (fn-rtc-buf-base (fn-rtc-nbufs cfg) cfg) (fn-rtc-octets-total cfg)))
  :hints (("Goal" :in-theory (enable fn-rtc-nbufs fn-rtc-npool fn-rtc-nhome fn-rtc-configp fn-rtc-octets-total
                                     fn-rtc-buf-base))))

(in-theory (disable fn-rtc-buf-base fn-rtc-octets-total))
(local (in-theory (enable fn-rtc-nhome fn-rtc-capf fn-rtc-capl fn-rtc-npool fn-rtc-nbufs)))

; -----------------------------------------------------------------------------
; The abstraction: the list state the concrete object stands for.  Buffer h
; is (gen owner octets) from its meta cell (gen owner fill) and the array's
; cells [base(h), base(h) + fill).

(defun fn-rtc-c-octets (i n bytes)
  (declare (xargs :guard (and (natp i) (natp n)) :verify-guards nil))
  (if (zp n)
      nil
    (cons (nth i bytes) (fn-rtc-c-octets (+ 1 (nfix i)) (- n 1) bytes))))

(defun fn-rtc-c-buffer (h cfg meta bytes)
  (declare (xargs :verify-guards nil))
  (let ((m (nth h meta)))
    (list (fn-rtc-get 0 m) (fn-rtc-get 1 m)
          (fn-rtc-c-octets (fn-rtc-buf-base h cfg) (nfix (fn-rtc-get 2 m)) bytes))))

(defun fn-rtc-c-pool (h n cfg meta bytes)
  (declare (xargs :verify-guards nil))
  (if (zp n)
      nil
    (cons (fn-rtc-c-buffer h cfg meta bytes)
          (fn-rtc-c-pool (+ 1 (nfix h)) (- n 1) cfg meta bytes))))

(defun fn-rtc-c-abs (c)
  (declare (xargs :verify-guards nil))
  (let ((cfg (nth *fn-rtc-c-cfg* c)))
    (fn-rtc-make cfg
          (nth *fn-rtc-c-slotsi* c)
          (fn-rtc-c-pool 0 (fn-rtc-nbufs cfg) cfg
                         (nth *fn-rtc-c-metai* c) (nth *fn-rtc-c-bytesi* c))
          (nth *fn-rtc-c-uses* c)
          (nth *fn-rtc-c-msi* c)
          (nth *fn-rtc-c-nop* c))))

; Each meta cell's generation and fill are naturals, the fill within its
; buffer's capacity (meta cell h is buffer h).
(defun fn-rtc-c-metas-okp (h meta cfg)
  (declare (xargs :guard (natp h) :measure (len meta)))
  (if (consp meta)
      (and (natp (fn-rtc-get 0 (car meta)))
           (natp (fn-rtc-get 2 (car meta)))
           (<= (fn-rtc-get 2 (car meta)) (fn-rtc-buf-cap h cfg))
           (fn-rtc-c-metas-okp (+ 1 (nfix h)) (cdr meta) cfg))
    t))

; The concrete invariant: the arrays have the configuration's lengths.
(defun fn-rtc-c-wfp (c)
  (declare (xargs :verify-guards nil))
  (let ((cfg (nth *fn-rtc-c-cfg* c)))
    (and (fn-rtc-configp cfg)
         (equal (len (nth *fn-rtc-c-slotsi* c)) (fn-rtc-nslots cfg))
         (equal (len (nth *fn-rtc-c-msi* c)) (fn-rtc-nslots cfg))
         (equal (len (nth *fn-rtc-c-metai* c)) (fn-rtc-nbufs cfg))
         (equal (len (nth *fn-rtc-c-bytesi* c)) (fn-rtc-octets-total cfg))
         (fn-rtc-c-metas-okp 0 (nth *fn-rtc-c-metai* c) cfg))))

(defun fn-rtc-st$corr (fn-rtc-st$c fn-rtc-st$a)
  (declare (xargs :verify-guards nil))
  (and (fn-rtc-st$cp fn-rtc-st$c)
       (fn-rtc-c-wfp fn-rtc-st$c)
       (equal fn-rtc-st$a (fn-rtc-c-abs fn-rtc-st$c))))

; -----------------------------------------------------------------------------
; The logical side: the shape every reachable list state has (the abstract
; recognizer).  `fn-rtc-invp' implies it.

(defun fn-rtc-pool-shapep (h pool cfg)
  (declare (xargs :guard (natp h) :measure (len pool)))
  (if (consp pool)
      (and (true-listp (car pool)) (equal (len (car pool)) 3)
           (natp (fn-rtc-get 0 (car pool)))
           (fn-cbor-octet-listp (fn-rtc-get 2 (car pool)))
           (<= (len (fn-rtc-get 2 (car pool))) (fn-rtc-buf-cap h cfg))
           (fn-rtc-pool-shapep (+ 1 (nfix h)) (cdr pool) cfg))
    (null pool)))

(defthm fn-rtc-pool-shapep-true-listp
  (implies (fn-rtc-pool-shapep h pool cfg) (true-listp pool)))

(defun fn-rtc-shapep (s)
  (declare (xargs :guard t))
  (let ((cfg (fn-rtc-config s)))
    (and (true-listp s) (equal (len s) 6)
         (fn-rtc-configp cfg)
         (true-listp (fn-rtc-slots s))
         (equal (len (fn-rtc-slots s)) (fn-rtc-nslots cfg))
         (true-listp (fn-rtc-mstates s))
         (equal (len (fn-rtc-mstates s)) (fn-rtc-nslots cfg))
         (fn-rtc-pool-shapep 0 (fn-rtc-pool s) cfg)
         (equal (len (fn-rtc-pool s)) (fn-rtc-nbufs cfg))
         (natp (fn-rtc-get 5 s)))))

; -----------------------------------------------------------------------------
; Octet ranges of the array: a write outside a range leaves it, a write inside
; it is the contract's splice.

(defun fn-rtc-c-write-list (i data bytes)
  (declare (xargs :guard (natp i) :verify-guards nil))
  (if (atom data)
      bytes
    (fn-rtc-c-write-list (+ 1 (nfix i)) (cdr data)
                         (if (< (nfix i) (len bytes)) (update-nth (nfix i) (car data) bytes) bytes))))

(defthm fn-rtc-c-len-of-octets
  (equal (len (fn-rtc-c-octets i n bytes)) (nfix n)))

(defthm fn-rtc-c-true-listp-of-octets
  (true-listp (fn-rtc-c-octets i n bytes))
  :rule-classes (:rewrite :type-prescription))

(defthm fn-rtc-c-len-of-write-list
  (equal (len (fn-rtc-c-write-list i data bytes)) (len bytes)))

(defthm fn-rtc-c-nth-of-write-list
  (implies (and (natp i) (natp p))
           (equal (nth i (fn-rtc-c-write-list p data bytes))
                  (if (and (<= p i) (< i (+ p (len data))) (< i (len bytes)))
                      (nth (- i p) data)
                    (nth i bytes)))))

(defthm fn-rtc-c-octets-of-write-list-outside
  (implies (and (natp i) (natp p)
                (or (<= (+ p (len data)) i) (<= (+ i (nfix n)) p)))
           (equal (fn-rtc-c-octets i n (fn-rtc-c-write-list p data bytes))
                  (fn-rtc-c-octets i n bytes))))

(defthm fn-rtc-c-octets-split
  (implies (and (natp a) (natp b))
           (equal (fn-rtc-c-octets i (+ a b) bytes)
                  (append (fn-rtc-c-octets i a bytes)
                          (fn-rtc-c-octets (+ (nfix i) a) b bytes)))))

(defthm fn-rtc-c-octets-of-write-list-inside
  (implies (and (natp p) (true-listp data) (<= (+ p (len data)) (len bytes)))
           (equal (fn-rtc-c-octets p (len data) (fn-rtc-c-write-list p data bytes))
                  data)))

(defthm fn-rtc-c-take-of-octets
  (implies (and (natp a) (<= a (nfix n)))
           (equal (take a (fn-rtc-c-octets i n bytes))
                  (fn-rtc-c-octets i a bytes))))

(local (defun fn-rtc-c-ind-nthcdr (a i n)
  (if (zp a) (list i n) (fn-rtc-c-ind-nthcdr (- a 1) (+ 1 i) (- n 1)))))

(defthm fn-rtc-c-nthcdr-of-octets
  (implies (and (natp a) (natp i))
           (equal (nthcdr a (fn-rtc-c-octets i n bytes))
                  (fn-rtc-c-octets (+ i a) (- (nfix n) a) bytes)))
  :hints (("Goal" :induct (fn-rtc-c-ind-nthcdr a i n))))

(defthm fn-rtc-c-true-list-fix-id
  (implies (true-listp x) (equal (true-list-fix x) x)))
(defthm fn-rtc-c-nthcdr-nil
  (equal (nthcdr n nil) nil))

(defthm fn-rtc-c-splice-of-octets
  (implies (and (natp base) (natp off) (natp fl) (<= off fl) (true-listp data))
           (equal (fn-rtc-splice (fn-rtc-c-octets base fl bytes) off data)
                  (append (fn-rtc-c-octets base off bytes)
                          data
                          (fn-rtc-c-octets (+ base off (len data)) (- fl (+ off (len data))) bytes))))
  :hints (("Goal" :in-theory (disable fn-rtc-c-octets-split))))

(defthm fn-rtc-c-octets-of-write-three
  (implies (and (natp base) (natp off) (natp fl)
                (<= off fl)
                (true-listp data)
                (<= (+ base off (len data)) (len bytes)))
           (equal (fn-rtc-c-octets base (max fl (+ off (len data)))
                                   (fn-rtc-c-write-list (+ base off) data bytes))
                  (append (fn-rtc-c-octets base off bytes)
                          data
                          (fn-rtc-c-octets (+ base off (len data)) (- fl (+ off (len data))) bytes))))
  :hints (("Goal" :in-theory (disable fn-rtc-c-octets-split)
           :use ((:instance fn-rtc-c-octets-split (i base) (a off)
                            (b (- (max fl (+ off (len data))) off))
                            (bytes (fn-rtc-c-write-list (+ base off) data bytes)))
                 (:instance fn-rtc-c-octets-split (i (+ base off)) (a (len data))
                            (b (- (max fl (+ off (len data))) (+ off (len data))))
                            (bytes (fn-rtc-c-write-list (+ base off) data bytes)))))))

; The fill after a write: kept closed so a splice's new fill stays one term.
(defun fn-rtc-c-max (a b) (declare (xargs :guard (and (rationalp a) (rationalp b)))) (if (< a b) b a))

(defthm fn-rtc-c-octets-of-splice
  (implies (and (natp base) (natp off) (natp fl)
                (<= off fl)
                (true-listp data)
                (<= (+ base off (len data)) (len bytes)))
           (equal (fn-rtc-c-octets base (fn-rtc-c-max fl (+ off (len data)))
                                   (fn-rtc-c-write-list (+ base off) data bytes))
                  (fn-rtc-splice (fn-rtc-c-octets base fl bytes) off data)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-c-max) (fn-rtc-c-octets-split fn-rtc-splice fn-rtc-c-octets-of-write-three
                                      fn-rtc-c-splice-of-octets))
           :use (fn-rtc-c-octets-of-write-three fn-rtc-c-splice-of-octets))))

(defthm fn-rtc-c-max-bounds
  (implies (and (natp a) (natp b))
           (and (natp (fn-rtc-c-max a b))
                (<= a (fn-rtc-c-max a b))
                (<= b (fn-rtc-c-max a b))
                (implies (and (<= a c) (<= b c)) (<= (fn-rtc-c-max a b) c))))
  :rule-classes ((:rewrite) (:linear :corollary (implies (and (natp a) (natp b)) (and (<= a (fn-rtc-c-max a b)) (<= b (fn-rtc-c-max a b)))))))

(in-theory (disable fn-rtc-c-octets-split fn-rtc-c-max))

; -----------------------------------------------------------------------------
; The abstract pool: one buffer per meta cell; a meta write or an array write
; inside buffer h's region changes buffer h only.

(defthm fn-rtc-c-len-of-pool
  (equal (len (fn-rtc-c-pool h n cfg meta bytes)) (nfix n)))

(defthm fn-rtc-c-true-listp-of-pool
  (true-listp (fn-rtc-c-pool h n cfg meta bytes))
  :rule-classes (:rewrite :type-prescription))

(local (defun fn-rtc-c-ind-get (j k n)
  (if (or (zp j) (zp n)) (list j k n) (fn-rtc-c-ind-get (- j 1) (+ 1 k) (- n 1)))))

(defthm fn-rtc-c-get-of-pool
  (implies (and (natp j) (natp k))
           (equal (fn-rtc-get j (fn-rtc-c-pool k n cfg meta bytes))
                  (if (< j (nfix n)) (fn-rtc-c-buffer (+ k j) cfg meta bytes) nil)))
  :hints (("Goal" :in-theory (disable fn-rtc-c-buffer) :induct (fn-rtc-c-ind-get j k n)
           :expand ((fn-rtc-c-pool k n cfg meta bytes)))))

(defthm fn-rtc-c-pool-of-update-meta-below
  (implies (and (natp h) (natp k) (< h k))
           (equal (fn-rtc-c-pool k n cfg (update-nth h v meta) bytes)
                  (fn-rtc-c-pool k n cfg meta bytes))))

(defthm fn-rtc-c-pool-of-update-meta-above
  (implies (and (natp h) (natp k) (<= (+ k (nfix n)) h))
           (equal (fn-rtc-c-pool k n cfg (update-nth h v meta) bytes)
                  (fn-rtc-c-pool k n cfg meta bytes))))

(defthm fn-rtc-c-pool-of-update-meta
  (implies (and (natp h) (natp k) (<= k h) (< h (+ k (nfix n))))
           (equal (fn-rtc-c-pool k n cfg (update-nth h v meta) bytes)
                  (fn-rtc-set (- h k) (fn-rtc-c-buffer h cfg (update-nth h v meta) bytes)
                              (fn-rtc-c-pool k n cfg meta bytes))))
  :hints (("Goal" :in-theory (disable fn-rtc-c-buffer update-nth)
           :induct (fn-rtc-c-pool k n cfg meta bytes))
          ("Subgoal *1/2" :expand ((fn-rtc-c-buffer k cfg (update-nth h v meta) bytes)
                                   (fn-rtc-c-buffer k cfg meta bytes)))))

(local (defun fn-rtc-c-ind-metas (j k meta)
  (if (or (zp j) (atom meta)) (list j k meta) (fn-rtc-c-ind-metas (- j 1) (+ 1 k) (cdr meta)))))

(defthm fn-rtc-c-fill-of-metas-okp-at
  (implies (and (fn-rtc-c-metas-okp k meta cfg) (natp k) (natp j))
           (<= (nfix (fn-rtc-get 2 (nth j meta))) (fn-rtc-buf-cap (+ k j) cfg)))
  :rule-classes nil
  :hints (("Goal" :induct (fn-rtc-c-ind-metas j k meta)
           :in-theory (enable nth))))

(defthm fn-rtc-c-fill-of-metas-okp
  (implies (and (fn-rtc-c-metas-okp 0 meta cfg) (natp j))
           (<= (nfix (fn-rtc-get 2 (nth j meta))) (fn-rtc-buf-cap j cfg)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :use ((:instance fn-rtc-c-fill-of-metas-okp-at (k 0))))))

(defthm fn-rtc-c-buffer-of-write-disjoint
  (implies (and (fn-rtc-c-metas-okp 0 meta cfg)
                (natp j) (natp p)
                (or (<= (+ p (len data)) (fn-rtc-buf-base j cfg))
                    (<= (+ (fn-rtc-buf-base j cfg) (fn-rtc-buf-cap j cfg)) p)))
           (equal (fn-rtc-c-buffer j cfg meta (fn-rtc-c-write-list p data bytes))
                  (fn-rtc-c-buffer j cfg meta bytes)))
  :hints (("Goal" :in-theory (disable fn-rtc-c-fill-of-metas-okp)
           :use ((:instance fn-rtc-c-fill-of-metas-okp)))))

(defthm fn-rtc-c-pool-of-write-below
  (implies (and (fn-rtc-c-metas-okp 0 meta cfg)
                (natp k) (natp p)
                (<= (+ p (len data)) (fn-rtc-buf-base k cfg)))
           (equal (fn-rtc-c-pool k n cfg meta (fn-rtc-c-write-list p data bytes))
                  (fn-rtc-c-pool k n cfg meta bytes)))
  :hints (("Goal" :in-theory (disable fn-rtc-c-buffer fn-rtc-buf-base-monotone)
           :induct (fn-rtc-c-pool k n cfg meta bytes))))

(defthm fn-rtc-c-pool-of-write
  (implies (and (fn-rtc-c-metas-okp 0 meta cfg)
                (natp h) (natp k) (natp p) (<= k h) (< h (+ k (nfix n)))
                (<= (fn-rtc-buf-base h cfg) p)
                (<= (+ p (len data)) (+ (fn-rtc-buf-base h cfg) (fn-rtc-buf-cap h cfg))))
           (equal (fn-rtc-c-pool k n cfg meta (fn-rtc-c-write-list p data bytes))
                  (fn-rtc-set (- h k) (fn-rtc-c-buffer h cfg meta (fn-rtc-c-write-list p data bytes))
                              (fn-rtc-c-pool k n cfg meta bytes))))
  :hints (("Goal" :in-theory (disable fn-rtc-c-buffer fn-rtc-buf-base-monotone fn-rtc-c-buffer-of-write-disjoint
                                      fn-rtc-c-pool-of-write-below)
           :induct (fn-rtc-c-pool k n cfg meta bytes))
          ("Subgoal *1/2"
           :use ((:instance fn-rtc-buf-base-monotone (j k) (h h))
                 (:instance fn-rtc-buf-base-of-succ (h h))
                 (:instance fn-rtc-c-buffer-of-write-disjoint (j k))
                 (:instance fn-rtc-c-pool-of-write-below (k (+ 1 k)) (n (- n 1)))))))

(defthm fn-rtc-c-make-shape
  (and (true-listp (fn-rtc-make c sl p u m n))
       (equal (len (fn-rtc-make c sl p u m n)) 6)
       (equal (fn-rtc-get 5 (fn-rtc-make c sl p u m n)) n))
  :hints (("Goal" :in-theory (enable fn-rtc-make))))

(defthm fn-rtc-c-get-of-cons
  (equal (fn-rtc-get i (cons a b))
         (if (zp (nfix i)) a (fn-rtc-get (- (nfix i) 1) b))))

; -----------------------------------------------------------------------------
; The abstraction of a well-formed concrete object has the shape.

(local (in-theory (disable nth update-nth)))

(defthm fn-rtc-c-octetp-of-nth-bytes
  (implies (and (fn-rtc-c-bytesp b) (natp i) (< i (len b)))
           (fn-cbor-octetp (nth i b)))
  :hints (("Goal" :in-theory (enable nth))))

(defthm fn-rtc-c-octet-listp-of-octets
  (implies (and (fn-rtc-c-bytesp b) (natp i) (<= (+ i (nfix n)) (len b)))
           (fn-cbor-octet-listp (fn-rtc-c-octets i n b))))

(defthm fn-rtc-c-gen-of-metas-okp-at
  (implies (and (fn-rtc-c-metas-okp k meta cfg) (natp k) (natp j) (< j (len meta)))
           (natp (fn-rtc-get 0 (nth j meta))))
  :hints (("Goal" :induct (fn-rtc-c-ind-metas j k meta) :in-theory (e/d (nth) (fn-rtc-buf-cap))
           :expand ((fn-rtc-c-metas-okp k meta cfg)))))

(defthm fn-rtc-c-gen-of-metas-okp
  (implies (and (fn-rtc-c-metas-okp 0 meta cfg) (natp j) (< j (len meta)))
           (natp (fn-rtc-get 0 (nth j meta))))
  :hints (("Goal" :use ((:instance fn-rtc-c-gen-of-metas-okp-at (k 0))))))

(defthm fn-rtc-c-pool-shapep-of-pool
  (implies (and (fn-rtc-c-metas-okp 0 meta cfg) (fn-rtc-c-bytesp bytes)
                (natp k)
                (<= (+ k (nfix n)) (len meta))
                (<= (fn-rtc-buf-base (+ k (nfix n)) cfg) (len bytes)))
           (fn-rtc-pool-shapep k (fn-rtc-c-pool k n cfg meta bytes) cfg))
  :hints (("Goal" :induct (fn-rtc-c-pool k n cfg meta bytes)
           :in-theory (disable fn-rtc-get fn-rtc-c-gen-of-metas-okp-at fn-rtc-c-fill-of-metas-okp
                               fn-rtc-c-octet-listp-of-octets))
          ("Subgoal *1/2"
           :use ((:instance fn-rtc-c-gen-of-metas-okp-at (j k) (k 0))
                 (:instance fn-rtc-c-fill-of-metas-okp (j k))
                 (:instance fn-rtc-buf-base-monotone (j k) (h (+ k (nfix n))))
                 (:instance fn-rtc-c-octet-listp-of-octets (b bytes) (i (fn-rtc-buf-base k cfg))
                            (n (nfix (fn-rtc-get 2 (nth k meta)))))))))

(defthm fn-rtc-c-slots-is-list
  (implies (fn-rtc-c-slotsp x) (true-listp x))
  :rule-classes :forward-chaining)

(defthm fn-rtc-c-ms-is-list
  (implies (fn-rtc-c-msp x) (true-listp x))
  :rule-classes :forward-chaining)

(defthm fn-rtc-c-meta-is-list
  (implies (fn-rtc-c-metap x) (true-listp x))
  :rule-classes :forward-chaining)

(defthm fn-rtc-c-bytes-is-list
  (implies (fn-rtc-c-bytesp x) (true-listp x))
  :rule-classes :forward-chaining)

(defthm fn-rtc-c-shapep-of-abs
  (implies (and (fn-rtc-st$cp c) (fn-rtc-c-wfp c))
           (fn-rtc-shapep (fn-rtc-c-abs c)))
  :hints (("Goal" :in-theory (disable fn-rtc-c-pool-shapep-of-pool fn-rtc-buf-base-of-nbufs)
           :use ((:instance fn-rtc-c-pool-shapep-of-pool (k 0) (n (fn-rtc-nbufs (nth *fn-rtc-c-cfg* c)))
                            (cfg (nth *fn-rtc-c-cfg* c))
                            (meta (nth *fn-rtc-c-metai* c)) (bytes (nth *fn-rtc-c-bytesi* c)))
                 (:instance fn-rtc-buf-base-of-nbufs (cfg (nth *fn-rtc-c-cfg* c)))))))

; -----------------------------------------------------------------------------
; The state an instance machine is stepped with (`fn-rtc-deliver'): the
; configuration and instance (ID INC)'s view of the pool, nothing else.  The
; machine-facing exports are the view's readers; over the stobj they read
; the arrays in place, classifying each buffer as the view does.

(defun fn-rtc-view-state (id inc s)
  (declare (xargs :guard t))
  (fn-rtc-make (fn-rtc-config s) nil (fn-rtc-view id inc s) nil nil 0))

(defun fn-rtc-vb (h id inc s)
  (declare (xargs :guard t))
  (fn-rtc-get h (fn-rtc-view id inc s)))

; -----------------------------------------------------------------------------
; The exports' logical side: the contract's own state operations.

(defun fn-rtc-in-leased-p (h s)
  (declare (xargs :guard t))
  (let ((o (fn-rtc-b-owner (fn-rtc-buffer h s))))
    (and (eq (fn-rtc-get 0 o) :leased) (eq (fn-rtc-get 3 o) :in))))

; A splice the pool can hold: within buffer H's bytes at its start, within
; capacity at its end, octets.
(defun fn-rtc-in-use-on-p (h uses)
  (declare (xargs :guard t))
  (if (consp uses)
      (or (and (member-eq (fn-rtc-get 0 (car uses)) *fn-rtc-in-kinds*)
               (fn-rtc-handlep (fn-rtc-u-hd (car uses)))
               (equal (fn-rtc-h-buf (fn-rtc-u-hd (car uses))) h))
          (fn-rtc-in-use-on-p h (cdr uses)))
    nil))

(defun fn-rtc-splice-target-p (h owner uses)
  (declare (xargs :guard t))
  (or (eq (fn-rtc-get 0 owner) :workspace) (fn-rtc-in-use-on-p h uses)))

(defun fn-rtc-splice-okp (h off data s)
  (declare (xargs :guard t))
  (let ((b (fn-rtc-buffer h s)) (cfg (fn-rtc-config s)))
    (and (natp h) (< h (fn-rtc-nbufs cfg))
         (fn-rtc-splice-target-p h (fn-rtc-b-owner b) (fn-rtc-uses s))
         (natp off) (<= off (len (fn-rtc-b-bytes b)))
         (fn-cbor-octet-listp data)
         (<= (+ off (len data)) (fn-rtc-buf-cap h cfg)))))

; Configurations the executable allocates: arrays of at most 2^40 octets.
(defun fn-rtc-st-cfg-okp (cfg)
  (declare (xargs :guard t))
  (and (fn-rtc-configp cfg)
       (< (fn-rtc-nslots cfg) (expt 2 32))
       (< (fn-rtc-nbufs cfg) (expt 2 32))
       (< (fn-rtc-capf cfg) (expt 2 32))
       (< (fn-rtc-capl cfg) (expt 2 32))
       (<= (fn-rtc-octets-total cfg) (expt 2 40))))

; The state `fn-rtc-init' starts from, before the listener's :accept is armed.
(defun fn-rtc-st-fresh (cfg)
  (declare (xargs :guard t))
  (fn-rtc-make cfg
               (cons *fn-rtc-listener* (fn-rtc-free-slots (nfix (- (fn-rtc-nslots cfg) 1))))
               (fn-rtc-free-pool (fn-rtc-nbufs cfg))
               nil
               (make-list (fn-rtc-nslots cfg) :initial-element nil)
               0))

(defun fn-rtc-st$ap (s) (declare (xargs :guard t)) (fn-rtc-shapep s))
(defun create-fn-rtc-st$a ()
  (declare (xargs :guard t))
  (fn-rtc-make '(2 0 0 0 0 0 0) '(nil nil) nil nil '(nil nil) 0))

(defun fn-rtc-st$a-config (s) (declare (xargs :guard t)) (fn-rtc-config s))
(defun fn-rtc-st$a-slot (id s) (declare (xargs :guard t)) (fn-rtc-slot id s))
(defun fn-rtc-st$a-mstate (id s) (declare (xargs :guard t)) (fn-rtc-mstate id s))
(defun fn-rtc-st$a-uses (s) (declare (xargs :guard t)) (fn-rtc-uses s))
(defun fn-rtc-st$a-next-op (s) (declare (xargs :guard t)) (fn-rtc-next-op s))
(defun fn-rtc-st$a-owner (h s) (declare (xargs :guard t)) (fn-rtc-b-owner (fn-rtc-buffer h s)))
(defun fn-rtc-st$a-gen (h s) (declare (xargs :guard t)) (fn-rtc-gen h s))
(defun fn-rtc-st$a-fill (h s) (declare (xargs :guard t)) (len (fn-rtc-bytes h s)))
(defun fn-rtc-st$a-byte (h i s)
  (declare (xargs :guard t))
  (let ((bytes (fn-rtc-bytes h s)))
    (if (true-listp bytes) (nth (nfix i) bytes) nil)))
(defun fn-rtc-st$a-free-slot (s) (declare (xargs :guard t)) (fn-rtc-free-slot 0 (fn-rtc-slots s)))
(defun fn-rtc-st$a-v-owner (h id inc s) (declare (xargs :guard t)) (fn-rtc-b-owner (fn-rtc-vb h id inc s)))
(defun fn-rtc-st$a-v-gen (h id inc s) (declare (xargs :guard t)) (fn-rtc-b-gen (fn-rtc-vb h id inc s)))
(defun fn-rtc-st$a-v-fill (h id inc s) (declare (xargs :guard t)) (len (fn-rtc-b-bytes (fn-rtc-vb h id inc s))))
(defun fn-rtc-st$a-v-byte (h i id inc s)
  (declare (xargs :guard t))
  (let ((bytes (fn-rtc-b-bytes (fn-rtc-vb h id inc s))))
    (if (true-listp bytes) (nth (nfix i) bytes) nil)))
(defun fn-rtc-st$a-v-pool (id inc s) (declare (xargs :guard t)) (fn-rtc-view id inc s))

(defun fn-rtc-st$a-set-slot (id slot s) (declare (xargs :guard t)) (fn-rtc-with-slot id slot s))
(defun fn-rtc-st$a-set-mstate (id m s) (declare (xargs :guard t)) (fn-rtc-with-mstate id m s))
(defun fn-rtc-st$a-set-uses (uses s) (declare (xargs :guard t)) (fn-rtc-with-uses uses s))
(defun fn-rtc-st$a-issue (use s) (declare (xargs :guard t)) (fn-rtc-issue use s))
(defun fn-rtc-st$a-set-meta (h gen owner s)
  (declare (xargs :guard t))
  (fn-rtc-with-buffer h (list (nfix gen) owner (fn-rtc-bytes h s)) s))
(defun fn-rtc-st$a-reset (h gen owner s)
  (declare (xargs :guard t))
  (fn-rtc-with-buffer h (list (nfix gen) owner nil) s))
(defun fn-rtc-st$a-splice (h off data s)
  (declare (xargs :guard t))
  (if (fn-rtc-splice-okp h off data s)
      (let ((b (fn-rtc-buffer h s)))
        (fn-rtc-with-buffer h (list (fn-rtc-get 0 b) (fn-rtc-get 1 b)
                                    (fn-rtc-splice (fn-rtc-b-bytes b) off data))
                            s))
    s))
(defun fn-rtc-st$a-release-all (id inc s)
  (declare (xargs :guard t))
  (fn-rtc-make (fn-rtc-config s) (fn-rtc-slots s) (fn-rtc-release-all (fn-rtc-pool s) id inc)
               (fn-rtc-uses s) (fn-rtc-mstates s) (fn-rtc-next-op s)))
(defun fn-rtc-st$a-init (cfg s)
  (declare (xargs :guard t))
  (if (fn-rtc-st-cfg-okp cfg) (fn-rtc-st-fresh cfg) s))

; -----------------------------------------------------------------------------
; The exports' executable side.  Each checks its indices against the arrays
; itself (a well-formed object always passes), so its guard is the
; recognizer and the argument types.

(defthm fn-rtc-c-octetp-is-unsigned-byte-p
  (implies (fn-cbor-octetp o) (unsigned-byte-p 8 o)))

(defun fn-rtc-st$c-config (fn-rtc-st$c)
  (declare (xargs :stobjs fn-rtc-st$c))
  (fn-rtc-c-cfg fn-rtc-st$c))

(defun fn-rtc-st$c-slot (id fn-rtc-st$c)
  (declare (xargs :stobjs fn-rtc-st$c))
  (let ((i (nfix id)))
    (if (< i (fn-rtc-c-slots-length fn-rtc-st$c)) (fn-rtc-c-slotsi i fn-rtc-st$c) nil)))

(defun fn-rtc-st$c-mstate (id fn-rtc-st$c)
  (declare (xargs :stobjs fn-rtc-st$c))
  (let ((i (nfix id)))
    (if (< i (fn-rtc-c-ms-length fn-rtc-st$c)) (fn-rtc-c-msi i fn-rtc-st$c) nil)))

(defun fn-rtc-st$c-uses (fn-rtc-st$c)
  (declare (xargs :stobjs fn-rtc-st$c))
  (fn-rtc-c-uses fn-rtc-st$c))

(defun fn-rtc-st$c-next-op (fn-rtc-st$c)
  (declare (xargs :stobjs fn-rtc-st$c))
  (fn-rtc-c-nop fn-rtc-st$c))

(defun fn-rtc-st$c-meta (h fn-rtc-st$c)
  (declare (xargs :stobjs fn-rtc-st$c))
  (let ((i (nfix h)))
    (if (< i (fn-rtc-c-meta-length fn-rtc-st$c)) (fn-rtc-c-metai i fn-rtc-st$c) nil)))

(defun fn-rtc-st$c-owner (h fn-rtc-st$c)
  (declare (xargs :stobjs fn-rtc-st$c))
  (fn-rtc-get 1 (fn-rtc-st$c-meta h fn-rtc-st$c)))

(defun fn-rtc-st$c-gen (h fn-rtc-st$c)
  (declare (xargs :stobjs fn-rtc-st$c))
  (nfix (fn-rtc-get 0 (fn-rtc-st$c-meta h fn-rtc-st$c))))

(defun fn-rtc-st$c-fill (h fn-rtc-st$c)
  (declare (xargs :stobjs fn-rtc-st$c))
  (nfix (fn-rtc-get 2 (fn-rtc-st$c-meta h fn-rtc-st$c))))

(defun fn-rtc-st$c-byte (h i fn-rtc-st$c)
  (declare (xargs :stobjs fn-rtc-st$c))
  (let* ((h (nfix h)) (i (nfix i))
         (k (+ (fn-rtc-buf-base h (fn-rtc-c-cfg fn-rtc-st$c)) i)))
    (if (and (< h (fn-rtc-c-meta-length fn-rtc-st$c))
             (< i (fn-rtc-st$c-fill h fn-rtc-st$c))
             (< k (fn-rtc-c-bytes-length fn-rtc-st$c)))
        (fn-rtc-c-bytesi k fn-rtc-st$c)
      nil)))

(defun fn-rtc-c-free-slot-loop (i fn-rtc-st$c)
  (declare (xargs :stobjs fn-rtc-st$c :guard (natp i)
                  :measure (nfix (- (fn-rtc-c-slots-length fn-rtc-st$c) (nfix i)))))
  (let ((i (nfix i)))
    (if (< i (fn-rtc-c-slots-length fn-rtc-st$c))
        (if (and (not (zp i)) (eq (fn-rtc-get 1 (fn-rtc-c-slotsi i fn-rtc-st$c)) :free))
            i
          (fn-rtc-c-free-slot-loop (+ 1 i) fn-rtc-st$c))
      nil)))

(defun fn-rtc-st$c-free-slot (fn-rtc-st$c)
  (declare (xargs :stobjs fn-rtc-st$c))
  (fn-rtc-c-free-slot-loop 0 fn-rtc-st$c))

(defun fn-rtc-st$c-in-leased (h fn-rtc-st$c)
  (declare (xargs :stobjs fn-rtc-st$c))
  (let ((o (fn-rtc-st$c-owner h fn-rtc-st$c)))
    (and (eq (fn-rtc-get 0 o) :leased) (eq (fn-rtc-get 3 o) :in))))

; How instance (ID INC)'s view shows buffer H: :own (whole), :mine (generation
; and owner), :other (opaque), or :none (no such buffer).
(defun fn-rtc-st$c-v-class (h id inc fn-rtc-st$c)
  (declare (xargs :stobjs fn-rtc-st$c))
  (let ((h (nfix h)))
    (if (< h (fn-rtc-c-meta-length fn-rtc-st$c))
        (let ((o (fn-rtc-st$c-owner h fn-rtc-st$c)))
          (cond ((fn-rtc-view-own-p o id inc) :own)
                ((fn-rtc-view-mine-p o h id inc (fn-rtc-c-cfg fn-rtc-st$c)) :mine)
                (t :other)))
      :none)))

(defun fn-rtc-st$c-v-owner (h id inc fn-rtc-st$c)
  (declare (xargs :stobjs fn-rtc-st$c))
  (case (fn-rtc-st$c-v-class h id inc fn-rtc-st$c)
    ((:own :mine) (fn-rtc-st$c-owner h fn-rtc-st$c))
    (:other '(:other))
    (otherwise nil)))

(defun fn-rtc-st$c-v-gen (h id inc fn-rtc-st$c)
  (declare (xargs :stobjs fn-rtc-st$c))
  (if (member-eq (fn-rtc-st$c-v-class h id inc fn-rtc-st$c) '(:own :mine))
      (fn-rtc-st$c-gen h fn-rtc-st$c)
    0))

(defun fn-rtc-st$c-v-fill (h id inc fn-rtc-st$c)
  (declare (xargs :stobjs fn-rtc-st$c))
  (if (eq (fn-rtc-st$c-v-class h id inc fn-rtc-st$c) :own) (fn-rtc-st$c-fill h fn-rtc-st$c) 0))

(defun fn-rtc-st$c-v-byte (h i id inc fn-rtc-st$c)
  (declare (xargs :stobjs fn-rtc-st$c))
  (if (eq (fn-rtc-st$c-v-class h id inc fn-rtc-st$c) :own) (fn-rtc-st$c-byte h i fn-rtc-st$c) nil))

; Cells [i, i + n) of the array as a list (the reference view only).
(defun fn-rtc-c-read-octets (i n fn-rtc-st$c)
  (declare (xargs :stobjs fn-rtc-st$c :guard (and (natp i) (natp n))))
  (if (zp n)
      nil
    (cons (if (< (nfix i) (fn-rtc-c-bytes-length fn-rtc-st$c)) (fn-rtc-c-bytesi (nfix i) fn-rtc-st$c) nil)
          (fn-rtc-c-read-octets (+ 1 (nfix i)) (- n 1) fn-rtc-st$c))))

(defun fn-rtc-c-v-pool-loop (h n id inc fn-rtc-st$c)
  (declare (xargs :stobjs fn-rtc-st$c :guard (and (natp h) (natp n))))
  (if (zp n)
      nil
    (let ((m (fn-rtc-st$c-meta h fn-rtc-st$c)))
      (cons (case (fn-rtc-st$c-v-class h id inc fn-rtc-st$c)
              (:own (list (fn-rtc-get 0 m) (fn-rtc-get 1 m)
                          (fn-rtc-c-read-octets (fn-rtc-buf-base h (fn-rtc-c-cfg fn-rtc-st$c))
                                                (nfix (fn-rtc-get 2 m)) fn-rtc-st$c)))
              (:mine (list (nfix (fn-rtc-get 0 m)) (fn-rtc-get 1 m) nil))
              (otherwise '(0 (:other) nil)))
            (fn-rtc-c-v-pool-loop (+ 1 (nfix h)) (- n 1) id inc fn-rtc-st$c)))))

(defun fn-rtc-st$c-v-pool (id inc fn-rtc-st$c)
  (declare (xargs :stobjs fn-rtc-st$c))
  (fn-rtc-c-v-pool-loop 0 (fn-rtc-nbufs (fn-rtc-c-cfg fn-rtc-st$c)) id inc fn-rtc-st$c))

(defun fn-rtc-st$c-set-slot (id slot fn-rtc-st$c)
  (declare (xargs :stobjs fn-rtc-st$c))
  (let ((i (nfix id)))
    (if (< i (fn-rtc-c-slots-length fn-rtc-st$c))
        (update-fn-rtc-c-slotsi i slot fn-rtc-st$c)
      fn-rtc-st$c)))

(defun fn-rtc-st$c-set-mstate (id m fn-rtc-st$c)
  (declare (xargs :stobjs fn-rtc-st$c))
  (let ((i (nfix id)))
    (if (< i (fn-rtc-c-ms-length fn-rtc-st$c))
        (update-fn-rtc-c-msi i m fn-rtc-st$c)
      fn-rtc-st$c)))

(defun fn-rtc-st$c-set-uses (uses fn-rtc-st$c)
  (declare (xargs :stobjs fn-rtc-st$c))
  (update-fn-rtc-c-uses uses fn-rtc-st$c))

(defun fn-rtc-st$c-issue (use fn-rtc-st$c)
  (declare (xargs :stobjs fn-rtc-st$c))
  (let ((fn-rtc-st$c (update-fn-rtc-c-uses (cons use (fn-rtc-c-uses fn-rtc-st$c)) fn-rtc-st$c)))
    (update-fn-rtc-c-nop (+ 1 (fn-rtc-c-nop fn-rtc-st$c)) fn-rtc-st$c)))

(defun fn-rtc-st$c-set-meta (h gen owner fn-rtc-st$c)
  (declare (xargs :stobjs fn-rtc-st$c))
  (let ((i (nfix h)))
    (if (< i (fn-rtc-c-meta-length fn-rtc-st$c))
        (update-fn-rtc-c-metai i (list (nfix gen) owner (fn-rtc-st$c-fill i fn-rtc-st$c)) fn-rtc-st$c)
      fn-rtc-st$c)))

(defun fn-rtc-st$c-reset (h gen owner fn-rtc-st$c)
  (declare (xargs :stobjs fn-rtc-st$c))
  (let ((i (nfix h)))
    (if (< i (fn-rtc-c-meta-length fn-rtc-st$c))
        (update-fn-rtc-c-metai i (list (nfix gen) owner 0) fn-rtc-st$c)
      fn-rtc-st$c)))

; Write DATA at cells i, i+1, ...
(defun fn-rtc-c-write (i data fn-rtc-st$c)
  (declare (xargs :stobjs fn-rtc-st$c :guard (and (natp i) (fn-cbor-octet-listp data))))
  (if (atom data)
      fn-rtc-st$c
    (let ((fn-rtc-st$c (if (< (nfix i) (fn-rtc-c-bytes-length fn-rtc-st$c))
                           (update-fn-rtc-c-bytesi (nfix i) (car data) fn-rtc-st$c)
                         fn-rtc-st$c)))
      (fn-rtc-c-write (+ 1 (nfix i)) (cdr data) fn-rtc-st$c))))

(defthm fn-rtc-c-update-nth-same
  (equal (update-nth i v (update-nth i w l)) (update-nth i v l))
  :hints (("Goal" :in-theory (enable update-nth))))

(defthm fn-rtc-c-update-nth-nth-same
  (implies (and (natp i) (< i (len l)))
           (equal (update-nth i (nth i l) l) l))
  :hints (("Goal" :in-theory (enable update-nth nth))))

(defthm fn-rtc-c-write-is-write-list
  (implies (and (true-listp c) (equal (len c) 7))
           (equal (fn-rtc-c-write i data c)
                  (update-nth *fn-rtc-c-bytesi*
                              (fn-rtc-c-write-list i data (nth *fn-rtc-c-bytesi* c))
                              c))))

(defthm fn-rtc-c-bytesp-of-update-nth
  (implies (and (fn-rtc-c-bytesp l) (unsigned-byte-p 8 v) (natp i) (< i (len l)))
           (fn-rtc-c-bytesp (update-nth i v l)))
  :hints (("Goal" :in-theory (enable update-nth))))

(defthm fn-rtc-c-bytesp-of-write-list
  (implies (and (fn-rtc-c-bytesp bytes) (fn-cbor-octet-listp data))
           (fn-rtc-c-bytesp (fn-rtc-c-write-list i data bytes))))

(defthm fn-rtc-c-cp-of-write
  (implies (and (fn-rtc-st$cp c) (fn-cbor-octet-listp data))
           (fn-rtc-st$cp (fn-rtc-c-write i data c)))
  :hints (("Goal" :in-theory (disable fn-rtc-c-write))))

(defun fn-rtc-st$c-splice (h off data fn-rtc-st$c)
  (declare (xargs :stobjs fn-rtc-st$c))
  (if (and (natp h) (< h (fn-rtc-c-meta-length fn-rtc-st$c))
           (natp off) (fn-cbor-octet-listp data))
      (let* ((m (fn-rtc-c-metai h fn-rtc-st$c))
             (fl (nfix (fn-rtc-get 2 m)))
             (cfg (fn-rtc-c-cfg fn-rtc-st$c))
             (end (+ off (len data))))
        (if (and (<= off fl) (<= end (fn-rtc-buf-cap h cfg))
                 (fn-rtc-splice-target-p h (fn-rtc-get 1 m) (fn-rtc-c-uses fn-rtc-st$c)))
            (let ((fn-rtc-st$c (fn-rtc-c-write (+ (fn-rtc-buf-base h cfg) off) data fn-rtc-st$c)))
              (update-fn-rtc-c-metai h (list (fn-rtc-get 0 m) (fn-rtc-get 1 m) (fn-rtc-c-max fl end))
                                     fn-rtc-st$c))
          fn-rtc-st$c))
    fn-rtc-st$c))

(defun fn-rtc-c-release-loop (h id inc fn-rtc-st$c)
  (declare (xargs :stobjs fn-rtc-st$c :guard (natp h)
                  :measure (nfix (- (fn-rtc-c-meta-length fn-rtc-st$c) (nfix h)))))
  (let ((h (nfix h)))
    (if (< h (fn-rtc-c-meta-length fn-rtc-st$c))
        (let* ((m (fn-rtc-c-metai h fn-rtc-st$c))
               (fn-rtc-st$c (if (equal (fn-rtc-get 1 m) (list :workspace id inc))
                                (update-fn-rtc-c-metai h (list (fn-rtc-get 0 m) '(:free) (fn-rtc-get 2 m))
                                                       fn-rtc-st$c)
                              fn-rtc-st$c)))
          (fn-rtc-c-release-loop (+ 1 h) id inc fn-rtc-st$c))
      fn-rtc-st$c)))

(defun fn-rtc-st$c-release-all (id inc fn-rtc-st$c)
  (declare (xargs :stobjs fn-rtc-st$c))
  (fn-rtc-c-release-loop 0 id inc fn-rtc-st$c))

(defun fn-rtc-c-fill-slots (i v fn-rtc-st$c)
  (declare (xargs :stobjs fn-rtc-st$c :guard (natp i)
                  :measure (nfix (- (fn-rtc-c-slots-length fn-rtc-st$c) (nfix i)))))
  (let ((i (nfix i)))
    (if (< i (fn-rtc-c-slots-length fn-rtc-st$c))
        (let ((fn-rtc-st$c (update-fn-rtc-c-slotsi i v fn-rtc-st$c)))
          (fn-rtc-c-fill-slots (+ 1 i) v fn-rtc-st$c))
      fn-rtc-st$c)))

(defun fn-rtc-c-fill-ms (i v fn-rtc-st$c)
  (declare (xargs :stobjs fn-rtc-st$c :guard (natp i)
                  :measure (nfix (- (fn-rtc-c-ms-length fn-rtc-st$c) (nfix i)))))
  (let ((i (nfix i)))
    (if (< i (fn-rtc-c-ms-length fn-rtc-st$c))
        (let ((fn-rtc-st$c (update-fn-rtc-c-msi i v fn-rtc-st$c)))
          (fn-rtc-c-fill-ms (+ 1 i) v fn-rtc-st$c))
      fn-rtc-st$c)))

(defun fn-rtc-c-fill-meta (i v fn-rtc-st$c)
  (declare (xargs :stobjs fn-rtc-st$c :guard (natp i)
                  :measure (nfix (- (fn-rtc-c-meta-length fn-rtc-st$c) (nfix i)))))
  (let ((i (nfix i)))
    (if (< i (fn-rtc-c-meta-length fn-rtc-st$c))
        (let ((fn-rtc-st$c (update-fn-rtc-c-metai i v fn-rtc-st$c)))
          (fn-rtc-c-fill-meta (+ 1 i) v fn-rtc-st$c))
      fn-rtc-st$c)))

; A fresh state: every slot free but the listener, every machine state nil,
; every buffer free and empty, no use, operation counter 0.
(defun fn-rtc-st$c-init (cfg fn-rtc-st$c)
  (declare (xargs :stobjs fn-rtc-st$c :verify-guards nil))
  (if (fn-rtc-st-cfg-okp cfg)
      (let* ((ns (fn-rtc-nslots cfg)) (nb (fn-rtc-nbufs cfg))
             (fn-rtc-st$c (update-fn-rtc-c-cfg cfg fn-rtc-st$c))
             (fn-rtc-st$c (resize-fn-rtc-c-slots ns fn-rtc-st$c))
             (fn-rtc-st$c (fn-rtc-c-fill-slots 1 '(0 :free nil) fn-rtc-st$c))
             (fn-rtc-st$c (update-fn-rtc-c-slotsi 0 *fn-rtc-listener* fn-rtc-st$c))
             (fn-rtc-st$c (resize-fn-rtc-c-ms ns fn-rtc-st$c))
             (fn-rtc-st$c (fn-rtc-c-fill-ms 0 nil fn-rtc-st$c))
             (fn-rtc-st$c (resize-fn-rtc-c-meta nb fn-rtc-st$c))
             (fn-rtc-st$c (fn-rtc-c-fill-meta 0 '(0 (:free) 0) fn-rtc-st$c))
             (fn-rtc-st$c (resize-fn-rtc-c-bytes (fn-rtc-octets-total cfg) fn-rtc-st$c))
             (fn-rtc-st$c (update-fn-rtc-c-uses nil fn-rtc-st$c)))
        (update-fn-rtc-c-nop 0 fn-rtc-st$c))
    fn-rtc-st$c))
