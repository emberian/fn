; fn prototype (lane proto-adt, 2026-09-27): the constructor-level library of
; a general persistent ADT backend.  NOT on a served path; no host calls it.
;
; A type is stated at the ADT level only: a SCHEMA is a list of field kinds
;   (:u8) (:u32) (:u64)   naturals below 2^8, 2^32, 2^64
;   (:nat B)              naturals at most B
;   (:bool)               t / nil
;   (:enum k1 ... kn)     one of the listed objects (a small sum tag)
;   (:octets)             a variable-length octet list
; and the logical value of a sequence-of-products type is a true list of
; records, each record the true list of its field values in schema order.
;
; The executable representation is the backend's business.  This library
; fixes one layout, over the LOGICAL image of a defstobj (a list of fields):
;   column ci, one per scalar field: a typed array of the encoded values;
;   two columns (offset, length) per :octets field, into
;   the pool P = (adt-ncols schema): one octet array shared by every field;
;   P+1 the record count, P+2 the pool fill.
; Every definition and lemma below is universally quantified over SCHEMA:
; `defadt' (books/proto/adt.lisp) instantiates them at a constant schema
; and proves nothing by hand.  The constructor lemmas are
;   scalar column:  adt-scol-corr-*   (typed column <-> decoded list)
;   octets column:  adt-ocol-corr-*   ((offset,length) into the pool <-> octets)
;   product:        adt-fields-corr-* (a record = one entry of every column)
;   sequence:       adt-corr-*        (count, append, nth, update-nth-of-field)
; and the three per-stobj recursive shapes a defstobj forces on every type
; (an array field's recognizer, the pool write loop, the pool read loop) are
; constrained functions here (adt-g-*), so each instance is a functional
; instantiation, not an induction.

(in-package "ACL2")
(local (include-book "arithmetic/top" :dir :system))

; -----------------------------------------------------------------------------
; Kinds and schemas.

(defun adt-kindp (k)
  (declare (xargs :guard t))
  (and (consp k)
       (case (car k)
         ((:u8 :u32 :u64 :bool :octets) (null (cdr k)))
         (:nat (and (consp (cdr k)) (natp (cadr k)) (null (cddr k))))
         (:enum (and (consp (cdr k)) (true-listp (cdr k))))
         (otherwise nil))))

(defun adt-schemap (s)
  (declare (xargs :guard t))
  (if (atom s) (null s) (and (adt-kindp (car s)) (adt-schemap (cdr s)))))

(defun adt-octets-kind-p (k)
  (declare (xargs :guard t))
  (and (consp k) (eq (car k) :octets)))

(defun adt-kind-width (k)
  (declare (xargs :guard t))
  (if (adt-octets-kind-p k) 2 1))

(defun adt-ncols (s)
  (declare (xargs :guard t))
  (if (atom s) 0 (+ (adt-kind-width (car s)) (adt-ncols (cdr s)))))

(defthm adt-ncols-natp
  (natp (adt-ncols s))
  :rule-classes :type-prescription)

; The column element type of a scalar kind (and of an offset/length column).
(defun adt-ctype (k)
  (declare (xargs :guard (adt-kindp k)))
  (case (car k)
    (:u8 '(:ub 8))
    (:u32 '(:ub 32))
    (:u64 '(:ub 64))
    (:bool '(:ub 1))
    (:nat (list :range (cadr k)))
    (:enum (list :range (1- (len (cdr k)))))
    (otherwise '(:nat))))

(defun adt-elt-p (ct x)
  (declare (xargs :guard t))
  (if (and (consp ct) (eq (car ct) :ub))
      (and (consp (cdr ct)) (unsigned-byte-p (nfix (cadr ct)) x))
    (if (and (consp ct) (eq (car ct) :range))
        (and (integerp x) (<= 0 x) (consp (cdr ct)) (<= x (rfix (cadr ct))))
      (and (integerp x) (<= 0 x)))))

(defun adt-all-elt-p (ct x)
  (declare (xargs :guard t))
  (if (atom x)
      (equal x nil)
    (and (adt-elt-p ct (car x)) (adt-all-elt-p ct (cdr x)))))

; -----------------------------------------------------------------------------
; Values (the logical side).

(defun adt-octetsp (x)
  (declare (xargs :guard t))
  (if (atom x) (null x) (and (unsigned-byte-p 8 (car x)) (adt-octetsp (cdr x)))))

(defun adt-val-okp (k v)
  (declare (xargs :guard (adt-kindp k)))
  (case (car k)
    (:u8 (unsigned-byte-p 8 v))
    (:u32 (unsigned-byte-p 32 v))
    (:u64 (unsigned-byte-p 64 v))
    (:bool (booleanp v))
    (:nat (and (natp v) (<= v (cadr k))))
    (:enum (if (member-equal v (cdr k)) t nil))
    (:octets (adt-octetsp v))
    (otherwise nil)))

(defun adt-rec-p (s r)
  (declare (xargs :guard (adt-schemap s)))
  (if (atom s)
      (null r)
    (and (consp r)
         (adt-val-okp (car s) (car r))
         (adt-rec-p (cdr s) (cdr r)))))

(defun adt-seq-p (s a)
  (declare (xargs :guard (adt-schemap s)))
  (if (atom a)
      (null a)
    (and (adt-rec-p s (car a)) (adt-seq-p s (cdr a)))))

; Scalar encoding into a column and back.
(defun adt-index (v l)
  (declare (xargs :guard t))
  (cond ((atom l) 0)
        ((equal v (car l)) 0)
        (t (1+ (adt-index v (cdr l))))))

(defun adt-enc (k v)
  (declare (xargs :guard t))
  (if (and (consp k) (eq (car k) :bool))
      (if v 1 0)
    (if (and (consp k) (eq (car k) :enum))
        (adt-index v (cdr k))
      v)))

(defun adt-dec (k x)
  (declare (xargs :guard (adt-kindp k)))
  (if (and (consp k) (eq (car k) :bool))
      (equal x 1)
    (if (and (consp k) (eq (car k) :enum))
        (nth (nfix x) (cdr k))
      x)))

(defthm adt-elt-p-of-ctype-zero
  (implies (adt-kindp k) (adt-elt-p (adt-ctype k) 0))
  :hints (("Goal" :expand ((len (cdr k))))))

(local
 (defthm adt-index-below-len
   (implies (member-equal v l) (< (adt-index v l) (len l)))
   :rule-classes :linear))

(local
 (defthm adt-nth-of-index
   (implies (member-equal v l) (equal (nth (adt-index v l) l) v))))

(defthm adt-elt-p-of-enc
  (implies (and (adt-kindp k) (not (adt-octets-kind-p k)) (adt-val-okp k v))
           (adt-elt-p (adt-ctype k) (adt-enc k v))))

(defthm adt-dec-of-enc
  (implies (and (adt-kindp k) (adt-val-okp k v))
           (equal (adt-dec k (adt-enc k v)) v)))

(defthm adt-true-listp-when-all-elt-p
  (implies (adt-all-elt-p ct x) (true-listp x))
  :rule-classes :forward-chaining)

(defthm adt-elt-p-of-nth-when-all-elt-p
  (implies (and (adt-all-elt-p ct x) (natp i) (< i (len x)))
           (adt-elt-p ct (nth i x))))

(defthm adt-true-listp-when-octetsp
  (implies (adt-octetsp x) (true-listp x))
  :rule-classes :forward-chaining)

(in-theory (disable adt-enc adt-dec adt-elt-p adt-ctype))

; -----------------------------------------------------------------------------
; Lists: resize and update.

(defthm adt-len-of-resize-list
  (equal (len (resize-list l n d)) (nfix n))
  :hints (("Goal" :in-theory (enable resize-list))))

(local
 (defun adt-resize-induct (i l n)
   (if (and (posp n) (posp i))
       (adt-resize-induct (1- i) (if (consp l) (cdr l) l) (1- n))
     (list i l n))))

(local
 (defthm adt-resize-list-open
   (implies (posp n)
            (equal (resize-list l n d)
                   (cons (if (atom l) d (car l))
                         (resize-list (if (atom l) l (cdr l)) (1- n) d))))
   :hints (("Goal" :in-theory (enable resize-list)))))

(defthm adt-nth-of-resize-list
  (implies (and (natp i) (< i (len l)) (< i (nfix n)))
           (equal (nth i (resize-list l n d)) (nth i l)))
  :hints (("Goal" :in-theory (disable resize-list)
           :induct (adt-resize-induct i l n))))

(local (in-theory (disable adt-resize-list-open resize-list)))

(defthm adt-all-elt-p-of-resize-list
  (implies (and (adt-all-elt-p ct l) (adt-elt-p ct d))
           (adt-all-elt-p ct (resize-list l n d)))
  :hints (("Goal" :in-theory (enable resize-list))))

(defthm adt-all-elt-p-of-update-nth
  (implies (and (adt-all-elt-p ct l) (adt-elt-p ct x) (natp n) (< n (len l)))
           (adt-all-elt-p ct (update-nth n x l))))

; Room for index N in a column: a column at or below N is resized to 2(N+1)
; (so N appends cost O(N) copying in all), filled with 0, which every
; column type admits.
(defun adt-col-room (col n)
  (declare (xargs :guard (and (natp n) (true-listp col))))
  (if (< n (len col)) col (resize-list col (* 2 (1+ n)) 0)))

(defun adt-col-put (col n x)
  (declare (xargs :guard (and (natp n) (true-listp col))))
  (update-nth n x (adt-col-room col n)))

(defthm adt-len-of-col-room
  (implies (natp n)
           (and (< n (len (adt-col-room col n)))
                (<= (len col) (len (adt-col-room col n)))))
  :rule-classes :linear)

(defthm adt-nth-of-col-room
  (implies (and (natp i) (< i (len col)) (natp n))
           (equal (nth i (adt-col-room col n)) (nth i col))))

(defthm adt-all-elt-p-of-col-room
  (implies (and (adt-all-elt-p ct col) (adt-elt-p ct 0) (natp n))
           (adt-all-elt-p ct (adt-col-room col n))))

(defthm adt-all-elt-p-of-col-put
  (implies (and (adt-all-elt-p ct col) (adt-elt-p ct 0) (adt-elt-p ct x) (natp n))
           (adt-all-elt-p ct (adt-col-put col n x))))

(defthm adt-len-of-col-put
  (implies (natp n)
           (and (< n (len (adt-col-put col n x)))
                (<= (len col) (len (adt-col-put col n x)))))
  :rule-classes :linear)

(defthm adt-nth-of-col-put
  (implies (and (natp i) (natp n))
           (equal (nth i (adt-col-put col n x))
                  (if (equal i n) x (if (< i (len col)) (nth i col) (nth i (adt-col-room col n)))))))

(in-theory (disable adt-col-room adt-col-put))

; -----------------------------------------------------------------------------
; Constructor 1: a typed scalar column.  (adt-scol-corr k col i v): the
; entries col[i .. i+|v|) exist and decode (under kind K) to the list V.

(local (in-theory (disable nth update-nth)))

(defun adt-scol-corr (k col i v)
  (declare (xargs :measure (len v)))
  (if (atom v)
      t
    (and (natp i) (< i (len col))
         (equal (adt-dec k (nth i col)) (car v))
         (adt-scol-corr k col (1+ i) (cdr v)))))

(local
 (defun adt-scol-set-induct (i m v)
   (declare (xargs :measure (len v)))
   (if (atom v) (list i m v) (adt-scol-set-induct (1+ i) (1- m) (cdr v)))))

(defthm adt-scol-corr-bound
  (implies (and (adt-scol-corr k col i v) (consp v))
           (< (+ i (len v)) (1+ (len col))))
  :rule-classes nil)

(defthm adt-scol-corr-get
  (implies (and (adt-scol-corr k col i v) (natp i) (natp m) (< m (len v)))
           (and (< (+ i m) (len col))
                (equal (adt-dec k (nth (+ i m) col)) (nth m v))))
  :rule-classes nil
  :hints (("Goal" :induct (adt-scol-set-induct i m v) :expand ((nth m v)))))

(defthm adt-scol-corr-get-0
  (implies (and (adt-scol-corr k col 0 v) (natp m) (< m (len v)))
           (and (< m (len col))
                (equal (adt-dec k (nth m col)) (nth m v))))
  :hints (("Goal" :use ((:instance adt-scol-corr-get (i 0))))))

(defthm adt-scol-corr-frame
  ; a column that agrees on [i, i+|v|) corresponds to the same list
  (implies (and (adt-scol-corr k col i v) (natp i) (natp n) (<= (+ i (len v)) n))
           (adt-scol-corr k (update-nth n x col) i v)))

(defthm adt-scol-corr-of-col-room
  (implies (and (adt-scol-corr k col i v) (natp n))
           (adt-scol-corr k (adt-col-room col n) i v)))

(defthm adt-scol-corr-append
  (implies (and (adt-scol-corr k col i v) (natp i)
                (equal n (+ i (len v))) (< n (len col))
                (equal (adt-dec k x) y))
           (adt-scol-corr k (update-nth n x col) i (append v (list y)))))

(defthm adt-scol-corr-of-col-put-append
  (implies (and (adt-scol-corr k col 0 v) (equal n (len v))
                (equal (adt-dec k x) y))
           (adt-scol-corr k (adt-col-put col n x) 0 (append v (list y))))
  :hints (("Goal" :in-theory (enable adt-col-put)
           :use ((:instance adt-scol-corr-append (i 0) (col (adt-col-room col n)))))))

(defthm adt-scol-corr-frame-below
  (implies (and (adt-scol-corr k col i v) (natp i) (natp n) (< n i))
           (adt-scol-corr k (update-nth n x col) i v)))

(defthm adt-car-of-update-nth
  (equal (car (update-nth m y v)) (if (zp m) y (car v)))
  :hints (("Goal" :in-theory (enable update-nth))))

(defthm adt-cdr-of-update-nth
  (equal (cdr (update-nth m y v))
         (if (zp m) (cdr v) (update-nth (1- m) y (cdr v))))
  :hints (("Goal" :in-theory (enable update-nth))))

(defthm adt-consp-of-update-nth
  (consp (update-nth m y v))
  :hints (("Goal" :in-theory (enable update-nth))))

(defthm adt-scol-corr-set
  (implies (and (adt-scol-corr k col i v) (natp i) (natp m) (< m (len v))
                (equal n (+ i m)) (equal (adt-dec k x) y))
           (adt-scol-corr k (update-nth n x col) i (update-nth m y v)))
  :hints (("Goal" :induct (adt-scol-set-induct i m v))))

(defthm adt-scol-corr-of-col-put-set
  (implies (and (adt-scol-corr k col 0 v) (natp m) (< m (len v))
                (equal (adt-dec k x) y))
           (adt-scol-corr k (adt-col-put col m x) 0 (update-nth m y v)))
  :hints (("Goal" :in-theory (enable adt-col-put)
           :use ((:instance adt-scol-corr-set (i 0) (n m) (col (adt-col-room col m)))))))

; -----------------------------------------------------------------------------
; Constructor 2: the octet pool and an (offset, length) column pair.

(defun adt-slice (pool off n)
  (declare (xargs :guard (and (natp off) (natp n) (true-listp pool))))
  (if (zp n) nil (cons (nth off pool) (adt-slice pool (1+ off) (1- n)))))

(defthm adt-len-of-slice
  (equal (len (adt-slice pool off n)) (nfix n)))

; P and Q agree below N.
(defun adt-prefix-eq (p q n)
  (declare (xargs :guard (and (natp n) (true-listp p) (true-listp q))))
  (if (zp n) t (and (equal (nth (1- n) p) (nth (1- n) q)) (adt-prefix-eq p q (1- n)))))

(defthm adt-prefix-eq-nth
  (implies (and (adt-prefix-eq p q n) (natp j) (< j (nfix n)))
           (equal (nth j q) (nth j p))))

(defthm adt-prefix-eq-refl (adt-prefix-eq p p n))

(defthm adt-prefix-eq-smaller
  (implies (and (adt-prefix-eq p q m) (<= (nfix n) (nfix m)))
           (adt-prefix-eq p q n))
  :hints (("Goal" :induct (adt-prefix-eq p q n))
          ("Subgoal *1/2" :use ((:instance adt-prefix-eq-nth (n m) (j (1- n)))))))

(defthm adt-prefix-eq-trans
  (implies (and (adt-prefix-eq p q n) (adt-prefix-eq q r m) (<= (nfix n) (nfix m)))
           (adt-prefix-eq p r n))
  :hints (("Goal" :induct (adt-prefix-eq p q n))
          ("Subgoal *1/2" :use ((:instance adt-prefix-eq-nth (p q) (q r) (n m) (j (1- n)))))))

(defthm adt-prefix-eq-update-above
  (implies (and (adt-prefix-eq p q n) (natp j) (<= (nfix n) j))
           (adt-prefix-eq p (update-nth j x q) n)))

(defthm adt-prefix-eq-resize
  (implies (and (adt-prefix-eq p q n) (<= (nfix n) (len q)) (<= (nfix n) (nfix k)))
           (adt-prefix-eq p (resize-list q k d) n)))

(defthm adt-slice-of-prefix-eq
  (implies (and (adt-prefix-eq p q f) (natp off) (<= (+ off (nfix n)) (nfix f)))
           (equal (adt-slice q off n) (adt-slice p off n))))

(in-theory (disable adt-prefix-eq-nth))

; Writing a list of octets into a pool, and the stobj-shaped loop over it.
(defun adt-pool-writes (pool i bytes)
  (declare (xargs :guard (and (natp i) (true-listp pool))))
  (if (atom bytes) pool
    (adt-pool-writes (update-nth i (car bytes) pool) (1+ i) (cdr bytes))))

(defthm adt-len-of-pool-writes
  (implies (and (natp i) (<= (+ i (len bytes)) (len pool)))
           (equal (len (adt-pool-writes pool i bytes)) (len pool))))

(defthm adt-nth-of-pool-writes-below
  (implies (and (natp i) (natp j) (< j i))
           (equal (nth j (adt-pool-writes pool i bytes)) (nth j pool))))

(defthm adt-prefix-eq-of-pool-writes
  (implies (and (adt-prefix-eq p pool n) (natp i) (<= (nfix n) i))
           (adt-prefix-eq p (adt-pool-writes pool i bytes) n)))

(defthm adt-slice-of-pool-writes
  (implies (and (natp i) (true-listp bytes) (<= (+ i (len bytes)) (len pool)))
           (equal (adt-slice (adt-pool-writes pool i bytes) i (len bytes)) bytes))
  :hints (("Goal" :induct (adt-pool-writes pool i bytes))))

(defthm adt-elt-p-ub8
  (implies (unsigned-byte-p 8 x) (adt-elt-p '(:ub 8) x))
  :hints (("Goal" :in-theory (enable adt-elt-p))))

(defthm adt-all-elt-p-of-pool-writes
  (implies (and (adt-all-elt-p '(:ub 8) pool) (adt-octetsp bytes) (natp i)
                (<= (+ i (len bytes)) (len pool)))
           (adt-all-elt-p '(:ub 8) (adt-pool-writes pool i bytes))))

(defun adt-poolw (p i bytes c)
  (declare (xargs :guard (and (natp p) (natp i) (true-listp c) (< p (len c))
                              (true-listp (nth p c)))
                  :verify-guards nil))
  (if (atom bytes) c
    (adt-poolw p (1+ i) (cdr bytes) (update-nth-array p i (car bytes) c))))

(defthm adt-update-nth-update-nth-same
  (equal (update-nth n x (update-nth n y l)) (update-nth n x l))
  :hints (("Goal" :in-theory (enable update-nth))))

(defthm adt-poolw-is-pool-writes
  (equal (adt-poolw p i bytes c)
         (if (consp bytes) (update-nth p (adt-pool-writes (nth p c) i bytes) c) c))
  :hints (("Goal" :in-theory (enable update-nth-array))))

; The pool read loop: backwards onto an accumulator (tail recursive, no
; stack in the octet count).
(defun adt-poolr (p off n acc c)
  (declare (xargs :guard (and (natp p) (natp off) (natp n) (true-listp c)
                              (< p (len c)) (true-listp (nth p c)))
                  :verify-guards nil))
  (if (zp n) acc
    (adt-poolr p off (1- n) (cons (nth (+ off (1- n)) (nth p c)) acc) c)))

(local
 (defthm adt-slice-snoc
   (implies (and (natp off) (posp n))
            (equal (adt-slice pool off n)
                   (append (adt-slice pool off (1- n)) (list (nth (+ off (1- n)) pool)))))
   :hints (("Goal" :induct (adt-slice pool off n)))))

(defthm adt-poolr-is-slice
  (implies (natp off)
           (equal (adt-poolr p off n acc c)
                  (append (adt-slice (nth p c) off n) acc)))
  :hints (("Goal" :induct (adt-poolr p off n acc c))))

(local (in-theory (disable adt-slice-snoc)))

; Room in the pool for NEED octets: doubling, never below NEED.
(defun adt-pool-room (p need c)
  (declare (xargs :guard (and (natp p) (natp need) (true-listp c) (true-listp (nth p c)))
                  :verify-guards nil))
  (if (<= need (len (nth p c)))
      c
    (update-nth p (resize-list (nth p c) (max need (* 2 (len (nth p c)))) 0) c)))

; Append BYTES to the pool at the fill (at P+2); the fill moves past them.
(defun adt-pool-push (p bytes c)
  (declare (xargs :verify-guards nil))
  (let* ((fl (nth (+ 2 p) c))
         (need (+ fl (len bytes)))
         (c (adt-pool-room p need c))
         (c (adt-poolw p fl bytes c)))
    (update-nth (+ 2 p) need c)))

(defthm adt-nth-of-pool-push-other
  (implies (and (natp k) (natp p) (not (equal k p)) (not (equal k (+ 2 p))))
           (equal (nth k (adt-pool-push p bytes c)) (nth k c))))

(defthm adt-fill-of-pool-push
  (implies (natp p)
           (equal (nth (+ 2 p) (adt-pool-push p bytes c))
                  (+ (nth (+ 2 p) c) (len bytes)))))

(defthm adt-pool-of-pool-push
  (implies (and (natp p) (natp (nth (+ 2 p) c)) (<= (nth (+ 2 p) c) (len (nth p c))))
           (let ((pool2 (nth p (adt-pool-push p bytes c)))
                 (fl (nth (+ 2 p) c)))
             (and (adt-prefix-eq (nth p c) pool2 fl)
                  (<= (+ fl (len bytes)) (len pool2))
                  (implies (true-listp bytes)
                           (equal (adt-slice pool2 fl (len bytes)) bytes))
                  (implies (and (adt-all-elt-p '(:ub 8) (nth p c)) (adt-octetsp bytes))
                           (adt-all-elt-p '(:ub 8) pool2)))))
  :hints (("Goal" :in-theory (enable adt-elt-p))))

(in-theory (disable adt-pool-push adt-poolw adt-poolr adt-pool-room))

; The (offset, length) pair column: entries i.. are slices of the pool
; below the fill.
(defun adt-ocol-corr (offs lens pool fl i v)
  (declare (xargs :measure (len v)))
  (if (atom v)
      t
    (and (natp i) (< i (len offs)) (< i (len lens))
         (natp (nth i offs)) (natp (nth i lens))
         (<= (+ (nth i offs) (nth i lens)) (nfix fl))
         (equal (adt-slice pool (nth i offs) (nth i lens)) (car v))
         (adt-ocol-corr offs lens pool fl (1+ i) (cdr v)))))

(defthm adt-ocol-corr-get
  (implies (and (adt-ocol-corr offs lens pool fl i v) (natp i) (natp m) (< m (len v)))
           (and (< (+ i m) (len offs)) (< (+ i m) (len lens))
                (natp (nth (+ i m) offs)) (natp (nth (+ i m) lens))
                (<= (+ (nth (+ i m) offs) (nth (+ i m) lens)) (nfix fl))
                (equal (adt-slice pool (nth (+ i m) offs) (nth (+ i m) lens)) (nth m v))))
  :rule-classes nil
  :hints (("Goal" :induct (adt-scol-set-induct i m v) :expand ((nth m v)))))

(defthm adt-ocol-corr-get-0
  (implies (and (adt-ocol-corr offs lens pool fl 0 v) (natp m) (< m (len v)))
           (and (< m (len offs)) (< m (len lens))
                (natp (nth m offs)) (natp (nth m lens))
                (<= (+ (nth m offs) (nth m lens)) (nfix fl))
                (equal (adt-slice pool (nth m offs) (nth m lens)) (nth m v))))
  :hints (("Goal" :use ((:instance adt-ocol-corr-get (i 0))))))

(defthm adt-ocol-corr-of-pool
  (implies (and (adt-ocol-corr offs lens pool fl i v)
                (adt-prefix-eq pool pool2 (nfix fl))
                (<= (nfix fl) (nfix fl2)))
           (adt-ocol-corr offs lens pool2 fl2 i v)))

(defthm adt-ocol-corr-frame
  (implies (and (adt-ocol-corr offs lens pool fl i v) (natp i) (natp n)
                (or (< n i) (<= (+ i (len v)) n)))
           (and (adt-ocol-corr (update-nth n x offs) lens pool fl i v)
                (adt-ocol-corr offs (update-nth n x lens) pool fl i v))))

(defthm adt-ocol-corr-frame-both
  (implies (and (adt-ocol-corr offs lens pool fl i v) (natp i) (natp n)
                (or (< n i) (<= (+ i (len v)) n)))
           (adt-ocol-corr (update-nth n o offs) (update-nth n l lens) pool fl i v)))

(defthm adt-ocol-corr-of-col-room
  (implies (and (adt-ocol-corr offs lens pool fl i v) (natp n))
           (and (adt-ocol-corr (adt-col-room offs n) lens pool fl i v)
                (adt-ocol-corr offs (adt-col-room lens n) pool fl i v))))

(defthm adt-ocol-corr-append
  (implies (and (adt-ocol-corr offs lens pool fl i v) (natp i)
                (equal n (+ i (len v))) (< n (len offs)) (< n (len lens))
                (natp o) (natp l) (<= (+ o l) (nfix fl))
                (equal (adt-slice pool o l) y))
           (adt-ocol-corr (update-nth n o offs) (update-nth n l lens) pool fl
                          i (append v (list y)))))

(defthm adt-ocol-corr-of-col-put-append
  (implies (and (adt-ocol-corr offs lens pool fl 0 v) (equal n (len v)) (natp fl)
                (natp o) (natp l) (<= (+ o l) (nfix fl))
                (equal (adt-slice pool o l) y))
           (adt-ocol-corr (adt-col-put offs n o) (adt-col-put lens n l) pool fl
                          0 (append v (list y))))
  :hints (("Goal" :in-theory (enable adt-col-put)
           :use ((:instance adt-ocol-corr-append (i 0)
                            (offs (adt-col-room offs n)) (lens (adt-col-room lens n)))))))

(defthm adt-ocol-corr-set
  (implies (and (adt-ocol-corr offs lens pool fl i v) (natp i) (natp m) (< m (len v))
                (equal n (+ i m)) (natp fl)
                (natp o) (natp l) (<= (+ o l) (nfix fl))
                (equal (adt-slice pool o l) y))
           (adt-ocol-corr (update-nth n o offs) (update-nth n l lens) pool fl
                          i (update-nth m y v)))
  :hints (("Goal" :induct (adt-scol-set-induct i m v))
          ("Subgoal *1/2" :expand ((:free (a b) (adt-ocol-corr a b pool fl i (update-nth m y v)))))))

(defthm adt-ocol-corr-of-col-put-set
  (implies (and (adt-ocol-corr offs lens pool fl 0 v) (natp m) (< m (len v)) (natp fl)
                (natp o) (natp l) (<= (+ o l) (nfix fl))
                (equal (adt-slice pool o l) y))
           (adt-ocol-corr (adt-col-put offs m o) (adt-col-put lens m l) pool fl
                          0 (update-nth m y v)))
  :hints (("Goal" :in-theory (enable adt-col-put)
           :use ((:instance adt-ocol-corr-set (i 0) (n m)
                            (offs (adt-col-room offs m)) (lens (adt-col-room lens m)))))))

; -----------------------------------------------------------------------------
; Constructor 3: a product.  A field of kind K at column CI (pool at P)
; corresponds to the list V of that field's values, one per record: its
; column(s) are typed, and the scalar or (offset, length) constructor holds.

(defun adt-field-corr (k ci p c v)
  (if (adt-octets-kind-p k)
      (and (adt-all-elt-p '(:nat) (nth ci c))
           (adt-all-elt-p '(:nat) (nth (+ 1 ci) c))
           (adt-ocol-corr (nth ci c) (nth (+ 1 ci) c) (nth p c) (nth (+ 2 p) c) 0 v))
    (and (adt-all-elt-p (adt-ctype k) (nth ci c))
         (adt-scol-corr k (nth ci c) 0 v))))

; Writing one field of row N: scalar, one column; octets, the pool push and
; the (offset, length) pair.
(defun adt-put-field (k ci p n v c)
  (declare (xargs :verify-guards nil))
  (if (adt-octets-kind-p k)
      (let* ((o (nth (+ 2 p) c))
             (c (adt-pool-push p v c))
             (c (update-nth ci (adt-col-put (nth ci c) n o) c)))
        (update-nth (+ 1 ci) (adt-col-put (nth (+ 1 ci) c) n (len v)) c))
    (update-nth ci (adt-col-put (nth ci c) n (adt-enc k v)) c)))

(defun adt-get-field (k ci p i c)
  (declare (xargs :verify-guards nil))
  (if (adt-octets-kind-p k)
      (adt-poolr p (nth i (nth ci c)) (nth i (nth (+ 1 ci) c)) nil c)
    (adt-dec k (nth i (nth ci c)))))

; What an executable read of field K at row I needs (its guard).
(defun adt-get-field-okp (k ci p i c)
  (declare (xargs :verify-guards nil))
  (if (adt-octets-kind-p k)
      (and (< i (len (nth ci c))) (< i (len (nth (+ 1 ci) c)))
           (<= (+ (nth i (nth ci c)) (nth i (nth (+ 1 ci) c))) (len (nth p c))))
    (< i (len (nth ci c)))))

; The pool invariant: the fill is a natural within the pool.
(defun adt-fill-okp (p c)
  (and (natp (nth (+ 2 p) c)) (<= (nth (+ 2 p) c) (len (nth p c)))))

(defthm adt-len-update-nth-local
  (equal (len (update-nth n x l)) (max (len l) (1+ (nfix n))))
  :hints (("Goal" :in-theory (enable update-nth))))

(defthm adt-nth-of-put-field-other
  (implies (and (natp k) (natp ci) (natp p)
                (or (< k ci) (<= (+ ci (adt-kind-width kd)) k))
                (not (equal k p)) (not (equal k (+ 2 p))))
           (equal (nth k (adt-put-field kd ci p n v c)) (nth k c))))

(defthm adt-nth-of-put-field-scalar
  (implies (and (not (adt-octets-kind-p kd)) (natp k) (natp ci) (not (equal k ci)))
           (equal (nth k (adt-put-field kd ci p n v c)) (nth k c))))

(defthm adt-fill-of-put-field
  (implies (and (adt-fill-okp p c) (natp ci) (natp p) (<= (+ ci (adt-kind-width kd)) p))
           (and (natp (nth (+ 2 p) (adt-put-field kd ci p n v c)))
                (<= (nth (+ 2 p) c) (nth (+ 2 p) (adt-put-field kd ci p n v c)))
                (<= (nth (+ 2 p) (adt-put-field kd ci p n v c))
                    (len (nth p (adt-put-field kd ci p n v c))))
                (adt-prefix-eq (nth p c) (nth p (adt-put-field kd ci p n v c))
                               (nth (+ 2 p) c))))
  :hints (("Goal" :use ((:instance adt-pool-of-pool-push (bytes v))))))

(defthm adt-pool-elts-of-put-field
  (implies (and (adt-fill-okp p c) (adt-all-elt-p '(:ub 8) (nth p c))
                (adt-val-okp kd v)
                (natp ci) (natp p) (<= (+ ci (adt-kind-width kd)) p))
           (adt-all-elt-p '(:ub 8) (nth p (adt-put-field kd ci p n v c))))
  :hints (("Goal" :use ((:instance adt-pool-of-pool-push (bytes v))))))

; A field's correspondence survives a write of another field (a column
; elsewhere, the pool extended above the fill).
(defthm adt-field-corr-of-put-field-other
  (implies (and (adt-field-corr k2 ci2 p c v2)
                (adt-fill-okp p c)
                (natp ci) (natp ci2) (natp p)
                (or (<= (+ ci (adt-kind-width k)) ci2) (<= (+ ci2 (adt-kind-width k2)) ci))
                (<= (+ ci (adt-kind-width k)) p) (<= (+ ci2 (adt-kind-width k2)) p))
           (adt-field-corr k2 ci2 p (adt-put-field k ci p n v c) v2))
  :hints (("Goal" :in-theory (disable adt-put-field adt-fill-okp adt-fill-of-put-field)
           :use ((:instance adt-fill-of-put-field (kd k))
                 (:instance adt-ocol-corr-of-pool
                            (offs (nth ci2 c)) (lens (nth (+ 1 ci2) c))
                            (pool (nth p c)) (fl (nth (+ 2 p) c))
                            (pool2 (nth p (adt-put-field k ci p n v c)))
                            (fl2 (nth (+ 2 p) (adt-put-field k ci p n v c)))
                            (i 0) (v v2))))))

(defthm adt-field-corr-of-update-other
  (implies (and (adt-field-corr k2 ci2 p c v2) (natp j) (natp ci2) (natp p)
                (<= (+ ci2 (adt-kind-width k2)) j)
                (not (equal j p)) (not (equal j (+ 2 p))))
           (adt-field-corr k2 ci2 p (update-nth j x c) v2)))

; ... and the written field corresponds to the extended / updated list.
(defthm adt-field-corr-of-put-field-append
  (implies (and (adt-field-corr k ci p c v) (adt-fill-okp p c) (adt-kindp k)
                (adt-val-okp k x) (equal n (len v))
                (natp ci) (natp p) (<= (+ ci (adt-kind-width k)) p))
           (adt-field-corr k ci p (adt-put-field k ci p n x c) (append v (list x))))
  :hints (("Goal" :in-theory (enable adt-fill-okp adt-elt-p)
           :use ((:instance adt-pool-of-pool-push (bytes x))))))

(defthm adt-field-corr-of-put-field-set
  (implies (and (adt-field-corr k ci p c v) (adt-fill-okp p c) (adt-kindp k)
                (adt-val-okp k x) (natp m) (< m (len v))
                (natp ci) (natp p) (<= (+ ci (adt-kind-width k)) p))
           (adt-field-corr k ci p (adt-put-field k ci p m x c) (update-nth m x v)))
  :hints (("Goal" :in-theory (enable adt-fill-okp adt-elt-p)
           :use ((:instance adt-pool-of-pool-push (bytes x))))))

(defthm adt-get-field-of-corr
  (implies (and (adt-field-corr k ci p c v) (natp m) (< m (len v)))
           (and (equal (adt-get-field k ci p m c) (nth m v))
                (implies (adt-fill-okp p c) (adt-get-field-okp k ci p m c))))
  :hints (("Goal" :in-theory (enable adt-fill-okp)
           :use ((:instance adt-ocol-corr-get-0 (offs (nth ci c)) (lens (nth (+ 1 ci) c))
                            (pool (nth p c)) (fl (nth (+ 2 p) c)))
                 (:instance adt-scol-corr-get-0 (col (nth ci c)))))))

(in-theory (disable adt-put-field adt-get-field adt-get-field-okp adt-field-corr))

(defthm adt-len-of-put-field
  (implies (and (natp ci) (natp p) (<= (+ ci (adt-kind-width kd)) p) (< (+ 2 p) (len c)))
           (equal (len (adt-put-field kd ci p n v c)) (len c)))
  :hints (("Goal" :in-theory (enable adt-put-field adt-pool-push adt-pool-room adt-poolw-is-pool-writes))))

(defthm adt-true-listp-of-update-nth
  (implies (true-listp l) (true-listp (update-nth n x l)))
  :hints (("Goal" :in-theory (enable update-nth))))

(defthm adt-true-listp-of-put-field
  (implies (true-listp c) (true-listp (adt-put-field kd ci p n v c)))
  :hints (("Goal" :in-theory (enable adt-put-field adt-pool-push adt-pool-room))))

; -----------------------------------------------------------------------------
; Constructor 4: a sequence of products.  RECS is a list of records (or of
; their tails, field by field); the product's fields at columns CI.. each
; correspond to their projection.

(defun adt-cars (recs)
  (if (atom recs) nil (cons (car (car recs)) (adt-cars (cdr recs)))))

(defun adt-cdrs (recs)
  (if (atom recs) nil (cons (cdr (car recs)) (adt-cdrs (cdr recs)))))

(defthm adt-len-cars (equal (len (adt-cars recs)) (len recs)))
(defthm adt-len-cdrs (equal (len (adt-cdrs recs)) (len recs)))

(defthm adt-cars-append
  (equal (adt-cars (append a b)) (append (adt-cars a) (adt-cars b))))
(defthm adt-cdrs-append
  (equal (adt-cdrs (append a b)) (append (adt-cdrs a) (adt-cdrs b))))

(defthm adt-nth-cars
  (implies (and (natp i) (< i (len recs)))
           (equal (nth i (adt-cars recs)) (car (nth i recs))))
  :hints (("Goal" :in-theory (enable nth))))
(defthm adt-nth-cdrs
  (implies (and (natp i) (< i (len recs)))
           (equal (nth i (adt-cdrs recs)) (cdr (nth i recs))))
  :hints (("Goal" :in-theory (enable nth))))

(defthm adt-cars-update-nth
  (implies (and (natp i) (< i (len recs)))
           (equal (adt-cars (update-nth i r recs)) (update-nth i (car r) (adt-cars recs))))
  :hints (("Goal" :in-theory (enable update-nth))))
(defthm adt-cdrs-update-nth
  (implies (and (natp i) (< i (len recs)))
           (equal (adt-cdrs (update-nth i r recs)) (update-nth i (cdr r) (adt-cdrs recs))))
  :hints (("Goal" :in-theory (enable update-nth))))

(defthm adt-update-nth-of-nth-same
  (implies (and (natp i) (< i (len l)))
           (equal (update-nth i (nth i l) l) l))
  :hints (("Goal" :in-theory (enable nth update-nth))))

(defthm adt-update-nth-cars-same
  (implies (and (natp i) (< i (len recs)))
           (equal (update-nth i (car (nth i recs)) (adt-cars recs)) (adt-cars recs)))
  :hints (("Goal" :use ((:instance adt-update-nth-of-nth-same (l (adt-cars recs)))))))

(defthm adt-update-nth-cdrs-same
  (implies (and (natp i) (< i (len recs)))
           (equal (update-nth i (cdr (nth i recs)) (adt-cdrs recs)) (adt-cdrs recs)))
  :hints (("Goal" :use ((:instance adt-update-nth-of-nth-same (l (adt-cdrs recs)))))))

(defthm adt-seq-p-cdrs
  (implies (and (adt-seq-p s recs) (consp s))
           (adt-seq-p (cdr s) (adt-cdrs recs))))

(defun adt-fields-corr (s ci p c recs)
  (if (atom s)
      t
    (and (adt-field-corr (car s) ci p c (adt-cars recs))
         (adt-fields-corr (cdr s) (+ (adt-kind-width (car s)) ci) p c (adt-cdrs recs)))))

(defun adt-append-fields (s ci p n rec c)
  (declare (xargs :verify-guards nil))
  (if (atom s)
      c
    (adt-append-fields (cdr s) (+ (adt-kind-width (car s)) ci) p n (cdr rec)
                       (adt-put-field (car s) ci p n (car rec) c))))

(defun adt-set-fields (s j ci p i v c)
  (declare (xargs :verify-guards nil))
  (if (atom s)
      c
    (if (zp j)
        (adt-put-field (car s) ci p i v c)
      (adt-set-fields (cdr s) (1- j) (+ (adt-kind-width (car s)) ci) p i v c))))

(defun adt-get-fields (s j ci p i c)
  (declare (xargs :verify-guards nil))
  (if (atom s)
      nil
    (if (zp j)
        (adt-get-field (car s) ci p i c)
      (adt-get-fields (cdr s) (1- j) (+ (adt-kind-width (car s)) ci) p i c))))

(defun adt-get-fields-okp (s j ci p i c)
  (declare (xargs :verify-guards nil))
  (if (atom s)
      nil
    (if (zp j)
        (adt-get-field-okp (car s) ci p i c)
      (adt-get-fields-okp (cdr s) (1- j) (+ (adt-kind-width (car s)) ci) p i c))))

(defthm adt-fields-corr-of-put-field-other
  (implies (and (adt-fields-corr s ci2 p c recs) (adt-fill-okp p c)
                (natp ci) (natp ci2) (natp p)
                (or (<= (+ ci (adt-kind-width k)) ci2) (<= (+ ci2 (adt-ncols s)) ci))
                (<= (+ ci (adt-kind-width k)) p) (<= (+ ci2 (adt-ncols s)) p))
           (adt-fields-corr s ci2 p (adt-put-field k ci p n v c) recs))
  :hints (("Goal" :in-theory (disable adt-fill-okp))))

(defthm adt-fields-corr-of-update-above
  (implies (and (adt-fields-corr s ci2 p c recs) (natp j) (natp ci2) (natp p)
                (<= (+ ci2 (adt-ncols s)) j) (not (equal j p)) (not (equal j (+ 2 p))))
           (adt-fields-corr s ci2 p (update-nth j x c) recs)))

(defthm adt-fill-okp-of-put-field
  (implies (and (adt-fill-okp p c) (natp ci) (natp p) (<= (+ ci (adt-kind-width kd)) p))
           (adt-fill-okp p (adt-put-field kd ci p n v c)))
  :hints (("Goal" :in-theory (e/d ((:definition adt-fill-okp)) (adt-fill-of-put-field))
           :use adt-fill-of-put-field)))

(defthm adt-fill-okp-of-append-fields
  (implies (and (adt-fill-okp p c) (natp ci) (natp p) (<= (+ ci (adt-ncols s)) p))
           (adt-fill-okp p (adt-append-fields s ci p n rec c)))
  :hints (("Goal" :in-theory (disable adt-fill-okp)
           :induct (adt-append-fields s ci p n rec c))))

(defthm adt-len-of-append-fields
  (implies (and (adt-fill-okp p c) (natp ci) (natp p) (<= (+ ci (adt-ncols s)) p)
                (< (+ 2 p) (len c)))
           (equal (len (adt-append-fields s ci p n rec c)) (len c)))
  :hints (("Goal" :in-theory (disable adt-fill-okp)
           :induct (adt-append-fields s ci p n rec c))))

(defthm adt-true-listp-of-append-fields
  (implies (true-listp c) (true-listp (adt-append-fields s ci p n rec c))))

(defthm adt-pool-elts-of-append-fields
  (implies (and (adt-fill-okp p c) (natp ci) (natp p) (<= (+ ci (adt-ncols s)) p)
                (adt-all-elt-p '(:ub 8) (nth p c)) (adt-rec-p s rec))
           (adt-all-elt-p '(:ub 8) (nth p (adt-append-fields s ci p n rec c))))
  :hints (("Goal" :in-theory (disable adt-fill-okp)
           :induct (adt-append-fields s ci p n rec c))))

(defthm adt-count-of-append-fields
  (implies (and (natp ci) (natp p) (<= (+ ci (adt-ncols s)) p))
           (equal (nth (+ 1 p) (adt-append-fields s ci p n rec c)) (nth (+ 1 p) c)))
  :hints (("Goal" :induct (adt-append-fields s ci p n rec c))))

(defthm adt-field-corr-of-append-fields-above
  (implies (and (adt-field-corr k ci p c v) (adt-fill-okp p c)
                (natp ci) (natp ci2) (natp p)
                (<= (+ ci (adt-kind-width k)) ci2) (<= (+ ci2 (adt-ncols s)) p))
           (adt-field-corr k ci p (adt-append-fields s ci2 p n rec c) v))
  :hints (("Goal" :in-theory (disable adt-fill-okp))))

(local
 (defun adt-af-induct (s ci p n rec c recs)
   (declare (xargs :verify-guards nil))
   (if (atom s)
       (list ci p n rec c recs)
     (adt-af-induct (cdr s) (+ (adt-kind-width (car s)) ci) p n (cdr rec)
                    (adt-put-field (car s) ci p n (car rec) c) (adt-cdrs recs)))))

(defthm adt-fields-corr-of-append-fields
  (implies (and (adt-fields-corr s ci p c recs) (adt-fill-okp p c)
                (adt-schemap s) (adt-rec-p s rec) (equal n (len recs))
                (natp ci) (natp p) (<= (+ ci (adt-ncols s)) p))
           (adt-fields-corr s ci p (adt-append-fields s ci p n rec c)
                            (append recs (list rec))))
  :hints (("Goal" :in-theory (disable adt-fill-okp)
           :induct (adt-af-induct s ci p n rec c recs))))

(local
 (defun adt-sf-induct (s j ci p i v c recs)
   (declare (xargs :verify-guards nil))
   (if (atom s)
       (list j ci p i v c recs)
     (if (zp j)
         (list j ci p i v c recs)
       (adt-sf-induct (cdr s) (1- j) (+ (adt-kind-width (car s)) ci) p i v c
                      (adt-cdrs recs))))))

(defthm adt-set-fields-invariants
  (implies (and (adt-fill-okp p c) (natp ci) (natp p) (<= (+ ci (adt-ncols s)) p))
           (and (adt-fill-okp p (adt-set-fields s j ci p i v c))
                (implies (< (+ 2 p) (len c))
                         (equal (len (adt-set-fields s j ci p i v c)) (len c)))
                (implies (true-listp c) (true-listp (adt-set-fields s j ci p i v c)))
                (equal (nth (+ 1 p) (adt-set-fields s j ci p i v c)) (nth (+ 1 p) c))))
  :hints (("Goal" :in-theory (disable adt-fill-okp)
           :induct (adt-sf-induct s j ci p i v c recs))))

(defthm adt-pool-elts-of-set-fields
  (implies (and (adt-fill-okp p c) (natp ci) (natp p) (<= (+ ci (adt-ncols s)) p)
                (adt-all-elt-p '(:ub 8) (nth p c)) (natp j) (< j (len s))
                (adt-val-okp (nth j s) v))
           (adt-all-elt-p '(:ub 8) (nth p (adt-set-fields s j ci p i v c))))
  :hints (("Goal" :in-theory (e/d (nth) (adt-fill-okp))
           :induct (adt-sf-induct s j ci p i v c recs))))

(defthm adt-field-corr-of-set-fields-above
  (implies (and (adt-field-corr k ci p c v2) (adt-fill-okp p c)
                (natp ci) (natp ci2) (natp p)
                (<= (+ ci (adt-kind-width k)) ci2) (<= (+ ci2 (adt-ncols s)) p))
           (adt-field-corr k ci p (adt-set-fields s j ci2 p i v c) v2))
  :hints (("Goal" :in-theory (disable adt-fill-okp)
           :induct (adt-sf-induct s j ci2 p i v c recs))))

(defthm adt-fields-corr-of-set-fields
  (implies (and (adt-fields-corr s ci p c recs) (adt-fill-okp p c)
                (adt-schemap s) (adt-seq-p s recs)
                (natp j) (< j (len s)) (natp i) (< i (len recs))
                (adt-val-okp (nth j s) v)
                (natp ci) (natp p) (<= (+ ci (adt-ncols s)) p))
           (adt-fields-corr s ci p (adt-set-fields s j ci p i v c)
                            (update-nth i (update-nth j v (nth i recs)) recs)))
  :hints (("Goal" :in-theory (disable adt-fill-okp)
           :induct (adt-sf-induct s j ci p i v c recs)
           :expand ((nth j s)))))

(defthm adt-nth-of-atom
  (implies (atom x) (equal (nth n x) nil))
  :hints (("Goal" :in-theory (enable nth))))

(defthm adt-get-fields-of-corr
  (implies (and (adt-fields-corr s ci p c recs) (natp j) (< j (len s))
                (natp i) (< i (len recs)))
           (and (equal (adt-get-fields s j ci p i c) (nth j (nth i recs)))
                (implies (adt-fill-okp p c) (adt-get-fields-okp s j ci p i c))))
  :hints (("Goal" :in-theory (disable adt-fill-okp)
           :induct (adt-sf-induct s j ci p i v c recs)
           :expand ((nth j (nth i recs))))))

(defun adt-cols-shape (s ci c)
  (if (atom s)
      t
    (and (if (adt-octets-kind-p (car s))
             (and (adt-all-elt-p '(:nat) (nth ci c))
                  (adt-all-elt-p '(:nat) (nth (+ 1 ci) c)))
           (adt-all-elt-p (adt-ctype (car s)) (nth ci c)))
         (adt-cols-shape (cdr s) (+ (adt-kind-width (car s)) ci) c))))

(defthm adt-cols-shape-of-fields-corr
  (implies (adt-fields-corr s ci p c recs) (adt-cols-shape s ci c))
  :hints (("Goal" :in-theory (enable adt-field-corr))))

(defthm adt-rec-p-of-update-nth
  (implies (and (adt-rec-p s r) (natp j) (< j (len s)) (adt-val-okp (nth j s) v))
           (adt-rec-p s (update-nth j v r)))
  :hints (("Goal" :in-theory (enable nth update-nth))))

(defthm adt-seq-p-of-append
  (implies (and (adt-seq-p s a) (adt-rec-p s rec))
           (adt-seq-p s (append a (list rec)))))

(defthm adt-seq-p-of-update-nth
  (implies (and (adt-seq-p s a) (natp i) (< i (len a)) (adt-rec-p s r))
           (adt-seq-p s (update-nth i r a)))
  :hints (("Goal" :in-theory (enable update-nth))))

(defthm adt-rec-p-of-nth
  (implies (and (adt-seq-p s a) (natp i) (< i (len a)))
           (adt-rec-p s (nth i a)))
  :hints (("Goal" :in-theory (enable nth))))

; -----------------------------------------------------------------------------
; The sequence ADT: its concrete layout, its correspondence, its operations,
; and the correspondence theorems every `defadt' instance cites.

(defun adt-shape-p (s c)
  (let ((p (adt-ncols s)))
    (and (true-listp c)
         (< (+ 2 p) (len c))
         (adt-cols-shape s 0 c)
         (adt-all-elt-p '(:ub 8) (nth p c))
         (natp (nth (+ 1 p) c))
         (natp (nth (+ 2 p) c)))))

(defun adt-corr (s c a)
  (let ((p (adt-ncols s)))
    (and (adt-schemap s)
         (adt-shape-p s c)
         (adt-fill-okp p c)
         (adt-seq-p s a)
         (equal (nth (+ 1 p) c) (len a))
         (adt-fields-corr s 0 p c a))))

(defun adt-count-c (s c)
  (nth (+ 1 (adt-ncols s)) c))

(defun adt-append-c (s rec c)
  (declare (xargs :verify-guards nil))
  (let* ((p (adt-ncols s))
         (n (nth (+ 1 p) c)))
    (update-nth (+ 1 p) (+ 1 n) (adt-append-fields s 0 p n rec c))))

(defun adt-set-c (s j i v c)
  (declare (xargs :verify-guards nil))
  (adt-set-fields s j 0 (adt-ncols s) i v c))

(defun adt-get-c (s j i c)
  (declare (xargs :verify-guards nil))
  (adt-get-fields s j 0 (adt-ncols s) i c))

(defun adt-get-okp (s j i c)
  (declare (xargs :verify-guards nil))
  (adt-get-fields-okp s j 0 (adt-ncols s) i c))

; The logical operations (each instance's :logic functions unfold to these).
(defun adt-set-a (j i v a)
  (declare (xargs :guard (and (natp i) (natp j) (true-listp a) (< i (len a))
                              (true-listp (nth i a)))))
  (update-nth i (update-nth j v (nth i a)) a))

(defthm adt-corr-shape
  (implies (adt-corr s c a) (adt-shape-p s c)))

(defthm adt-corr-count
  (implies (adt-corr s c a) (equal (adt-count-c s c) (len a))))

(defthm adt-corr-get
  (implies (and (adt-corr s c a) (natp j) (< j (len s)) (natp i) (< i (len a)))
           (and (equal (adt-get-c s j i c) (nth j (nth i a)))
                (adt-get-okp s j i c)))
  :hints (("Goal" :in-theory (disable adt-fill-okp adt-get-fields-of-corr)
           :use ((:instance adt-get-fields-of-corr (ci 0) (p (adt-ncols s)) (recs a))))))

(defthm adt-len-of-append
  (equal (len (append a b)) (+ (len a) (len b))))

(defthm adt-fill-okp-of-update-count
  (implies (natp p)
           (equal (adt-fill-okp p (update-nth (+ 1 p) x c)) (adt-fill-okp p c)))
  :hints (("Goal" :in-theory (enable adt-fill-okp))))

(defthm adt-fill-natp-when-fill-okp
  (implies (adt-fill-okp p c) (natp (nth (+ 2 p) c)))
  :hints (("Goal" :in-theory (enable adt-fill-okp))))

(local
 (deftheory adt-top-closed
   '(adt-fields-corr adt-cols-shape adt-schemap adt-seq-p adt-rec-p adt-ncols
     adt-append-fields adt-set-fields adt-fill-okp)))

(defthm adt-corr-append
  (implies (and (adt-corr s c a) (adt-rec-p s rec))
           (adt-corr s (adt-append-c s rec c) (append a (list rec))))
  :hints (("Goal" :in-theory (e/d (adt-corr adt-shape-p adt-append-c) (adt-top-closed))
           :use ((:instance adt-len-of-append-fields (ci 0) (p (adt-ncols s)) (n (len a)))
                 (:instance adt-cols-shape-of-fields-corr (ci 0) (p (adt-ncols s))
                            (c (adt-append-c s rec c)) (recs (append a (list rec))))))))

(defthm adt-corr-set
  (implies (and (adt-corr s c a) (natp j) (< j (len s)) (natp i) (< i (len a))
                (adt-val-okp (nth j s) v))
           (adt-corr s (adt-set-c s j i v c) (adt-set-a j i v a)))
  :hints (("Goal" :in-theory (e/d (adt-corr adt-shape-p adt-set-c adt-set-a)
                                  (adt-top-closed adt-set-fields-invariants))
           :use ((:instance adt-set-fields-invariants (ci 0) (p (adt-ncols s)))
                 (:instance adt-cols-shape-of-fields-corr (ci 0) (p (adt-ncols s))
                            (c (adt-set-c s j i v c)) (recs (adt-set-a j i v a)))))))

(defthm adt-seq-p-of-set-a
  (implies (and (adt-seq-p s a) (natp j) (< j (len s)) (natp i) (< i (len a))
                (adt-val-okp (nth j s) v))
           (adt-seq-p s (adt-set-a j i v a))))

(in-theory (disable adt-corr adt-count-c adt-append-c adt-set-c adt-get-c adt-get-okp
                    adt-set-a adt-shape-p))

; -----------------------------------------------------------------------------
; The three recursive shapes a defstobj forces on every instance, as
; constrained functions.  An instance's own array recognizer, pool write
; loop and pool read loop are functional instances of these (defadt emits
; one `:functional-instance' hint per shape; the obligation ACL2 generates
; is the instance's own definition equation).

(encapsulate
  (((adt-g-ct) => *) ((adt-g-colp *) => *))
  (local (defun adt-g-ct () '(:nat)))
  (local (defun adt-g-colp (x) (adt-all-elt-p '(:nat) x)))
  (defthm adt-g-colp-def
    (equal (adt-g-colp x)
           (if (atom x) (equal x nil) (and (adt-elt-p (adt-g-ct) (car x)) (adt-g-colp (cdr x)))))
    :rule-classes nil))

(defthm adt-g-colp-is-all-elt-p
  (equal (adt-g-colp x) (adt-all-elt-p (adt-g-ct) x))
  :hints (("Goal" :induct (len x))
          ("Subgoal *1/2" :use ((:instance adt-g-colp-def)))
          ("Subgoal *1/1" :use ((:instance adt-g-colp-def)))))

(encapsulate
  (((adt-g-p) => *) ((adt-g-poolw * * *) => *))
  (local (defun adt-g-p () 0))
  (local (defun adt-g-poolw (i bytes c) (adt-poolw 0 i bytes c)))
  (defthm adt-g-poolw-def
    (equal (adt-g-poolw i bytes c)
           (if (atom bytes)
               c
             (adt-g-poolw (1+ i) (cdr bytes) (update-nth-array (adt-g-p) i (car bytes) c))))
    :rule-classes nil
    :hints (("Goal" :in-theory (enable adt-poolw)))))

(local
 (defun adt-g-poolw-induct (i bytes c)
   (if (atom bytes)
       (list i c)
     (adt-g-poolw-induct (1+ i) (cdr bytes) (update-nth-array (adt-g-p) i (car bytes) c)))))

(defthm adt-g-poolw-is-poolw
  (equal (adt-g-poolw i bytes c) (adt-poolw (adt-g-p) i bytes c))
  :hints (("Goal" :induct (adt-g-poolw-induct i bytes c)
           :in-theory (e/d (adt-poolw) (adt-poolw-is-pool-writes)))
          ("Subgoal *1/2" :use ((:instance adt-g-poolw-def)))
          ("Subgoal *1/1" :use ((:instance adt-g-poolw-def)))))

(encapsulate
  (((adt-g-q) => *) ((adt-g-poolr * * * *) => *))
  (local (defun adt-g-q () 0))
  (local (defun adt-g-poolr (off n acc c) (adt-poolr 0 off n acc c)))
  (defthm adt-g-poolr-def
    (equal (adt-g-poolr off n acc c)
           (if (zp n)
               acc
             (adt-g-poolr off (1- n) (cons (nth (+ off (1- n)) (nth (adt-g-q) c)) acc) c)))
    :rule-classes nil
    :hints (("Goal" :in-theory (enable adt-poolr)))))

(local
 (defun adt-g-poolr-induct (off n acc c)
   (if (zp n)
       (list off acc c)
     (adt-g-poolr-induct off (1- n) (cons (nth (+ off (1- n)) (nth (adt-g-q) c)) acc) c))))

(defthm adt-g-poolr-is-poolr
  (equal (adt-g-poolr off n acc c) (adt-poolr (adt-g-q) off n acc c))
  :hints (("Goal" :induct (adt-g-poolr-induct off n acc c)
           :in-theory (e/d (adt-poolr) (adt-poolr-is-slice)))
          ("Subgoal *1/2" :use ((:instance adt-g-poolr-def)))
          ("Subgoal *1/1" :use ((:instance adt-g-poolr-def)))))

; The column write an instance executes (grow when full, then write), as
; the library's `adt-col-put'.
(defthm adt-col-put-exec
  (equal (update-nth-array ci n x (if (< n (len (nth ci c)))
                                      c
                                    (update-nth ci (resize-list (nth ci c) (* 2 (+ 1 n)) 0) c)))
         (update-nth ci (adt-col-put (nth ci c) n x) c))
  :hints (("Goal" :in-theory (enable update-nth-array adt-col-put adt-col-room))))

; Openers: on a constant schema the schema-recursive definitions unfold (an
; instance's by-definition bridge between its executable and the library's
; operation).
(defthm adt-append-fields-open
  (implies (and (syntaxp (quotep s)) (consp s))
           (equal (adt-append-fields s ci p n rec c)
                  (adt-append-fields (cdr s) (+ (adt-kind-width (car s)) ci) p n (cdr rec)
                                     (adt-put-field (car s) ci p n (car rec) c))))
  :hints (("Goal" :in-theory (enable adt-append-fields))))

(defthm adt-set-fields-open
  (implies (and (syntaxp (and (quotep s) (quotep j))) (consp s))
           (equal (adt-set-fields s j ci p i v c)
                  (if (zp j)
                      (adt-put-field (car s) ci p i v c)
                    (adt-set-fields (cdr s) (1- j) (+ (adt-kind-width (car s)) ci) p i v c))))
  :hints (("Goal" :in-theory (enable adt-set-fields))))

(defthm adt-get-fields-open
  (implies (and (syntaxp (and (quotep s) (quotep j))) (consp s))
           (equal (adt-get-fields s j ci p i c)
                  (if (zp j)
                      (adt-get-field (car s) ci p i c)
                    (adt-get-fields (cdr s) (1- j) (+ (adt-kind-width (car s)) ci) p i c))))
  :hints (("Goal" :in-theory (enable adt-get-fields))))

(defthm adt-get-fields-okp-open
  (implies (and (syntaxp (and (quotep s) (quotep j))) (consp s))
           (equal (adt-get-fields-okp s j ci p i c)
                  (if (zp j)
                      (adt-get-field-okp (car s) ci p i c)
                    (adt-get-fields-okp (cdr s) (1- j) (+ (adt-kind-width (car s)) ci) p i c))))
  :hints (("Goal" :in-theory (enable adt-get-fields-okp))))

(defthm adt-cols-shape-open
  (implies (and (syntaxp (quotep s)) (consp s))
           (equal (adt-cols-shape s ci c)
                  (and (if (adt-octets-kind-p (car s))
                           (and (adt-all-elt-p '(:nat) (nth ci c))
                                (adt-all-elt-p '(:nat) (nth (+ 1 ci) c)))
                         (adt-all-elt-p (adt-ctype (car s)) (nth ci c)))
                       (adt-cols-shape (cdr s) (+ (adt-kind-width (car s)) ci) c))))
  :hints (("Goal" :in-theory (enable adt-cols-shape))))

(defthm adt-rec-p-open
  (implies (and (syntaxp (quotep s)) (consp s))
           (equal (adt-rec-p s r)
                  (and (consp r) (adt-val-okp (car s) (car r)) (adt-rec-p (cdr s) (cdr r)))))
  :hints (("Goal" :in-theory (enable adt-rec-p))))

(defthm adt-schema-fns-of-atom
  (implies (atom s)
           (and (equal (adt-append-fields s ci p n rec c) c)
                (equal (adt-set-fields s j ci p i v c) c)
                (equal (adt-get-fields s j ci p i c) nil)
                (equal (adt-get-fields-okp s j ci p i c) nil)
                (equal (adt-cols-shape s ci c) t)
                (equal (adt-rec-p s r) (null r))))
  :hints (("Goal" :in-theory (enable adt-append-fields adt-set-fields adt-get-fields
                                     adt-get-fields-okp adt-cols-shape adt-rec-p))))

(in-theory (disable adt-append-fields adt-set-fields adt-get-fields adt-get-fields-okp
                    adt-schema-fns-of-atom
                    adt-cols-shape adt-fields-corr adt-append-fields-open adt-set-fields-open
                    adt-get-fields-open adt-get-fields-okp-open adt-cols-shape-open
                    adt-rec-p-open))

(deftheory adt-instance-unfold
  '(adt-append-fields-open adt-set-fields-open adt-get-fields-open
    adt-get-fields-okp-open adt-cols-shape-open adt-schema-fns-of-atom adt-rec-p-open
    adt-append-c adt-set-c adt-get-c adt-get-okp adt-count-c adt-shape-p
    adt-put-field adt-get-field adt-get-field-okp adt-pool-push adt-pool-room
    adt-kind-width adt-octets-kind-p adt-ncols adt-ctype
    (:executable-counterpart adt-ncols) (:executable-counterpart adt-ctype)
    (:executable-counterpart adt-kind-width) (:executable-counterpart adt-octets-kind-p)))

(defthm adt-true-listp-when-seq-p
  (implies (adt-seq-p s a) (true-listp a))
  :rule-classes :forward-chaining)

(defthm adt-true-listp-when-rec-p
  (implies (adt-rec-p s r) (true-listp r))
  :hints (("Goal" :in-theory (enable adt-rec-p))))

(defthm adt-true-listp-nth-when-seq-p
  (implies (and (adt-seq-p s a) (natp i) (< i (len a)))
           (true-listp (nth i a)))
  :hints (("Goal" :use adt-rec-p-of-nth :in-theory (disable adt-rec-p-of-nth))))

(defthm adt-nat-col-nth
  (implies (and (adt-all-elt-p '(:nat) x) (natp i) (< i (len x)))
           (and (integerp (nth i x)) (<= 0 (nth i x))))
  :hints (("Goal" :use ((:instance adt-elt-p-of-nth-when-all-elt-p (ct '(:nat))))
           :in-theory (e/d (adt-elt-p) (adt-elt-p-of-nth-when-all-elt-p)))))

; -----------------------------------------------------------------------------
; The canonical image.  The concrete image a sequence of operations reaches
; is a pure function of that sequence (every capacity, pool position and fill
; is computed here, in ACL2: nothing depends on allocation order), but two
; histories with the same logical value can reach different images (a set of
; an :octets field leaves its old octets in the pool; capacities differ).
; `adt-canon' is the image of the logical value ALONE: the empty image with
; the records appended in order.  A digest of a snapshot is a digest of the
; canonical image (or of the logical value; the two determine each other),
; so it is verifiable by replay of the log.

(defun adt-nils (n)
  (if (zp n) nil (cons nil (adt-nils (1- n)))))

(defun adt-empty-c (s)
  (append (adt-nils (adt-ncols s)) (list nil 0 0)))

(defun adt-build (s a c)
  (declare (xargs :verify-guards nil))
  (if (atom a) c (adt-build s (cdr a) (adt-append-c s (car a) c))))

(defun adt-canon (s a)
  (declare (xargs :verify-guards nil))
  (adt-build s a (adt-empty-c s)))

(local
 (defun adt-kn-induct (k n)
   (if (or (zp k) (zp n)) (list k n) (adt-kn-induct (1- k) (1- n)))))

(local
 (defthm adt-nth-of-make-list-prefix
   (implies (and (natp k) (< k (nfix n)))
            (equal (nth k (append (adt-nils n) tail)) nil))
   :hints (("Goal" :in-theory (enable nth) :induct (adt-kn-induct k n) :expand ((adt-nils n))))))

(local
 (defthm adt-nth-of-make-list-suffix
   (implies (and (natp k) (natp n))
            (equal (nth (+ n k) (append (adt-nils n) tail)) (nth k tail)))
   :hints (("Goal" :in-theory (enable nth) :induct (adt-nils n)))))

(local
 (defthm adt-len-nils
   (equal (len (adt-nils n)) (nfix n))))

(local
 (defthm adt-fields-corr-of-empty-columns
   (implies (and (natp ci) (natp n) (<= (+ ci (adt-ncols s)) n))
            (adt-fields-corr s ci p (append (adt-nils n) tail) nil))
   :hints (("Goal" :in-theory (enable adt-fields-corr adt-field-corr)))))

(local
 (defthm adt-cols-shape-of-empty-columns
   (implies (and (natp ci) (natp n) (<= (+ ci (adt-ncols s)) n))
            (adt-cols-shape s ci (append (adt-nils n) tail)))
   :hints (("Goal" :in-theory (enable adt-cols-shape)))))

(defthm adt-corr-empty
  (implies (adt-schemap s) (adt-corr s (adt-empty-c s) nil))
  :hints (("Goal" :in-theory (enable adt-corr adt-shape-p adt-fill-okp)
           :use ((:instance adt-nth-of-make-list-suffix (k 0) (n (adt-ncols s)) (tail (list nil 0 0)))
                 (:instance adt-nth-of-make-list-suffix (k 1) (n (adt-ncols s)) (tail (list nil 0 0)))
                 (:instance adt-nth-of-make-list-suffix (k 2) (n (adt-ncols s)) (tail (list nil 0 0)))))))

; -----------------------------------------------------------------------------
; The cleared image (lane paged-catalog, 2026-10-01): every column, the
; pool, the count and the fill reset IN PLACE -- what an instance's
; NAME$c-clear executes as a resize of each column and of the pool to 0 and
; the two counters to 0 -- whatever the foundation holds beyond its fields.
; It corresponds to the empty sequence: the creator's correspondence with a
; tail.

(defun adt-clear-down (p c)
  (if (zp p) c (update-nth (- p 1) nil (adt-clear-down (- p 1) c))))

(defun adt-clear-c (s c)
  (let ((p (adt-ncols s)))
    (update-nth (+ 2 p) 0 (update-nth (+ 1 p) 0 (update-nth p nil (adt-clear-down p c))))))

(local
 (defthm adt-update-nth-past-len-of-append
   (implies (and (natp i) (<= (len a) i))
            (equal (update-nth i v (append a b))
                   (append a (update-nth (- i (len a)) v b))))
   :hints (("Goal" :in-theory (enable update-nth) :induct (update-nth i v a)))))

(local
 (defthm adt-update-nth-0
   (equal (update-nth 0 v x) (cons v (cdr x)))
   :hints (("Goal" :in-theory (enable update-nth)))))

(local
 (defthm adt-update-nth-of-cons
   (implies (not (zp i))
            (equal (update-nth i v (cons a x)) (cons a (update-nth (- i 1) v x))))
   :hints (("Goal" :in-theory (enable update-nth)))))

(local
 (defthm adt-nils-cons-nil
   (equal (append (adt-nils k) (cons nil x))
          (cons nil (append (adt-nils k) x)))))

(local
 (defthm adt-cdr-of-nthcdr
   (equal (cdr (nthcdr k c)) (nthcdr (+ 1 (nfix k)) c))))

(local
 (defthm adt-nthcdr-of-nil
   (equal (nthcdr k nil) nil)))

(local
 (defthm adt-nthcdr-3
   (implies (natp n) (equal (nthcdr (+ 3 n) c) (nthcdr n (cdddr c))))
   :hints (("Goal" :expand ((nthcdr (+ 3 n) c) (nthcdr (+ 2 n) (cdr c)) (nthcdr (+ 1 n) (cddr c)))))))

(local
 (defthm adt-clear-down-is-nils
   (implies (natp p)
            (equal (adt-clear-down p c) (append (adt-nils p) (nthcdr p c))))
   :hints (("Goal" :induct (adt-clear-down p c)))))

(local
 (defthm adt-true-listp-of-nthcdr
   (implies (true-listp c) (true-listp (nthcdr k c)))))

(local
 (defthm adt-corr-empty-with-tail
   (implies (and (adt-schemap s) (true-listp tail))
            (adt-corr s (append (adt-nils (adt-ncols s)) (list* nil 0 0 tail)) nil))
   :hints (("Goal" :in-theory (e/d (adt-corr adt-shape-p adt-fill-okp)
                                   (adt-nils-cons-nil adt-nth-of-make-list-suffix))
            :use ((:instance adt-nth-of-make-list-suffix (k 0) (n (adt-ncols s)) (tail (list* nil 0 0 tail)))
                  (:instance adt-nth-of-make-list-suffix (k 1) (n (adt-ncols s)) (tail (list* nil 0 0 tail)))
                  (:instance adt-nth-of-make-list-suffix (k 2) (n (adt-ncols s)) (tail (list* nil 0 0 tail))))))))

(defthm adt-corr-of-clear-c
  (implies (and (adt-schemap s) (true-listp c))
           (adt-corr s (adt-clear-c s c) nil))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (adt-clear-c) (adt-corr-empty-with-tail adt-nils-cons-nil))
           :use ((:instance adt-corr-empty-with-tail (tail (nthcdr (+ 3 (adt-ncols s)) c)))))))

; What an instance's clear obligation needs of its correspondence hypothesis.
(defthm adt-corr-true-listp-c
  (implies (adt-corr s c a) (true-listp c))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable adt-corr adt-shape-p))))

(in-theory (disable adt-clear-c))

(local
 (defthm adt-append-snoc-assoc
   (equal (append (append b (list x)) rest) (append b (cons x rest)))))

(local
 (defun adt-build-induct (s a c b)
   (declare (xargs :verify-guards nil))
   (if (atom a)
       (list c b)
     (adt-build-induct s (cdr a) (adt-append-c s (car a) c) (append b (list (car a)))))))

(defthm adt-corr-true-listp
  (implies (adt-corr s c a) (true-listp a))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable adt-corr))))

(defthm adt-corr-build
  (implies (and (adt-corr s c b) (adt-seq-p s a))
           (adt-corr s (adt-build s a c) (append b a)))
  :hints (("Goal" :induct (adt-build-induct s a c b)
           :in-theory (enable adt-build))))

(defthm adt-corr-canon
  (implies (and (adt-schemap s) (adt-seq-p s a))
           (adt-corr s (adt-canon s a) a))
  :hints (("Goal" :use ((:instance adt-corr-build (c (adt-empty-c s)) (b nil))
                        adt-corr-empty)
           :in-theory (e/d (adt-canon) (adt-corr-build adt-corr-empty adt-empty-c)))))

(in-theory (disable adt-empty-c adt-build adt-canon))


; -----------------------------------------------------------------------------
; THE POOL'S LOAD (lane paged-catalog-4, 2026-10-01; Codex r21 F1, D27).  The
; fill of the octet pool is what the sequence's octets need, exactly, as
; long as no octets field is ever rewritten: `adt-load' sums the lengths of
; every record's octets fields, and `adt-fill-is-load' (fill = load) holds
; of the empty image, of the cleared image, after an append, and after a
; set of a SCALAR field.  A set of an octets field pushes the new value
; into the pool and abandons the old extent, which is why an instance
; declared write-once (def-representation :write-once) exports no such set:
; its pool is then bounded by its live records' octets, not by the history
; of its writes (books/def-representation.lisp, the generated
; NAME$C-FILL-IS-LOAD-* theorems).

(defun adt-rec-load (s rec)
  (if (atom s)
      0
    (+ (if (adt-octets-kind-p (car s)) (len (car rec)) 0)
       (adt-rec-load (cdr s) (cdr rec)))))

(defun adt-load (s a)
  (if (atom a)
      0
    (+ (adt-rec-load s (car a)) (adt-load s (cdr a)))))

(defthm adt-load-of-append
  (equal (adt-load s (append a b)) (+ (adt-load s a) (adt-load s b))))

(defthm adt-load-of-atom
  (implies (atom a) (equal (adt-load s a) 0)))

(local
 (defun adt-rl-induct (s j r)
   (if (atom s) (list j r) (adt-rl-induct (cdr s) (1- j) (cdr r)))))

(defthm adt-rec-load-of-update-nth-scalar
  (implies (and (natp j) (not (adt-octets-kind-p (nth j s))))
           (equal (adt-rec-load s (update-nth j v r)) (adt-rec-load s r)))
  :hints (("Goal" :in-theory (enable nth update-nth) :induct (adt-rl-induct s j r))))

(local
 (defun adt-load-induct (i a)
   (if (zp i) a (adt-load-induct (1- i) (cdr a)))))

(defthm adt-load-of-update-nth-same-load
  (implies (and (natp i) (< i (len a)) (equal (adt-rec-load s r) (adt-rec-load s (nth i a))))
           (equal (adt-load s (update-nth i r a)) (adt-load s a)))
  :hints (("Goal" :in-theory (enable nth update-nth) :induct (adt-load-induct i a))))

(defthm adt-fill-of-put-field-load
  (implies (and (natp ci) (natp p) (<= (+ ci (adt-kind-width k)) p) (natp (nth (+ 2 p) c)))
           (equal (nth (+ 2 p) (adt-put-field k ci p n v c))
                  (+ (nth (+ 2 p) c) (if (adt-octets-kind-p k) (len v) 0))))
  :hints (("Goal" :in-theory (enable adt-put-field adt-kind-width))))

(defthm adt-fill-of-append-fields-load
  (implies (and (natp ci) (natp p) (<= (+ ci (adt-ncols s)) p) (natp (nth (+ 2 p) c)))
           (equal (nth (+ 2 p) (adt-append-fields s ci p n rec c))
                  (+ (nth (+ 2 p) c) (adt-rec-load s rec))))
  :hints (("Goal" :induct (adt-append-fields s ci p n rec c)
           :in-theory (e/d (adt-append-fields adt-ncols) (adt-put-field)))))

(defthm adt-fill-of-set-fields-load
  (implies (and (natp ci) (natp p) (<= (+ ci (adt-ncols s)) p) (natp (nth (+ 2 p) c))
                (natp j) (< j (len s)))
           (equal (nth (+ 2 p) (adt-set-fields s j ci p i v c))
                  (+ (nth (+ 2 p) c) (if (adt-octets-kind-p (nth j s)) (len v) 0))))
  :hints (("Goal" :induct (adt-set-fields s j ci p i v c)
           :in-theory (e/d (adt-set-fields adt-ncols nth) (adt-put-field)))))

(defthm adt-load-natp
  (natp (adt-load s a))
  :rule-classes :type-prescription)

(defun adt-fill-is-load (s c a)
  (equal (nth (+ 2 (adt-ncols s)) c) (adt-load s a)))

(defthm adt-fill-is-load-of-append-c
  (implies (adt-fill-is-load s c a)
           (adt-fill-is-load s (adt-append-c s rec c) (append a (list rec))))
  :hints (("Goal" :in-theory (e/d (adt-append-c) (adt-append-fields))
           :use ((:instance adt-fill-of-append-fields-load (ci 0) (p (adt-ncols s))
                            (n (nth (+ 1 (adt-ncols s)) c)))))))

(defthm adt-fill-is-load-of-set-c
  (implies (and (adt-fill-is-load s c a) (natp j) (< j (len s))
                (not (adt-octets-kind-p (nth j s)))
                (natp i) (< i (len a)))
           (adt-fill-is-load s (adt-set-c s j i v c) (adt-set-a j i v a)))
  :hints (("Goal" :in-theory (e/d (adt-set-c adt-set-a) (adt-set-fields))
           :use ((:instance adt-fill-of-set-fields-load (ci 0) (p (adt-ncols s)))))))

(defthm adt-fill-is-load-of-clear-c
  (adt-fill-is-load s (adt-clear-c s c) nil)
  :hints (("Goal" :in-theory (union-theories '(adt-clear-c adt-fill-is-load nth-update-nth adt-load
                                               (:executable-counterpart adt-load) fix)
                                             (theory 'minimal-theory)))))

(defthm adt-nth-past-nils
  (implies (natp k)
           (equal (nth (+ k (nfix n)) (append (adt-nils n) y)) (nth k y)))
  :hints (("Goal" :in-theory (enable nth adt-nils) :induct (adt-nils n))))

(defthm adt-fill-is-load-of-empty-c
  (adt-fill-is-load s (adt-empty-c s) nil)
  :hints (("Goal" :in-theory (e/d (adt-empty-c) (adt-nth-past-nils))
           :use ((:instance adt-nth-past-nils (k 2) (n (adt-ncols s)) (y (list nil 0 0)))))))

(in-theory (disable adt-fill-is-load))
