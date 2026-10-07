; fn: what `def-representation' (books/def-representation.lisp) needs beyond
; the proto library books/proto/adt-lib.lisp: the total list operations a
; LIST foundation executes with (so that a generic's :exec functions are
; guard-verified at `:guard t' and the obligations open them to `nth',
; `update-nth' and `append'), and the SCALAR view, under which a
; one-field representation's logical value is the list of the field's
; values rather than a list of one-element records.  Each lemma is proved
; once here; an instance's obligations cite them by one uniform hint.

(in-package "ACL2")
(include-book "proto/adt-lib")
(include-book "def-representation-paged")

; -----------------------------------------------------------------------------
; Total list operations for a list foundation.

(defun adt-l-nth (i x)
  (declare (xargs :guard t))
  (if (or (not (integerp i)) (<= i 0))
      (if (consp x) (car x) nil)
    (adt-l-nth (- i 1) (if (consp x) (cdr x) nil))))

(defun adt-l-update-nth (i v x)
  (declare (xargs :guard t))
  (if (or (not (integerp i)) (<= i 0))
      (cons v (if (consp x) (cdr x) nil))
    (cons (if (consp x) (car x) nil)
          (adt-l-update-nth (- i 1) v (if (consp x) (cdr x) nil)))))

(defun adt-l-snoc (x e)
  (declare (xargs :guard t))
  (if (consp x)
      (cons (car x) (adt-l-snoc (cdr x) e))
    (list e)))

(defthm adt-l-nth-is-nth
  (equal (adt-l-nth i x) (nth i x))
  :hints (("Goal" :in-theory (enable nth))))

(defthm adt-l-update-nth-is-update-nth
  (equal (adt-l-update-nth i v x) (update-nth i v x))
  :hints (("Goal" :in-theory (enable update-nth))))

(defthm adt-l-snoc-is-append
  (implies (true-listp x)
           (equal (adt-l-snoc x e) (append x (list e)))))

(in-theory (disable adt-l-nth adt-l-update-nth adt-l-snoc))

; An element of a typed column is a natural, as a TYPE-PRESCRIPTION: what
; the guard of an :octets field's `-okp' (the offset plus the length
; against the pool's length, a `rationalp' of a sum) needs once
; `adt-elt-p' is open, where the library's rewrite
; `adt-elt-p-of-nth-when-all-elt-p' no longer matches and no rewrite rule
; reaches the type of a sum (lane paged-catalog, 2026-10-01: the
; eleven-field `fn-crow' instance was refused at fn-crow$c-get-msgid-okp;
; the three-field pilot found it by induction).
(defthm adt-nth-of-all-elt-p-natp
  (implies (and (adt-all-elt-p ct x) (natp i) (< i (len x)))
           (natp (nth i x)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable adt-elt-p nth))))

; -----------------------------------------------------------------------------
; The scalar view: a sequence of one-field records, seen as the list of
; the field's values.  `adt-wrap1' is the bridge from the scalar list to
; the record sequence the column library reasons about.

(defun adt-wrap1 (a)
  (declare (xargs :guard t))
  (if (consp a) (cons (list (car a)) (adt-wrap1 (cdr a))) nil))

(defun adt-scalar-seq-p (k a)
  (declare (xargs :guard (adt-kindp k)))
  (if (atom a)
      (null a)
    (and (adt-val-okp k (car a)) (adt-scalar-seq-p k (cdr a)))))

(defthm adt-scalar-seq-p-true-listp
  (implies (adt-scalar-seq-p k a) (true-listp a))
  :rule-classes :forward-chaining)

(defthm adt-seq-p-of-wrap1
  (implies (adt-scalar-seq-p k a)
           (adt-seq-p (list k) (adt-wrap1 a)))
  :hints (("Goal" :in-theory (enable adt-rec-p))))

(defthm adt-len-of-wrap1
  (equal (len (adt-wrap1 a)) (len a)))

(defthm adt-nth-of-wrap1
  (implies (and (natp i) (< i (len a)))
           (equal (nth i (adt-wrap1 a)) (list (nth i a))))
  :hints (("Goal" :in-theory (enable nth))))

(defthm adt-wrap1-of-append-list
  (implies (true-listp a)
           (equal (adt-wrap1 (append a (list v)))
                  (append (adt-wrap1 a) (list (list v))))))

(defthm adt-wrap1-of-update-nth
  (implies (and (natp i) (< i (len a)))
           (equal (adt-wrap1 (update-nth i v a))
                  (update-nth i (list v) (adt-wrap1 a))))
  :hints (("Goal" :in-theory (enable update-nth))))

(defthm adt-set-a-0-of-wrap1
  (implies (and (natp i) (< i (len a)))
           (equal (adt-set-a 0 i v (adt-wrap1 a))
                  (adt-wrap1 (update-nth i v a))))
  :hints (("Goal" :in-theory (enable adt-set-a))))

(defthm adt-scalar-seq-p-of-append
  (implies (and (adt-scalar-seq-p k a) (adt-val-okp k v))
           (adt-scalar-seq-p k (append a (list v)))))

(defthm adt-scalar-seq-p-of-update-nth
  (implies (and (adt-scalar-seq-p k a) (natp i) (< i (len a)) (adt-val-okp k v))
           (adt-scalar-seq-p k (update-nth i v a)))
  :hints (("Goal" :in-theory (enable update-nth))))

(defthm adt-rec-p-of-list1
  (equal (adt-rec-p (list k) (list v)) (adt-val-okp k v))
  :hints (("Goal" :in-theory (enable adt-rec-p))))

; The correspondence after a scalar set, stated in the form the obligation
; takes once `adt-wrap1-of-update-nth' has fired: `adt-corr-set' at column
; 0 with the one-field record update folded.
(defthm adt-corr-set-scalar
  (implies (and (adt-corr s c (adt-wrap1 a)) (equal (len s) 1)
                (natp i) (< i (len a)) (adt-val-okp (car s) v))
           (adt-corr s (adt-set-c s 0 i v c) (update-nth i (list v) (adt-wrap1 a))))
  :hints (("Goal" :use ((:instance adt-corr-set (j 0) (a (adt-wrap1 a))))
           :in-theory (e/d (adt-set-a) (adt-corr-set)))))

; The same over the paged foundation (lane gate-b-2): `adt-pg-corr-set' at
; column 0, for a paged :scalar instance's set obligation.
(defthm adt-pg-corr-set-scalar
  (implies (and (adt-pg-corr s r q c (adt-wrap1 a)) (equal (len s) 1)
                (natp i) (< i (len a)) (adt-val-okp (car s) v))
           (adt-pg-corr s r q (adt-pg-set-c s 0 i v r q dp c) (update-nth i (list v) (adt-wrap1 a))))
  :hints (("Goal" :use ((:instance adt-pg-corr-set (j 0) (a (adt-wrap1 a))))
           :in-theory (e/d (adt-set-a) (adt-pg-corr-set)))))

(in-theory (disable adt-wrap1 adt-scalar-seq-p))

; The octet-sequence reader (books/def-representation.lisp, :scalar
; :octet-seq): past the end of a list `nth' is NIL.  A defthmd: an instance
; enables it for its own obligations, no other book sees a new rule.
(defthmd adt-nth-beyond-len
  (implies (and (natp i) (<= (len a) i))
           (equal (nth i a) nil))
  :hints (("Goal" :in-theory (enable nth))))

; The octets [I, N) of a list, for the stobj-to-stobj copy loop of
; :octet-seq (books/def-representation.lisp).  Defthmds: an instance
; enables them for its own induction.
(defun adt-between (i n a)
  (declare (xargs :measure (nfix (- n i)) :verify-guards nil))
  (if (and (natp i) (natp n) (< i n))
      (cons (nth i a) (adt-between (+ 1 i) n a))
    nil))
(defthmd adt-between-done
  (implies (<= n i) (equal (adt-between i n a) nil))
  :hints (("Goal" :in-theory (enable adt-between))))
(defthmd adt-between-step
  (implies (and (natp i) (natp n) (< i n))
           (equal (adt-between i n a)
                  (cons (nth i a) (adt-between (+ 1 i) n a))))
  :hints (("Goal" :in-theory (enable adt-between))))
(defthmd adt-nthcdr-cons
  (implies (and (natp i) (< i (len a)))
           (equal (nthcdr i a) (cons (nth i a) (nthcdr (+ 1 i) a))))
  :hints (("Goal" :induct (nthcdr i a) :in-theory (enable nth nthcdr))))
(defthmd adt-between-nthcdr
  (implies (and (natp i) (true-listp a))
           (equal (adt-between i (len a) a) (nthcdr i a)))
  :hints (("Goal" :induct (adt-between i (len a) a)
                  :in-theory (enable adt-between adt-nthcdr-cons))))
(defthmd adt-between-whole
  (implies (true-listp a) (equal (adt-between 0 (len a) a) a))
  :hints (("Goal" :use (:instance adt-between-nthcdr (i 0)) :in-theory (union-theories (disable adt-between adt-between-nthcdr) (quote (nthcdr))))))

; -----------------------------------------------------------------------------
; The scalar :octets vocabulary (`def-representation' :exports roles
; payload-len, inner-get, seal-buffer and seal-range).  The columnar
; layout of one :octets field is the offset column 0, the length column 1,
; the pool 2, the count 3 and the fill 4; what the correspondence says of
; one row, proved once here for the schema ((:octets)).

(defthm adt-cars-of-wrap1
  (equal (adt-cars (adt-wrap1 a)) (true-list-fix a))
  :hints (("Goal" :in-theory (enable adt-cars adt-wrap1))))

(local
 (defun adt-sn-ind (i off n)
   (if (zp i) (list off n) (adt-sn-ind (1- i) (1+ off) (1- n)))))

; Cell I of a slice of the pool is cell OFF+I of the pool.
(defthm adt-nth-of-slice
  (implies (and (natp off) (natp n) (natp i) (< i n))
           (equal (nth i (adt-slice pool off n)) (nth (+ off i) pool)))
  :hints (("Goal" :in-theory (enable adt-slice) :induct (adt-sn-ind i off n)
                  :expand ((adt-slice pool off n)))))

(local
 (defthm adt-so-nth-of-true-list-fix
   (equal (nth i (true-list-fix a)) (nth i a))
   :hints (("Goal" :in-theory (enable nth true-list-fix)))))

(local
 (defthm adt-so-len-of-true-list-fix
   (equal (len (true-list-fix a)) (len a))))

(local
 (defthm adt-so-unfold
   (implies (adt-corr '((:octets)) c (adt-wrap1 a))
            (and (adt-ocol-corr (nth 0 c) (nth 1 c) (nth 2 c) (nth 4 c) 0 (true-list-fix a))
                 (adt-fill-okp 2 c) (equal (nth 3 c) (len a))))
   :hints (("Goal" :in-theory (e/d (adt-corr adt-fields-corr adt-field-corr adt-octets-kind-p
                                             adt-kind-width adt-ncols adt-cars-of-wrap1)
                                   (adt-ocol-corr))))))

(local
 (defthm adt-so-fill
   (implies (adt-corr '((:octets)) c (adt-wrap1 a))
            (and (natp (nth 4 c)) (<= (nth 4 c) (len (nth 2 c)))))
   :rule-classes nil
   :hints (("Goal" :use adt-so-unfold :in-theory (e/d (adt-fill-okp) (adt-so-unfold))))))

; Row H of a scalar :octets instance: its offset and length are naturals in
; the columns, the row lies in the pool, the length column holds the length
; of the payload, and the pool holds its octets at the offset.
(defthm adt-corr-scalar-octets-row
  (implies (and (adt-corr '((:octets)) c (adt-wrap1 a)) (natp h) (< h (len a)))
           (and (natp (nth h (nth 0 c))) (natp (nth h (nth 1 c)))
                (< h (len (nth 0 c))) (< h (len (nth 1 c)))
                (<= (+ (nth h (nth 0 c)) (nth h (nth 1 c))) (len (nth 2 c)))
                (equal (nth h (nth 1 c)) (len (nth h a)))
                (implies (and (natp i) (< i (len (nth h a))))
                         (equal (nth (+ (nth h (nth 0 c)) i) (nth 2 c)) (nth i (nth h a))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable adt-ocol-corr-get-0 adt-slice adt-len-of-slice adt-ocol-corr
                                      adt-nth-of-slice adt-fill-okp)
           :use (adt-so-unfold adt-so-fill
                 (:instance adt-ocol-corr-get-0 (offs (nth 0 c)) (lens (nth 1 c)) (pool (nth 2 c))
                            (fl (nth 4 c)) (v (true-list-fix a)) (m h))
                 (:instance adt-len-of-slice (pool (nth 2 c)) (off (nth h (nth 0 c)))
                            (n (nth h (nth 1 c))))
                 (:instance adt-nth-of-slice (pool (nth 2 c)) (off (nth h (nth 0 c)))
                            (n (nth h (nth 1 c)))))
           :do-not-induct t)))

; The octets [A, B) of a list (`adt-between') are the take of the drop.
(local
 (defthmd adt-so-nth-is-car-nthcdr
   (equal (nth a x) (car (nthcdr a x)))
   :hints (("Goal" :in-theory (enable nth nthcdr)))))

(local
 (defthmd adt-so-nthcdr-add1
   (implies (natp a) (equal (nthcdr (+ 1 a) x) (cdr (nthcdr a x))))
   :hints (("Goal" :in-theory (enable nthcdr)))))

(defthmd adt-between-is-take-nthcdr
  (implies (and (natp a) (natp b) (<= a b))
           (equal (adt-between a b x) (take (- b a) (nthcdr a x))))
  :hints (("Goal" :induct (adt-between a b x)
                  :in-theory (enable adt-between adt-so-nth-is-car-nthcdr adt-so-nthcdr-add1)
                  :expand ((take (- b a) (nthcdr a x))))))

(defthm adt-len-of-between
  (implies (and (natp a) (natp b) (<= a b)) (equal (len (adt-between a b x)) (- b a)))
  :hints (("Goal" :in-theory (enable adt-between))))

(defthmd adt-take-len
  (implies (true-listp x) (equal (take (len x) x) x)))

(local
 (defthm adt-so-octetsp-nth
   (implies (and (adt-octetsp x) (natp a) (< a (len x))) (unsigned-byte-p 8 (nth a x)))
   :hints (("Goal" :in-theory (enable adt-octetsp nth)))))

(local
 (defthmd adt-so-octetsp-car-nthcdr
   (implies (and (adt-octetsp x) (natp a) (< a (len x)))
            (unsigned-byte-p 8 (car (nthcdr a x))))
   :hints (("Goal" :use adt-so-octetsp-nth :in-theory (e/d (adt-so-nth-is-car-nthcdr)
                                                           (adt-so-octetsp-nth))))))

(local
 (defun adt-so-ind (n a) (if (zp n) a (adt-so-ind (1- n) (1+ a)))))

; A slice of an octet list that lies within it is an octet list.
(defthmd adt-octetsp-of-take-nthcdr
  (implies (and (adt-octetsp x) (natp a) (natp n) (<= (+ a n) (len x)))
           (adt-octetsp (take n (nthcdr a x))))
  :hints (("Goal" :induct (adt-so-ind n a)
                  :in-theory (enable adt-octetsp adt-so-nth-is-car-nthcdr adt-so-nthcdr-add1
                                     adt-so-octetsp-car-nthcdr)
                  :expand ((take n (nthcdr a x))))))

; A payload of a scalar :octets sequence is an octet list, so a true list
; (the guard of `nth' into it).
(defthm adt-octetsp-of-nth-of-scalar-seq
  (implies (and (adt-scalar-seq-p '(:octets) a) (natp h) (< h (len a)))
           (adt-octetsp (nth h a)))
  :hints (("Goal" :in-theory (enable adt-scalar-seq-p adt-val-okp nth))))

(defthm adt-true-listp-of-nth-of-scalar-seq
  (implies (and (adt-scalar-seq-p '(:octets) a) (natp h) (< h (len a)))
           (true-listp (nth h a)))
  :hints (("Goal" :use adt-octetsp-of-nth-of-scalar-seq
                  :in-theory (disable adt-octetsp-of-nth-of-scalar-seq))))
