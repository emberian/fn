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

(in-theory (disable adt-wrap1 adt-scalar-seq-p))
