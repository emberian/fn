; fn: the TREE field of `def-representation' (lane gate-b-2, 2026-10-01;
; D27; stage 3 of planning/design-store-representation-2026-10-01.md).
;
; A `(F :tree)' field is an :octets field whose value is the postfix
; program of a tree (books/store-tree-codec.lisp, `fn-scc-program'); its
; append walks the tree into the pool, so the program never exists as a
; list.  books/def-representation-tree-walk.lisp holds the walk (the
; counts without lists, the writer over any put and its meaning, the
; columnar instance's checked put).  This book is what an instance with a
; tree field includes; it adds the PAGED instance's half:
;   * the paged checked put `adt-pg-cput' and its fold, which with the room
;     made is the pool write at the fill and the fill moved
;     (`adt-pg-cputs-is-poolw');
;   * the put of a tree into one row (`adt-pg-put-tree'), which is the
;     octets put of its program (`adt-pg-put-tree-is-put-field');
;   * the record append with a MASK of tree fields (`adt-pg-append-t-c'),
;     which is the paged append of the encoded record
;     (`adt-pg-append-t-c-is-append-c'), so an instance's NAME-APPEND-T
;     inherits NAME-APPEND's correspondence.
; Each paged instance's executables are bridged to these by definition
; (books/def-representation.lisp, `adt-pg-tree-exec-events').

(in-package "ACL2")
(include-book "def-representation-tree-walk")
(include-book "def-representation-paged")
(local (include-book "arithmetic/top" :dir :system))

; The paged checked put: an octet at the fill when a pool page has room for
; it, else nothing; its fold, with the room made, is the pool write at the
; fill and the fill moved past it.
(defun adt-pg-cput (b q c)
  (declare (xargs :verify-guards nil))
  (let ((fl (nth 3 c)))
    (if (and (unsigned-byte-p 8 b) (natp fl) (< fl (* q (nth 5 c))))
        (update-nth 3 (+ 1 fl) (adt-pg-pput fl b q c))
      c)))

(defun adt-pg-cputs (bytes q c)
  (declare (xargs :verify-guards nil))
  (if (atom bytes) c (adt-pg-cputs (cdr bytes) q (adt-pg-cput (car bytes) q c))))

(local
 (defthm adt-tree-update-nth-nth-natp
   (implies (and (natp k) (natp (nth k c)))
            (equal (update-nth k (nth k c) c) c))
   :hints (("Goal" :in-theory (enable nth update-nth)))))

(local
 (defthm adt-tree-pput-of-update-fill
   (equal (adt-pg-pput i b q (update-nth 3 x c))
          (update-nth 3 x (adt-pg-pput i b q c)))
   :hints (("Goal" :in-theory (enable adt-pg-pput)))))

(local
 (defthm adt-tree-poolw-of-update-fill
   (equal (adt-pg-poolw i bytes q (update-nth 3 x c))
          (update-nth 3 x (adt-pg-poolw i bytes q c)))
   :hints (("Goal" :in-theory (enable adt-pg-poolw)))))

(defthm adt-pg-cputs-is-poolw
  (implies (and (adt-pg-pokp q c) (natp (nth 3 c)) (adt-octetsp bytes)
                (<= (+ (nth 3 c) (len bytes)) (* q (nth 5 c))))
           (equal (adt-pg-cputs bytes q c)
                  (update-nth 3 (+ (nth 3 c) (len bytes)) (adt-pg-poolw (nth 3 c) bytes q c))))
  :hints (("Goal" :induct (adt-pg-cputs bytes q c)
           :in-theory (enable adt-pg-poolw adt-pg-cput))))

(in-theory (disable adt-pg-cput adt-pg-cputs))

; -----------------------------------------------------------------------------
; The put of a tree into row N at columns CI (offset) and CI+1 (length).

(defun adt-pg-put-tree (ci n x r q c)
  (declare (xargs :verify-guards nil))
  (let* ((o (nth 3 c))
         (c (adt-pg-cputs (fn-scc-program x) q c))
         (c (adt-pg-rput ci n o r c)))
    (adt-pg-rput (+ 1 ci) n (len (fn-scc-program x)) r c)))

; What an instance's walk and length are, in the library's terms.
(defthm adt-tree-program-of-repeat-0
  (equal (append (fn-scc-program x) (fn-scc-repeat 0 v)) (fn-scc-program x))
  :hints (("Goal" :in-theory (enable fn-scc-repeat))))

(defthm adt-tree-plen-0
  (equal (adt-tree-plen x 0) (len (fn-scc-program x))))

(local
 (defthm adt-pt-octet-listp-is-adt-octetsp
   (equal (fn-scc-octet-listp x) (adt-octetsp x))
   :hints (("Goal" :in-theory (enable adt-octetsp fn-scc-octet-listp fn-scc-octetp unsigned-byte-p)))))
(local
 (defthm adt-pt-program-octets
   (implies (fn-sccb-treep x) (adt-octetsp (fn-scc-program x)))
   :hints (("Goal" :use fn-sccb-treep-encodes-octets
            :in-theory (disable fn-sccb-treep fn-scc-program)))))

(defthm adt-pg-put-tree-is-put-field
  (implies (and (adt-pg-pokp q c) (natp (nth 3 c)) (fn-sccb-treep x)
                (<= (+ (nth 3 c) (len (fn-scc-program x))) (* q (nth 5 c))))
           (equal (adt-pg-put-tree ci n x r q c)
                  (adt-pg-put-field '(:octets) ci n (fn-scc-program x) r q c)))
  :hints (("Goal" :in-theory (enable adt-pg-put-field))))

; An octets put reads its kind only as an octets kind.
(local
 (defthm adt-pt-put-field-octets-kind
   (implies (and (adt-octets-kind-p k) (syntaxp (not (equal k ''(:octets)))))
            (equal (adt-pg-put-field k ci n v r q c)
                   (adt-pg-put-field '(:octets) ci n v r q c)))
   :hints (("Goal" :in-theory (enable adt-pg-put-field)))))

(in-theory (disable adt-pg-put-tree))

; -----------------------------------------------------------------------------
; A record with a MASK: a true entry marks a tree field (its value a tree,
; its put the walk), a nil entry any other field.

(defun adt-pg-tmask-enc (mask rec)
  (declare (xargs :verify-guards nil))
  (if (atom mask)
      nil
    (cons (if (car mask) (fn-scc-program (car rec)) (car rec))
          (adt-pg-tmask-enc (cdr mask) (cdr rec)))))

(defun adt-pg-tmask-okp (mask rec)
  (declare (xargs :verify-guards nil))
  (if (atom mask)
      t
    (and (or (not (car mask)) (fn-sccb-treep (car rec)))
         (adt-pg-tmask-okp (cdr mask) (cdr rec)))))

(defun adt-pg-tmask-kinds-okp (s mask)
  (declare (xargs :guard t))
  (if (atom s)
      (atom mask)
    (and (consp mask)
         (or (not (car mask)) (adt-octets-kind-p (car s)))
         (adt-pg-tmask-kinds-okp (cdr s) (cdr mask)))))

(defun adt-pg-append-fields-t (s mask ci n rec r q c)
  (declare (xargs :verify-guards nil))
  (if (atom s)
      c
    (adt-pg-append-fields-t (cdr s) (cdr mask) (+ (adt-kind-width (car s)) ci) n (cdr rec) r q
                            (if (car mask)
                                (adt-pg-put-tree ci n (car rec) r q c)
                              (adt-pg-put-field (car s) ci n (car rec) r q c)))))

(defthm adt-pg-append-fields-t-is-append-fields
  (implies (and (adt-pg-rokp (adt-ncols s0) r c) (adt-pg-pokp q c)
                (natp ci) (<= (+ ci (adt-ncols s)) (adt-ncols s0))
                (natp n) (< n (* r (nth 4 c))) (natp (nth 3 c))
                (adt-pg-tmask-kinds-okp s mask) (adt-pg-tmask-okp mask rec)
                (<= (+ (nth 3 c) (adt-rec-load s (adt-pg-tmask-enc mask rec))) (* q (nth 5 c))))
           (equal (adt-pg-append-fields-t s mask ci n rec r q c)
                  (adt-pg-append-fields s ci n (adt-pg-tmask-enc mask rec) r q c)))
  :hints (("Goal" :induct (adt-pg-append-fields-t s mask ci n rec r q c)
           :in-theory (e/d (adt-pg-append-fields adt-ncols adt-rec-load)
                           (adt-put-field adt-pg-append-fields-meaning)))))

(defun adt-pg-append-t-c (s mask rec r q d dp c)
  (declare (xargs :verify-guards nil))
  (let* ((c (adt-pg-append-room s (adt-pg-tmask-enc mask rec) r q d dp c))
         (n (nth 2 c)))
    (update-nth 2 (+ 1 n) (adt-pg-append-fields-t s mask 0 n rec r q c))))

(defthm adt-pg-append-t-c-is-append-c
  (implies (and (adt-pg-corr s r q c a) (consp s)
                (adt-pg-tmask-kinds-okp s mask) (adt-pg-tmask-okp mask rec))
           (equal (adt-pg-append-t-c s mask rec r q d dp c)
                  (adt-pg-append-c s (adt-pg-tmask-enc mask rec) r q d dp c)))
  :hints (("Goal" :in-theory (e/d (adt-pg-append-c adt-pg-append-at adt-pg-corr adt-pg-okp)
                                  (adt-pg-append-room-meaning adt-pg-append-room adt-pg-corr-count
                                   adt-pg-append-fields-t-is-append-fields))
           :do-not-induct t
           :use ((:instance adt-pg-append-room-meaning (rec (adt-pg-tmask-enc mask rec)))
                 (:instance adt-pg-corr-count
                            (c (adt-pg-append-room s (adt-pg-tmask-enc mask rec) r q d dp c)))
                 (:instance adt-pg-corr-fill-natp
                            (c (adt-pg-append-room s (adt-pg-tmask-enc mask rec) r q d dp c)))
                 (:instance adt-pg-append-fields-t-is-append-fields
                            (s0 s) (ci 0)
                            (c (adt-pg-append-room s (adt-pg-tmask-enc mask rec) r q d dp c))
                            (n (nth 2 (adt-pg-append-room s (adt-pg-tmask-enc mask rec) r q d dp c))))))))

(in-theory (disable adt-pg-append-fields-t adt-pg-append-t-c))
