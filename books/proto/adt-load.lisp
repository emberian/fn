; fn prototype library: the pool's load (lane paged-catalog-4, 2026-10-01).
; Its own book, included by books/proto/adt.lisp (the generator) and not by
; adt-lib, whose includers reach the served image (proto/adt-bytes-lib ->
; history-pages): a write-once instance's theorems need it, nothing else does.

(in-package "ACL2")
(include-book "adt-lib")
(local (in-theory (disable nth update-nth)))
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
