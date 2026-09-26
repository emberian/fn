; The octet buffer's slices as the BP checkpoint reader uses them (lane
; bp-checkpoint-open): the tail-recursive slice builder and the facts that
; relate `fn-oct-slice-list' to `fn-frame-split', proved in a small world
; so that they stay cheap.  Prefix `fn-bpnrb-' (shared with
; books/bp-node-rotation-buffer.lisp, the reader).
(in-package "ACL2")
(include-book "octets-stobj")
(include-book "frame-octets")

; The slice is reasoned about as itself, never as take/nthcdr.
(local (in-theory (disable fn-oct-slice-list-is-take-nthcdr)))

; st[i..n) consed from the top down: tail-recursive, since a counted run in
; a checkpoint can be megabytes.
(defun fn-bpnrb-slice-acc (i n acc fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (natp n) (<= n (fn-octets-len fn-octets))
                              (true-listp acc))
                  :measure (nfix (- n i))))
  (if (or (not (natp i)) (not (natp n)) (<= n i))
      acc
    (fn-bpnrb-slice-acc i (1- n) (cons (fn-octets-get (1- n) fn-octets) acc)
                        fn-octets)))

(defthm fn-bpnrb-slice-consp
  (equal (consp (fn-oct-slice-list i n x))
         (and (natp i) (natp n) (< i n)))
  :hints (("Goal" :expand ((fn-oct-slice-list i n x)))))

(defthm fn-bpnrb-slice-car
  (implies (and (natp i) (natp n) (< i n))
           (equal (car (fn-oct-slice-list i n x)) (nth i x)))
  :hints (("Goal" :expand ((fn-oct-slice-list i n x)))))

(defthm fn-bpnrb-slice-cdr
  (implies (and (natp i) (natp n))
           (equal (cdr (fn-oct-slice-list i n x))
                  (fn-oct-slice-list (1+ i) n x)))
  :hints (("Goal" :expand ((fn-oct-slice-list i n x)
                           (fn-oct-slice-list (1+ i) n x)))))

(defthm fn-bpnrb-slice-true-listp
  (true-listp (fn-oct-slice-list i n x))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :induct (fn-oct-slice-list i n x)
           :in-theory (enable fn-oct-slice-list))))

(defthm fn-bpnrb-slice-len
  (implies (and (natp i) (natp n) (<= i n))
           (equal (len (fn-oct-slice-list i n x)) (- n i)))
  :hints (("Goal" :induct (fn-oct-slice-list i n x)
           :in-theory (enable fn-oct-slice-list))))

(defthm fn-bpnrb-slice-octets
  (implies (and (fn-cbor-octet-listp x) (natp n) (<= n (len x)))
           (fn-cbor-octet-listp (fn-oct-slice-list i n x)))
  :hints (("Goal" :induct (fn-oct-slice-list i n x)
           :in-theory (enable fn-oct-slice-list))))

(local
 (defthm fn-bpnrb-slice-snoc
   (implies (and (natp i) (natp n) (< i n))
            (equal (fn-oct-slice-list i n x)
                   (append (fn-oct-slice-list i (1- n) x) (list (nth (1- n) x)))))
   :rule-classes nil
   :hints (("Goal" :induct (fn-oct-slice-list i n x)
            :in-theory (enable fn-oct-slice-list)))))

(local
 (defthm fn-bpnrb-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

(defthm fn-bpnrb-slice-acc-is-slice
  (equal (fn-bpnrb-slice-acc i n acc x)
         (append (fn-oct-slice-list i n x) acc))
  :hints (("Goal" :induct (fn-bpnrb-slice-acc i n acc x))
          ("Subgoal *1/2" :use ((:instance fn-bpnrb-slice-snoc)))))

(local
 (defthm fn-bpnrb-slice-shift
   (implies (and (natp i) (natp n))
            (equal (fn-oct-slice-list (+ 1 i) (+ 1 n) (cons a x))
                   (fn-oct-slice-list i n x)))
   :hints (("Goal" :induct (fn-oct-slice-list i n x)
            :in-theory (enable fn-oct-slice-list)))))

; The whole buffer is its own slice.
(defthm fn-bpnrb-slice-all
  (implies (true-listp x)
           (equal (fn-oct-slice-list 0 (len x) x) x))
  :hints (("Goal" :induct (len x) :in-theory (disable fn-bpnrb-slice-shift))
          ("Subgoal *1/1" :expand ((fn-oct-slice-list 0 (len x) x)
                                    (fn-oct-slice-list 0 (+ 1 (len (cdr x))) x))
           :use ((:instance fn-bpnrb-slice-shift (a (car x)) (x (cdr x))
                            (i 0) (n (len (cdr x))))))))

; A frame split of a slice is two slices.
(local
 (defun fn-bpnrb-split-ind (k i)
   (declare (xargs :measure (nfix k)))
   (if (zp k) i (fn-bpnrb-split-ind (1- k) (1+ i)))))

(defthm fn-bpnrb-split-of-slice
  (implies (and (natp i) (natp n) (natp k) (<= i n))
           (equal (fn-frame-split k (fn-oct-slice-list i n x))
                  (if (<= (+ i k) n)
                      (cons (fn-oct-slice-list i (+ i k) x)
                            (fn-oct-slice-list (+ i k) n x))
                    nil)))
  :hints (("Goal" :induct (fn-bpnrb-split-ind k i)
           :in-theory (enable fn-frame-split))
          ("Subgoal *1/2" :expand ((fn-oct-slice-list i (+ i k) x)))))
