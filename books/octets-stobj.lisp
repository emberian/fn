; fn: the octet buffer, an abstract stobj (D27 boundary 6, wave B).
;
; The logical model of every codec in this tree is an octet list.  At the
; host boundary the octets are a byte array (a socket read, a file read),
; and today every call converts the array to a list (`fnn-octet-list',
; host/native/io.lisp).  This book is the one place where a byte array is
; the executable and the octet list stays the logical view: an abstract
; stobj `fn-octets' whose logical value IS the octet list (recognizer
; `fn-cbor-octet-listp', creator nil) and whose executable is a resizable
; `(unsigned-byte 8)' array with a fill count.
;
; The abstraction relation is `fn-octets$corr': the array's first FILL
; cells, read in order, are the logical list, the fill count is within the
; array, and the concrete object is well-formed.  It is established by the
; creator and preserved by every export, and every export's logical result
; equals the list-model operation on the abstraction: these are the
; {CORRESPONDENCE}, {PRESERVED} and {GUARD-THM} theorems below, each stated
; exactly as `defabsstobj-missing-events' prints it and proved before the
; `defabsstobj' event, which then admits them by name.  No `skip-proofs'.
;
; Exports (logic / exec):
;   fn-octets-len            (len st)                / the fill count
;   fn-octets-get i          (nth i st)              / one array read
;   fn-octets-put i o        (update-nth i o st)     / one array write
;   fn-octets-append-octet o (append st (list o))    / one array write
;   fn-octets-clear          nil                     / fill := 0
;   fn-octets-reserve n      st                      / grow the array to n
;   fn-octets-list           st                      / the list, consed once
;   fn-octets-from-list xs   xs                      / clear, then write xs
;
; The host fills the array from a byte vector in raw Lisp (`fnn-octets-fill',
; host/native/io.lisp): `fn-octets-reserve', one `replace', then the fill
; count.  That write is the host boundary, at the same trust as
; `fnn-octet-list' handing a list to the core today (A-HOST): the host
; asserts that the logical value is the list of the bytes it wrote, and
; nothing else can reach the array.
;
; Derived readers (`fn-oct-slice-list', `fn-oct-prefix-equalp',
; `fn-oct-suffix-equalp', `fn-oct-line-end') are the vocabulary a codec twin
; reads the buffer with; each is equal to its `take'/`nthcdr' term over the
; logical list, so a twin's boundary theorem reasons with the list model.

(in-package "ACL2")
(include-book "cbor")

; -----------------------------------------------------------------------------
; The concrete stobj.

(defstobj fn-octets$c
  (fn-octets$c-buf :type (array (unsigned-byte 8) (0)) :initially 0 :resizable t)
  (fn-octets$c-fill :type (integer 0 *) :initially 0)
  :inline t)

; -----------------------------------------------------------------------------
; The abstraction: buf[i..n) as a list, over the raw array list.  Every
; lemma the obligations need is a lemma about this function on lists.

(defun fn-oct-list-from (i n buf)
  (declare (xargs :guard (and (natp i) (natp n) (true-listp buf))
                  :measure (nfix (- n i))))
  (if (or (not (natp i)) (not (natp n)) (<= n i))
      nil
    (cons (nth i buf) (fn-oct-list-from (1+ i) n buf))))

(defthm fn-oct-len-of-list-from
  (equal (len (fn-oct-list-from i n buf))
         (if (and (natp i) (natp n) (< i n)) (- n i) 0)))

(defthm fn-oct-true-listp-of-list-from
  (true-listp (fn-oct-list-from i n buf)))

(local
 (defun fn-oct-ind-ik (i k n buf)
   (declare (xargs :measure (nfix (- n i))))
   (if (or (not (natp i)) (not (natp n)) (<= n i))
       (list i k buf)
     (fn-oct-ind-ik (1+ i) (1- k) n buf))))

(defthm fn-oct-nth-of-list-from
  (implies (and (natp i) (natp n) (natp k) (< (+ i k) n))
           (equal (nth k (fn-oct-list-from i n buf))
                  (nth (+ i k) buf)))
  :hints (("Goal" :induct (fn-oct-ind-ik i k n buf))))

(defthm fn-oct-list-from-empty
  (implies (and (natp i) (natp n) (<= n i))
           (equal (fn-oct-list-from i n buf) nil)))

; The split of buf[i..n+1) at its last cell.  Not a rewrite rule: as one it
; would unroll every constant range.
(defthm fn-oct-list-from-snoc
  (implies (and (natp i) (natp n) (<= i n))
           (equal (fn-oct-list-from i (1+ n) buf)
                  (append (fn-oct-list-from i n buf) (list (nth n buf)))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-oct-list-from i n buf))))

(defthm fn-oct-list-from-of-update-nth-outside
  (implies (and (natp j) (natp n) (or (< j (nfix i)) (<= n j)))
           (equal (fn-oct-list-from i n (update-nth j v buf))
                  (fn-oct-list-from i n buf))))

(defthm fn-oct-list-from-of-update-nth-inside
  (implies (and (natp i) (natp j) (natp n) (<= i j) (< j n))
           (equal (fn-oct-list-from i n (update-nth j v buf))
                  (update-nth (- j i) v (fn-oct-list-from i n buf)))))

(defthm fn-oct-len-of-resize-list
  (equal (len (resize-list buf m d)) (nfix m)))

(local
 (defun fn-oct-ind-resize (k m buf)
   (if (zp m)
       (list k buf)
     (fn-oct-ind-resize (1- k) (1- m) (if (consp buf) (cdr buf) buf)))))

(defthm fn-oct-nth-of-resize-list
  (implies (and (natp k) (< k (nfix m)) (< k (len buf)))
           (equal (nth k (resize-list buf m d)) (nth k buf)))
  :hints (("Goal" :induct (fn-oct-ind-resize k m buf))))

(defthm fn-oct-list-from-of-resize-list
  (implies (and (natp n) (<= n (len buf)) (<= n (nfix m)))
           (equal (fn-oct-list-from i n (resize-list buf m d))
                  (fn-oct-list-from i n buf))))

; The array recognizer: a cell within the array is an octet, and writes of
; octets and resizes keep it.

(defthm fn-oct-bufp-cell-is-octet
  (implies (and (fn-octets$c-bufp buf) (natp k) (< k (len buf)))
           (and (integerp (nth k buf))
                (<= 0 (nth k buf))
                (< (nth k buf) 256)))
  :rule-classes ((:rewrite :corollary
                  (implies (and (fn-octets$c-bufp buf) (natp k) (< k (len buf)))
                           (and (integerp (nth k buf))
                                (<= 0 (nth k buf))
                                (< (nth k buf) 256))))
                 (:rewrite :corollary
                  (implies (and (fn-octets$c-bufp buf) (natp k) (< k (len buf)))
                           (fn-cbor-octetp (nth k buf))))
                 (:rewrite :corollary
                  (implies (and (fn-octets$c-bufp buf) (natp k) (< k (len buf)))
                           (unsigned-byte-p 8 (nth k buf))))))

(defthm fn-oct-bufp-true-listp
  (implies (fn-octets$c-bufp buf) (true-listp buf)))

(defthm fn-oct-bufp-of-update-nth
  (implies (and (fn-octets$c-bufp buf) (natp k) (< k (len buf))
                (unsigned-byte-p 8 v))
           (fn-octets$c-bufp (update-nth k v buf))))

(defthm fn-oct-bufp-of-resize-list
  (implies (fn-octets$c-bufp buf)
           (fn-octets$c-bufp (resize-list buf m 0))))

(defthm fn-oct-octet-listp-of-list-from
  (implies (and (fn-octets$c-bufp buf) (natp n) (<= n (len buf)))
           (fn-cbor-octet-listp (fn-oct-list-from i n buf))))

; The abstraction stays closed from here on: opened at the constant index 0
; it turns into a cons no lemma above is about.
(local (in-theory (disable fn-oct-list-from)))

; -----------------------------------------------------------------------------
; The executable readers: buf[0..n) consed from the top down in a tail call
; (constant stack whatever the length; large-article, 2026-09-25).

(defun fn-oct-buf-list-down (n acc fn-octets$c)
  (declare (xargs :stobjs fn-octets$c
                  :guard (and (natp n) (<= n (fn-octets$c-buf-length fn-octets$c))
                              (true-listp acc))
                  :measure (nfix n)))
  (if (zp n)
      acc
    (fn-oct-buf-list-down (1- n)
                          (cons (fn-octets$c-bufi (1- n) fn-octets$c) acc)
                          fn-octets$c)))

(local
 (defthm fn-oct-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

(defthm fn-oct-buf-list-down-is-list-from
  (implies (and (natp n) (true-listp acc))
           (equal (fn-oct-buf-list-down n acc fn-octets$c)
                  (append (fn-oct-list-from 0 n (nth 0 fn-octets$c)) acc)))
  :hints (("Goal" :induct (fn-oct-buf-list-down n acc fn-octets$c)
           :in-theory (disable fn-oct-list-from))
          ("Subgoal *1/2" :use ((:instance fn-oct-list-from-snoc
                                           (i 0) (n (1- n)) (buf (nth 0 fn-octets$c)))))))

; -----------------------------------------------------------------------------
; The exec functions, one per export.

(defun fn-octets$c-wfp (fn-octets$c)
  ; The concrete invariant: the fill count is within the array.
  (declare (xargs :stobjs fn-octets$c))
  (<= (fn-octets$c-fill fn-octets$c) (fn-octets$c-buf-length fn-octets$c)))

(defun fn-octets$c-len (fn-octets$c)
  (declare (xargs :stobjs fn-octets$c))
  (fn-octets$c-fill fn-octets$c))

(defun fn-octets$c-get (i fn-octets$c)
  (declare (xargs :stobjs fn-octets$c
                  :guard (and (natp i) (< i (fn-octets$c-fill fn-octets$c))
                              (fn-octets$c-wfp fn-octets$c))))
  (fn-octets$c-bufi i fn-octets$c))

(defun fn-octets$c-append-octet (o fn-octets$c)
  (declare (xargs :stobjs fn-octets$c
                  :guard (and (fn-cbor-octetp o) (fn-octets$c-wfp fn-octets$c))))
  (let* ((n (fn-octets$c-fill fn-octets$c))
         (fn-octets$c (if (< n (fn-octets$c-buf-length fn-octets$c))
                          fn-octets$c
                        (resize-fn-octets$c-buf (max 1024 (* 2 n)) fn-octets$c)))
         (fn-octets$c (update-fn-octets$c-bufi n o fn-octets$c)))
    (update-fn-octets$c-fill (1+ n) fn-octets$c)))

(defun fn-octets$c-put (i o fn-octets$c)
  (declare (xargs :stobjs fn-octets$c
                  :guard (and (natp i) (< i (fn-octets$c-fill fn-octets$c))
                              (fn-cbor-octetp o) (fn-octets$c-wfp fn-octets$c))))
  (update-fn-octets$c-bufi i o fn-octets$c))

(defun fn-octets$c-clear (fn-octets$c)
  (declare (xargs :stobjs fn-octets$c))
  (update-fn-octets$c-fill 0 fn-octets$c))

(defun fn-octets$c-reserve (n fn-octets$c)
  ; Grow the array so that N octets fit; the contents and the fill count
  ; are unchanged.  The host calls this before its raw fill.
  (declare (xargs :stobjs fn-octets$c :guard (natp n)))
  (if (<= n (fn-octets$c-buf-length fn-octets$c))
      fn-octets$c
    (resize-fn-octets$c-buf n fn-octets$c)))

(defun fn-octets$c-list (fn-octets$c)
  (declare (xargs :stobjs fn-octets$c :guard (fn-octets$c-wfp fn-octets$c)))
  (fn-oct-buf-list-down (fn-octets$c-fill fn-octets$c) nil fn-octets$c))

(defun fn-oct-write-list (xs fn-octets$c)
  ; Append XS at the fill point, one write per octet.
  (declare (xargs :stobjs fn-octets$c
                  :guard (and (fn-cbor-octet-listp xs) (fn-octets$c-wfp fn-octets$c))))
  (if (atom xs)
      fn-octets$c
    (let ((fn-octets$c (fn-octets$c-append-octet (car xs) fn-octets$c)))
      (fn-oct-write-list (cdr xs) fn-octets$c))))

(defun fn-octets$c-from-list (xs fn-octets$c)
  (declare (xargs :stobjs fn-octets$c
                  :guard (and (fn-cbor-octet-listp xs) (fn-octets$c-wfp fn-octets$c))))
  (let ((fn-octets$c (fn-octets$c-clear fn-octets$c)))
    (fn-oct-write-list xs fn-octets$c)))

; -----------------------------------------------------------------------------
; The logical side: the octet list itself.  The :logic functions never run
; (the exec twins do), so each is written over guard-free list helpers that
; equal `nth', `append' and `update-nth' on true lists, which every value of
; the stobj is (its recognizer is `fn-cbor-octet-listp').

(defun fn-oct-nth (i xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (if (or (not (natp i)) (= i 0)) (car xs) (fn-oct-nth (1- i) (cdr xs)))
    nil))

(defthm fn-oct-nth-is-nth
  (equal (fn-oct-nth i xs) (nth i xs)))

(defun fn-oct-snoc (xs o)
  (declare (xargs :guard t))
  (if (consp xs)
      (cons (car xs) (fn-oct-snoc (cdr xs) o))
    (list o)))

(defthm fn-oct-snoc-is-append
  (implies (true-listp xs)
           (equal (fn-oct-snoc xs o) (append xs (list o)))))

(defun fn-oct-update (i o xs)
  (declare (xargs :guard t))
  (if (or (not (natp i)) (= i 0))
      (cons o (if (consp xs) (cdr xs) nil))
    (cons (if (consp xs) (car xs) nil)
          (fn-oct-update (1- i) o (if (consp xs) (cdr xs) nil)))))

(defthm fn-oct-update-is-update-nth
  (implies (and (natp i) (< i (len xs)) (true-listp xs))
           (equal (fn-oct-update i o xs) (update-nth i o xs))))

(defthm fn-oct-octet-listp-of-update-nth
  (implies (and (fn-cbor-octet-listp xs) (fn-cbor-octetp o) (natp i) (< i (len xs)))
           (fn-cbor-octet-listp (update-nth i o xs))))

(defthm fn-oct-octet-listp-of-append-one
  (implies (and (fn-cbor-octet-listp xs) (fn-cbor-octetp o))
           (fn-cbor-octet-listp (append xs (list o)))))

(defun fn-octets$ap (x)
  (declare (xargs :guard t))
  (fn-cbor-octet-listp x))

(defun create-fn-octets$a ()
  (declare (xargs :guard t))
  nil)

(defun fn-octets$a-len (fn-octets$a)
  (declare (xargs :guard t))
  (len fn-octets$a))

(defun fn-octets$a-get (i fn-octets$a)
  (declare (xargs :guard (and (natp i) (< i (fn-octets$a-len fn-octets$a)))))
  (fn-oct-nth i fn-octets$a))

(defun fn-octets$a-put (i o fn-octets$a)
  (declare (xargs :guard (and (natp i) (< i (fn-octets$a-len fn-octets$a))
                              (fn-cbor-octetp o))))
  (fn-oct-update i o fn-octets$a))

(defun fn-octets$a-append-octet (o fn-octets$a)
  (declare (xargs :guard (fn-cbor-octetp o)))
  (fn-oct-snoc fn-octets$a o))

(defun fn-octets$a-clear (fn-octets$a)
  (declare (xargs :guard t) (ignore fn-octets$a))
  nil)

(defun fn-octets$a-reserve (n fn-octets$a)
  (declare (xargs :guard (natp n)) (ignore n))
  fn-octets$a)

(defun fn-octets$a-list (fn-octets$a)
  (declare (xargs :guard t))
  fn-octets$a)

(defun fn-octets$a-from-list (xs fn-octets$a)
  (declare (xargs :guard (fn-cbor-octet-listp xs)) (ignore fn-octets$a))
  xs)

; -----------------------------------------------------------------------------
; The abstraction relation.

(defun fn-octets$corr (fn-octets$c fn-octets$a)
  ; The concrete object is an ordinary value here, so that its array can be
  ; read as the list it is.
  (declare (xargs :verify-guards nil))
  (and (fn-octets$cp fn-octets$c)
       (fn-cbor-octet-listp fn-octets$a)
       (<= (nth *fn-octets$c-fill* fn-octets$c) (len (nth *fn-octets$c-bufi* fn-octets$c)))
       (equal (fn-oct-list-from 0 (nth *fn-octets$c-fill* fn-octets$c)
                                (nth *fn-octets$c-bufi* fn-octets$c))
              fn-octets$a)))

; From here on `nth' and `update-nth' stay closed: opened at a constant
; index they turn the stobj into car/cdr/cons forms that no lemma is about
; (rep-sha256, 2026-09-25).  The built-in `nth-update-nth',
; `len-update-nth' and `true-listp-update-nth' read through the writers.
(local (in-theory (disable nth update-nth)))
(local (in-theory (enable update-nth-array)))

; What the concrete recognizer says about the two fields, and that the
; two writers and the resize keep it.

(defthm fn-oct-cp-fields
  (implies (fn-octets$cp fn-octets$c)
           (and (true-listp fn-octets$c)
                (equal (len fn-octets$c) 2)
                (fn-octets$c-bufp (nth 0 fn-octets$c))
                (integerp (nth 1 fn-octets$c))
                (<= 0 (nth 1 fn-octets$c))))
  :rule-classes ((:forward-chaining :trigger-terms ((fn-octets$cp fn-octets$c)))))

(defthm fn-oct-cp-of-update-buf
  ; Replacing the array by any well-formed array keeps the recognizer; the
  ; writes and the resize produce well-formed arrays by the list lemmas.
  (implies (and (fn-octets$cp fn-octets$c) (fn-octets$c-bufp buf))
           (fn-octets$cp (update-nth 0 buf fn-octets$c))))

(defthm fn-oct-cp-of-update-fill
  (implies (and (fn-octets$cp fn-octets$c) (natp n))
           (fn-octets$cp (update-nth 1 n fn-octets$c))))

(defthm fn-oct-octetp-is-unsigned-byte-p
  (implies (fn-cbor-octetp o) (unsigned-byte-p 8 o)))

(local (in-theory (disable fn-octets$cp)))

; One append at the fill point: the abstraction extends by one, the
; concrete invariant is kept.  The lemma every chain of writes uses.

(defthm fn-oct-append-octet-step
  (implies (and (fn-octets$cp fn-octets$c)
                (<= (nth 1 fn-octets$c) (len (nth 0 fn-octets$c)))
                (fn-cbor-octetp o))
           (let ((next (fn-octets$c-append-octet o fn-octets$c)))
             (and (fn-octets$cp next)
                  (<= (nth 1 next) (len (nth 0 next)))
                  (equal (fn-oct-list-from 0 (nth 1 next) (nth 0 next))
                         (append (fn-oct-list-from 0 (nth 1 fn-octets$c) (nth 0 fn-octets$c))
                                 (list o))))))
  :hints (("Goal" :use ((:instance fn-oct-list-from-snoc
                                   (i 0) (n (nth 1 fn-octets$c))
                                   (buf (update-nth (nth 1 fn-octets$c) o (nth 0 fn-octets$c))))
                        (:instance fn-oct-list-from-snoc
                                   (i 0) (n (nth 1 fn-octets$c))
                                   (buf (update-nth (nth 1 fn-octets$c) o
                                                    (resize-list (nth 0 fn-octets$c)
                                                                 (max 1024 (* 2 (nth 1 fn-octets$c)))
                                                                 0))))))))

(local (in-theory (disable fn-octets$c-append-octet)))

(defthm fn-oct-write-list-steps
  (implies (and (fn-octets$cp fn-octets$c)
                (<= (nth 1 fn-octets$c) (len (nth 0 fn-octets$c)))
                (fn-cbor-octet-listp xs))
           (let ((next (fn-oct-write-list xs fn-octets$c)))
             (and (fn-octets$cp next)
                  (<= (nth 1 next) (len (nth 0 next)))
                  (equal (fn-oct-list-from 0 (nth 1 next) (nth 0 next))
                         (append (fn-oct-list-from 0 (nth 1 fn-octets$c) (nth 0 fn-octets$c))
                                 xs)))))
  :hints (("Goal" :induct (fn-oct-write-list xs fn-octets$c)
           :in-theory (disable fn-oct-list-from))))

; -----------------------------------------------------------------------------
; The obligations, each as `defabsstobj-missing-events' states it.

(defthm create-fn-octets{correspondence}
  (fn-octets$corr (create-fn-octets$c) (create-fn-octets$a))
  :rule-classes nil)

(defthm create-fn-octets{preserved}
  (fn-octets$ap (create-fn-octets$a))
  :rule-classes nil)

(defthm fn-octets-len{correspondence}
  (implies (fn-octets$corr fn-octets$c fn-octets)
           (equal (fn-octets$c-len fn-octets$c) (fn-octets$a-len fn-octets)))
  :rule-classes nil)

(defthm fn-octets-get{correspondence}
  (implies (and (fn-octets$corr fn-octets$c fn-octets)
                (natp i) (< i (fn-octets$a-len fn-octets)))
           (equal (fn-octets$c-get i fn-octets$c) (fn-octets$a-get i fn-octets)))
  :rule-classes nil)

(defthm fn-octets-get{guard-thm}
  (implies (and (fn-octets$corr fn-octets$c fn-octets)
                (natp i) (< i (fn-octets$a-len fn-octets)))
           (and (natp i) (< i (fn-octets$c-fill fn-octets$c))
                (fn-octets$c-wfp fn-octets$c)))
  :rule-classes nil)

(defthm fn-octets-put{correspondence}
  (implies (and (fn-octets$corr fn-octets$c fn-octets)
                (natp i) (< i (fn-octets$a-len fn-octets)) (fn-cbor-octetp o))
           (fn-octets$corr (fn-octets$c-put i o fn-octets$c)
                           (fn-octets$a-put i o fn-octets)))
  :rule-classes nil)

(defthm fn-octets-put{guard-thm}
  (implies (and (fn-octets$corr fn-octets$c fn-octets)
                (natp i) (< i (fn-octets$a-len fn-octets)) (fn-cbor-octetp o))
           (and (natp i) (< i (fn-octets$c-fill fn-octets$c))
                (fn-cbor-octetp o) (fn-octets$c-wfp fn-octets$c)))
  :rule-classes nil)

(defthm fn-octets-put{preserved}
  (implies (and (fn-octets$ap fn-octets)
                (natp i) (< i (fn-octets$a-len fn-octets)) (fn-cbor-octetp o))
           (fn-octets$ap (fn-octets$a-put i o fn-octets)))
  :rule-classes nil)

(defthm fn-octets-append-octet{correspondence}
  (implies (and (fn-octets$corr fn-octets$c fn-octets) (fn-cbor-octetp o))
           (fn-octets$corr (fn-octets$c-append-octet o fn-octets$c)
                           (fn-octets$a-append-octet o fn-octets)))
  :rule-classes nil)

(defthm fn-octets-append-octet{guard-thm}
  (implies (and (fn-octets$corr fn-octets$c fn-octets) (fn-cbor-octetp o))
           (and (fn-cbor-octetp o) (fn-octets$c-wfp fn-octets$c)))
  :rule-classes nil)

(defthm fn-octets-append-octet{preserved}
  (implies (and (fn-octets$ap fn-octets) (fn-cbor-octetp o))
           (fn-octets$ap (fn-octets$a-append-octet o fn-octets)))
  :rule-classes nil)

(defthm fn-octets-clear{correspondence}
  (implies (fn-octets$corr fn-octets$c fn-octets)
           (fn-octets$corr (fn-octets$c-clear fn-octets$c) (fn-octets$a-clear fn-octets)))
  :rule-classes nil)

(defthm fn-octets-clear{preserved}
  (implies (fn-octets$ap fn-octets)
           (fn-octets$ap (fn-octets$a-clear fn-octets)))
  :rule-classes nil)

(defthm fn-octets-reserve{correspondence}
  (implies (and (fn-octets$corr fn-octets$c fn-octets) (natp n))
           (fn-octets$corr (fn-octets$c-reserve n fn-octets$c)
                           (fn-octets$a-reserve n fn-octets)))
  :rule-classes nil)

(defthm fn-octets-reserve{preserved}
  (implies (and (fn-octets$ap fn-octets) (natp n))
           (fn-octets$ap (fn-octets$a-reserve n fn-octets)))
  :rule-classes nil)

(defthm fn-octets-list{correspondence}
  (implies (fn-octets$corr fn-octets$c fn-octets)
           (equal (fn-octets$c-list fn-octets$c) (fn-octets$a-list fn-octets)))
  :rule-classes nil)

(defthm fn-octets-list{guard-thm}
  (implies (fn-octets$corr fn-octets$c fn-octets)
           (fn-octets$c-wfp fn-octets$c))
  :rule-classes nil)

(defthm fn-octets-from-list{correspondence}
  (implies (and (fn-octets$corr fn-octets$c fn-octets) (fn-cbor-octet-listp xs))
           (fn-octets$corr (fn-octets$c-from-list xs fn-octets$c)
                           (fn-octets$a-from-list xs fn-octets)))
  :rule-classes nil)

(defthm fn-octets-from-list{guard-thm}
  (implies (and (fn-octets$corr fn-octets$c fn-octets) (fn-cbor-octet-listp xs))
           (and (fn-cbor-octet-listp xs) (fn-octets$c-wfp fn-octets$c)))
  :rule-classes nil)

(defthm fn-octets-from-list{preserved}
  (implies (and (fn-octets$ap fn-octets) (fn-cbor-octet-listp xs))
           (fn-octets$ap (fn-octets$a-from-list xs fn-octets)))
  :rule-classes nil)

(defabsstobj fn-octets
  :foundation fn-octets$c
  :recognizer (fn-octets-p :logic fn-octets$ap :exec fn-octets$cp)
  :creator (create-fn-octets :logic create-fn-octets$a :exec create-fn-octets$c)
  :corr-fn fn-octets$corr
  :exports ((fn-octets-len :logic fn-octets$a-len :exec fn-octets$c-len)
            (fn-octets-get :logic fn-octets$a-get :exec fn-octets$c-get)
            (fn-octets-put :logic fn-octets$a-put :exec fn-octets$c-put :protect t)
            (fn-octets-append-octet :logic fn-octets$a-append-octet
                                    :exec fn-octets$c-append-octet :protect t)
            (fn-octets-clear :logic fn-octets$a-clear :exec fn-octets$c-clear)
            (fn-octets-reserve :logic fn-octets$a-reserve :exec fn-octets$c-reserve
                               :protect t)
            (fn-octets-list :logic fn-octets$a-list :exec fn-octets$c-list)
            (fn-octets-from-list :logic fn-octets$a-from-list
                                 :exec fn-octets$c-from-list :protect t)))

; -----------------------------------------------------------------------------
; The logical view, opened: the stobj's value is the list, its length is
; `len', a read is `nth'.  A cell of the logical list is an octet.

(defthm fn-oct-octets-p-is-octet-listp
  (equal (fn-octets-p x) (fn-cbor-octet-listp x)))

(defthm fn-oct-len-is-len
  (equal (fn-octets-len fn-octets) (len fn-octets)))

(defthm fn-oct-get-is-nth
  (equal (fn-octets-get i fn-octets) (nth i fn-octets)))

(defthm fn-oct-list-is-identity
  (equal (fn-octets-list fn-octets) fn-octets))

(defthm fn-oct-nth-of-octet-listp-is-octet
  (implies (and (fn-cbor-octet-listp xs) (natp k) (< k (len xs)))
           (and (integerp (nth k xs))
                (<= 0 (nth k xs))
                (< (nth k xs) 256)))
  :rule-classes ((:rewrite :corollary
                  (implies (and (fn-cbor-octet-listp xs) (natp k) (< k (len xs)))
                           (and (integerp (nth k xs)) (<= 0 (nth k xs)) (< (nth k xs) 256))))
                 (:rewrite :corollary
                  (implies (and (fn-cbor-octet-listp xs) (natp k) (< k (len xs)))
                           (fn-cbor-octetp (nth k xs)))))
  :hints (("Goal" :in-theory (enable nth))))

; What a buffer value is, for every guard and theorem over the stobj.
(defthm fn-oct-octets-p-forward
  (implies (fn-octets-p x)
           (and (fn-cbor-octet-listp x) (true-listp x)))
  :rule-classes :forward-chaining)

(in-theory (disable fn-octets-p fn-octets-len fn-octets-get fn-octets-list
                    fn-oct-octets-p-is-octet-listp))

; -----------------------------------------------------------------------------
; Derived readers over the abstract stobj: the vocabulary a codec twin reads
; the buffer with.  Each is equal to its list term over the logical value.

(defun fn-oct-slice-list (i n fn-octets)
  ; st[i..n) as a list.
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (natp n) (<= i n) (<= n (fn-octets-len fn-octets)))
                  :measure (nfix (- n i))))
  (if (or (not (natp i)) (not (natp n)) (<= n i))
      nil
    (cons (fn-octets-get i fn-octets)
          (fn-oct-slice-list (1+ i) n fn-octets))))

(defun fn-oct-prefix-equalp (i xs fn-octets)
  ; Whether st[i..) opens with XS, read in place.  XS is any object.
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (<= i (fn-octets-len fn-octets)))
                  :measure (len xs)))
  (if (atom xs)
      t
    (and (< i (fn-octets-len fn-octets))
         (equal (fn-octets-get i fn-octets) (car xs))
         (fn-oct-prefix-equalp (1+ i) (cdr xs) fn-octets))))

(defun fn-oct-suffix-equalp (i xs fn-octets)
  ; Whether st[i..len) is exactly XS, read in place.  XS is any object: the
  ; walk is total over it, and a non-list answers nil at the buffer's end.
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (<= i (fn-octets-len fn-octets)))
                  :measure (nfix (- (fn-octets-len fn-octets) i))))
  (if (or (not (natp i)) (>= i (fn-octets-len fn-octets)))
      (null xs)
    (and (consp xs)
         (equal (fn-octets-get i fn-octets) (car xs))
         (fn-oct-suffix-equalp (1+ i) (cdr xs) fn-octets))))

(defun fn-oct-line-end (i fn-octets)
  ; The index just past the first LF at or after I, or the length.
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (<= i (fn-octets-len fn-octets)))
                  :measure (nfix (- (fn-octets-len fn-octets) i))))
  (if (or (not (natp i)) (>= i (fn-octets-len fn-octets)))
      (fn-octets-len fn-octets)
    (if (equal (fn-octets-get i fn-octets) 10)
        (1+ i)
      (fn-oct-line-end (1+ i) fn-octets))))

; The list facts the correspondences rest on.

(local
 (defthm fn-oct-nthcdr-of-true-listp
   (implies (true-listp xs) (true-listp (nthcdr i xs)))
   :hints (("Goal" :in-theory (enable nthcdr)))))

(local
 (defthm fn-oct-consp-nthcdr-within
   (implies (and (natp i) (true-listp xs) (< i (len xs)))
            (consp (nthcdr i xs)))
   :hints (("Goal" :in-theory (enable nthcdr)))))

(local
 (defthm fn-oct-consp-nthcdr-beyond
   (implies (and (natp i) (true-listp xs) (<= (len xs) i))
            (not (consp (nthcdr i xs))))
   :hints (("Goal" :in-theory (enable nthcdr)))))

(local
 (defthm fn-oct-nthcdr-beyond-is-nil
   (implies (and (natp i) (true-listp xs) (<= (len xs) i))
            (equal (nthcdr i xs) nil))
   :hints (("Goal" :in-theory (enable nthcdr)))))

(local
 (defthm fn-oct-car-nthcdr
   (equal (car (nthcdr i xs)) (nth i xs))
   :hints (("Goal" :in-theory (enable nth nthcdr)))))

(local
 (defthm fn-oct-cdr-nthcdr
   (implies (natp i)
            (equal (cdr (nthcdr i xs)) (nthcdr (1+ i) xs)))
   :hints (("Goal" :in-theory (enable nthcdr)))))

(local
 (defthm fn-oct-nthcdr-equal-split
   (implies (and (natp i) (< i (len l)) (true-listp l))
            (equal (equal (nthcdr i l) xs)
                   (and (consp xs) (equal (nth i l) (car xs))
                        (equal (nthcdr (1+ i) l) (cdr xs)))))
   :hints (("Goal" :in-theory (enable nth nthcdr)))))

(local (in-theory (disable nthcdr)))

(defthm fn-oct-slice-list-empty
  (implies (<= n i)
           (equal (fn-oct-slice-list i n fn-octets) nil)))

(defthm fn-oct-slice-list-is-take-nthcdr
  (implies (and (natp i) (natp n) (<= i n) (<= n (len fn-octets))
                (true-listp fn-octets))
           (equal (fn-oct-slice-list i n fn-octets)
                  (take (- n i) (nthcdr i fn-octets))))
  :hints (("Goal" :induct (fn-oct-slice-list i n fn-octets))))

; "L opens with XS", the list-model shape of a prefix test (the shape
; `fn-inj-strip' has).  Not `take': past the end `take' pads with nil, and
; a prefix holding nil would then match where the buffer has nothing.
(defun fn-oct-list-prefixp (xs l)
  (declare (xargs :guard t))
  (if (atom xs)
      t
    (and (consp l)
         (equal (car l) (car xs))
         (fn-oct-list-prefixp (cdr xs) (cdr l)))))

(defthm fn-oct-prefix-equalp-is-list-prefixp
  (implies (and (natp i) (true-listp fn-octets))
           (equal (fn-oct-prefix-equalp i xs fn-octets)
                  (fn-oct-list-prefixp xs (nthcdr i fn-octets))))
  :hints (("Goal" :induct (fn-oct-prefix-equalp i xs fn-octets))))

(defthm fn-oct-suffix-equalp-is-equal
  (implies (and (natp i) (true-listp fn-octets))
           (equal (fn-oct-suffix-equalp i xs fn-octets)
                  (equal (nthcdr i fn-octets) xs)))
  :hints (("Goal" :induct (fn-oct-suffix-equalp i xs fn-octets))))

(defthm fn-oct-line-end-bounds
  (implies (and (natp i) (<= i (len fn-octets)))
           (and (<= i (fn-oct-line-end i fn-octets))
                (<= (fn-oct-line-end i fn-octets) (len fn-octets))))
  ; The trigger is the walk itself, never `len': as a linear rule with
  ; `(len st)' among its trigger terms it would fire on every length with
  ; I free.
  :rule-classes ((:linear :trigger-terms ((fn-oct-line-end i fn-octets))))
  :hints (("Goal" :induct (fn-oct-line-end i fn-octets))))

(in-theory (disable fn-oct-slice-list fn-oct-prefix-equalp fn-oct-suffix-equalp
                    fn-oct-line-end))
