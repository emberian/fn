; fn: the octet buffer, an abstract stobj (D27 boundary 6; the megaspike, D28).
;
; The logical model of every codec in this tree is an octet list.  At the
; host boundary the octets arrive as a byte array (a socket read, a file
; read) and leave as one, and today every call converts the array to a list
; (`fnn-octet-list', host/native/io.lisp) and every codec copies the list
; again at each split and append.  This book is the one place where a byte
; array is the executable and the octet list stays the logical view: an
; abstract stobj `fn-octets' whose logical value IS the octet list (the
; recognizer is `fn-cbor-octet-listp', the creator is nil) and whose
; executable is a resizable `(unsigned-byte 8)' array with a fill count.
;
; The correspondence is proved once, as the abstract stobj's obligations:
; `fn-octets$corr' says the array's first FILL cells, read in order, are the
; logical list.  Every export's {CORRESPONDENCE}, {PRESERVED} and {GUARD-THM}
; theorem is below; the ones ACL2 proved on this image are ordinary defthms,
; the ones deferred on the spike are `skip-proofs' with a `;; SPIKE:' mark,
; each stated exactly as the dev lane proves it.
;
; Exports (logic / exec):
;   fn-octets-len            (len st)                / the fill count
;   fn-octets-get i          (nth i st)              / one array read
;   fn-octets-append-octet o (append st (list o))    / one array write
;   fn-octets-put i o        (update-nth i o st)     / one array write
;   fn-octets-clear          nil                     / fill := 0
;   fn-octets-reserve n      st                      / grow the array to n
;   fn-octets-list           st                      / the list, consed once
;   fn-octets-from-list xs   xs                      / clear, then write xs
;   fn-octets-string         the string of st's codes / consed once
;
; The host fills the array from a byte vector in raw Lisp (`fnn-octets-fill',
; host/native/io.lisp): one `replace' after `fn-octets-reserve', then the
; fill count.  That write is the host boundary, at the same trust as
; `fnn-octet-list' handing a list to the core today: the host asserts that
; the logical value is the list of the bytes it wrote, and nothing else can
; reach the array.

(in-package "ACL2")
(include-book "cbor")

; -----------------------------------------------------------------------------
; The concrete stobj.

(defstobj fn-octets$c
  (fn-octets$c-buf :type (array (unsigned-byte 8) (0)) :initially 0 :resizable t)
  (fn-octets$c-fill :type (integer 0 *) :initially 0)
  :inline t)

; A cell of the array is an octet: the fact every guard below needs.
(defthm fn-oct-bufp-cell-is-octet
  (implies (and (fn-octets$c-bufp buf) (natp k) (< k (len buf)))
           (and (integerp (nth k buf))
                (<= 0 (nth k buf))
                (< (nth k buf) 256)))
  :rule-classes ((:rewrite :corollary
                  (implies (and (fn-octets$c-bufp buf) (natp k) (< k (len buf)))
                           (and (integerp (nth k buf)) (<= 0 (nth k buf)) (< (nth k buf) 256))))
                 (:rewrite :corollary
                  (implies (and (fn-octets$c-bufp buf) (natp k) (< k (len buf)))
                           (unsigned-byte-p 8 (nth k buf)))))
  :hints (("Goal" :in-theory (enable nth))))

(local
 (defthm fn-oct-len-of-resize-list
   (equal (len (resize-list lst n default)) (nfix n))
   :hints (("Goal" :induct (resize-list lst n default)))))

; buf[0..n) as a list, consed from the top down in a tail call (constant
; stack whatever the length; large-article, 2026-09-25).
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

; buf[i..n) as a list, the simple recursion the proofs reason with.
(defun fn-oct-buf-list-from (i n fn-octets$c)
  (declare (xargs :stobjs fn-octets$c
                  :guard (and (natp i) (natp n) (<= i n)
                              (<= n (fn-octets$c-buf-length fn-octets$c)))
                  :measure (nfix (- n i))))
  (if (or (not (natp i)) (not (natp n)) (<= n i))
      nil
    (cons (fn-octets$c-bufi i fn-octets$c)
          (fn-oct-buf-list-from (1+ i) n fn-octets$c))))

;; SPIKE: defers fn-oct-buf-list-down-is-from (the tail-recursive reader is
;; the simple recursion; by the split of buf[i..n) at its last cell).
(skip-proofs
 (defthm fn-oct-buf-list-down-is-from
   (implies (and (natp n) (true-listp acc))
            (equal (fn-oct-buf-list-down n acc fn-octets$c)
                   (append (fn-oct-buf-list-from 0 n fn-octets$c) acc)))))

(defun fn-oct-buf-chars-down (n acc fn-octets$c)
  (declare (xargs :stobjs fn-octets$c
                  :guard (and (natp n) (<= n (fn-octets$c-buf-length fn-octets$c))
                              (character-listp acc))
                  :measure (nfix n)))
  (if (zp n)
      acc
    (fn-oct-buf-chars-down (1- n)
                           (cons (code-char (fn-octets$c-bufi (1- n) fn-octets$c)) acc)
                           fn-octets$c)))

(defthm fn-oct-buf-chars-down-is-character-listp
  (implies (character-listp acc)
           (character-listp (fn-oct-buf-chars-down n acc fn-octets$c)))
  :hints (("Goal" :induct (fn-oct-buf-chars-down n acc fn-octets$c))))

(defun fn-oct-write-list (xs fn-octets$c)
  ; Append XS at the fill point, growing the array as needed.
  (declare (xargs :stobjs fn-octets$c
                  :guard (and (fn-cbor-octet-listp xs)
                              (<= (fn-octets$c-fill fn-octets$c)
                                  (fn-octets$c-buf-length fn-octets$c)))))
  (if (atom xs)
      fn-octets$c
    (let* ((n (fn-octets$c-fill fn-octets$c))
           (fn-octets$c (if (< n (fn-octets$c-buf-length fn-octets$c))
                            fn-octets$c
                          (resize-fn-octets$c-buf (max 1024 (* 2 n)) fn-octets$c)))
           (fn-octets$c (update-fn-octets$c-bufi n (car xs) fn-octets$c))
           (fn-octets$c (update-fn-octets$c-fill (1+ n) fn-octets$c)))
      (fn-oct-write-list (cdr xs) fn-octets$c))))

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

(defun fn-octets$c-from-list (xs fn-octets$c)
  (declare (xargs :stobjs fn-octets$c
                  :guard (and (fn-cbor-octet-listp xs) (fn-octets$c-wfp fn-octets$c))))
  (let ((fn-octets$c (fn-octets$c-clear fn-octets$c)))
    (fn-oct-write-list xs fn-octets$c)))

(defun fn-octets$c-string (fn-octets$c)
  (declare (xargs :stobjs fn-octets$c :guard (fn-octets$c-wfp fn-octets$c)))
  (coerce (fn-oct-buf-chars-down (fn-octets$c-fill fn-octets$c) nil fn-octets$c)
          'string))

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
  (equal (fn-oct-nth i xs) (nth i xs))
  :hints (("Goal" :in-theory (enable nth))))

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
           (equal (fn-oct-update i o xs) (update-nth i o xs)))
  :hints (("Goal" :in-theory (enable update-nth))))

; The shape facts a chain of writes needs: a write within range keeps the
; length and the domain, an append extends the length by one.
(defthm fn-oct-len-of-update
  (implies (and (natp i) (< i (len xs)))
           (equal (len (fn-oct-update i o xs)) (len xs))))

(defthm fn-oct-octet-listp-of-update
  (implies (and (fn-cbor-octet-listp xs) (fn-cbor-octetp o) (natp i) (< i (len xs)))
           (fn-cbor-octet-listp (fn-oct-update i o xs))))

(defthm fn-oct-len-of-snoc
  (equal (len (fn-oct-snoc xs o)) (1+ (len xs))))

(defthm fn-oct-octet-listp-of-snoc
  (implies (and (fn-cbor-octet-listp xs) (fn-cbor-octetp o))
           (fn-cbor-octet-listp (fn-oct-snoc xs o))))

(defun fn-oct-octets-chars (xs)
  ; The characters whose codes are XS (an octet that is not one reads as 0).
  (declare (xargs :guard t))
  (if (consp xs)
      (cons (code-char (if (fn-cbor-octetp (car xs)) (car xs) 0))
            (fn-oct-octets-chars (cdr xs)))
    nil))

(defthm fn-oct-octets-chars-is-character-listp
  (character-listp (fn-oct-octets-chars xs)))

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

(defun fn-octets$a-string (fn-octets$a)
  ; The string whose character codes are the octets, in order.
  (declare (xargs :guard t))
  (coerce (fn-oct-octets-chars fn-octets$a) 'string))

; -----------------------------------------------------------------------------
; The correspondence and its obligations.

(defun fn-octets$corr (fn-octets$c fn-octets$a)
  (declare (xargs :stobjs fn-octets$c :verify-guards nil))
  (and (fn-octets$cp fn-octets$c)
       (fn-cbor-octet-listp fn-octets$a)
       (fn-octets$c-wfp fn-octets$c)
       (equal (fn-oct-buf-list-from 0 (fn-octets$c-fill fn-octets$c) fn-octets$c)
              fn-octets$a)))

(local (in-theory (disable fn-octets$cp)))

;; SPIKE: defers the abstract stobj obligations below, each stated exactly as
;; ACL2's `defabsstobj-missing-events' prints it.  The dev lane proves them
;; from the four facts they need: `nth' of `fn-oct-buf-list-from' is `bufi'
;; within range; `fn-oct-buf-list-from' is unchanged by an `update-bufi' at
;; or past the range and by a `resize' that keeps the range; appending at the
;; fill point extends it by one; and the creator's array is empty.

(skip-proofs
 (progn
   (defthm create-fn-octets{correspondence} (fn-octets$corr (create-fn-octets$c) (create-fn-octets$a)) :rule-classes nil)
   (defthm create-fn-octets{preserved} (fn-octets$ap (create-fn-octets$a)) :rule-classes nil)
   (defthm fn-octets-len{correspondence} (implies (fn-octets$corr fn-octets$c fn-octets) (equal (fn-octets$c-len fn-octets$c) (fn-octets$a-len fn-octets))) :rule-classes nil)
   (defthm fn-octets-get{correspondence} (implies (and (fn-octets$corr fn-octets$c fn-octets) (natp i) (< i (fn-octets$a-len fn-octets))) (equal (fn-octets$c-get i fn-octets$c) (fn-octets$a-get i fn-octets))) :rule-classes nil)
   (defthm fn-octets-get{guard-thm} (implies (and (fn-octets$corr fn-octets$c fn-octets) (natp i) (< i (fn-octets$a-len fn-octets))) (and (natp i) (< i (fn-octets$c-fill fn-octets$c)) (fn-octets$c-wfp fn-octets$c))) :rule-classes nil)
   (defthm fn-octets-append-octet{correspondence} (implies (and (fn-octets$corr fn-octets$c fn-octets) (fn-cbor-octetp o)) (fn-octets$corr (fn-octets$c-append-octet o fn-octets$c) (fn-octets$a-append-octet o fn-octets))) :rule-classes nil)
   (defthm fn-octets-append-octet{guard-thm} (implies (and (fn-octets$corr fn-octets$c fn-octets) (fn-cbor-octetp o)) (and (fn-cbor-octetp o) (fn-octets$c-wfp fn-octets$c))) :rule-classes nil)
   (defthm fn-octets-append-octet{preserved} (implies (and (fn-octets$ap fn-octets) (fn-cbor-octetp o)) (fn-octets$ap (fn-octets$a-append-octet o fn-octets))) :rule-classes nil)
   (defthm fn-octets-put{correspondence} (implies (and (fn-octets$corr fn-octets$c fn-octets) (natp i) (< i (fn-octets$a-len fn-octets)) (fn-cbor-octetp o)) (fn-octets$corr (fn-octets$c-put i o fn-octets$c) (fn-octets$a-put i o fn-octets))) :rule-classes nil)
   (defthm fn-octets-put{guard-thm} (implies (and (fn-octets$corr fn-octets$c fn-octets) (natp i) (< i (fn-octets$a-len fn-octets)) (fn-cbor-octetp o)) (and (natp i) (< i (fn-octets$c-fill fn-octets$c)) (fn-cbor-octetp o) (fn-octets$c-wfp fn-octets$c))) :rule-classes nil)
   (defthm fn-octets-put{preserved} (implies (and (fn-octets$ap fn-octets) (natp i) (< i (fn-octets$a-len fn-octets)) (fn-cbor-octetp o)) (fn-octets$ap (fn-octets$a-put i o fn-octets))) :rule-classes nil)
   (defthm fn-octets-clear{correspondence} (implies (fn-octets$corr fn-octets$c fn-octets) (fn-octets$corr (fn-octets$c-clear fn-octets$c) (fn-octets$a-clear fn-octets))) :rule-classes nil)
   (defthm fn-octets-clear{preserved} (implies (fn-octets$ap fn-octets) (fn-octets$ap (fn-octets$a-clear fn-octets))) :rule-classes nil)
   (defthm fn-octets-reserve{correspondence} (implies (and (fn-octets$corr fn-octets$c fn-octets) (natp n)) (fn-octets$corr (fn-octets$c-reserve n fn-octets$c) (fn-octets$a-reserve n fn-octets))) :rule-classes nil)
   (defthm fn-octets-reserve{preserved} (implies (and (fn-octets$ap fn-octets) (natp n)) (fn-octets$ap (fn-octets$a-reserve n fn-octets))) :rule-classes nil)
   (defthm fn-octets-list{correspondence} (implies (fn-octets$corr fn-octets$c fn-octets) (equal (fn-octets$c-list fn-octets$c) (fn-octets$a-list fn-octets))) :rule-classes nil)
   (defthm fn-octets-list{guard-thm} (implies (fn-octets$corr fn-octets$c fn-octets) (fn-octets$c-wfp fn-octets$c)) :rule-classes nil)
   (defthm fn-octets-from-list{correspondence} (implies (and (fn-octets$corr fn-octets$c fn-octets) (fn-cbor-octet-listp xs)) (fn-octets$corr (fn-octets$c-from-list xs fn-octets$c) (fn-octets$a-from-list xs fn-octets))) :rule-classes nil)
   (defthm fn-octets-from-list{guard-thm} (implies (and (fn-octets$corr fn-octets$c fn-octets) (fn-cbor-octet-listp xs)) (and (fn-cbor-octet-listp xs) (fn-octets$c-wfp fn-octets$c))) :rule-classes nil)
   (defthm fn-octets-from-list{preserved} (implies (and (fn-octets$ap fn-octets) (fn-cbor-octet-listp xs)) (fn-octets$ap (fn-octets$a-from-list xs fn-octets))) :rule-classes nil)
   (defthm fn-octets-string{correspondence} (implies (fn-octets$corr fn-octets$c fn-octets) (equal (fn-octets$c-string fn-octets$c) (fn-octets$a-string fn-octets))) :rule-classes nil)
   (defthm fn-octets-string{guard-thm} (implies (fn-octets$corr fn-octets$c fn-octets) (fn-octets$c-wfp fn-octets$c)) :rule-classes nil)))

(defabsstobj fn-octets
  :foundation fn-octets$c
  :recognizer (fn-octets-p :logic fn-octets$ap :exec fn-octets$cp)
  :creator (create-fn-octets :logic create-fn-octets$a :exec create-fn-octets$c)
  :corr-fn fn-octets$corr
  :exports ((fn-octets-len :logic fn-octets$a-len :exec fn-octets$c-len)
            (fn-octets-get :logic fn-octets$a-get :exec fn-octets$c-get)
            (fn-octets-append-octet :logic fn-octets$a-append-octet
                                    :exec fn-octets$c-append-octet :protect t)
            (fn-octets-put :logic fn-octets$a-put :exec fn-octets$c-put :protect t)
            (fn-octets-clear :logic fn-octets$a-clear :exec fn-octets$c-clear)
            (fn-octets-reserve :logic fn-octets$a-reserve :exec fn-octets$c-reserve
                               :protect t)
            (fn-octets-list :logic fn-octets$a-list :exec fn-octets$c-list)
            (fn-octets-from-list :logic fn-octets$a-from-list
                                 :exec fn-octets$c-from-list :protect t)
            (fn-octets-string :logic fn-octets$a-string :exec fn-octets$c-string)))

; A cell of the logical list is an octet: the fact every derived guard needs.
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

; -----------------------------------------------------------------------------
; Derived readers over the abstract stobj.  These are the vocabulary the
; codec twins use; each is stated over the logical list, so a twin's
; correspondence theorem reasons with `nth', `len' and `take'.

(defun fn-oct-slice-list (i n fn-octets)
  ; (take (- n i) (nthcdr i st)) consed from the top down.
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (natp n) (<= i n) (<= n (fn-octets-len fn-octets)))
                  :measure (nfix (- n i))))
  (if (or (not (natp i)) (not (natp n)) (<= n i))
      nil
    (cons (fn-octets-get i fn-octets)
          (fn-oct-slice-list (1+ i) n fn-octets))))

(defun fn-oct-slice-list-down (i n acc fn-octets)
  ; The tail-recursive twin: st[i..n) consed onto ACC.
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (natp n) (<= i n) (<= n (fn-octets-len fn-octets))
                              (true-listp acc))
                  :measure (nfix (- n i))))
  (if (or (not (natp i)) (not (natp n)) (<= n i))
      acc
    (fn-oct-slice-list-down i (1- n) (cons (fn-octets-get (1- n) fn-octets) acc)
                            fn-octets)))

(defun fn-oct-slice-chars-down (i n acc fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (natp n) (<= i n) (<= n (fn-octets-len fn-octets))
                              (character-listp acc))
                  :measure (nfix (- n i))))
  (if (or (not (natp i)) (not (natp n)) (<= n i))
      acc
    (fn-oct-slice-chars-down i (1- n)
                             (cons (code-char (fn-octets-get (1- n) fn-octets)) acc)
                             fn-octets)))

(defthm fn-oct-slice-chars-down-is-character-listp
  (implies (character-listp acc)
           (character-listp (fn-oct-slice-chars-down i n acc fn-octets)))
  :hints (("Goal" :induct (fn-oct-slice-chars-down i n acc fn-octets))))

(defun fn-oct-slice-string (i n fn-octets)
  ; st[i..n) as a string of character codes.
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (natp n) (<= i n) (<= n (fn-octets-len fn-octets)))))
  (coerce (fn-oct-slice-chars-down i n nil fn-octets) 'string))

(defun fn-oct-append-list (xs fn-octets)
  ; Append an octet list to the buffer, one write per octet, no copy.
  (declare (xargs :stobjs fn-octets :guard (fn-cbor-octet-listp xs)))
  (if (atom xs)
      fn-octets
    (let ((fn-octets (fn-octets-append-octet (car xs) fn-octets)))
      (fn-oct-append-list (cdr xs) fn-octets))))

(defun fn-oct-append-string-from (i s fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (stringp s) (natp i) (<= i (length s)))
                  :measure (nfix (- (length s) i))))
  (if (or (not (natp i)) (not (stringp s)) (<= (length s) i))
      fn-octets
    (let ((fn-octets (fn-octets-append-octet (char-code (char s i)) fn-octets)))
      (fn-oct-append-string-from (1+ i) s fn-octets))))

(defun fn-oct-string-octets-from (i s)
  ; The character codes of S from index I: the list the string denotes.
  (declare (xargs :guard (and (stringp s) (natp i) (<= i (length s)))
                  :measure (nfix (- (length s) i))))
  (if (or (not (natp i)) (not (stringp s)) (<= (length s) i))
      nil
    (cons (char-code (char s i)) (fn-oct-string-octets-from (1+ i) s))))

(defun fn-oct-append-string (s fn-octets)
  ; Append a string's character codes to the buffer, read in place.
  (declare (xargs :stobjs fn-octets :guard (stringp s)))
  (fn-oct-append-string-from 0 s fn-octets))

(defun fn-oct-prefix-equalp (i xs fn-octets)
  ; Whether st[i..i+len xs) is XS, read in place.
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (fn-cbor-octet-listp xs)
                              (<= (+ i (len xs)) (fn-octets-len fn-octets)))
                  :measure (len xs)))
  (if (atom xs)
      t
    (if (not (equal (fn-octets-get i fn-octets) (car xs)))
        nil
      (fn-oct-prefix-equalp (1+ i) (cdr xs) fn-octets))))

;; SPIKE: defers the five vocabulary theorems below (each derived reader is
;; its `take'/`nthcdr'/`append' term over the logical list); the dev lane
;; proves them from the take-of-nthcdr identity.
; The correspondence of the derived readers to the list vocabulary.
(skip-proofs
 (progn
(defthm fn-oct-slice-list-is-take-nthcdr
  (implies (and (natp i) (natp n) (<= i n) (<= n (len (fn-octets-list fn-octets))))
           (equal (fn-oct-slice-list i n fn-octets)
                  (take (- n i) (nthcdr i (fn-octets-list fn-octets)))))
  :hints (("Goal" :induct (fn-oct-slice-list i n fn-octets)
           :in-theory (enable nth nthcdr))))

(defthm fn-oct-slice-list-down-is-slice-list
  (implies (and (natp i) (natp n) (<= i n) (true-listp acc))
           (equal (fn-oct-slice-list-down i n acc fn-octets)
                  (append (fn-oct-slice-list i n fn-octets) acc)))
  :hints (("Goal" :induct (fn-oct-slice-list-down i n acc fn-octets))))

(defthm fn-oct-append-list-is-append
  (implies (fn-cbor-octet-listp xs)
           (equal (fn-octets-list (fn-oct-append-list xs fn-octets))
                  (append (fn-octets-list fn-octets) xs)))
  :hints (("Goal" :induct (fn-oct-append-list xs fn-octets))))

(defthm fn-oct-append-string-from-is-append
  (implies (and (stringp s) (natp i) (<= i (length s)))
           (equal (fn-octets-list (fn-oct-append-string-from i s fn-octets))
                  (append (fn-octets-list fn-octets)
                          (fn-oct-string-octets-from i s))))
  :hints (("Goal" :induct (fn-oct-append-string-from i s fn-octets))))

(defthm fn-oct-prefix-equalp-is-equal
  (implies (and (natp i) (fn-cbor-octet-listp xs)
                (<= (+ i (len xs)) (len (fn-octets-list fn-octets))))
           (equal (fn-oct-prefix-equalp i xs fn-octets)
                  (equal (take (len xs) (nthcdr i (fn-octets-list fn-octets))) xs)))
  :hints (("Goal" :induct (fn-oct-prefix-equalp i xs fn-octets)
           :in-theory (enable nth nthcdr))))))
