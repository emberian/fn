; fn: the WALK of a TREE field of `def-representation' (lane
; paged-catalog-3, 2026-10-01; stage 3 of
; planning/design-store-representation-2026-10-01.md).  Instances include
; books/def-representation-tree.lisp, which includes this book and adds the
; paged instance's half; the writer over any put (`adt-h-tw-tree-is-puts',
; lane gate-b) is at the end of this book.
;
; An :octets field whose value is the postfix program of a tree
; (books/store-tree-codec.lisp, `fn-scc-program'; KEYSTONE
; fn-scc-decode-tree-of-encode) can be appended without the program ever
; existing as a list: the writer walks the tree and puts each octet into
; the pool at the fill.  Before it the catalog's commit built the program
; with the specification's nested `append' (26.5 KB consed for a 181-octet
; row remainder) and checked encodability with `fn-sccb-treep' (3.8 KB, the
; atoms' octet lists), 38 KB a commit in all (lane paged-catalog-2's
; measurement).
;
; This book is the instance-independent half:
;   * `adt-tree-okp', `fn-sccb-treep' without building an octet list
;     (`adt-tree-okp-is-sccb-treep');
;   * `adt-tree-plen', the program's length without the program
;     (`adt-tree-plen-is-len');
;   * the logical put (`adt-pool-put': one octet at the fill of the pool
;     at P, the fill advanced) and its fold (`adt-pool-puts'), which is the
;     library's push when the room is made first (`adt-pool-push-is-puts');
;   * the WRITER over a constrained put (`adt-g-put', constrained to be
;     `adt-pool-put' at `(adt-g-pp)'), whose meaning is the puts of the
;     program followed by N CONS operations (`adt-g-tw-tree-is-puts').
; `def-representation' emits each instance's writer with the instance's
; own put and obtains its meaning by functional instance of these
; theorems; nothing about the codec is proved per instance.

(in-package "ACL2")
(include-book "def-representation-lib")
(include-book "store-checkpoint-buffer")
(local (include-book "arithmetic/top" :dir :system))

; The codec (books/store-tree-codec.lisp) is opened in the hints of the
; proofs that read it, never in this book's scope (AGENTS.md; Codex r37 F3,
; r40 F1): `adt-tree-codec' names its definitions for those hints, and the
; three the included chain leaves enabled (fn-scc-octets-valuep,
; fn-scc-octetp, fn-scc-le-digits; r47 F6) are disabled here locally, so
; every member starts closed in this book.  The included books' own scopes
; (store-checkpoint-buffer's local enable) are theirs.
(local (deftheory adt-tree-codec
         '(fn-scc-program fn-scc-atom-octets fn-scc-atomp fn-scc-nat-octets
           fn-scc-nat-encodablep fn-scc-string-octets fn-scc-octets-valuep
           fn-scc-octet-listp fn-scc-octetp fn-sccb-treep fn-scc-le-digits)))
(local (in-theory (disable fn-scc-octets-valuep fn-scc-octetp fn-scc-le-digits)))

; -----------------------------------------------------------------------------
; Counts without lists.

; What an instance's digit writer needs for its measure and guards, in a
; book without arithmetic (exported: the instance is admitted there).
(defthm adt-tree-floor-256-decreases
  (implies (and (natp n) (not (zp n)))
           (< (floor n 256) n))
  :rule-classes (:rewrite :linear))

(defthm adt-tree-floor-256-natp
  (implies (natp n) (natp (floor n 256)))
  :rule-classes (:rewrite :type-prescription))

(defun adt-tree-ndig (n)
  ; (len (fn-scc-le-digits n)) without the digits.
  (declare (xargs :guard (natp n)))
  (if (zp n) 0 (+ 1 (adt-tree-ndig (floor n 256)))))

(defthm adt-tree-ndig-is-len-digits
  (equal (adt-tree-ndig n) (len (fn-scc-le-digits n)))
  :hints (("Goal" :in-theory (enable fn-scc-le-digits))))

(local
 (defthm adt-tree-len-chars-octets
   (equal (len (fn-scc-chars-octets chars)) (len chars))
   :hints (("Goal" :in-theory (enable fn-scc-chars-octets)))))

(local
 (defthm adt-tree-chars-octets-octets
   (fn-scc-octet-listp (fn-scc-chars-octets chars))
   :hints (("Goal" :in-theory (union-theories (theory 'adt-tree-codec) (enable fn-scc-chars-octets))))))

; An atom's encodability without its octets.
(defun adt-tree-atom-okp (x)
  (declare (xargs :guard t))
  (cond ((null x) t)
        ((natp x) (< (adt-tree-ndig x) 256))
        ((integerp x) (< (adt-tree-ndig (- -1 x)) 256))
        ((characterp x) t)
        ((stringp x) (< (adt-tree-ndig (length x)) 256))
        ((symbolp x) (and (fn-scc-package-index (symbol-package-name x))
                          (< (adt-tree-ndig (length (symbol-name x))) 256)))
        (t nil)))

(defun adt-tree-okp (x)
  (declare (xargs :guard t))
  (cond ((fn-scc-octets-valuep x) (< (adt-tree-ndig (len x)) 256))
        ((consp x) (and (adt-tree-okp (car x)) (adt-tree-okp (cdr x))))
        (t (adt-tree-atom-okp x))))

(local
 (defthm adt-tree-octet-listp-of-cons
   (equal (fn-scc-octet-listp (cons a b))
          (and (fn-scc-octetp a) (fn-scc-octet-listp b)))
  :hints (("Goal" :in-theory (union-theories (theory 'adt-tree-codec) (current-theory :here))))))

(local
 (defthm adt-tree-octet-listp-of-append
   (implies (true-listp a)
            (equal (fn-scc-octet-listp (append a b))
                   (and (fn-scc-octet-listp a) (fn-scc-octet-listp b))))))

;; The codec's octet facts the equivalence reads, each opened in its hint.
(local (defthm adt-tree-octetsp-le-digits
         (adt-octetsp (fn-scc-le-digits n))
         :hints (("Goal" :in-theory (enable fn-scc-le-digits adt-octetsp)))))
(local (defthm adt-tree-octetsp-append
         (implies (and (adt-octetsp a) (adt-octetsp b)) (adt-octetsp (append a b)))
         :hints (("Goal" :in-theory (enable adt-octetsp)))))
(local (defthm adt-tree-octetsp-chars-octets
         (adt-octetsp (fn-scc-chars-octets cs))
         :hints (("Goal" :in-theory (enable fn-scc-chars-octets adt-octetsp)))))

(defthm adt-tree-okp-is-sccb-treep
  (equal (adt-tree-okp x) (fn-sccb-treep x))
  :hints (("Goal" :in-theory (union-theories (theory 'adt-tree-codec) (current-theory :here)) :induct (adt-tree-okp x))))

; The program's length, along the cdr spine onto an accumulator.
(defun adt-tree-atom-plen (x)
  (declare (xargs :guard t))
  (cond ((null x) 1)
        ((natp x) (+ 2 (adt-tree-ndig x)))
        ((integerp x) (+ 2 (adt-tree-ndig (- -1 x))))
        ((characterp x) 2)
        ((stringp x) (+ 2 (adt-tree-ndig (length x)) (length x)))
        (t (let ((s (if (symbolp x) (symbol-name x) "")))
             (+ 3 (adt-tree-ndig (length s)) (length s))))))

(defun adt-tree-plen (x acc)
  (declare (xargs :guard (natp acc) :measure (acl2-count x) :verify-guards nil))
  (cond ((fn-scc-octets-valuep x) (+ acc 2 (adt-tree-ndig (len x)) (len x)))
        ((consp x) (adt-tree-plen (cdr x) (adt-tree-plen (car x) (+ 1 acc))))
        (t (+ acc (adt-tree-atom-plen x)))))

(local
 (defthm adt-tree-len-append
   (equal (len (append a b)) (+ (len a) (len b)))))

(defthm adt-tree-plen-is-len
  (implies (acl2-numberp acc)
           (equal (adt-tree-plen x acc) (+ acc (len (fn-scc-program x)))))
  :hints (("Goal" :in-theory (union-theories (theory 'adt-tree-codec) (current-theory :here)) :induct (adt-tree-plen x acc))))

(defthm adt-tree-plen-natp
  (implies (natp acc) (natp (adt-tree-plen x acc)))
  :rule-classes :type-prescription)

(verify-guards adt-tree-plen)

; -----------------------------------------------------------------------------
; The logical put and its fold.

(defun adt-pool-put (p b c)
  (declare (xargs :verify-guards nil))
  (let ((fl (nth (+ 2 p) c)))
    (update-nth (+ 2 p) (+ 1 fl) (update-nth-array p fl b c))))

(defun adt-pool-puts (p bytes c)
  (declare (xargs :verify-guards nil))
  (if (atom bytes) c (adt-pool-puts p (cdr bytes) (adt-pool-put p (car bytes) c))))

(defthm adt-pool-puts-of-append
  (equal (adt-pool-puts p (append a b) c)
         (adt-pool-puts p b (adt-pool-puts p a c))))

(defthm adt-pool-puts-of-cons
  (equal (adt-pool-puts p (cons b bytes) c)
         (adt-pool-puts p bytes (adt-pool-put p b c))))

(defthm adt-pool-puts-of-atom
  (implies (atom bytes) (equal (adt-pool-puts p bytes c) c)))

(in-theory (disable adt-pool-puts))

; The puts are the library's write loop at the fill, then the fill moved
; once: so the push (the room, then that) is the room then the puts.
(local
 (defthm adt-tree-update-nth-swap
   (implies (and (natp i) (natp j) (not (equal i j)))
            (equal (update-nth i x (update-nth j y l))
                   (update-nth j y (update-nth i x l))))
   :hints (("Goal" :in-theory (enable update-nth)))))

(local
 (defthm adt-tree-poolw-other
   (implies (and (natp p) (natp k) (not (equal k p)))
            (equal (nth k (adt-poolw p i bytes c)) (nth k c)))
   :hints (("Goal" :in-theory (enable adt-poolw update-nth-array)))))

(local
 (defthm adt-tree-poolw-of-update-other
   (implies (and (natp p) (natp k) (not (equal k p)))
            (equal (adt-poolw p i bytes (update-nth k v c))
                   (update-nth k v (adt-poolw p i bytes c))))
   :hints (("Goal" :in-theory (e/d (adt-poolw update-nth-array) (adt-poolw-is-pool-writes))))))

(local
 (defthm adt-tree-len-poolw
   (implies (and (natp p) (< p (len c)))
            (equal (len (adt-poolw p i bytes c)) (len c)))
   :hints (("Goal" :in-theory (e/d (adt-poolw update-nth-array) (adt-poolw-is-pool-writes))))))

(local
 (defthm adt-tree-update-nth-of-nth
   (implies (and (natp i) (< i (len l)))
            (equal (update-nth i (nth i l) l) l))
   :hints (("Goal" :in-theory (enable update-nth nth)))))

(local
 (defthm adt-tree-puts-is-poolw-len
   (implies (and (natp p) (natp (nth (+ 2 p) c)) (< (+ 2 p) (len c)))
            (equal (adt-pool-puts p bytes c)
                   (update-nth (+ 2 p) (+ (nth (+ 2 p) c) (len bytes))
                               (adt-poolw p (nth (+ 2 p) c) bytes c))))
   :hints (("Goal" :induct (adt-pool-puts p bytes c)
            :expand ((adt-poolw p (nth (+ 2 p) c) bytes c))
            :in-theory (e/d (adt-pool-puts adt-pool-put update-nth-array)
                            (adt-poolw-is-pool-writes))))))

(local
 (defthm adt-tree-nth-in-range
   (implies (natp (nth i c)) (< (nfix i) (len c)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable nth)))))

(local
 (defthm adt-tree-puts-is-poolw
   (implies (and (natp p) (natp (nth (+ 2 p) c)) (consp bytes))
            (equal (adt-pool-puts p bytes c)
                   (update-nth (+ 2 p) (+ (nth (+ 2 p) c) (len bytes))
                               (adt-poolw p (nth (+ 2 p) c) bytes c))))
   :hints (("Goal" :use ((:instance adt-tree-nth-in-range (i (+ 2 p))))))))

(local
 (defthm adt-tree-nth-of-room-other
   (implies (and (natp p) (natp k) (not (equal k p)))
            (equal (nth k (adt-pool-room p need c)) (nth k c)))
   :hints (("Goal" :in-theory (enable adt-pool-room)))))

(defthm adt-pool-push-is-puts
  (implies (and (natp p) (natp (nth (+ 2 p) c)) (consp bytes))
           (equal (adt-pool-push p bytes c)
                  (adt-pool-puts p bytes (adt-pool-room p (+ (nth (+ 2 p) c) (len bytes)) c))))
  :hints (("Goal" :in-theory (e/d (adt-pool-push) (adt-poolw-is-pool-writes adt-tree-puts-is-poolw))
           :use ((:instance adt-tree-puts-is-poolw
                            (c (adt-pool-room p (+ (nth (+ 2 p) c) (len bytes)) c)))))))

(defthm adt-pool-put-shape
  (implies (natp p)
           (and (equal (nth (+ 2 p) (adt-pool-put p b c)) (+ 1 (nth (+ 2 p) c)))
                (equal (len (nth p (adt-pool-put p b c)))
                       (max (len (nth p c)) (+ 1 (nfix (nth (+ 2 p) c)))))))
  :hints (("Goal" :in-theory (enable update-nth-array))))

(in-theory (disable adt-pool-put))

; The CHECKED put the executables run: an octet that is not one, or a fill
; at the end of the pool, writes nothing (two fixnum comparisons an octet;
; the writers' guards are then about their arguments only).  With the room
; made first and octets to write, the checked puts are the puts.
(defun adt-pool-cput (p b c)
  (declare (xargs :verify-guards nil))
  (if (and (unsigned-byte-p 8 b) (natp (nth (+ 2 p) c)) (< (nth (+ 2 p) c) (len (nth p c))))
      (adt-pool-put p b c)
    c))

(defun adt-pool-cputs (p bytes c)
  (declare (xargs :verify-guards nil))
  (if (atom bytes) c (adt-pool-cputs p (cdr bytes) (adt-pool-cput p (car bytes) c))))

(defthm adt-pool-cputs-of-append
  (equal (adt-pool-cputs p (append a b) c)
         (adt-pool-cputs p b (adt-pool-cputs p a c))))

(defthm adt-pool-cputs-of-cons
  (equal (adt-pool-cputs p (cons b bytes) c)
         (adt-pool-cputs p bytes (adt-pool-cput p b c))))

(defthm adt-pool-cputs-of-atom
  (implies (atom bytes) (equal (adt-pool-cputs p bytes c) c)))

(local
 (defthm adt-tree-adt-octetsp-facts
   (implies (adt-octetsp x)
            (and (true-listp x)
                 (adt-octetsp (cdr x))
                 (implies (consp x) (unsigned-byte-p 8 (car x)))))
   :hints (("Goal" :in-theory (enable adt-octetsp)))))

(defthm adt-pool-cputs-is-puts
  (implies (and (natp p) (adt-octetsp bytes) (natp (nth (+ 2 p) c))
                (<= (+ (nth (+ 2 p) c) (len bytes)) (len (nth p c))))
           (equal (adt-pool-cputs p bytes c) (adt-pool-puts p bytes c)))
  :hints (("Goal" :induct (adt-pool-cputs p bytes c)
           :in-theory (e/d (adt-pool-puts adt-pool-cput)
                           (adt-tree-puts-is-poolw adt-tree-puts-is-poolw-len))
           :expand ((adt-pool-puts p bytes c)))))

(in-theory (disable adt-pool-cputs adt-pool-cput))

(local
 (defthm adt-tree-nthcdr-open
   (implies (and (natp k) (< k (len l)))
            (equal (nthcdr k l) (cons (nth k l) (nthcdr (+ 1 k) l))))
   :hints (("Goal" :in-theory (enable nth nthcdr)))))

(local
 (defthm adt-tree-chars-octets-of-nthcdr
   (implies (and (stringp s) (natp k) (< k (length s)))
            (equal (fn-scc-chars-octets (nthcdr k (coerce s 'list)))
                   (cons (char-code (char s k))
                         (fn-scc-chars-octets (nthcdr (+ 1 k) (coerce s 'list))))))
   :hints (("Goal" :in-theory (e/d (char) (nthcdr))
            :use ((:instance adt-tree-nthcdr-open (l (coerce s 'list))))
            :expand ((fn-scc-chars-octets (cons (nth k (coerce s 'list))
                                                (nthcdr (+ 1 k) (coerce s 'list)))))))))

(local
 (defthm adt-tree-nthcdr-past
   (implies (and (natp k) (<= (len l) k))
            (not (consp (nthcdr k l))))))


; -----------------------------------------------------------------------------
; The writer over ANY put (lane gate-b, 2026-10-01): the walk is the fold of
; its put over the tree's program, whatever the put is.  A paged instance
; (books/def-representation-paged.lisp) instantiates it at its paged checked
; put, whose fold is `adt-pg-cputs' below.

(encapsulate
  (((adt-h-put * *) => *))
  (local (defun adt-h-put (b c) (cons b c))))

(defun adt-h-puts (bytes c)
  (declare (xargs :verify-guards nil))
  (if (atom bytes) c (adt-h-puts (cdr bytes) (adt-h-put (car bytes) c))))

(defthm adt-h-puts-of-append
  (equal (adt-h-puts (append a b) c) (adt-h-puts b (adt-h-puts a c))))

(defthm adt-h-puts-of-atom
  (implies (atom bytes) (equal (adt-h-puts bytes c) c)))

(defun adt-h-tw-digits (n c)
  (declare (xargs :verify-guards nil))
  (if (zp n) c (adt-h-tw-digits (floor n 256) (adt-h-put (mod n 256) c))))

(defun adt-h-tw-chars (s k c)
  (declare (xargs :verify-guards nil :measure (nfix (- (length s) (nfix k)))))
  (if (and (stringp s) (natp k) (< k (length s)))
      (adt-h-tw-chars s (+ 1 k) (adt-h-put (char-code (char s k)) c))
    c))

(defun adt-h-tw-bytes (xs c)
  (declare (xargs :verify-guards nil))
  (if (atom xs) c (adt-h-tw-bytes (cdr xs) (adt-h-put (car xs) c))))

(defun adt-h-tw-ops (n c)
  (declare (xargs :verify-guards nil))
  (if (zp n) c (adt-h-tw-ops (1- n) (adt-h-put *fn-scc-op-cons* c))))

(defun adt-h-tw-atom (x c)
  (declare (xargs :verify-guards nil))
  (cond ((null x) (adt-h-put *fn-scc-op-nil* c))
        ((natp x) (adt-h-tw-digits x (adt-h-put (adt-tree-ndig x) (adt-h-put *fn-scc-op-nat* c))))
        ((integerp x) (adt-h-tw-digits (- -1 x) (adt-h-put (adt-tree-ndig (- -1 x))
                                                           (adt-h-put *fn-scc-op-neg* c))))
        ((characterp x) (adt-h-put (char-code x) (adt-h-put *fn-scc-op-char* c)))
        ((stringp x) (adt-h-tw-chars x 0 (adt-h-tw-digits (length x)
                                                          (adt-h-put (adt-tree-ndig (length x))
                                                                     (adt-h-put *fn-scc-op-string* c)))))
        (t (let ((s (symbol-name x)))
             (adt-h-tw-chars s 0 (adt-h-tw-digits (length s)
                                                  (adt-h-put (adt-tree-ndig (length s))
                                                             (adt-h-put (fn-scc-package-index (symbol-package-name x))
                                                                        (adt-h-put *fn-scc-op-symbol* c)))))))))

(defun adt-h-tw-tree (x n c)
  (declare (xargs :verify-guards nil :measure (acl2-count x)))
  (cond ((fn-scc-octets-valuep x)
         (adt-h-tw-ops n (adt-h-tw-bytes x (adt-h-tw-digits (len x)
                                                            (adt-h-put (adt-tree-ndig (len x))
                                                                       (adt-h-put *fn-scc-op-octets* c))))))
        ((consp x) (adt-h-tw-tree (cdr x) (+ 1 (nfix n)) (adt-h-tw-tree (car x) 0 c)))
        (t (adt-h-tw-ops n (adt-h-tw-atom x c)))))

(defthm adt-h-puts-of-cons
  (equal (adt-h-puts (cons b bytes) c) (adt-h-puts bytes (adt-h-put b c))))

(local (in-theory (disable adt-h-puts)))

(defthm adt-h-tw-digits-is-puts
  (equal (adt-h-tw-digits n c) (adt-h-puts (fn-scc-le-digits n) c))
  :hints (("Goal" :induct (adt-h-tw-digits n c) :in-theory (enable fn-scc-le-digits))))

(defthm adt-h-tw-chars-is-puts
  (implies (and (stringp s) (natp k))
           (equal (adt-h-tw-chars s k c)
                  (adt-h-puts (fn-scc-chars-octets (nthcdr k (coerce s 'list))) c)))
  :hints (("Goal" :induct (adt-h-tw-chars s k c))
          ("Subgoal *1/1" :use ((:instance adt-tree-chars-octets-of-nthcdr))
           :in-theory (disable adt-tree-chars-octets-of-nthcdr))
          ("Subgoal *1/2" :expand ((fn-scc-chars-octets (nthcdr k (coerce s 'list)))))))

(defthm adt-h-tw-bytes-is-puts
  (equal (adt-h-tw-bytes xs c) (adt-h-puts xs c))
  :hints (("Goal" :induct (adt-h-tw-bytes xs c))))

(defthm adt-h-tw-ops-is-puts
  (equal (adt-h-tw-ops n c) (adt-h-puts (fn-scc-repeat (nfix n) *fn-scc-op-cons*) c))
  :hints (("Goal" :induct (adt-h-tw-ops n c) :in-theory (enable fn-scc-repeat))))

(defthm adt-h-tw-atom-is-puts
  (implies (and (atom x) (not (fn-scc-octets-valuep x)))
           (equal (adt-h-tw-atom x c) (adt-h-puts (fn-scc-atom-octets x) c)))
  :hints (("Goal" :in-theory (union-theories (theory 'adt-tree-codec) (enable fn-scc-chars-octets)))))

(local
 (defthm adt-h-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

(defthm adt-h-tw-tree-is-puts
  (equal (adt-h-tw-tree x n c)
         (adt-h-puts (append (fn-scc-program x) (fn-scc-repeat (nfix n) *fn-scc-op-cons*)) c))
  :hints (("Goal" :induct (adt-h-tw-tree x n c)
           :in-theory (union-theories (theory 'adt-tree-codec) (enable fn-scc-repeat)))))

(in-theory (disable adt-h-puts))

; -----------------------------------------------------------------------------
; The writer over a constrained put.

(encapsulate
  (((adt-g-pp) => *) ((adt-g-put * *) => *))
  (local (defun adt-g-pp () 0))
  (local (defun adt-g-put (b c) (adt-pool-cput 0 b c)))
  (defthm adt-g-put-def
    (equal (adt-g-put b c) (adt-pool-cput (adt-g-pp) b c))
    :rule-classes nil))

(defun adt-g-tw-digits (n c)
  (declare (xargs :verify-guards nil))
  (if (zp n) c (adt-g-tw-digits (floor n 256) (adt-g-put (mod n 256) c))))

(defun adt-g-tw-chars (s k c)
  (declare (xargs :verify-guards nil :measure (nfix (- (length s) (nfix k)))))
  (if (and (stringp s) (natp k) (< k (length s)))
      (adt-g-tw-chars s (+ 1 k) (adt-g-put (char-code (char s k)) c))
    c))

(defun adt-g-tw-bytes (xs c)
  (declare (xargs :verify-guards nil))
  (if (atom xs) c (adt-g-tw-bytes (cdr xs) (adt-g-put (car xs) c))))

(defun adt-g-tw-ops (n c)
  (declare (xargs :verify-guards nil))
  (if (zp n) c (adt-g-tw-ops (1- n) (adt-g-put *fn-scc-op-cons* c))))

(defun adt-g-tw-atom (x c)
  (declare (xargs :verify-guards nil))
  (cond ((null x) (adt-g-put *fn-scc-op-nil* c))
        ((natp x) (adt-g-tw-digits x (adt-g-put (adt-tree-ndig x) (adt-g-put *fn-scc-op-nat* c))))
        ((integerp x) (adt-g-tw-digits (- -1 x) (adt-g-put (adt-tree-ndig (- -1 x))
                                                           (adt-g-put *fn-scc-op-neg* c))))
        ((characterp x) (adt-g-put (char-code x) (adt-g-put *fn-scc-op-char* c)))
        ((stringp x) (adt-g-tw-chars x 0 (adt-g-tw-digits (length x)
                                                          (adt-g-put (adt-tree-ndig (length x))
                                                                     (adt-g-put *fn-scc-op-string* c)))))
        (t (let ((s (symbol-name x)))
             (adt-g-tw-chars s 0 (adt-g-tw-digits (length s)
                                                  (adt-g-put (adt-tree-ndig (length s))
                                                             (adt-g-put (fn-scc-package-index (symbol-package-name x))
                                                                        (adt-g-put *fn-scc-op-symbol* c)))))))))

(defun adt-g-tw-tree (x n c)
  (declare (xargs :verify-guards nil :measure (acl2-count x)))
  (cond ((fn-scc-octets-valuep x)
         (adt-g-tw-ops n (adt-g-tw-bytes x (adt-g-tw-digits (len x)
                                                            (adt-g-put (adt-tree-ndig (len x))
                                                                       (adt-g-put *fn-scc-op-octets* c))))))
        ((consp x) (adt-g-tw-tree (cdr x) (+ 1 (nfix n)) (adt-g-tw-tree (car x) 0 c)))
        (t (adt-g-tw-ops n (adt-g-tw-atom x c)))))

(local (in-theory (enable adt-pool-cputs)))

(local
 (defthm adt-g-put-is-puts
   (equal (adt-g-put b c) (adt-pool-cputs (adt-g-pp) (list b) c))
   :hints (("Goal" :use adt-g-put-def))))

(local (in-theory (disable adt-pool-cputs)))

(defthm adt-g-tw-digits-is-puts
  (equal (adt-g-tw-digits n c) (adt-pool-cputs (adt-g-pp) (fn-scc-le-digits n) c))
  :hints (("Goal" :induct (adt-g-tw-digits n c) :in-theory (enable fn-scc-le-digits))))

(defthm adt-g-tw-chars-is-puts
  (implies (and (stringp s) (natp k))
           (equal (adt-g-tw-chars s k c)
                  (adt-pool-cputs (adt-g-pp) (fn-scc-chars-octets (nthcdr k (coerce s 'list))) c)))
  :hints (("Goal" :induct (adt-g-tw-chars s k c))
          ("Subgoal *1/1" :expand ((fn-scc-chars-octets (nthcdr k (coerce s 'list)))))))

(defthm adt-g-tw-bytes-is-puts
  (equal (adt-g-tw-bytes xs c) (adt-pool-cputs (adt-g-pp) xs c))
  :hints (("Goal" :induct (adt-g-tw-bytes xs c))))

(defthm adt-g-tw-ops-is-puts
  (equal (adt-g-tw-ops n c) (adt-pool-cputs (adt-g-pp) (fn-scc-repeat (nfix n) *fn-scc-op-cons*) c))
  :hints (("Goal" :induct (adt-g-tw-ops n c) :in-theory (enable fn-scc-repeat))))

(defthm adt-g-tw-atom-is-puts
  (implies (not (fn-scc-octets-valuep x))
           (implies (atom x)
                    (equal (adt-g-tw-atom x c) (adt-pool-cputs (adt-g-pp) (fn-scc-atom-octets x) c))))
  :hints (("Goal" :in-theory (union-theories (theory 'adt-tree-codec) (enable fn-scc-chars-octets)))))

(local
 (defthm adt-tree-append-repeat-cons
   (equal (append (fn-scc-repeat n v) (cons v y))
          (cons v (append (fn-scc-repeat n v) y)))
   :hints (("Goal" :in-theory (enable fn-scc-repeat)))))

(defthm adt-g-tw-tree-is-puts
  (equal (adt-g-tw-tree x n c)
         (adt-pool-cputs (adt-g-pp)
                        (append (fn-scc-program x) (fn-scc-repeat (nfix n) *fn-scc-op-cons*))
                        c))
  :hints (("Goal" :in-theory (enable adt-pool-cputs fn-scc-octets-valuep fn-scc-octetp fn-scc-le-digits)
           :use ((:functional-instance adt-h-tw-tree-is-puts
                                       (adt-h-put adt-g-put)
                                       (adt-h-puts (lambda (bytes c) (adt-pool-cputs (adt-g-pp) bytes c)))
                                       (adt-h-tw-digits adt-g-tw-digits)
                                       (adt-h-tw-chars adt-g-tw-chars)
                                       (adt-h-tw-bytes adt-g-tw-bytes)
                                       (adt-h-tw-ops adt-g-tw-ops)
                                       (adt-h-tw-atom adt-g-tw-atom)
                                       (adt-h-tw-tree adt-g-tw-tree))))))

; -----------------------------------------------------------------------------
; The push of a tree's program: the room made for its length, then the
; checked puts of it.  What each instance's NAME$C-TW-PUSH is.

(local
 (defthm adt-tree-program-consp
   (consp (fn-scc-program x))
   :hints (("Goal" :in-theory (enable fn-scc-program fn-scc-atom-octets)))))

(local
 (defthm adt-tree-octet-listp-is-adt-octetsp
   (equal (fn-scc-octet-listp x) (adt-octetsp x))
   :hints (("Goal" :in-theory (enable adt-octetsp fn-scc-octet-listp fn-scc-octetp unsigned-byte-p)))))

(local
 (defthm adt-tree-room-shape
   (implies (and (natp p) (natp need))
            (and (<= need (len (nth p (adt-pool-room p need c))))
                 (equal (nth (+ 2 p) (adt-pool-room p need c)) (nth (+ 2 p) c))))
   :hints (("Goal" :in-theory (enable adt-pool-room)))))

(local
 (defthm adt-tree-append-nil
   (implies (true-listp x) (equal (append x nil) x))))

(defthm adt-tree-push-is-push
  (implies (and (natp p) (fn-sccb-treep x) (natp (nth (+ 2 p) c)))
           (equal (adt-pool-cputs p (append (fn-scc-program x) (fn-scc-repeat 0 *fn-scc-op-cons*))
                                  (adt-pool-room p (+ (nth (+ 2 p) c) (adt-tree-plen x 0)) c))
                  (adt-pool-push p (fn-scc-program x) c)))
  :hints (("Goal" :in-theory (e/d (fn-scc-repeat) (fn-sccb-treep fn-scc-program))
           :use ((:instance fn-sccb-treep-encodes-octets)))))

; -----------------------------------------------------------------------------
; The foundation's shape is kept by the checked put (what an instance's
; writers need for their guards: each returns a well-formed foundation).

(local
 (defthm adt-tree-all-ub8-of-update-nth
   (implies (and (adt-all-elt-p '(:ub 8) l) (natp i) (< i (len l)) (unsigned-byte-p 8 b))
            (adt-all-elt-p '(:ub 8) (update-nth i b l)))
   :hints (("Goal" :in-theory (enable update-nth adt-elt-p)))))

(local
 (defthm adt-tree-cols-shape-of-update-nth-above
   (implies (and (natp ci) (natp k) (<= (+ ci (adt-ncols s)) k))
            (equal (adt-cols-shape s ci (update-nth k v c))
                   (adt-cols-shape s ci c)))
   :hints (("Goal" :induct (adt-cols-shape s ci c)
            :in-theory (enable adt-cols-shape adt-ncols)))))

(defthm adt-tree-shape-of-cput
  (implies (and (adt-shape-p s c) (equal p (adt-ncols s)))
           (and (adt-shape-p s (adt-pool-cput p b c))
                (equal (len (adt-pool-cput p b c)) (len c))))
  :hints (("Goal" :in-theory (enable adt-shape-p adt-pool-cput adt-pool-put update-nth-array))))

(encapsulate
  (((adt-g-okc *) => *))
  (local (defun adt-g-okc (c) (declare (ignore c)) t))
  (defthm adt-g-okc-of-put
    (implies (adt-g-okc c) (adt-g-okc (adt-g-put b c)))))

(defthm adt-g-tw-digits-okc
  (implies (adt-g-okc c) (adt-g-okc (adt-g-tw-digits n c)))
  :hints (("Goal" :induct (adt-g-tw-digits n c) :in-theory (disable adt-g-put-is-puts floor adt-g-tw-tree-is-puts adt-g-tw-atom-is-puts adt-g-tw-digits-is-puts adt-g-tw-chars-is-puts adt-g-tw-bytes-is-puts adt-g-tw-ops-is-puts))))

(defthm adt-g-tw-chars-okc
  (implies (adt-g-okc c) (adt-g-okc (adt-g-tw-chars s k c)))
  :hints (("Goal" :induct (adt-g-tw-chars s k c) :in-theory (disable adt-g-put-is-puts floor adt-g-tw-tree-is-puts adt-g-tw-atom-is-puts adt-g-tw-digits-is-puts adt-g-tw-chars-is-puts adt-g-tw-bytes-is-puts adt-g-tw-ops-is-puts))))

(defthm adt-g-tw-bytes-okc
  (implies (adt-g-okc c) (adt-g-okc (adt-g-tw-bytes xs c)))
  :hints (("Goal" :induct (adt-g-tw-bytes xs c) :in-theory (disable adt-g-put-is-puts floor adt-g-tw-tree-is-puts adt-g-tw-atom-is-puts adt-g-tw-digits-is-puts adt-g-tw-chars-is-puts adt-g-tw-bytes-is-puts adt-g-tw-ops-is-puts))))

(defthm adt-g-tw-ops-okc
  (implies (adt-g-okc c) (adt-g-okc (adt-g-tw-ops n c)))
  :hints (("Goal" :induct (adt-g-tw-ops n c) :in-theory (disable adt-g-put-is-puts floor adt-g-tw-tree-is-puts adt-g-tw-atom-is-puts adt-g-tw-digits-is-puts adt-g-tw-chars-is-puts adt-g-tw-bytes-is-puts adt-g-tw-ops-is-puts))))

(defthm adt-g-tw-atom-okc
  (implies (adt-g-okc c) (adt-g-okc (adt-g-tw-atom x c)))
  :hints (("Goal" :in-theory (disable adt-g-put-is-puts floor adt-g-tw-tree-is-puts adt-g-tw-atom-is-puts adt-g-tw-digits-is-puts adt-g-tw-chars-is-puts adt-g-tw-bytes-is-puts adt-g-tw-ops-is-puts))))

(defthm adt-g-tw-tree-okc
  (implies (adt-g-okc c) (adt-g-okc (adt-g-tw-tree x n c)))
  :hints (("Goal" :induct (adt-g-tw-tree x n c) :in-theory (disable adt-g-put-is-puts floor adt-g-tw-tree-is-puts adt-g-tw-atom-is-puts adt-g-tw-digits-is-puts adt-g-tw-chars-is-puts adt-g-tw-bytes-is-puts adt-g-tw-ops-is-puts))))

; An instance's guards read `adt-tree-okp' by its definition (the walk's
; cases); the equality with `fn-sccb-treep' is cited where it is wanted.
(in-theory (disable adt-tree-okp-is-sccb-treep))
