; fn: the TREE field of a PAGED `def-representation' instance (lane gate-b,
; 2026-10-01; D27).  books/def-representation-tree.lisp proves the tree
; writer's meaning over a put constrained to be the columnar pool's checked
; put; a paged instance's put writes a pool PAGE, so the writer is proved
; here once more over a put about which nothing is assumed (`adt-h-put'):
; the walk is the fold of its put over the tree's program
; (adt-h-tw-tree-is-puts).  The paged checked put `adt-pg-cput' and its
; fold `adt-pg-cputs' are defined here; with the room made, the fold is the
; pool write at the fill and the fill moved past it (adt-pg-cputs-is-poolw),
; which is what the instance's tree put needs to be its octets put
; (books/def-representation.lisp, `adt-pg-tree-exec-events').

(in-package "ACL2")
(include-book "def-representation-tree")
(include-book "def-representation-paged")
(local (include-book "arithmetic/top" :dir :system))

(local (in-theory (enable fn-scc-program fn-scc-atom-octets fn-scc-atomp fn-scc-nat-octets
                          fn-scc-nat-encodablep fn-scc-string-octets fn-scc-octets-valuep
                          fn-scc-octet-listp fn-scc-octetp fn-sccb-treep fn-scc-le-digits)))

(local
 (defthm adt-pt-len-chars-octets
   (equal (len (fn-scc-chars-octets chars)) (len chars))
   :hints (("Goal" :in-theory (enable fn-scc-chars-octets)))))

(local
 (defthm adt-pt-nthcdr-open
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
            :use ((:instance adt-pt-nthcdr-open (l (coerce s 'list))))
            :expand ((fn-scc-chars-octets (cons (nth k (coerce s 'list))
                                                (nthcdr (+ 1 k) (coerce s 'list)))))))))

(local
 (defthm adt-pt-nthcdr-past
   (implies (and (natp k) (<= (len l) k))
            (not (consp (nthcdr k l))))))
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

(defthm adt-h-puts-of-puts
  (equal (adt-h-puts b (adt-h-puts a c)) (adt-h-puts (append a b) c)))

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

(local
 (defthm adt-h-put-is-puts
   (equal (adt-h-put b c) (adt-h-puts (list b) c))
   :hints (("Goal" :expand ((adt-h-puts (list b) c))))))

(local (in-theory (disable adt-h-puts)))

(defthm adt-h-tw-digits-is-puts
  (equal (adt-h-tw-digits n c) (adt-h-puts (fn-scc-le-digits n) c))
  :hints (("Goal" :induct (adt-h-tw-digits n c))))

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
  :hints (("Goal" :in-theory (enable fn-scc-chars-octets))))

(local
 (defthm adt-h-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

(defthm adt-h-tw-tree-is-puts
  (equal (adt-h-tw-tree x n c)
         (adt-h-puts (append (fn-scc-program x) (fn-scc-repeat (nfix n) *fn-scc-op-cons*)) c))
  :hints (("Goal" :induct (adt-h-tw-tree x n c)
           :in-theory (enable fn-scc-repeat))))

(in-theory (disable adt-h-puts))

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
