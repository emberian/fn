; fn: the byte encoding of a Store checkpoint (P3, `fn-c' schema 2 in the
; design's table; magic FNSC here because the value differs from schema 1's
; node checkpoint).
;
; A checkpoint value (books/store-checkpoint-open.lisp) is an ACL2 tree: the
; record list and each replay fold's accumulator.  The existing TREE codec
; (checkpoint-codec.lisp) admits naturals below 2^32 and four symbols, which
; the Store state exceeds, so this book gives a second tree codec:
;
;   * a postfix program for a stack machine.  An atom is one instruction
;     that pushes it; a cons is its car's program, its cdr's program, then
;     CONS.  A list of n elements is therefore its elements' programs and n
;     CONS octets.  The decoder is a tail-recursive loop with an explicit
;     value stack, so its depth does not grow with the data; the encoder
;     recurses on car only and loops along each list spine.
;   * atoms: NIL, naturals (a length octet L then L little-endian octets, so
;     below 2^2040), negative integers, characters, strings, symbols of the
;     KEYWORD, ACL2 and COMMON-LISP packages (by name, never through the
;     reader), and non-empty octet lists as one instruction.
;
; The payload is then cut into segments of at most SEG octets, each an
; FN-style frame: header (magic, schema, index, count, length, sequence), the
; chunk, and a trailer `fn-frame-trailer' over the previous trailer, the
; header and the chunk.  The host reads the file one segment at a time
; (books/byte-store-range-read.lisp), and each segment is one bounded read.
; `fn-scc-decode-segments' refuses reorder (index), truncation (count),
; splice (sequence and the trailer chain) and a corrupt octet (trailer).
(in-package "ACL2")
(include-book "frame-trailer")
(local (include-book "arithmetic/top" :dir :system))
(local
 (defthm fn-scc-len-append
   (equal (len (append a b)) (+ (len a) (len b)))))

(local
 (defthm fn-scc-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

(defconst *fn-scc-magic* '(70 78 83 67))         ; "FNSC"
(defconst *fn-scc-schema* 2)
(defconst *fn-scc-segment-header-octets* 37)    ; 4 + 1 + 4 * 8
(defconst *fn-scc-op-nil* 0)
(defconst *fn-scc-op-nat* 1)
(defconst *fn-scc-op-neg* 2)
(defconst *fn-scc-op-string* 3)
(defconst *fn-scc-op-symbol* 4)
(defconst *fn-scc-op-cons* 5)
(defconst *fn-scc-op-octets* 6)
(defconst *fn-scc-op-char* 7)
(defconst *fn-scc-packages* '("KEYWORD" "ACL2" "COMMON-LISP"))

; -----------------------------------------------------------------------------
; List helpers, all tail-recursive in execution

(defun fn-scc-octetp (x)
  (declare (xargs :guard t))
  (and (natp x) (< x 256)))

(defun fn-scc-octet-listp (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (fn-scc-octetp (car x)) (fn-scc-octet-listp (cdr x)))
    (null x)))

(defthm fn-scc-octet-listp-facts
  (implies (fn-scc-octet-listp x)
           (and (true-listp x)
                (fn-scc-octet-listp (nthcdr n x))
                (fn-scc-octet-listp (cdr x))
                (implies (consp x) (and (natp (car x)) (< (car x) 256)))))
  :rule-classes ((:rewrite :corollary
                  (implies (fn-scc-octet-listp x)
                           (and (fn-scc-octet-listp (nthcdr n x))
                                (fn-scc-octet-listp (cdr x)))))
                 (:forward-chaining :corollary
                  (implies (fn-scc-octet-listp x) (true-listp x)))
                 (:rewrite :corollary
                  (implies (and (fn-scc-octet-listp x) (consp x))
                           (and (natp (car x)) (< (car x) 256))))))

(defthm fn-scc-octet-listp-take
  (implies (and (fn-scc-octet-listp x) (<= (nfix n) (len x)))
           (fn-scc-octet-listp (take n x))))

(defun fn-scc-long-enoughp (n xs)
  (declare (xargs :guard (natp n)))
  (if (zp n) t (and (consp xs) (fn-scc-long-enoughp (1- n) (cdr xs)))))

(local
 (defthm fn-scc-long-enoughp-is-len
   (implies (natp n)
            (equal (fn-scc-long-enoughp n xs) (<= n (len xs))))))

(local
 (defthm fn-scc-take-of-append-len
   (implies (and (true-listp a) (equal n (len a)))
            (equal (take n (append a b)) a))))

(local
 (defthm fn-scc-nthcdr-of-append-len
   (implies (equal n (len a))
            (equal (nthcdr n (append a b)) b))))

(local
 (defthm fn-scc-len-nthcdr
   (implies (and (natp n) (<= n (len xs)))
            (equal (len (nthcdr n xs)) (- (len xs) n)))))

; -----------------------------------------------------------------------------
; Naturals: little-endian digits

(defun fn-scc-le-digits (n)
  (declare (xargs :guard (natp n)))
  (if (zp n) nil (cons (mod n 256) (fn-scc-le-digits (floor n 256)))))

(defun fn-scc-le-value (xs)
  (declare (xargs :guard t))
  (if (consp xs) (+ (nfix (car xs)) (* 256 (fn-scc-le-value (cdr xs)))) 0))

(defthm fn-scc-le-value-natp
  (natp (fn-scc-le-value xs))
  :rule-classes :type-prescription)

(local
 (defthm fn-scc-le-value-of-digits
   (implies (natp n) (equal (fn-scc-le-value (fn-scc-le-digits n)) n))))

(defthm fn-scc-le-digits-octets
  (fn-scc-octet-listp (fn-scc-le-digits n)))

(defun fn-scc-nat-octets (n)
  (declare (xargs :guard (natp n)))
  (cons (len (fn-scc-le-digits n)) (fn-scc-le-digits n)))

(defun fn-scc-nat-encodablep (n)
  (declare (xargs :guard t))
  (and (natp n) (< (len (fn-scc-le-digits n)) 256)))

; (cons value rest), or nil when the octets are short.
(defun fn-scc-read-nat (xs)
  (declare (xargs :guard (fn-scc-octet-listp xs)))
  (if (and (consp xs) (fn-scc-long-enoughp (car xs) (cdr xs)))
      (cons (fn-scc-le-value (take (car xs) (cdr xs)))
            (nthcdr (car xs) (cdr xs)))
    nil))

(defthm fn-scc-read-nat-facts
  (implies (and (fn-scc-octet-listp xs) (fn-scc-read-nat xs))
           (and (consp (fn-scc-read-nat xs))
                (natp (car (fn-scc-read-nat xs)))
                (fn-scc-octet-listp (cdr (fn-scc-read-nat xs)))
                (< (len (cdr (fn-scc-read-nat xs))) (len xs))))
  :hints (("Goal" :do-not-induct t :in-theory (disable fn-scc-le-value))))

(defthm fn-scc-read-nat-of-octets
  (implies (natp n)
           (equal (fn-scc-read-nat (append (fn-scc-nat-octets n) rest))
                  (cons n rest))))

; Fixed eight octets, for the segment header.
(defun fn-scc-u64 (n k)
  (declare (xargs :guard (and (natp n) (natp k))))
  (if (zp k) nil (cons (mod (nfix n) 256) (fn-scc-u64 (floor (nfix n) 256) (1- k)))))

(local
 (defthm fn-scc-le-value-of-u64
   (implies (and (natp n) (natp k) (< n (expt 256 k)))
            (equal (fn-scc-le-value (fn-scc-u64 n k)) n))
   :hints (("Goal" :induct (fn-scc-u64 n k)))))

(defthm fn-scc-u64-shape
  (and (fn-scc-octet-listp (fn-scc-u64 n k))
       (equal (len (fn-scc-u64 n k)) (nfix k))))

; -----------------------------------------------------------------------------
; Strings and symbols

(defun fn-scc-chars-octets (chars)
  (declare (xargs :guard (character-listp chars)))
  (if (consp chars)
      (cons (char-code (car chars)) (fn-scc-chars-octets (cdr chars)))
    nil))

(defun fn-scc-octets-chars (xs)
  (declare (xargs :guard (fn-scc-octet-listp xs)))
  (if (consp xs)
      (cons (code-char (car xs)) (fn-scc-octets-chars (cdr xs)))
    nil))

(defthm fn-scc-octets-chars-character-listp
  (character-listp (fn-scc-octets-chars xs)))

(local
 (defthm fn-scc-octets-chars-of-chars-octets
   (implies (character-listp chars)
            (equal (fn-scc-octets-chars (fn-scc-chars-octets chars)) chars))))

(local
 (defthm fn-scc-len-chars-octets
   (equal (len (fn-scc-chars-octets chars)) (len chars))))

(defthm fn-scc-chars-octets-true-listp
  (true-listp (fn-scc-chars-octets chars)))

(defun fn-scc-string-octets (s)
  (declare (xargs :guard (stringp s)))
  (let ((codes (fn-scc-chars-octets (coerce s 'list))))
    (append (fn-scc-nat-octets (len codes)) codes)))

(defun fn-scc-read-string (xs)
  ; (cons string rest) or nil.
  (declare (xargs :guard (fn-scc-octet-listp xs)))
  (let ((n (fn-scc-read-nat xs)))
    (if (and (consp n) (fn-scc-long-enoughp (car n) (cdr n)))
        (cons (coerce (fn-scc-octets-chars (take (car n) (cdr n))) 'string)
              (nthcdr (car n) (cdr n)))
      nil)))

(defthm fn-scc-read-string-facts
  (implies (and (fn-scc-octet-listp xs) (fn-scc-read-string xs))
           (and (consp (fn-scc-read-string xs))
                (stringp (car (fn-scc-read-string xs)))
                (fn-scc-octet-listp (cdr (fn-scc-read-string xs)))
                (< (len (cdr (fn-scc-read-string xs))) (len xs))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-scc-read-nat-facts))
           :in-theory (disable fn-scc-read-nat fn-scc-read-nat-facts
                               fn-scc-octets-chars))))

(defthm fn-scc-read-string-of-octets
  (implies (stringp s)
           (equal (fn-scc-read-string (append (fn-scc-string-octets s) rest))
                  (cons s rest)))
  :hints (("Goal"
           :use ((:instance fn-scc-read-nat-of-octets
                            (n (len (coerce s 'list)))
                            (rest (append (fn-scc-chars-octets (coerce s 'list))
                                          rest))))
           :in-theory (e/d (fn-scc-string-octets fn-scc-read-string)
                           (fn-scc-read-nat fn-scc-nat-octets
                            fn-scc-read-nat-of-octets)))))

(defun fn-scc-package-index (name)
  (declare (xargs :guard t))
  (cond ((equal name "KEYWORD") 0)
        ((equal name "ACL2") 1)
        ((equal name "COMMON-LISP") 2)
        (t nil)))

(defun fn-scc-intern (index name)
  (declare (xargs :guard (stringp name)))
  (cond ((equal index 0) (intern-in-package-of-symbol name :fn-scc))
        ((equal index 1) (intern-in-package-of-symbol name 'fn-scc-intern))
        ((equal index 2) (intern-in-package-of-symbol name 'car))
        (t nil)))

(defthm fn-scc-intern-of-symbol
  (implies (and (symbolp x)
                (fn-scc-package-index (symbol-package-name x)))
           (equal (fn-scc-intern (fn-scc-package-index (symbol-package-name x))
                                 (symbol-name x))
                  x))
  :hints (("Goal" :in-theory (enable fn-scc-intern))))

; -----------------------------------------------------------------------------
; The tree universe and its postfix program

(defun fn-scc-octets-valuep (x)
  (declare (xargs :guard t))
  (and (consp x) (fn-scc-octet-listp x)))

(defun fn-scc-atomp (x)
  (declare (xargs :guard t))
  (or (null x)
      (fn-scc-nat-encodablep x)
      (and (integerp x) (< x 0) (fn-scc-nat-encodablep (- -1 x)))
      (characterp x)
      (stringp x)
      (and (symbolp x) (fn-scc-package-index (symbol-package-name x)) t)))

(defun fn-scc-treep (x)
  (declare (xargs :guard t))
  (cond ((fn-scc-octets-valuep x) t)
        ((consp x) (and (fn-scc-treep (car x)) (fn-scc-treep (cdr x))))
        (t (fn-scc-atomp x))))

(defun fn-scc-atom-octets (x)
  (declare (xargs :guard (fn-scc-atomp x)))
  (cond ((null x) (list *fn-scc-op-nil*))
        ((natp x) (cons *fn-scc-op-nat* (fn-scc-nat-octets x)))
        ((integerp x) (cons *fn-scc-op-neg* (fn-scc-nat-octets (- -1 x))))
        ((characterp x) (list *fn-scc-op-char* (char-code x)))
        ((stringp x) (cons *fn-scc-op-string* (fn-scc-string-octets x)))
        (t (cons *fn-scc-op-symbol*
                 (cons (fn-scc-package-index (symbol-package-name x))
                       (fn-scc-string-octets (symbol-name x)))))))

; The specification: a plain recursion.
(defun fn-scc-program (x)
  (declare (xargs :guard (fn-scc-treep x) :verify-guards nil))
  (cond ((fn-scc-octets-valuep x)
         (cons *fn-scc-op-octets* (append (fn-scc-nat-octets (len x)) x)))
        ((consp x) (append (fn-scc-program (car x))
                           (fn-scc-program (cdr x))
                           (list *fn-scc-op-cons*)))
        (t (fn-scc-atom-octets x))))

; -----------------------------------------------------------------------------
; The decoder: one instruction, then a loop

; (cons stack rest) or nil.
(defun fn-scc-step (xs stack)
  (declare (xargs :guard (and (consp xs) (fn-scc-octet-listp xs))))
  (let ((op (car xs)) (xs (cdr xs)))
    (cond ((equal op *fn-scc-op-nil*) (cons (cons nil stack) xs))
          ((equal op *fn-scc-op-nat*)
           (let ((n (fn-scc-read-nat xs)))
             (and n (cons (cons (car n) stack) (cdr n)))))
          ((equal op *fn-scc-op-neg*)
           (let ((n (fn-scc-read-nat xs)))
             (and n (cons (cons (- -1 (car n)) stack) (cdr n)))))
          ((equal op *fn-scc-op-char*)
           (and (consp xs) (cons (cons (code-char (car xs)) stack) (cdr xs))))
          ((equal op *fn-scc-op-string*)
           (let ((s (fn-scc-read-string xs)))
             (and s (cons (cons (car s) stack) (cdr s)))))
          ((equal op *fn-scc-op-symbol*)
           (and (consp xs)
                (let ((s (fn-scc-read-string (cdr xs))))
                  (and s (fn-scc-package-index
                          (nth (car xs) *fn-scc-packages*))
                       (cons (cons (fn-scc-intern (car xs) (car s)) stack)
                             (cdr s))))))
          ((equal op *fn-scc-op-cons*)
           (and (consp stack) (consp (cdr stack))
                (cons (cons (cons (cadr stack) (car stack)) (cddr stack)) xs)))
          ((equal op *fn-scc-op-octets*)
           (let ((n (fn-scc-read-nat xs)))
             (and n (fn-scc-long-enoughp (car n) (cdr n))
                  (cons (cons (take (car n) (cdr n)) stack)
                        (nthcdr (car n) (cdr n))))))
          (t nil))))

(defthm fn-scc-step-facts
  (implies (and (consp xs) (fn-scc-octet-listp xs) (fn-scc-step xs stack))
           (and (consp (fn-scc-step xs stack))
                (fn-scc-octet-listp (cdr (fn-scc-step xs stack)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-scc-read-nat fn-scc-read-string fn-scc-intern))))

(defthm fn-scc-step-shrinks
  (implies (and (consp xs) (fn-scc-octet-listp xs) (fn-scc-step xs stack))
           (< (len (cdr (fn-scc-step xs stack))) (len xs)))
  :rule-classes :linear
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-scc-read-nat-facts (xs (cdr xs)))
                 (:instance fn-scc-read-string-facts (xs (cdr xs)))
                 (:instance fn-scc-read-string-facts (xs (cddr xs))))
           :in-theory (disable fn-scc-read-nat fn-scc-read-string fn-scc-intern
                               fn-scc-read-nat-facts fn-scc-read-string-facts))))

(defun fn-scc-run (xs stack)
  (declare (xargs :guard (fn-scc-octet-listp xs) :measure (len xs)
                  :verify-guards nil))
  (if (not (consp xs))
      stack
    (let ((next (fn-scc-step xs stack)))
      (if (and next (mbt (< (len (cdr next)) (len xs))))
          (fn-scc-run (cdr next) (car next))
        :refused))))

(local
 (defthm fn-scc-step-of-atom
   (implies (fn-scc-atomp x)
            (equal (fn-scc-step (append (fn-scc-atom-octets x) rest) stack)
                   (cons (cons x stack) rest)))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d ()
                            (fn-scc-read-nat fn-scc-read-string fn-scc-string-octets
                             fn-scc-nat-octets))))))

(local
 (defthm fn-scc-step-of-octets
   (implies (fn-scc-octets-valuep x)
            (equal (fn-scc-step (cons *fn-scc-op-octets*
                                      (append (fn-scc-nat-octets (len x))
                                              (append x rest)))
                                stack)
                   (cons (cons x stack) rest)))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-scc-read-nat-of-octets (n (len x))
                             (rest (append x rest))))
            :in-theory (e/d () (fn-scc-read-nat fn-scc-nat-octets
                                fn-scc-read-nat-of-octets))))))

(local
 (defthm fn-scc-atom-octets-consp
   (and (consp (fn-scc-atom-octets x))
        (consp (append (fn-scc-atom-octets x) rest)))))

(local
 (defthm fn-scc-atom-octets-len
   (< 0 (len (fn-scc-atom-octets x)))
   :rule-classes :linear))

(local
 (defun fn-scc-ind (x rest stack)
   (declare (xargs :verify-guards nil))
   (cond ((fn-scc-octets-valuep x) (list rest stack))
         ((consp x)
          (list (fn-scc-ind (car x)
                            (append (fn-scc-program (cdr x))
                                    (cons *fn-scc-op-cons* rest))
                            stack)
                (fn-scc-ind (cdr x) (cons *fn-scc-op-cons* rest)
                            (cons (car x) stack))))
         (t (list rest stack)))))

(defthm fn-scc-run-of-program
  (implies (fn-scc-treep x)
           (equal (fn-scc-run (append (fn-scc-program x) rest) stack)
                  (fn-scc-run rest (cons x stack))))
  :hints (("Goal" :induct (fn-scc-ind x rest stack)
           :in-theory (disable fn-scc-step fn-scc-atom-octets fn-scc-nat-octets
                               fn-scc-atomp fn-scc-octets-valuep))
          ("Subgoal *1/3" :expand ((fn-scc-run (append (fn-scc-atom-octets x) rest)
                                               stack)))
          ("Subgoal *1/1" :expand ((:free (r) (fn-scc-run (cons *fn-scc-op-octets* r)
                                                          stack))))
          ("Subgoal *1/2" :expand ((fn-scc-run (cons *fn-scc-op-cons* rest)
                                               (cons (cdr x) (cons (car x) stack))))
           :in-theory (e/d (fn-scc-step)
                           (fn-scc-atom-octets fn-scc-nat-octets
                            fn-scc-atomp fn-scc-octets-valuep)))))

; -----------------------------------------------------------------------------
; The encoder the host runs: tail-recursive along each list spine

(defun fn-scc-repeat (n v)
  (declare (xargs :guard (natp n)))
  (if (zp n) nil (cons v (fn-scc-repeat (1- n) v))))

(defun fn-scc-cons-ops (n acc)
  (declare (xargs :guard (natp n)))
  (if (zp n) acc (fn-scc-cons-ops (1- n) (cons *fn-scc-op-cons* acc))))

; (fn-scc-renc x racc n): the program of x, reversed, onto racc, then n CONS.
(defun fn-scc-renc (x racc n)
  (declare (xargs :guard (and (fn-scc-treep x) (natp n)) :verify-guards nil
                  :measure (acl2-count x)))
  (cond ((fn-scc-octets-valuep x)
         (fn-scc-cons-ops n (revappend (cons *fn-scc-op-octets*
                                             (append (fn-scc-nat-octets (len x)) x))
                                       racc)))
        ((consp x)
         (fn-scc-renc (cdr x) (fn-scc-renc (car x) racc 0) (+ 1 (nfix n))))
        (t (fn-scc-cons-ops n (revappend (fn-scc-atom-octets x) racc)))))

(local
 (defthm fn-scc-append-repeat-cons
   (equal (append (fn-scc-repeat n v) (cons v y))
          (cons v (append (fn-scc-repeat n v) y)))
   :hints (("Goal" :in-theory (enable fn-scc-repeat)))))

(local
 (defthm fn-scc-cons-ops-is-append
   (equal (fn-scc-cons-ops n acc)
          (append (fn-scc-repeat (nfix n) *fn-scc-op-cons*) acc))
   :hints (("Goal" :in-theory (enable fn-scc-repeat)))))

(local
 (defthm fn-scc-revappend-of-append
   (equal (revappend (append a b) r) (revappend b (revappend a r)))))


(defthm fn-scc-renc-is-program
  (equal (fn-scc-renc x racc n)
         (append (fn-scc-repeat (nfix n) *fn-scc-op-cons*)
                 (revappend (fn-scc-program x) racc)))
  :hints (("Goal" :induct (fn-scc-renc x racc n)
           :in-theory (enable fn-scc-repeat))))

(defun fn-scc-encode (x)
  (declare (xargs :guard (fn-scc-treep x) :verify-guards nil))
  (revappend (fn-scc-renc x nil 0) nil))

(local
 (defthm fn-scc-revappend-revappend-gen
   (equal (revappend (revappend a b) c) (revappend b (append a c)))))

(local
 (defthm fn-scc-append-nil-true-list
   (implies (true-listp a) (equal (append a nil) a))))

(local
 (defthm fn-scc-revappend-revappend
   (implies (true-listp a)
            (equal (revappend (revappend a nil) nil) a))
   :hints (("Goal" :use ((:instance fn-scc-revappend-revappend-gen (b nil) (c nil)))
            :in-theory (disable fn-scc-revappend-revappend-gen)))))

(defthm fn-scc-program-true-listp
  (true-listp (fn-scc-program x)))

(defthm fn-scc-encode-is-program
  (equal (fn-scc-encode x) (fn-scc-program x)))

(defun fn-scc-decode-tree (octets)
  (declare (xargs :guard (fn-scc-octet-listp octets) :verify-guards nil))
  (let ((stack (fn-scc-run octets nil)))
    (if (and (consp stack) (null (cdr stack)))
        (list :ok (car stack))
      (list :refused :tree))))

(defthm fn-scc-decode-tree-of-encode
  (implies (fn-scc-treep x)
           (equal (fn-scc-decode-tree (fn-scc-encode x)) (list :ok x)))
  :hints (("Goal" :use ((:instance fn-scc-run-of-program (rest nil) (stack nil)))
           :in-theory (disable fn-scc-run-of-program))))

; -----------------------------------------------------------------------------
; Segments

(defconst *fn-scc-u64-bound* 18446744073709551616)
(defconst *fn-scc-genesis* '(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                             0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0))

(defun fn-scc-header (index count length sequence)
  (declare (xargs :guard (and (natp index) (natp count) (natp length)
                              (natp sequence))))
  (append *fn-scc-magic*
          (list *fn-scc-schema*)
          (fn-scc-u64 index 8) (fn-scc-u64 count 8)
          (fn-scc-u64 length 8) (fn-scc-u64 sequence 8)))

(defun fn-scc-seal (prev header chunk)
  (declare (xargs :guard t))
  (fn-frame-trailer (append (true-list-fix prev) (true-list-fix header) chunk)))

; The chunks of a payload, each at most SEG octets (one chunk when SEG is 0).
(defun fn-scc-chunks (payload seg)
  (declare (xargs :guard (and (true-listp payload) (natp seg)) :measure (len payload)))
  (if (or (zp seg) (not (fn-scc-long-enoughp (+ 1 seg) payload)))
      (list payload)
    (cons (take seg payload) (fn-scc-chunks (nthcdr seg payload) seg))))

(defun fn-scc-frames (chunks index count sequence prev)
  (declare (xargs :guard (and (true-list-listp chunks)
                              (natp index) (natp count) (natp sequence))
                  :verify-guards nil))
  (if (consp chunks)
      (let* ((chunk (car chunks))
             (header (fn-scc-header index count (len chunk) sequence))
             (trailer (fn-scc-seal prev header chunk)))
        (cons (append header chunk trailer)
              (fn-scc-frames (cdr chunks) (+ 1 index) count sequence trailer)))
    nil))

(defun fn-scc-concat (segments)
  (declare (xargs :guard t))
  (if (consp segments)
      (append (true-list-fix (car segments)) (fn-scc-concat (cdr segments)))
    nil))

; The record count a checkpoint value covers: its second element's length.
(defun fn-scc-value-sequence (c)
  (declare (xargs :guard t))
  (len (and (consp c) (consp (cdr c)) (cadr c))))

(defun fn-scc-segments (c segment-octets)
  (declare (xargs :guard (natp segment-octets) :verify-guards nil))
  (if (not (fn-scc-treep c))
      :unencodable
    (let ((chunks (fn-scc-chunks (fn-scc-encode c) segment-octets)))
      (fn-scc-frames chunks 0 (len chunks) (fn-scc-value-sequence c)
                     *fn-scc-genesis*))))

; What the host writes through fn-bs-scp-program.
(defun fn-scc-file-octets (c segment-octets)
  (declare (xargs :guard (natp segment-octets) :verify-guards nil))
  (let ((segments (fn-scc-segments c segment-octets)))
    (if (eq segments :unencodable) :unencodable (fn-scc-concat segments))))

(defun fn-scc-segment-max-octets (segment-octets)
  (declare (xargs :guard (natp segment-octets)))
  (+ *fn-scc-segment-header-octets* segment-octets *fn-frame-trailer-octets*))

; -----------------------------------------------------------------------------
; Reading a segment

(defun fn-scc-u64-at (xs)
  (declare (xargs :guard (fn-scc-octet-listp xs) :verify-guards nil))
  (fn-scc-le-value (take 8 xs)))

(defun fn-scc-parse-header (seg)
  ; (list index count length sequence rest) or nil; rest follows the header.
  (declare (xargs :guard (fn-scc-octet-listp seg) :verify-guards nil))
  (if (and (fn-scc-long-enoughp *fn-scc-segment-header-octets* seg)
           (equal (take 4 seg) *fn-scc-magic*)
           (equal (nth 4 seg) *fn-scc-schema*))
      (let* ((r1 (nthcdr 5 seg)) (r2 (nthcdr 8 r1)) (r3 (nthcdr 8 r2))
             (r4 (nthcdr 8 r3)))
        (list (fn-scc-u64-at r1) (fn-scc-u64-at r2) (fn-scc-u64-at r3)
              (fn-scc-u64-at r4) (nthcdr 8 r4)))
    nil))

; The host reads a header of *fn-scc-segment-header-octets*, asks this for
; the whole segment's length, and reads the rest.
(defun fn-scc-segment-extent (header)
  (declare (xargs :guard (fn-scc-octet-listp header) :verify-guards nil))
  (let ((h (fn-scc-parse-header header)))
    (and h (+ *fn-scc-segment-header-octets* (nth 2 h) *fn-frame-trailer-octets*))))

; (list chunk trailer) when SEG is one well-formed segment at INDEX of COUNT
; with SEQUENCE, chained to PREV; otherwise nil.
(defun fn-scc-open-segment (seg index count sequence prev)
  (declare (xargs :guard (and (fn-scc-octet-listp seg) (true-listp prev))
                  :verify-guards nil))
  (let ((h (fn-scc-parse-header seg)))
    (and h
         (equal (nth 0 h) index)
         (equal (nth 1 h) count)
         (equal (nth 3 h) sequence)
         (let* ((body (nth 4 h))
                (chunk (take (nth 2 h) body))
                (trailer (nthcdr (nth 2 h) body)))
           (and (fn-scc-long-enoughp (nth 2 h) body)
                (equal trailer
                       (fn-scc-seal prev (take *fn-scc-segment-header-octets* seg)
                                    chunk))
                (list chunk trailer))))))

(defun fn-scc-segment-listp (segs)
  (declare (xargs :guard t))
  (if (consp segs)
      (and (fn-scc-octet-listp (car segs)) (fn-scc-segment-listp (cdr segs)))
    (null segs)))

(defun fn-scc-join (segs index count sequence prev racc)
  (declare (xargs :guard (and (fn-scc-segment-listp segs) (true-listp prev)
                              (true-listp racc))
                  :verify-guards nil))
  (if (consp segs)
      (let ((o (fn-scc-open-segment (car segs) index count sequence prev)))
        (if o
            (fn-scc-join (cdr segs) (+ 1 (nfix index)) count sequence (cadr o)
                         (revappend (car o) racc))
          (list :refused :segment)))
    (if (and (equal index count) (null segs))
        (list :ok (revappend racc nil))
      (list :refused :truncated))))

(defun fn-scc-decode-segments (segs)
  (declare (xargs :guard (fn-scc-segment-listp segs) :verify-guards nil))
  (let ((h (and (consp segs) (fn-scc-parse-header (car segs)))))
    (if (not h)
        (list :refused :header)
      (let ((payload (fn-scc-join segs 0 (nth 1 h) (nth 3 h) *fn-scc-genesis* nil)))
        (if (not (eq (car payload) :ok))
            payload
          (let ((tree (fn-scc-decode-tree (nth 1 payload))))
            (if (and (eq (car tree) :ok)
                     (equal (fn-scc-value-sequence (nth 1 tree)) (nth 3 h)))
                tree
              (list :refused :value))))))))

; -----------------------------------------------------------------------------
; The segment round trip

(local
 (defthm fn-scc-u64-true-listp
   (true-listp (fn-scc-u64 n k))))

(local
 (defthm fn-scc-header-shape
   (and (true-listp (fn-scc-header i n l q))
        (equal (len (fn-scc-header i n l q)) 37))))

(local
 (defthm fn-scc-long-enoughp-append
   (implies (and (natp k) (<= k (len a)))
            (fn-scc-long-enoughp k (append a b)))))

(local
 (defthm fn-scc-take-of-append-short
   (implies (and (true-listp a) (natp k) (<= k (len a)))
            (equal (take k (append a b)) (take k a)))))

(local
 (defthm fn-scc-take-all
   (implies (and (true-listp x) (equal k (len x)))
            (equal (take k x) x))))

(local
 (defthm fn-scc-u64-read
   (implies (and (natp n) (< n *fn-scc-u64-bound*))
            (equal (fn-scc-u64-at (append (fn-scc-u64 n 8) rest)) n))
   :hints (("Goal" :in-theory (disable fn-scc-u64)))))

(local
 (defthm fn-scc-parse-header-of-segment
   (implies (and (natp i) (< i *fn-scc-u64-bound*)
                 (natp n) (< n *fn-scc-u64-bound*)
                 (natp l) (< l *fn-scc-u64-bound*)
                 (natp q) (< q *fn-scc-u64-bound*))
            (equal (fn-scc-parse-header (append (fn-scc-header i n l q) rest))
                   (list i n l q rest)))
   :hints (("Goal" :in-theory (e/d (fn-scc-header) (fn-scc-u64 fn-scc-u64-at))))))

(local
 (defthm fn-scc-open-segment-of-frame
   (implies (and (natp i) (< i *fn-scc-u64-bound*)
                 (natp n) (< n *fn-scc-u64-bound*)
                 (true-listp chunk) (< (len chunk) *fn-scc-u64-bound*)
                 (natp q) (< q *fn-scc-u64-bound*))
            (equal (fn-scc-open-segment
                    (append (fn-scc-header i n (len chunk) q)
                            (append chunk
                                    (fn-scc-seal prev (fn-scc-header i n (len chunk) q)
                                                 chunk)))
                    i n q prev)
                   (list chunk (fn-scc-seal prev (fn-scc-header i n (len chunk) q)
                                            chunk))))
   :hints (("Goal" :in-theory (e/d () (fn-scc-header fn-scc-seal fn-scc-parse-header))))))

(defun fn-scc-chunk-listp (chunks)
  (declare (xargs :guard t))
  (if (consp chunks)
      (and (true-listp (car chunks))
           (< (len (car chunks)) *fn-scc-u64-bound*)
           (fn-scc-chunk-listp (cdr chunks)))
    t))

(local
 (defun fn-scc-join-ind (chunks i n q prev racc)
   (declare (xargs :verify-guards nil))
   (if (consp chunks)
       (let* ((h (fn-scc-header i n (len (car chunks)) q))
              (tr (fn-scc-seal prev h (car chunks))))
         (fn-scc-join-ind (cdr chunks) (+ 1 i) n q tr
                          (revappend (car chunks) racc)))
     (list i n q prev racc))))

(local
 (defthm fn-scc-true-list-fix-id
   (implies (true-listp x) (equal (true-list-fix x) x))))

(local
 (defthm fn-scc-join-of-frames
   (implies (and (fn-scc-chunk-listp chunks)
                 (natp i) (natp n) (<= (+ i (len chunks)) n)
                 (< n *fn-scc-u64-bound*)
                 (natp q) (< q *fn-scc-u64-bound*))
            (equal (fn-scc-join (fn-scc-frames chunks i n q prev) i n q prev racc)
                   (if (equal (+ i (len chunks)) n)
                       (list :ok (revappend (revappend (fn-scc-concat chunks) racc) nil))
                     (list :refused :truncated))))
   :hints (("Goal" :induct (fn-scc-join-ind chunks i n q prev racc)
            :in-theory (e/d () (fn-scc-header fn-scc-seal fn-scc-open-segment))))))

(local
 (defthm fn-scc-append-take-nthcdr
   (implies (and (natp k) (<= k (len x)))
            (equal (append (take k x) (nthcdr k x)) x))))

(local
 (defthm fn-scc-concat-of-chunks
   (implies (true-listp payload)
            (equal (fn-scc-concat (fn-scc-chunks payload seg)) payload))))

(local
 (defthm fn-scc-len-take
   (equal (len (take k x)) (nfix k))))

(local
 (defthm fn-scc-chunks-shape
   (implies (and (true-listp payload) (< (len payload) *fn-scc-u64-bound*))
            (and (fn-scc-chunk-listp (fn-scc-chunks payload seg))
                 (<= (len (fn-scc-chunks payload seg)) (+ 1 (len payload)))
                 (consp (fn-scc-chunks payload seg))))))

(local
 (defthm fn-scc-concat-true-listp
   (true-listp (fn-scc-concat x))))

(local
 (defthm fn-scc-join-of-chunks
   (implies (and (true-listp p) (< (+ 1 (len p)) *fn-scc-u64-bound*)
                 (natp q) (< q *fn-scc-u64-bound*))
            (equal (fn-scc-join (fn-scc-frames (fn-scc-chunks p seg) 0
                                               (len (fn-scc-chunks p seg)) q prev)
                                0 (len (fn-scc-chunks p seg)) q prev nil)
                   (list :ok p)))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-scc-chunks-shape (payload p))
                  (:instance fn-scc-join-of-frames (chunks (fn-scc-chunks p seg))
                             (i 0) (n (len (fn-scc-chunks p seg))) (racc nil)))
            :in-theory (e/d () (fn-scc-chunks-shape fn-scc-join-of-frames
                                fn-scc-chunks fn-scc-frames fn-scc-join))))))

(local
 (defthm fn-scc-parse-header-of-first-frame
   (implies (and (consp chunks) (fn-scc-chunk-listp chunks)
                 (natp n) (< n *fn-scc-u64-bound*)
                 (natp q) (< q *fn-scc-u64-bound*))
            (equal (nth 1 (fn-scc-parse-header (car (fn-scc-frames chunks 0 n q prev))))
                   n))
   :hints (("Goal" :expand ((fn-scc-frames chunks 0 n q prev))
            :in-theory (e/d () (fn-scc-header fn-scc-seal))))))

(local
 (defthm fn-scc-parse-header-of-first-frame-sequence
   (implies (and (consp chunks) (fn-scc-chunk-listp chunks)
                 (natp n) (< n *fn-scc-u64-bound*)
                 (natp q) (< q *fn-scc-u64-bound*))
            (and (fn-scc-parse-header (car (fn-scc-frames chunks 0 n q prev)))
                 (equal (nth 3 (fn-scc-parse-header
                                (car (fn-scc-frames chunks 0 n q prev))))
                        q)))
   :hints (("Goal" :expand ((fn-scc-frames chunks 0 n q prev))
            :in-theory (e/d () (fn-scc-header fn-scc-seal))))))

(local
 (defthm fn-scc-frames-consp
   (equal (consp (fn-scc-frames chunks i n q prev)) (consp chunks))))

(local
 (defthm fn-scc-decode-tree-of-program
   (implies (fn-scc-treep x)
            (equal (fn-scc-decode-tree (fn-scc-program x)) (list :ok x)))
   :hints (("Goal" :use fn-scc-decode-tree-of-encode
            :in-theory (disable fn-scc-decode-tree-of-encode fn-scc-decode-tree)))))

; The codec round trip: the segments the writer produces decode to the value.
; The two width hypotheses are the u64 header fields' codec width.
(defthm fn-scc-decode-segments-of-segments
  (implies (and (fn-scc-treep c)
                (< (+ 1 (len (fn-scc-encode c))) *fn-scc-u64-bound*)
                (< (fn-scc-value-sequence c) *fn-scc-u64-bound*))
           (equal (fn-scc-decode-segments (fn-scc-segments c segment-octets))
                  (list :ok c)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-scc-chunks-shape (payload (fn-scc-program c))
                            (seg segment-octets)))
           :in-theory (e/d (fn-scc-decode-segments fn-scc-segments)
                           (fn-scc-chunks-shape fn-scc-program
                            fn-scc-header fn-scc-seal fn-scc-chunks fn-scc-frames
                            fn-scc-decode-tree fn-scc-join fn-scc-treep
                            fn-scc-parse-header fn-scc-value-sequence)))))

; -----------------------------------------------------------------------------
; Guards: the host runs the encoder and the decoder compiled.

(defthm fn-scc-octet-listp-true
  (implies (fn-scc-octet-listp x) (true-listp x)))

(defthm fn-scc-parse-header-facts
  (implies (and (fn-scc-octet-listp seg) (fn-scc-parse-header seg))
           (and (natp (nth 2 (fn-scc-parse-header seg)))
                (fn-scc-octet-listp (nth 4 (fn-scc-parse-header seg)))))
  :hints (("Goal" :in-theory (enable fn-scc-parse-header fn-scc-u64-at))))

(defthm fn-scc-open-segment-facts
  (implies (and (fn-scc-octet-listp seg)
                (fn-scc-open-segment seg index count sequence prev))
           (and (true-listp (car (fn-scc-open-segment seg index count sequence prev)))
                (true-listp (cadr (fn-scc-open-segment seg index count sequence prev)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-scc-parse-header-facts)
                 (:instance fn-scc-octet-listp-true
                            (x (nthcdr (nth 2 (fn-scc-parse-header seg))
                                       (nth 4 (fn-scc-parse-header seg))))))
           :in-theory (e/d (fn-scc-open-segment)
                           (fn-scc-parse-header fn-scc-seal fn-scc-parse-header-facts
                            fn-scc-octet-listp-true)))))

(defthm fn-scc-open-segment-chunk-octets
  (implies (and (fn-scc-octet-listp seg)
                (fn-scc-open-segment seg index count sequence prev))
           (fn-scc-octet-listp (car (fn-scc-open-segment seg index count sequence prev))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-scc-parse-header-facts))
           :in-theory (e/d (fn-scc-open-segment)
                           (fn-scc-parse-header fn-scc-seal fn-scc-parse-header-facts)))))

(defthm fn-scc-revappend-octets
  (implies (and (fn-scc-octet-listp a) (fn-scc-octet-listp b))
           (fn-scc-octet-listp (revappend a b))))

(defthm fn-scc-join-octets
  (implies (and (fn-scc-segment-listp segs) (fn-scc-octet-listp racc)
                (equal (car (fn-scc-join segs index count sequence prev racc)) :ok))
           (fn-scc-octet-listp (nth 1 (fn-scc-join segs index count sequence prev racc))))
  :hints (("Goal" :induct (fn-scc-join segs index count sequence prev racc)
           :in-theory (e/d (fn-scc-join) (fn-scc-open-segment)))))

(verify-guards fn-scc-u64-at)
(verify-guards fn-scc-parse-header)
(verify-guards fn-scc-segment-extent)
(verify-guards fn-scc-open-segment
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-scc-parse-header-facts))
           :in-theory (disable fn-scc-parse-header fn-scc-parse-header-facts))))
(verify-guards fn-scc-join
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-scc-open-segment-facts (seg (car segs))))
           :in-theory (disable fn-scc-open-segment fn-scc-open-segment-facts))))
(verify-guards fn-scc-run)
(verify-guards fn-scc-decode-tree)
(verify-guards fn-scc-decode-segments
  :hints (("Goal" :in-theory (disable fn-scc-parse-header fn-scc-join fn-scc-decode-tree))))
(verify-guards fn-scc-program)
(verify-guards fn-scc-renc)
(verify-guards fn-scc-encode)
(defthm fn-scc-chunks-true-list-listp
  (implies (true-listp payload)
           (true-list-listp (fn-scc-chunks payload seg))))
(verify-guards fn-scc-frames)
(verify-guards fn-scc-segments)
(verify-guards fn-scc-file-octets)
