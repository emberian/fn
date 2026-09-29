; fn: the tree codec of the store checkpoint (FNSC) -- the postfix program
; for a stack machine and its decoder (lane arena-store-8, 2026-09-28: split
; out of books/store-checkpoint-codec.lisp, whose segment framing includes
; books/frame-trailer and so books/crypto-attach).  Prefix fn-scc-.
;
; The history image (books/history-pages.lisp) stores each event's tree as
; this program and decodes it on access; it needs the tree codec and
; nothing of the segment framing, the frame trailer or the digest
; attachments.  Keeping those out of the image's closure keeps them out of
; books/store-files' closure, which the served image includes from every
; top-level include (the native image's thread-local storage, see
; planning/evidence/arena-store-8-tls.md).
;
; The codec (store-checkpoint-codec's former sections 1-5):
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
; KEYSTONE fn-scc-decode-tree-of-encode.
(in-package "ACL2")
;; The floor/mod lemmas the codec was proved with when it lived in
;; store-checkpoint-codec, over frame-trailer's closure (books/cbor-invariants
;; includes them there); local here, so no includer's theory changes.
(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
(local (include-book "arithmetic/top" :dir :system))
(local
 (defthm fn-scc-len-append
   (equal (len (append a b)) (+ (len a) (len b)))))

(local
 (defthm fn-scc-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

(defconst *fn-scc-magic* '(70 78 83 67))         ; "FNSC"
(defconst *fn-scc-schema* 3)
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

; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-scc-chars-octets-loop (chars acc)
  (declare (xargs :guard (and (character-listp chars) (true-listp acc)) :verify-guards nil))
  (if (consp chars)
      (fn-scc-chars-octets-loop (cdr chars) (cons (char-code (car chars)) acc))
    (revappend acc nil)))

(defun fn-scc-chars-octets (chars)
  (declare (xargs :verify-guards nil :guard (character-listp chars)))
  (mbe :logic
       (if (consp chars)
           (cons (char-code (car chars)) (fn-scc-chars-octets (cdr chars)))
         nil)
       :exec (fn-scc-chars-octets-loop chars nil)))

(local
 (defthm fn-scc-chars-octets-loop-is-revappend
   (equal (fn-scc-chars-octets-loop chars acc)
          (revappend acc (fn-scc-chars-octets chars)))
   :hints (("Goal" :induct (fn-scc-chars-octets-loop chars acc)
                   :in-theory (union-theories '(fn-scc-chars-octets-loop fn-scc-chars-octets revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-scc-chars-octets-loop)

(verify-guards fn-scc-chars-octets
  :hints (("Goal"
           :in-theory
           (union-theories '(revappend fn-scc-chars-octets)
                           (union-theories (theory 'minimal-theory)
                                           (executable-counterpart-theory :here)))
           :use
           ((:instance fn-scc-chars-octets-loop-is-revappend (acc nil))))))


; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-scc-octets-chars-loop (xs acc)
  (declare (xargs :guard (and (fn-scc-octet-listp xs) (true-listp acc)) :verify-guards nil))
  (if (consp xs)
      (fn-scc-octets-chars-loop (cdr xs) (cons (code-char (car xs)) acc))
    (revappend acc nil)))

(defun fn-scc-octets-chars (xs)
  (declare (xargs :verify-guards nil :guard (fn-scc-octet-listp xs)))
  (mbe :logic
       (if (consp xs)
           (cons (code-char (car xs)) (fn-scc-octets-chars (cdr xs)))
         nil)
       :exec (fn-scc-octets-chars-loop xs nil)))

(local
 (defthm fn-scc-octets-chars-loop-is-revappend
   (equal (fn-scc-octets-chars-loop xs acc)
          (revappend acc (fn-scc-octets-chars xs)))
   :hints (("Goal" :induct (fn-scc-octets-chars-loop xs acc)
                   :in-theory (union-theories '(fn-scc-octets-chars-loop fn-scc-octets-chars revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-scc-octets-chars-loop)

(verify-guards fn-scc-octets-chars
  :hints (("Goal"
           :in-theory
           (union-theories '(revappend fn-scc-octets-chars)
                           (union-theories (theory 'minimal-theory)
                                           (executable-counterpart-theory :here)))
           :use
           ((:instance fn-scc-octets-chars-loop-is-revappend (acc nil))))))


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

