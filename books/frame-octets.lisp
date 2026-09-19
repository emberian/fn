; fn frame, part 1 of 4: octet primitives.
;
; Layout constants, the A-CRYPTO trailer function, the bounded splitter and
; the big-endian field conversions.  The grammar that uses them is in
; `frame-fields'; `books/frame.lisp' is the book an includer names and holds
; the prose introduction and the export theory for all four parts.

(in-package "ACL2")
(include-book "cbor-invariants")
(local (include-book "arithmetic/top" :dir :system))

; The CBOR big-endian conversions are this part's subject, so its proofs open
; them; the local disable after the u64 lemmas closes them again.
(local (in-theory (enable fn-cbor-codec-vocabulary
                          fn-cbor-invariants-vocabulary)))

; -----------------------------------------------------------------------------
; Layout constants

(defconst *fn-frame-magic-octets* 4)
(defconst *fn-frame-trailer-octets* 32)
; MAGIC(4) VERSION(1) KIND(1) LENGTH(4)
(defconst *fn-frame-header-octets* 10)
(defconst *fn-frame-overhead-octets* 42)

; A payload ceiling above every schema's own cap.  Callers pass their smaller
; cap; this constant only keeps the cons preflight a fixed amount of work.
(defconst *fn-frame-max-payload* 4194304)

; Field-level caps, matching the durable journals they describe.
(defconst *fn-frame-max-text* 512)
(defconst *fn-frame-max-blob* 131072)
(defconst *fn-frame-max-nat* 18446744073709551615)

(defconst *fn-frame-u32-modulus* 4294967296)

; -----------------------------------------------------------------------------
; A-CRYPTO: the integrity trailer function

; The only thing ACL2 knows about the trailer function is that it yields 32
; octets.  Collision resistance, preimage resistance and the concrete SHA-256
; algorithm are outside the logic; no theorem below claims any of them.  The
; local witness proves the constraints are satisfiable.
(encapsulate
  (((fn-frame-digest *) => *))
  (local (defun fn-frame-digest (octets)
           (declare (ignore octets))
           '(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
             0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)))
  (defthm fn-frame-digest-octet-listp
    (fn-cbor-octet-listp (fn-frame-digest octets)))
  (defthm fn-frame-digest-length
    (equal (len (fn-frame-digest octets)) *fn-frame-trailer-octets*)))

(defun fn-frame-digestp (xs)
  (declare (xargs :guard t))
  (and (fn-cbor-octet-listp xs)
       (equal (len xs) *fn-frame-trailer-octets*)))

(defun fn-frame-magicp (xs)
  (declare (xargs :guard t))
  (and (fn-cbor-octet-listp xs)
       (equal (len xs) *fn-frame-magic-octets*)))

; -----------------------------------------------------------------------------
; Bounded splitting
;
; One helper takes the first `n` octets off a list or reports that fewer than
; `n` are present.  It allocates at most `n` conses and examines at most `n`,
; so every caller below can put its bound check in front of its split.

(defun fn-frame-split (n xs)
  (declare (xargs :guard (and (natp n) (true-listp xs))))
  (if (zp n)
      (cons nil xs)
    (if (consp xs)
        (let ((rest (fn-frame-split (1- n) (cdr xs))))
          (and rest (cons (cons (car xs) (car rest)) (cdr rest))))
      nil)))

; A total positional accessor.  Every result record below is read through it,
; so no guard obligation anywhere depends on the shape of a value that failed
; to parse.
(defun fn-frame-item (n xs)
  (declare (xargs :guard (natp n)))
  (if (consp xs)
      (if (zp n) (car xs) (fn-frame-item (- n 1) (cdr xs)))
    nil))

; -----------------------------------------------------------------------------
; Structural facts about the splitter.  These are the shape lemmas every guard
; below needs; the value-level round trips live in `frame-invariants`.

(defthm fn-frame-octet-listp-true-listp
  (implies (fn-cbor-octet-listp xs) (true-listp xs))
  :rule-classes (:rewrite :forward-chaining))

(defthm fn-frame-at-mostp-bounds-len
  (implies (and (fn-cbor-at-mostp xs bound) (natp bound))
           (<= (len xs) bound))
  :rule-classes :linear)

(defthm fn-frame-split-prefix-len
  (implies (fn-frame-split n xs)
           (equal (len (car (fn-frame-split n xs))) (nfix n))))

(defthm fn-frame-split-prefix-true-listp
  (true-listp (car (fn-frame-split n xs))))

(defthm fn-frame-split-suffix-true-listp
  (implies (true-listp xs)
           (true-listp (cdr (fn-frame-split n xs)))))

(defthm fn-frame-split-prefix-octets
  (implies (and (fn-cbor-octet-listp xs) (fn-frame-split n xs))
           (fn-cbor-octet-listp (car (fn-frame-split n xs)))))

(defthm fn-frame-split-suffix-octets
  (implies (and (fn-cbor-octet-listp xs) (fn-frame-split n xs))
           (fn-cbor-octet-listp (cdr (fn-frame-split n xs)))))

; A successful split, stated both as the term callers test and as the cons it
; produces.  Rewriting a term to T is sound only in a propositional context,
; so the first form cannot turn `(car (fn-frame-split ...))` into `(car t)`.
(defthm fn-frame-split-exists
  (implies (<= (nfix n) (len xs))
           (fn-frame-split n xs)))

(defthm fn-frame-split-exists-consp
  (implies (<= (nfix n) (len xs))
           (consp (fn-frame-split n xs))))

(defthm fn-frame-split-suffix-len
  (implies (fn-frame-split n xs)
           (equal (len (cdr (fn-frame-split n xs)))
                  (- (len xs) (nfix n)))))

(defthm fn-frame-split-reassembles
  (implies (and (true-listp xs) (fn-frame-split n xs))
           (equal (append (car (fn-frame-split n xs))
                          (cdr (fn-frame-split n xs)))
                  xs)))

(defthm fn-frame-not-consp-when-len-zero
  (implies (equal (len a) 0) (not (consp a)))
  :hints (("Goal" :expand ((len a)))))

(defthm fn-frame-split-of-append
  (implies (and (true-listp a) (equal (len a) (nfix n)))
           (equal (fn-frame-split n (append a b)) (cons a b)))
  :hints (("Goal" :induct (fn-frame-split n a)
           :in-theory (enable fn-frame-split))))

; `len` counts conses, so a known length supplies the cons structure that the
; fixed-width big-endian readers' guards require.
(defthm fn-frame-len-2-conses
  (implies (equal (len xs) 2)
           (and (consp xs) (consp (cdr xs))))
  :hints (("Goal" :expand ((len xs) (len (cdr xs))))))

(defthm fn-frame-len-4-conses
  (implies (equal (len xs) 4)
           (and (consp xs) (consp (cdr xs))
                (consp (cdr (cdr xs))) (consp (cdr (cdr (cdr xs))))))
  :hints (("Goal" :expand ((len xs) (len (cdr xs)) (len (cdr (cdr xs)))
                           (len (cdr (cdr (cdr xs))))))))

(defthm fn-frame-len-8-conses
  (implies (equal (len xs) 8)
           (and (consp xs) (consp (cdr xs))
                (consp (cdr (cdr xs))) (consp (cdr (cdr (cdr xs))))))
  :hints (("Goal" :expand ((len xs) (len (cdr xs)) (len (cdr (cdr xs)))
                           (len (cdr (cdr (cdr xs))))))))

; Every fact the splitter is used for is now a lemma.  Opening its definition
; on a literal length would unroll it and defeat those lemmas, so from here it
; is reasoned about only through them.
(in-theory (disable (:d fn-frame-split)))

(defthm fn-frame-symbol-listp-true-listp
  (implies (symbol-listp xs) (true-listp xs))
  :rule-classes (:rewrite :forward-chaining))

(defthm fn-frame-u16-from-natp
  (implies (and (fn-cbor-octet-listp xs) (consp xs) (consp (cdr xs)))
           (natp (fn-cbor-u16-from xs)))
  :rule-classes (:rewrite :type-prescription))

(defthm fn-frame-u32-from-natp
  (implies (and (fn-cbor-octet-listp xs) (consp xs) (consp (cdr xs))
                (consp (cdr (cdr xs))) (consp (cdr (cdr (cdr xs)))))
           (natp (fn-cbor-u32-from xs)))
  :rule-classes (:rewrite :type-prescription))

; -----------------------------------------------------------------------------
; Unsigned big-endian fields beyond the CBOR profile's 32-bit argument

(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))

; Two CBOR 32-bit arguments, high half first.  The outer `mod` on the high
; half is a no-op for every value in the field's domain; it is written so that
; the guard obligation is the modulus bound rather than a division bound.
(defun fn-frame-u64-bytes (n)
  (declare (xargs :guard (and (natp n) (<= n *fn-frame-max-nat*))
                  :verify-guards nil))
  (append (fn-cbor-u32-bytes (mod (floor (nfix n) *fn-frame-u32-modulus*)
                                  *fn-frame-u32-modulus*))
          (fn-cbor-u32-bytes (mod (nfix n) *fn-frame-u32-modulus*))))

(verify-guards fn-frame-u64-bytes
  :hints (("Goal" :in-theory (disable floor))))

(defthm fn-frame-octet-listp-of-append
  (implies (and (fn-cbor-octet-listp a) (fn-cbor-octet-listp b))
           (fn-cbor-octet-listp (append a b))))

(defthm fn-frame-len-of-append
  (equal (len (append a b)) (+ (len a) (len b))))

(defthm fn-frame-u16-bytes-len
  (equal (len (fn-cbor-u16-bytes n)) 2)
  :hints (("Goal" :in-theory (e/d (fn-cbor-u16-bytes) (floor mod)))))

(defthm fn-frame-u32-bytes-len
  (equal (len (fn-cbor-u32-bytes n)) 4)
  :hints (("Goal" :in-theory (e/d (fn-cbor-u32-bytes) (floor mod)))))

(defthm fn-frame-u64-bytes-are-octets
  (fn-cbor-octet-listp (fn-frame-u64-bytes n))
  :hints (("Goal" :in-theory (e/d (fn-frame-u64-bytes)
                                  (floor mod fn-cbor-u32-bytes)))))

(defthm fn-frame-u64-bytes-len
  (equal (len (fn-frame-u64-bytes n)) 8)
  :hints (("Goal" :in-theory (e/d (fn-frame-u64-bytes)
                                  (floor mod fn-cbor-u32-bytes)))))

; The shape of every big-endian field is now a lemma, so nothing below has to
; reason about quotients and remainders again.
(local (in-theory (disable fn-cbor-u16-bytes fn-cbor-u32-bytes)))
(in-theory (disable (:d fn-frame-u64-bytes)))

(defun fn-frame-u64-from (xs)
  (declare (xargs :guard (and (fn-cbor-octet-listp xs) (equal (len xs) 8))
                  :verify-guards nil))
  (let ((split (fn-frame-split 4 xs)))
    (+ (* *fn-frame-u32-modulus* (fn-cbor-u32-from (car split)))
       (fn-cbor-u32-from (cdr split)))))

(verify-guards fn-frame-u64-from)

; -----------------------------------------------------------------------------
; Export theory.
;
; Every rule here is a shape fact about the splitter or a big-endian field:
; each one concludes `consp', `len', `true-listp' or an octet recognizer and
; backchains into another of them.  Left enabled they cost `frame-invariants'
; 108 s on a plain `append' associativity goal and `identity-invariants' 619 s
; on one octet lemma (3.1b of planning/lanes/LANEDUMP-twins-into-acl2.md).
; They are the frame cluster's proof vocabulary, named here in one place; the
; parts above enable this theory locally.

(deftheory fn-frame-octet-vocabulary
  '(    fn-frame-octet-listp-true-listp fn-frame-at-mostp-bounds-len
    fn-frame-split-prefix-len fn-frame-split-prefix-true-listp
    fn-frame-split-suffix-true-listp fn-frame-split-prefix-octets
    fn-frame-split-suffix-octets fn-frame-split-exists
    fn-frame-split-exists-consp fn-frame-split-suffix-len
    fn-frame-split-reassembles fn-frame-not-consp-when-len-zero
    fn-frame-split-of-append fn-frame-len-2-conses fn-frame-len-4-conses
    fn-frame-len-8-conses fn-frame-symbol-listp-true-listp
    fn-frame-u16-from-natp fn-frame-u32-from-natp
    fn-frame-octet-listp-of-append fn-frame-len-of-append
    fn-frame-u16-bytes-len fn-frame-u32-bytes-len
    fn-frame-u64-bytes-are-octets fn-frame-u64-bytes-len))

(in-theory (disable fn-frame-octet-listp-true-listp fn-frame-at-mostp-bounds-len
             fn-frame-split-prefix-len fn-frame-split-prefix-true-listp
             fn-frame-split-suffix-true-listp fn-frame-split-prefix-octets
             fn-frame-split-suffix-octets fn-frame-split-exists
             fn-frame-split-exists-consp fn-frame-split-suffix-len
             fn-frame-split-reassembles fn-frame-not-consp-when-len-zero
             fn-frame-split-of-append fn-frame-len-2-conses
             fn-frame-len-4-conses fn-frame-len-8-conses
             fn-frame-symbol-listp-true-listp fn-frame-u16-from-natp
             fn-frame-u32-from-natp fn-frame-octet-listp-of-append
             fn-frame-len-of-append fn-frame-u16-bytes-len
             fn-frame-u32-bytes-len fn-frame-u64-bytes-are-octets
             fn-frame-u64-bytes-len))
