; fn: the statement item codec seam.
;
; Every statement, receipt, detached signature, keyring snapshot and policy
; body is an item list turned into octets by one item-sequence codec (see the
; head of books/statement.lisp).  This book constrains that codec:
; `fn-stmt-encode-items', `fn-stmt-decode-items-bounded' and
; `fn-stmt-decode-prefix-items-bounded' are constrained functions whose local
; witnesses are the implementation (books/statement-codec.lisp).  Every book
; above the item codec -- books/statement.lisp's header, statement and
; receipt codecs first, then the stx, policy, principal and hybrid books --
; reasons about them through the constraints below and nothing else, so no
; goal above this book can carry the bounded decoder's body (plan 2026-09-22
; §4.1, step T1; review 2026-09-22, F3).  books/statement-attach.lisp
; attaches the implementation with `defattach' for evaluation.
;
; WHAT THE CONSTRAINTS SAY:
;   fn-stmt-encode-items-of-atom             an empty item list encodes to no octets
;   fn-stmt-encode-items-of-cons             an item list encodes to its items' CBOR encodings,
;                                            concatenated in order (the stream is self-delimiting)
;   fn-stmt-decode-items-bounded-of-encode   at the profile budgets, a list of at most FUEL items
;                                            whose encoding fits the input cap decodes to itself
;   fn-stmt-decode-items-bounded-canonical   at the profile budgets, an accepted input is the
;                                            encoding of the items it decodes to
;   fn-stmt-decode-items-bounded-items       at the profile budgets, what an accepted input
;                                            decodes to is an item list
; The two encoder equations determine the encoder completely: it is the
; concatenation the format specifies, and nothing in it is worth hiding.
; The decoder is what the seam hides; the three facts about it are the ones
; the books above used before the seam existed
; (`fn-stmt-decode-items-of-encode-items', `fn-stmt-encode-items-of-decode-items',
; `fn-stmt-decode-items-value-is-item-list', derived below under their old
; names for the profile wrapper `fn-stmt-decode-items').
;
; WHAT THEY DO NOT SAY: anything about the bounded decoder at other budgets,
; or anything about `fn-stmt-decode-prefix-items-bounded' beyond its guard.
; No book proves such a fact today (checkpoint-compaction and the keyring
; and accept records call those decoders in definitions whose guards are
; not verified or do not reach them); a book that needs one has found a
; property this seam should export, which is a change here and in
; statement-codec together.

(in-package "ACL2")
(include-book "statement-items")

(encapsulate
  (((fn-stmt-encode-items *) => *
    :formals (items) :guard (fn-stmt-item-listp items))
   ((fn-stmt-decode-items-bounded * * * *) => *
    :formals (fuel octets outer-budget item-budget)
    :guard (and (natp fuel) (natp outer-budget) (natp item-budget)))
   ((fn-stmt-decode-prefix-items-bounded * * * *) => *
    :formals (count octets outer-budget item-budget)
    :guard (and (natp count) (natp outer-budget) (natp item-budget))))

  (local (include-book "statement-codec"))

  (local (defun fn-stmt-encode-items (items)
           (declare (xargs :guard (fn-stmt-item-listp items)))
           (fn-stmt-encode-items-impl items)))

  (local (defun fn-stmt-decode-items-bounded (fuel octets outer-budget item-budget)
           (declare (xargs :guard (and (natp fuel) (natp outer-budget)
                                       (natp item-budget))))
           (fn-stmt-decode-items-bounded-impl fuel octets outer-budget item-budget)))

  (local (defun fn-stmt-decode-prefix-items-bounded (count octets outer-budget item-budget)
           (declare (xargs :guard (and (natp count) (natp outer-budget)
                                       (natp item-budget))))
           (fn-stmt-decode-prefix-items-bounded-impl count octets outer-budget
                                                     item-budget)))

  (defthm fn-stmt-encode-items-of-atom
    (implies (not (consp items))
             (equal (fn-stmt-encode-items items) nil))
    :hints (("Goal" :use fn-stmt-impl-encode-items-of-atom)))

  (defthm fn-stmt-encode-items-of-cons
    (equal (fn-stmt-encode-items (cons item items))
           (append (fn-cbor-encode item) (fn-stmt-encode-items items)))
    :hints (("Goal" :use fn-stmt-impl-encode-items-of-cons)))

  (defthm fn-stmt-decode-items-bounded-of-encode
    (implies (and (fn-stmt-item-listp items)
                  (natp fuel)
                  (<= (len items) fuel)
                  (<= (len (fn-stmt-encode-items items)) *fn-cbor-max-input*))
             (equal (fn-stmt-decode-items-bounded
                     fuel (fn-stmt-encode-items items)
                     *fn-cbor-max-input* *fn-cbor-max-bytes*)
                    (fn-stmt-ok items)))
    :hints (("Goal" :use fn-stmt-impl-decode-items-bounded-of-encode)))

  (defthm fn-stmt-decode-items-bounded-canonical
    (implies (fn-stmt-okp (fn-stmt-decode-items-bounded
                           fuel octets *fn-cbor-max-input* *fn-cbor-max-bytes*))
             (equal (fn-stmt-encode-items
                     (fn-stmt-value (fn-stmt-decode-items-bounded
                                     fuel octets
                                     *fn-cbor-max-input* *fn-cbor-max-bytes*)))
                    octets))
    :hints (("Goal" :use fn-stmt-impl-decode-items-bounded-canonical)))

  (defthm fn-stmt-decode-items-bounded-items
    (implies (fn-stmt-okp (fn-stmt-decode-items-bounded
                           fuel octets *fn-cbor-max-input* *fn-cbor-max-bytes*))
             (fn-stmt-item-listp
              (fn-stmt-value (fn-stmt-decode-items-bounded
                              fuel octets
                              *fn-cbor-max-input* *fn-cbor-max-bytes*))))
    :hints (("Goal" :use fn-stmt-impl-decode-items-bounded-items))))

; -----------------------------------------------------------------------------
; The profile wrapper, and the facts the books above cite by their old names.
; `fn-stmt-decode-items' was always this wrapper; it stays an ordinary,
; enabled definition over the constrained decoder.

(defun fn-stmt-decode-items (fuel octets)
  (declare (xargs :guard (natp fuel)))
  (fn-stmt-decode-items-bounded fuel octets
                                *fn-cbor-max-input* *fn-cbor-max-bytes*))

; The cons equation in the form a definition opens in: under `consp'.
(defthm fn-stmt-encode-items-when-consp
  (implies (consp items)
           (equal (fn-stmt-encode-items items)
                  (append (fn-cbor-encode (car items))
                          (fn-stmt-encode-items (cdr items)))))
  :hints (("Goal" :use ((:instance fn-stmt-encode-items-of-cons
                                   (item (car items)) (items (cdr items))))
           :in-theory (disable fn-stmt-encode-items-of-cons))))

(local (in-theory (enable fn-cbor-invariants-vocabulary
                          fn-record-invariants-vocabulary)))

(defthm fn-stmt-encode-items-is-octet-list
  (fn-cbor-octet-listp (fn-stmt-encode-items items))
  :hints (("Goal" :induct (len items))))

(defthm fn-stmt-encode-items-is-true-list
  (true-listp (fn-stmt-encode-items items))
  :hints (("Goal" :induct (len items))))

(defthm fn-stmt-encode-items-of-append
  (equal (fn-stmt-encode-items (append a b))
         (append (fn-stmt-encode-items a) (fn-stmt-encode-items b)))
  :hints (("Goal" :induct (len a))))

(local (in-theory (disable fn-cbor-invariants-vocabulary
                           fn-record-invariants-vocabulary)))

; Opening the encoder on a term merely known to be a cons is left to a
; caller that asks for it by name: enabled, it takes apart an encoding whose
; length a caller's own bound already describes (`fn-stmt-encoding-bound',
; over `fn-stmt-header-items').  The cons equation opens explicit lists, as
; the definition did before the seam.
(in-theory (disable fn-stmt-encode-items-when-consp))

(defthm fn-stmt-decode-items-of-encode-items
  (implies (and (fn-stmt-item-listp items)
                (natp fuel)
                (<= (len items) fuel)
                (<= (len (fn-stmt-encode-items items)) *fn-cbor-max-input*))
           (equal (fn-stmt-decode-items fuel (fn-stmt-encode-items items))
                  (fn-stmt-ok items)))
  :hints (("Goal" :use fn-stmt-decode-items-bounded-of-encode
           :in-theory (e/d (fn-stmt-decode-items)
                           (fn-stmt-decode-items-bounded-of-encode
                            fn-stmt-encode-items-when-consp)))))

(defthm fn-stmt-encode-items-of-decode-items
  (implies (fn-stmt-okp (fn-stmt-decode-items fuel octets))
           (equal (fn-stmt-encode-items
                   (fn-stmt-value (fn-stmt-decode-items fuel octets)))
                  octets))
  :hints (("Goal" :use fn-stmt-decode-items-bounded-canonical
           :in-theory (e/d (fn-stmt-decode-items)
                           (fn-stmt-decode-items-bounded-canonical
                            fn-stmt-encode-items-when-consp)))))

(defthm fn-stmt-decode-items-value-is-item-list
  (implies (fn-stmt-okp (fn-stmt-decode-items fuel octets))
           (fn-stmt-item-listp
            (fn-stmt-value (fn-stmt-decode-items fuel octets))))
  :hints (("Goal" :use fn-stmt-decode-items-bounded-items
           :in-theory (e/d (fn-stmt-decode-items)
                           (fn-stmt-decode-items-bounded-items)))))
