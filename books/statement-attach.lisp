; fn: the statement item codec's attachment.
;
; books/statement-seam.lisp constrains `fn-stmt-encode-items',
; `fn-stmt-decode-items-bounded' and `fn-stmt-decode-prefix-items-bounded'.
; This book attaches the implementation (books/statement-codec.lisp) to them.
; `defattach' introduces no axiom: ACL2 proves the attached functions satisfy
; every constraint of the seam (the hint cites the five implementation facts
; of statement-codec) and in exchange makes ground calls evaluate, in the
; ACL2 loop and in the saved image.  ACL2 never uses an attachment inside a
; proof and ignores one while evaluating a `defconst'.  The image build files
; and the test books that evaluate ground vectors include this book; no proof
; book above the seam does.

(in-package "ACL2")
(include-book "statement-seam")
(include-book "statement-codec")

(defattach (fn-stmt-encode-items fn-stmt-encode-items-impl)
           (fn-stmt-decode-items-bounded fn-stmt-decode-items-bounded-impl)
           (fn-stmt-decode-prefix-items-bounded
            fn-stmt-decode-prefix-items-bounded-impl)
           :hints (("Goal"
                    :use (fn-stmt-impl-encode-items-of-atom
                          fn-stmt-impl-encode-items-of-cons
                          fn-stmt-impl-decode-items-bounded-of-encode
                          fn-stmt-impl-decode-items-bounded-canonical
                          fn-stmt-impl-decode-items-bounded-items)
                    :in-theory (theory 'minimal-theory))))
