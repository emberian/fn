; fn: statement item sequences and result records, without the item codec.
;
; What a book above the statement item codec may see of an item sequence:
; the result records `(:ok value)', `(:ok value rest)', `(:error code)' with
; their total accessors, and `fn-stmt-item-listp', a list of bounded CBOR
; values.  Neither is a codec.  The codec that turns an item list into octets
; and back is `books/statement-codec.lisp' (the implementation) behind
; `books/statement-seam.lisp' (the constrained functions every book above it
; calls); plan 2026-09-22 section 4.1, step T1.

(in-package "ACL2")
(include-book "crypto-seam")
(include-book "statement-results")
(include-book "statement-items-shape")

; -----------------------------------------------------------------------------
; Result records.  (:ok value) / (:ok value rest) / (:error code).  Accessors
; are total so every consumer has guard T.








; -----------------------------------------------------------------------------
; Item sequences



; The two shape facts an indexing consumer of an item sequence needs, the
; twins of `fn-stmt-id-listp-implies-true-listp' below.  A successful bounded
; decode delivers `fn-stmt-item-listp' of its value
; (fn-stmt-decode-items-value-is-item-list, books/statement-invariants); from
; that a caller's `nth' guard needs the sequence to be proper and its `cdr'
; guard needs an index to land on an item pair or off the end.  With a literal
; fuel the decoder suggests no induction, so these are what decide those
; guards -- measured 2026-09-22 on `fn-hsig-keyring-snapshot-value'
; (books/hybrid-store), whose extraction runs before its own shape checks.
; Both are withdrawn immediately: a `true-listp' rewrite rule that backchains
; into a recognizer joins the other recognizer-implies-true-listp rules of the
; books above into a rewriter loop (call depth 1000 in
; books/statement-invariants, same date), so a caller names them in its hint.




(in-theory (disable fn-stmt-item-listp-implies-true-listp
                    fn-stmt-item-listp-nth-is-item-or-nil))
