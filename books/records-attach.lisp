; fn: the record codec's attachment.
;
; `books/records-seam.lisp' constrains `fn-record-encode' and
; `fn-record-decode-exact'.  A constrained function has no executable
; counterpart, so without this book no ground term over either evaluates.
; This book attaches the implementation, `fn-record-encode-impl' and
; `fn-record-decode-exact-impl' (books/records.lisp).
;
; WHAT THE ATTACHMENT CHANGES IN THE LOGIC: nothing.  `defattach' introduces
; no axiom; ACL2 proves that the attached pair satisfies every constraint of
; the seam's `encapsulate' (the hint cites the six implementation facts of
; books/records-canonicality.lisp) and in exchange makes ground calls
; evaluate, in the ACL2 loop and in the saved image.  ACL2 never uses an
; attachment inside a proof, and ignores one while evaluating a `defconst';
; a book that needs a ground record encoding in a constant computes it with
; the implementation name.
;
; WHO INCLUDES IT: the image build files (host/native/build.lisp,
; host/native/build-dtn.lisp) and the test books that evaluate ground
; vectors.  No proof book above the seam includes it.

(in-package "ACL2")
(include-book "records-seam")
(include-book "records-canonicality")

(defattach (fn-record-encode fn-record-encode-impl)
           (fn-record-decode-exact fn-record-decode-exact-impl)
           :hints (("Goal"
                    :use (fn-record-impl-encode-domain
                          fn-record-impl-round-trip
                          fn-record-impl-accepted-input-is-canonical
                          fn-record-impl-accepted-input-bounds
                          fn-record-impl-accepted-input-magic
                          fn-record-impl-accepted-schema-is-the-stamp-kind
                          fn-record-impl-encode-length-bound
                          fn-record-impl-encode-narrow-length-bound)
                    :in-theory (theory 'minimal-theory))))
