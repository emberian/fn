; fn: the record encoder's attachment in the host image, over the concrete
; recognizer.
;
; books/records-attach.lisp attaches fn-record-encode-impl to the seam's
; fn-record-encode; every book that evaluates ground records includes it
; (through books/codec-attach.lisp).  This book replaces that attachment,
; for the host images that include it after codec-attach
; (host/native/build.lisp, build-dtn.lisp, build-store-test.lisp, and
; tools/run_store.py's session), with fn-rcon-record-encode-impl
; (books/records-codec-concrete.lisp): the implementation with the record
; recognised over its strings in place, EQUAL to fn-record-encode-impl on
; every input with no hypothesis
; (fn-rcon-record-encode-impl-is-record-encode-impl).  The decoder keeps
; its attachment; a seam's functions are attached together, so it is
; named again.
;
; Why a second attachment book rather than an edit of records-attach: the
; attachment is not logic, so the two attachments evaluate every ground
; fn-record-encode to the same value (the keystone above), and records-attach
; is in the include closure of most certified roots, which an edit would
; send back to certification for no change in any theorem.  The host
; evaluates through this one.
;
; WHAT THE ATTACHMENT CHANGES IN THE LOGIC: nothing (see records-attach).

(in-package "ACL2")
(include-book "records-attach")
(include-book "records-codec-concrete")

; The implementation facts are stated of fn-record-encode-impl; the twin's
; keystone rewrites the attached function to it.
(defattach (fn-record-encode fn-rcon-record-encode-impl)
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
                    :in-theory (union-theories
                                 '(fn-rcon-record-encode-impl-is-record-encode-impl)
                                 (theory 'minimal-theory)))))
