; Layer C: served authority's ordered records (docs/design/AUTHORITY-20261105.md
; section 2). These are ordered authorization decisions, not entries of
; identity.lisp's Message-ID relation; accounts*.lisp stays the ledger.
; Each schema lands with its served producer (D46): fn2-principals with E's
; principal-create (books/authority.lisp).
(in-package "ACL2")
(include-book "runs-schema")
(fn2-book-layer :c)

; A principal's name (at most 64 octets) to its durable identity, D7's
; fn2-account-principal-id (slot * 2^32 + incarnation). Unique: a name is
; created once for the store's life; a repeated principal-create of the same
; name reads this row and answers its recorded identity. Written by
; principal-create's transaction and at store genesis ("anonymous", "owner");
; read by principal-bind and by principal-create's repeat lookup.
(defrunschema fn2-principals :id 16
 :key ((name (:octets 64)))
 :value ((principal (:id principal)))
 :merge :unique)
