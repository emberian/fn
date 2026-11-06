; Layer C: served authority's ordered records (docs/design/AUTHORITY-20261105.md
; section 2). These are ordered authorization decisions, not entries of
; identity.lisp's Message-ID relation; accounts*.lisp stays the ledger.
; Each schema lands with its served producer (D46): fn2-principals with E's
; principal-create, fn2-grants and its two folds with grant-set
; (books/authority.lisp).
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

; The owner-issued grants (section 2): one immutable row per grant mutation,
; keyed by the mutation's own commit event (the grant id is its revision);
; ENABLED 0 is a revocation, retained with its chain; PREVIOUS is the
; grantee's preceding authority-head (0 for its first). Written only by
; grant-set's transaction (authority.lisp), in one member with the current
; pointer, the head and the operation outcome.
(defrunschema fn2-grants :id 17
 :key ((grant (:id grant)))
 :value ((grantor (:id principal)) (grantee (:id principal))
         (right (:enum fn2-authority-right (:consume :read :append)))
         (scope (:enum fn2-authority-scope (:own-consumers :stream)))
         (target (:id stream)) (enabled :bool) (previous (:id grant)))
 :merge :unique)

; The current grant per (grantee, right, scope, target): the newest grant
; event naming it, in local committed order (never wall-clock); RIGHT and
; SCOPE are the port enums' codes. Declared :latest entries, not folds: the
; value is the writing member's own commit event, and a fold event's args
; cannot take it (fn2-succ-arg: :event is an insert's source only). The fold
; declaration over the grant events is owed with that generator growth.
(defrunschema fn2-grant-current :id 18
 :key ((grantee (:id principal)) (right :u8) (scope :u8) (target (:id stream)))
 :value ((grant (:id grant)))
 :merge :latest)

; A principal's authority head: its newest grant event, the revision that
; names its complete grant state (B's envelope grant field names it).
; :latest entries for the same reason as fn2-grant-current.
(defrunschema fn2-authority-head :id 19
 :key ((principal (:id principal)))
 :value ((grant (:id grant)))
 :merge :latest)
