; Persistent extent reclamation is not yet connected to the served machine.
; An unbound requirement is deliberate: allocator-local release predicates
; cannot discharge the lifetime of reads, recovery roots and persisted release.
(in-package "ACL2")
(include-book "owed")
(fn2-book-layer :b)

(make-event
 (value
  (fn2-declare '(:square fn2-persistent-reclamation-lifetime)
   '(:schema :invariant :layer :b
     :owner (:square fn2-persistent-reclamation-lifetime)
     :doc "Served persistent extent recycling preserves every reachable or pinned article across reads, borrows, outstanding I/O, recovery roots and checkpoint installation; reuse follows persisted release and excludes stale generations. The current allocator model has no served reclamation coordinator. Unbound until the composed served lifetime contract exists; retaining everything does not establish reclamation progress."
     :proof (:owed) :checks nil)
   nil nil)))
