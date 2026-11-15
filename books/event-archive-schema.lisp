; Lossless physical event archive. Its key is the journal's physical history
; namespace, distinct from semantic lineage/domain inside the canonical bytes.
; The bound is one existing journal sector, not a stored-history count limit.
(in-package "ACL2")
(include-book "runs-schema")
(fn2-book-layer :c)
(defconst *fn2-event-archive-schema* 20)
; Schema21 is reserved for actual shared Merkle carry outputs. No proof-node
; layout or inclusion-path authority is claimed by the member archive alone.
(defrunschema fn2-event-archive-member :id 20 :internal t
 :key ((history (:id history)) (incarnation (:id incarnation)) (event (:id event)))
 :value ((canonical (:octets 4096)) (leaf :digest))
 :merge :unique)
