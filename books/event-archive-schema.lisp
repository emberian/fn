; Lossless canonical archive keyed in the checkpoint archive's physical pair.
; Original journal physical namespace is preserved by the exact witness bytes;
; semantic lineage/domain remains inside the canonical record headers.
; The bound is one existing journal sector, not a stored-history count limit.
(in-package "ACL2")
(include-book "runs-schema")
(fn2-book-layer :c)
(defconst *fn2-event-archive-schema* 20)
; Schema21 is reserved for actual shared Merkle carry outputs. No proof-node
; layout or inclusion-path authority is claimed by the member archive alone.
(make-event
 (value `(defrunschema fn2-event-archive-member :id 20 :internal t
 :key ((history (:id history)) (incarnation (:id incarnation)) (event (:id event)))
 :value ((canonical (:octets 4096)) (leaf :digest)
         (batch-first (:id event))
         (original-records-header (:octets ,*fn2-format-frame-header-max-size*))
         (original-sealed-batch (:octets ,*fn2-format-sealed-batch-max-size*)))
 :merge :unique)))
