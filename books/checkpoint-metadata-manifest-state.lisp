; Manifest continuation state, independent of its source builder.
(in-package "ACL2")
(include-book "columns")
(fn2-book-layer :c)

(defcolumns fn2-checkpoint-metadata-manifest
 ((phase (:enum fn2-checkpoint-metadata-manifest-phase (:idle :adding :finishing :scan :complete :uncertain)))
  (token :u60) (owner-kind :u8) (owner-slot :u32) (owner-gen :u60)
  (build :u32) (candidate :u32) (entry-base :u32) (hash-slot :u32) (hash-gen :u60)
  (entries :u60) (root-level :u8) (root-extent :u32)
  (scan-row :u32) (seen :u60) (intended-bytes :u60) (completed-bytes :u60)
  ; Disjoint extent-indexed pending catalog; control uses the original row0 fields.
  ; A producer token names only accepted directory emits, never publication.
  (catalog-token :u60) (catalog-rank :u60) (catalog-source-kind :u8)
  (catalog-source-row :u32) (catalog-source-order :u60) (catalog-schema :u60)
  (catalog-top :u8) (catalog-entries :u60) (catalog-epoch :u60) (catalog-allocation :u60)
  (catalog-hash-0 :u32) (catalog-hash-1 :u32) (catalog-hash-2 :u32) (catalog-hash-3 :u32) (catalog-hash-4 :u32) (catalog-hash-5 :u32) (catalog-hash-6 :u32) (catalog-hash-7 :u32)))
