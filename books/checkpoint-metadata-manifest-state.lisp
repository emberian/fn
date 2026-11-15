; Manifest continuation state, independent of its source builder.
(in-package "ACL2")
(include-book "columns")
(fn2-book-layer :c)

(defcolumns fn2-checkpoint-metadata-manifest
 ((phase (:enum fn2-checkpoint-metadata-manifest-phase (:idle :adding :finishing :scan :complete :uncertain)))
  (token :u60) (owner-kind :u8) (owner-slot :u32) (owner-gen :u60)
  (build :u32) (candidate :u32) (entry-base :u32) (hash-slot :u32) (hash-gen :u60)
  (entries :u60) (root-level :u8) (root-extent :u32)
  (scan-row :u32) (seen :u60) (intended-bytes :u60) (completed-bytes :u60)))
