; Selected cold investigation provenance, not serving or discard authority.
(in-package "ACL2")
(include-book "columns")
(fn2-book-layer :b)
(defcolumns fn2-checkpoint-selected-source
 ((phase (:enum fn2-checkpoint-selected-source-phase
    (:idle :investigating :validated :projecting :projected :uncertain)))
  (tag :u60) (owner-kind :u8) (owner-slot :u32) (owner-gen :u60)
  (candidate :u32) (checkpoint :u60) (cut-commit :u60) (cut-event :u60)
  (history :u60) (incarnation :u60) (generation :u60))
 :extra-fields
 ((fn2-checkpoint-selected-source-descriptor :type (array (unsigned-byte 8) (32)) :initially 0
   :why "Exact chosen descriptor survives re-investigation; it grants no allocator or serving authority.")))
