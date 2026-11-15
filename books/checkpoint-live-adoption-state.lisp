; One actual live adoption continuation for the sole maintenance actor.
(in-package "ACL2")
(include-book "checkpoint-summary-state")
(include-book "columns-row-swap")
(fn2-book-layer :c)
(defcolumn-row-swap fn2-checkpoint-summary)
(defcolumns fn2-checkpoint-live-adoption
 ((phase (:enum fn2-checkpoint-live-adoption-phase
   (:idle :preflight :prepared :install :versions :retire-runs :retire-overlays :swap :adopted :old-released :complete)))
  (token :u60) (owner-kind :u8) (owner-slot :u32) (owner-gen :u60) (writer-token :u60)
  (candidate :u32) (catalog-tag :u60) (old-tag :u60) (cut-commit :u60) (cut-event :u60)
  (history :u60) (incarnation :u60) (base :u60) (version :u60)
  (cursor :u32) (source-cursor :u32) (insert-cursor :u32) (free :u32)
  (run-limit :u32) (overlay-limit :u32) (source-limit :u32)))
