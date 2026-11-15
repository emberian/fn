; One retained, exact-owner checkpoint inventory source. Original E rows stay
; owned and immutable through the held cut; this state never fabricates E rows.
(in-package "ACL2")
(include-book "columns")
(fn2-book-layer :b)
(defcolumns fn2-release-inventory-build
 ((phase (:enum fn2-release-inventory-build-phase
    (:idle :scan :reserve :zero :entries :header :physical-header :page :bound :tail :done :uncertain)))
  (token :u60) (owner-kind :u8) (owner-slot :u32) (owner-gen :u60)
  (candidate :u32) (cut-commit :u60) (cut-event :u60) (history :u60) (incarnation :u60)
  (slot :u32) (gen :u60) (scratch :u32) (scratch-gen :u60)
  (rows-count :u32) (scan :u32) (count :u32) (cursor :u32) (remaining :u32)
  (pages :u60) (ordinal :u60) (first :u32) (end :u32) (zero :u32) (payload :u32)
  (extent :u32) (epoch :u60) (allocation :u60) (child :u32) (head :u32)
  (completed-pages :u60) (completed-bytes :u60)
  (transfer-cursor :u32)))
