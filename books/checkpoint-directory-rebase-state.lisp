; Exact owner/cut and bounded source/suffix scan for runtime base publication.
(in-package "ACL2")
(include-book "columns")
(fn2-book-layer :b)
(defcolumns fn2-directory-rebase
 ((phase (:enum fn2-directory-rebase-phase (:idle :scan :source-scanned :committed)))
  (token :u60) (owner-kind :u8) (owner-slot :u32) (owner-gen :u60)
  (candidate :u32) (checkpoint :u60) (history :u60) (incarnation :u60)
  (base-batch :u60) (base-event :u60) (target :u60) (target-event :u60)
  (cursor :u60) (last-event :u60) (scanned :u60)
  (installation :u60) (installation-event :u60) (suffix-scanned :u60)
  (source-row :u32) (source-extent :u32) (source-epoch :u60) (source-allocation :u60))
 :extra-fields ((fn2-directory-rebase-seal-words :type (array (unsigned-byte 32) (8)) :initially 0
  :why "Exact final scanned batch seal; tentative predecessor until summary and bank evidence joins.")))
