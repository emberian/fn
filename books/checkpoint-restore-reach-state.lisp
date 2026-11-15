; Shared cold reach identities, minted before allocation-map intake. The
; semantic constructor FIFO keeps its own uniqueness tag and is not this tag.
(in-package "ACL2")
(include-book "columns")
(fn2-book-layer :b)
(defcolumns fn2-checkpoint-restore-reach
 ((generation :u60) (epoch :u60) (allocation :u60) (role-bits :u16)
  (state (:enum fn2-checkpoint-restore-reach-state (:empty :named :mapped)))
  (last-role (:enum fn2-checkpoint-restore-reach-role
    (:descriptor :semantic :allocation-map :event-directory :frontier :arena
     :journal :journal-ticket :payload-manifest :payload-raw :payload-block :semantic-source)))))
(defcolumns fn2-checkpoint-restore-reach-control
 ((generation :u60) (candidate :u32) (source-checkpoint :u60)
  (source-cut-commit :u60) (source-cut-event :u60)
  (source-history :u60) (source-incarnation :u60))
 :extra-fields
 ((fn2-checkpoint-restore-reach-control-descriptor :type (array (unsigned-byte 8) (32)) :initially 0
   :why "Exact authenticated descriptor identity shared by map, roots, semantic and payload reach investigations.")))
