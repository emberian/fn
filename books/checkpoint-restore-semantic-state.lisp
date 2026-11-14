; Cold semantic page carrier: state only, independent of C codec assembly.
(in-package "ACL2")
(include-book "checkpoint-restore-provenance")
(fn2-book-layer :b)
(defcolumns fn2-checkpoint-restore-semantic
 ((phase (:enum fn2-checkpoint-restore-semantic-phase (:idle :read :verify :header :entries :uncertain)))
  (candidate :u32) (source-checkpoint :u60) (source-cut-commit :u60) (source-cut-event :u60)
  (source-history :u60) (source-incarnation :u60) (unit :u60) (epoch :u60) (allocation :u60)
  (cursor :u32) (checker-row :u32) (field-base :u32) (checker-phase :u8) (checker-pos :u32)
  (checker-zero :u32) (checker-pad :u32) (checker-pad-end :u32) (checker-geom :u32) (checker-previous-seal-offset :u32)
  (slot :u32) (gen :u60) (owner-kind :u8) (owner-slot :u32) (owner-gen :u60)
  (schema :u60) (run :u60) (level :u8) (entries :u32))
 :extra-fields
 ((fn2-checkpoint-restore-semantic-hash :type (array (unsigned-byte 8) (64)) :initially 0
   :why "Root1 expected hash and exact source descriptor hash retained across physical reads.")))

