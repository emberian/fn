; Cold semantic page carrier: state only, independent of C codec assembly.
(in-package "ACL2")
(include-book "checkpoint-restore-provenance")
(fn2-book-layer :b)
(defcolumns fn2-checkpoint-restore-semantic
 ((phase (:enum fn2-checkpoint-restore-semantic-phase (:idle :read :verify :header :entries :uncertain :find :complete :payload)))
  (tag :u60) (scan :u32) (expected-known :bool) (expected-count :u60) (seen :u60) (page-kind :u8)
  (candidate :u32) (source-checkpoint :u60) (source-cut-commit :u60) (source-cut-event :u60)
  (source-history :u60) (source-incarnation :u60) (unit :u60) (epoch :u60) (allocation :u60)
  (cursor :u32) (checker-row :u32) (field-base :u32) (checker-phase :u8) (checker-pos :u32)
  (checker-zero :u32) (checker-pad :u32) (checker-pad-end :u32) (checker-geom :u32) (checker-previous-seal-offset :u32)
  (slot :u32) (gen :u60) (owner-kind :u8) (owner-slot :u32) (owner-gen :u60)
  (schema :u60) (run :u60) (level :u8) (entries :u32))
 :extra-fields
 ((fn2-checkpoint-restore-semantic-hash :type (array (unsigned-byte 8) (64)) :initially 0
   :why "Root1 expected hash and exact source descriptor hash retained across physical reads.")))


; One pending/done physical page per actual allocator extent. Tags separate
; candidate investigations without an unbounded clear at begin.
(defcolumns fn2-checkpoint-restore-semantic-work
 ((tag :u60) (state (:enum fn2-checkpoint-restore-semantic-work-state (:empty :pending :done)))
  (unit :u60) (epoch :u60) (allocation :u60) (page-kind :u8)
  (schema :u60) (run :u60) (level :u8) (expected-count :u60)
  (hash-0 :u32)
  (hash-1 :u32)
  (hash-2 :u32)
  (hash-3 :u32)
  (hash-4 :u32)
  (hash-5 :u32)
  (hash-6 :u32)
  (hash-7 :u32)
))
