; Captured authenticated C sources are a physical catalog, never a readiness bit.
; Each source root owns an actual extent; the table has one row per extent.
(in-package "ACL2")
(include-book "checkpoint-restore-semantic-state")
(fn2-book-layer :b)
(defcolumns fn2-checkpoint-summary
 ((phase (:enum fn2-checkpoint-summary-phase (:idle :capture :captured :applying :applied :retiring :retired :uncertain)))
  (tag :u60) (candidate :u32) (checkpoint :u60) (cut-commit :u60) (cut-event :u60)
  (history :u60) (incarnation :u60) (generation :u60) (semantic-tag :u60) (owner-kind :u8) (owner-slot :u32) (owner-gen :u60)
  (priority-base :u60) (application-stage :u8) (count :u60) (cursor :u32) (installed :u60) (lease-count :u32))
 :extra-fields
 ((fn2-checkpoint-summary-descriptor :type (array (unsigned-byte 8) (32)) :initially 0
   :why "Exact source descriptor retained independently of the mutable cold investigation.")))
(defcolumns fn2-checkpoint-summary-sources
 ((tag :u60) (schema :u60) (rank :u60) (top :u8) (entries :u60)
  (unit :u60) (epoch :u60) (allocation :u60)
  (hash-0 :u32) (hash-1 :u32) (hash-2 :u32) (hash-3 :u32)
  (hash-4 :u32) (hash-5 :u32) (hash-6 :u32) (hash-7 :u32)))
; A loader/query retains its exact source until the corresponding close.
; Owner and generation bind the lease; a new catalog cannot overwrite it.
(defcolumns fn2-checkpoint-summary-leases
 ((live :bool) (tag :u60) (extent :u32) (run-row :u32) (owner-kind :u8) (owner-slot :u32) (owner-gen :u60)))
