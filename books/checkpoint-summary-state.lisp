; Captured authenticated C sources are a physical catalog, never a readiness bit.
; Each source root owns an actual extent; the table has one row per extent.
(in-package "ACL2")
(include-book "checkpoint-restore-semantic-state")
(fn2-book-layer :b)
(defcolumns fn2-checkpoint-summary
 ((phase (:enum fn2-checkpoint-summary-phase (:idle :capture :captured :applying :applied :retiring :retired :uncertain :promoting)))
  (tag :u60) (candidate :u32) (checkpoint :u60) (cut-commit :u60) (cut-event :u60)
  (history :u60) (incarnation :u60) (generation :u60) (semantic-tag :u60) (owner-kind :u8) (owner-slot :u32) (owner-gen :u60)
  (priority-base :u60) (bank :bool) (application-stage :u8) (count :u60) (cursor :u32) (target :u32) (free-count :u32) (installed :u60) (lease-count :u32))
 :extra-fields
 ((fn2-checkpoint-summary-descriptor :type (array (unsigned-byte 8) (64)) :initially 0
   :why "Active and sole pending catalog descriptors occupy disjoint 32-byte rows; old query identity survives until actual drain.")
  (fn2-checkpoint-summary-next-tag :type (unsigned-byte 60) :initially 0
   :why "Monotone catalog identity across cold investigation, live pending capture, abort and active replacement.")))
; Only actual cold/live constructors consume this value; no caller chooses
; a catalog tag. Include both extant rows so even a seeded old field cannot
; make the next constructor alias an extant source lease.
(defun fn2-checkpoint-summary-fresh-tag (fn2-checkpoint-summary)
 (declare (xargs :stobjs fn2-checkpoint-summary :guard (fn2-checkpoint-summary-wfp fn2-checkpoint-summary)))
 (+ 1 (max (fn2-checkpoint-summary-next-tag fn2-checkpoint-summary)
           (max (if (< 0 (fn2-checkpoint-summary-rows fn2-checkpoint-summary))
                    (fn2-checkpoint-summary-tag 0 fn2-checkpoint-summary) 0)
                (if (< 1 (fn2-checkpoint-summary-rows fn2-checkpoint-summary))
                    (fn2-checkpoint-summary-tag 1 fn2-checkpoint-summary) 0)))))

(defun fn2-checkpoint-summary-descriptor-word (r i fn2-checkpoint-summary)
 (declare (xargs :stobjs fn2-checkpoint-summary
 :guard (and (fn2-checkpoint-summary-wfp fn2-checkpoint-summary) (natp r) (< r 2)
             (< r (fn2-checkpoint-summary-rows fn2-checkpoint-summary)) (natp i) (< i 8))))
 (let ((at (+ (* 32 r) (* 4 i))))
  (+ (fn2-checkpoint-summary-descriptori at fn2-checkpoint-summary)
     (* 256 (fn2-checkpoint-summary-descriptori (+ at 1) fn2-checkpoint-summary))
     (* 65536 (fn2-checkpoint-summary-descriptori (+ at 2) fn2-checkpoint-summary))
     (* 16777216 (fn2-checkpoint-summary-descriptori (+ at 3) fn2-checkpoint-summary)))))

(defcolumns fn2-checkpoint-summary-sources
 ((tag :u60) (schema :u60) (rank :u60) (top :u8) (entries :u60)
  (unit :u60) (epoch :u60) (allocation :u60)
  (hash-0 :u32) (hash-1 :u32) (hash-2 :u32) (hash-3 :u32)
  (hash-4 :u32) (hash-5 :u32) (hash-6 :u32) (hash-7 :u32)))
; A loader/query retains its exact source until the corresponding close.
; Owner and generation bind the lease; a new catalog cannot overwrite it.
(defcolumns fn2-checkpoint-summary-leases
 ((live :bool) (tag :u60) (extent :u32) (run-row :u32) (owner-kind :u8) (owner-slot :u32) (owner-gen :u60)))
