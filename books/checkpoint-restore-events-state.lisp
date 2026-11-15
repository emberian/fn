; Cold event source state shares the actual map investigation generation.
; A journal queue is distinct from alias-permitting typed protection rows.
(in-package "ACL2")
(include-book "checkpoint-restore-reach-state")
(include-book "event-read-state")
(include-book "event-proof-format")
(fn2-book-layer :b)
(defcolumns fn2-checkpoint-restore-events-work
 ((generation :u60) (commit :u60) (first :u60) (members :u32)
  (epoch :u60) (allocation :u60) (extent :u32) (next :u32) (consumed :bool))
 :init-name fn2-checkpoint-restore-events-work-columns-init
 :extra-fields
 ((fn2-checkpoint-restore-events-work-seals :type (array (unsigned-byte 8) (0)) :initially 0 :resizable t
   :why "One immutable 32-byte authenticated semantic-seal identity per tagged journal allocation; no page hash is substituted.")))
; The layout is shared: lower half belongs only to cold investigations;
; upper half retains the selected catalog across later candidate scans. The
; argument to INIT remains the physical extent count, charged as two stripes.
(defun fn2-checkpoint-restore-events-work-capacity (fn2-checkpoint-restore-events-work)
 (declare (xargs :stobjs fn2-checkpoint-restore-events-work
  :guard (fn2-checkpoint-restore-events-work-wfp fn2-checkpoint-restore-events-work)))
 (floor (fn2-checkpoint-restore-events-work-rows fn2-checkpoint-restore-events-work) 2))
(defun fn2-checkpoint-restore-events-work-init (rows fn2-checkpoint-restore-events-work)
 (declare (xargs :stobjs fn2-checkpoint-restore-events-work :verify-guards nil
  :guard (and (fn2-checkpoint-restore-events-work-wfp fn2-checkpoint-restore-events-work) (unsigned-byte-p 32 rows))))
 (let* ((fn2-checkpoint-restore-events-work (fn2-checkpoint-restore-events-work-columns-init (* 2 rows) fn2-checkpoint-restore-events-work))
        (fn2-checkpoint-restore-events-work (resize-fn2-checkpoint-restore-events-work-seals (* 64 rows) fn2-checkpoint-restore-events-work)))
  fn2-checkpoint-restore-events-work))
(defcolumns fn2-checkpoint-restore-events
 ((phase (:enum fn2-checkpoint-restore-events-phase
    (:idle :directory :journal-bind :journal :frontier-begin :frontier :peaks :padding :complete :uncertain)))
  (candidate :u32) (generation :u60) (cut-commit :u60) (cut-event :u60)
  (checkpoint :u60) (history :u60) (incarnation :u60)
  (owner-kind :u8) (owner-slot :u32) (owner-gen :u60)
  (slot :u32) (gen :u60) (record-slot :u32) (record-gen :u60)
  (head :u32) (tail :u32) (count :u60) (next-event :u60)
  (cursor :u32) (previous :u32) (consumed :u60) (peak :u8))
 :extra-fields
 ((fn2-checkpoint-restore-events-catalog-descriptor :type (array (unsigned-byte 8) (32)) :initially 0
   :why "Retained row1 catalog descriptor survives scratch row0 candidate reuse.")
  (fn2-checkpoint-restore-events-frontier :type (array (unsigned-byte 8) (*fn2-event-frontier-bytes*)) :initially 0
   :why "Actual authenticated and recomputed 60-peak frontier, retained outside shared checker/Merkle scratch until selected-summary adoption.")))
