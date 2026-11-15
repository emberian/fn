; Cold event source state shares the actual map investigation generation.
; A journal queue is distinct from alias-permitting typed protection rows.
(in-package "ACL2")
(include-book "checkpoint-restore-reach-state")
(include-book "event-read-state")
(include-book "event-proof-format")
(fn2-book-layer :b)
(defcolumns fn2-checkpoint-restore-events-work
 ((generation :u60) (commit :u60) (first :u60) (members :u32)
  (epoch :u60) (allocation :u60) (next :u32) (consumed :bool))
 :init-name fn2-checkpoint-restore-events-work-columns-init
 :extra-fields
 ((fn2-checkpoint-restore-events-work-seals :type (array (unsigned-byte 8) (0)) :initially 0 :resizable t
   :why "One immutable 32-byte authenticated semantic-seal identity per tagged journal allocation; no page hash is substituted.")))
(defun fn2-checkpoint-restore-events-work-init (rows fn2-checkpoint-restore-events-work)
 (declare (xargs :stobjs fn2-checkpoint-restore-events-work :verify-guards nil
  :guard (and (fn2-checkpoint-restore-events-work-wfp fn2-checkpoint-restore-events-work) (unsigned-byte-p 32 rows))))
 (let* ((fn2-checkpoint-restore-events-work (fn2-checkpoint-restore-events-work-columns-init rows fn2-checkpoint-restore-events-work))
        (fn2-checkpoint-restore-events-work (resize-fn2-checkpoint-restore-events-work-seals (* 32 rows) fn2-checkpoint-restore-events-work)))
  fn2-checkpoint-restore-events-work))
(defcolumns fn2-checkpoint-restore-events
 ((phase (:enum fn2-checkpoint-restore-events-phase
    (:idle :directory :journal-bind :journal :frontier-begin :frontier :peaks :padding :complete :uncertain)))
  (candidate :u32) (generation :u60) (cut-commit :u60) (cut-event :u60)
  (owner-kind :u8) (owner-slot :u32) (owner-gen :u60)
  (slot :u32) (gen :u60) (record-slot :u32) (record-gen :u60)
  (head :u32) (tail :u32) (count :u60) (next-event :u60)
  (cursor :u32) (previous :u32) (consumed :u60) (peak :u8))
 :extra-fields
 ((fn2-checkpoint-restore-events-frontier :type (array (unsigned-byte 8) (*fn2-event-frontier-bytes*)) :initially 0
   :why "Actual authenticated and recomputed 60-peak frontier, retained outside shared checker/Merkle scratch until selected-summary adoption.")))
