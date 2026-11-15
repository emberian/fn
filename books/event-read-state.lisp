; One retained reader over the actual installed journal, not an archive model.
; Only exact physical read completion grants a buffer to the format verifier.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "arm-children")
(include-book "event-read-witness-geometry")
(fn2-book-layer :b)
(defcolumns fn2-event-read
 ((phase (:enum fn2-event-read-phase (:idle :read-seal :wait-seal :frame-seal :seal-span :seal-tail :semantic-seal :witness-seal :witness-header
                                     :read-records :wait-records :frame-records :members :next :complete :uncertain)))
  (token :u60) (owner-kind :u8) (owner-slot :u32) (owner-gen :u60)
  (journal-history :u60) (journal-incarnation :u60)
  (cut-commit :u60) (cut-event :u60) (commit :u60) (next-event :u60)
  (extent :u32) (epoch :u60) (allocation :u60) (first :u60) (members :u32)
  (slot :u32) (gen :u60) (checker :u32) (field-base :u32) (leaf-digest :u32)
  (body-off :u32) (body-len :u32)
  (seal-span-started :bool) (seal-span-next :u32) (seal-span-length :u32) (op-slot :u32) (op-gen :u60) (pending :bool)
  ; Enabled only by the actual archive constructor's owned working source.
  (witness-enabled :bool) (witness-token :u60) (witness-slot :u32) (witness-gen :u60)
  (witness-phase (:enum fn2-event-witness-phase (:idle :bound :seal :records :ready :emitted :uncertain)))
  (witness-commit :u60) (witness-first :u60) (witness-members :u32)
  (witness-seal-length :u32) (witness-header-length :u32) (witness-cursor :u32) (witness-staged-event :u60)
  ; Physical identity captured from the owner-bound configured origin.
  (history :u60) (history-incarnation :u60)))

; Format work owns one bounded source visit; callers yield before it at zero.
(defun fn2-event-read-format-phase-p (phase)
 (declare (xargs :guard t))
 (and (member-equal phase (list *fn2-event-read-phase-frame-seal* *fn2-event-read-phase-seal-span* *fn2-event-read-phase-seal-tail*
                               *fn2-event-read-phase-semantic-seal* *fn2-event-read-phase-witness-seal*
                               *fn2-event-read-phase-witness-header* *fn2-event-read-phase-frame-records*)) t))

(defun fn2-event-read-harvest (opslot opgen cell evkind outcome reason count aux0 aux1 fn2-event-read)
 (declare (xargs :stobjs fn2-event-read :guard (fn2-event-read-wfp fn2-event-read)))
 (declare (ignore reason aux0 aux1))
 (b* (((unless (< 0 (fn2-event-read-rows fn2-event-read))) (mv :ok fn2-event-read))
      (phase (fn2-event-read-phase 0 fn2-event-read))
      (seal (equal phase *fn2-event-read-phase-wait-seal*))
      ((unless (and (or seal (equal phase *fn2-event-read-phase-wait-records*))
                     (equal (fn2-event-read-pending 0 fn2-event-read) 1)
                     (equal opslot (fn2-event-read-op-slot 0 fn2-event-read))
                     (equal opgen (fn2-event-read-op-gen 0 fn2-event-read))
                     (equal cell 0) (equal evkind *fn2-event-read-result*)))
       (mv :ok fn2-event-read))
      (good (and (equal outcome *fn2-outcome-done*) (equal count 4096)))
      (fn2-event-read (fn2-event-read-put 0 (pending 0)
       (phase (if good (if seal *fn2-event-read-phase-frame-seal* *fn2-event-read-phase-frame-records*)
                *fn2-event-read-phase-uncertain*)))))
  (mv :ok fn2-event-read)))
(fn2-event-read-preserves fn2-event-read-harvest
 (opslot opgen cell evkind outcome reason count aux0 aux1 fn2-event-read) :position 1)
