; One actual checkpoint construction job. Physical completion is distinct from
; durable allocation/installation, which stay with the existing B journal.
(in-package "ACL2")
(include-book "checkpoint-member")
(include-book "checkpoint-production")
(include-book "c-snapshot")
(include-book "origin")
(fn2-book-layer :c)
(defcolumns fn2-checkpoint-build
 ((phase (:enum fn2-checkpoint-build-phase (:idle :await-roots :pack :page :bound :ready :uncertain)))
  (owner-kind :u8) (owner-slot :u32) (owner-gen :u60) (snapshot-token :u60)
  (candidate :u32) (checkpoint :u60) (cut-commit :u60) (cut-event :u60)
  (extent :u32) (epoch :u60) (allocation :u60)
  (slot :u32) (gen :u60) (scratch :u32) (scratch-gen :u60)
  (checker-row :u32) (field-base :u32)
  (intended-bytes :u60) (completed-bytes :u60)
  ; Physical identity captured from the owner-bound configured origin.
  (history :u60) (history-incarnation :u60)))

; These five carriers are produced by actual metadata/map/proof/frontier/arena
; constructors bound to this frozen token. A read/decoded candidate has token0.
; No generic flag setter is exposed. Constructors still need to be connected;
; until then production descriptor admission remains roots-pending.


(defun fn2-checkpoint-build-ownerp (token okind oslot ogen fn2-checkpoint-build fn2-csnapshot)
 (declare (xargs :stobjs (fn2-checkpoint-build fn2-csnapshot)
  :guard (and (fn2-checkpoint-build-wfp fn2-checkpoint-build) (fn2-csnapshot-wfp fn2-csnapshot))))
 (and (< 0 (fn2-checkpoint-build-rows fn2-checkpoint-build))
      (fn2-origin-physicalp (fn2-checkpoint-build-history 0 fn2-checkpoint-build) (fn2-checkpoint-build-history-incarnation 0 fn2-checkpoint-build))
      (not (equal (fn2-checkpoint-build-phase 0 fn2-checkpoint-build) *fn2-checkpoint-build-phase-idle*))
      (fn2-csnapshot-ownerp token okind oslot ogen fn2-csnapshot)
      (equal (fn2-csnapshot-phase 0 fn2-csnapshot) *fn2-csnapshot-phase-held*)
      (equal token (fn2-checkpoint-build-snapshot-token 0 fn2-checkpoint-build))
      (equal okind (fn2-checkpoint-build-owner-kind 0 fn2-checkpoint-build))
      (equal oslot (fn2-checkpoint-build-owner-slot 0 fn2-checkpoint-build))
      (equal ogen (fn2-checkpoint-build-owner-gen 0 fn2-checkpoint-build))
      (equal (fn2-checkpoint-build-cut-commit 0 fn2-checkpoint-build) (fn2-csnapshot-cut-commit 0 fn2-csnapshot))
      (equal (fn2-checkpoint-build-cut-event 0 fn2-checkpoint-build) (fn2-csnapshot-cut-event 0 fn2-csnapshot))))
