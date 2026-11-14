; One actual checkpoint construction job. Physical completion is distinct from
; durable allocation/installation, which stay with the existing B journal.
(in-package "ACL2")
(include-book "checkpoint-member")
(include-book "c-snapshot")
(fn2-book-layer :b)
(defcolumns fn2-checkpoint-build
 ((phase (:enum fn2-checkpoint-build-phase (:idle :pack :seal :verify :write :wait-write :ready :uncertain)))
  (owner-kind :u8) (owner-slot :u32) (owner-gen :u60) (snapshot-token :u60)
  (candidate :u32) (checkpoint :u60) (cut-commit :u60) (cut-event :u60)
  (extent :u32) (epoch :u60) (allocation :u60)
  (slot :u32) (gen :u60) (scratch :u32) (scratch-gen :u60)
  (checker-row :u32) (field-base :u32) (write-cursor :u32)
  (intended-bytes :u60) (completed-bytes :u60)
  (op-slot :u32) (op-gen :u60) (pending :bool)))

; These five carriers are produced by actual metadata/map/proof/frontier/arena
; constructors bound to this frozen token. A read/decoded candidate has token0.
; No generic flag setter is exposed. Constructors still need to be connected;
; until then production descriptor admission remains roots-pending.
(defun fn2-checkpoint-built-roots-p (role c token fn2-checkpoint-refs)
 (declare (xargs :stobjs fn2-checkpoint-refs :measure (nfix (- 6 (nfix role)))
  :guard (and (fn2-checkpoint-refs-wfp fn2-checkpoint-refs) (natp role) (<= role 6)
              (natp c) (<= (* 6 (+ 1 c)) (fn2-checkpoint-refs-rows fn2-checkpoint-refs)))))
 (if (or (not (natp role)) (>= role 6)) t
  (let ((r (+ (* 6 c) role)))
   (and (posp token) (equal (fn2-checkpoint-refs-root-build-token r fn2-checkpoint-refs) token)
        (equal (fn2-checkpoint-refs-root-source-complete r fn2-checkpoint-refs) 1)
        (posp (fn2-checkpoint-refs-encoded-length r fn2-checkpoint-refs))
        (<= (fn2-checkpoint-refs-encoded-length r fn2-checkpoint-refs)
            (fn2-checkpoint-refs-root-intended-bytes r fn2-checkpoint-refs))
        (equal (fn2-checkpoint-refs-root-intended-bytes r fn2-checkpoint-refs)
               (fn2-checkpoint-refs-root-completed-bytes r fn2-checkpoint-refs))
        (fn2-checkpoint-built-roots-p (+ 1 role) c token fn2-checkpoint-refs)))))

(defun fn2-checkpoint-build-ownerp (token okind oslot ogen fn2-checkpoint-build fn2-csnapshot)
 (declare (xargs :stobjs (fn2-checkpoint-build fn2-csnapshot)
  :guard (and (fn2-checkpoint-build-wfp fn2-checkpoint-build) (fn2-csnapshot-wfp fn2-csnapshot))))
 (and (< 0 (fn2-checkpoint-build-rows fn2-checkpoint-build))
      (not (equal (fn2-checkpoint-build-phase 0 fn2-checkpoint-build) *fn2-checkpoint-build-phase-idle*))
      (fn2-csnapshot-ownerp token okind oslot ogen fn2-csnapshot)
      (equal (fn2-csnapshot-phase 0 fn2-csnapshot) *fn2-csnapshot-phase-held*)
      (equal token (fn2-checkpoint-build-snapshot-token 0 fn2-checkpoint-build))
      (equal okind (fn2-checkpoint-build-owner-kind 0 fn2-checkpoint-build))
      (equal oslot (fn2-checkpoint-build-owner-slot 0 fn2-checkpoint-build))
      (equal ogen (fn2-checkpoint-build-owner-gen 0 fn2-checkpoint-build))
      (equal (fn2-checkpoint-build-cut-commit 0 fn2-checkpoint-build) (fn2-csnapshot-cut-commit 0 fn2-csnapshot))
      (equal (fn2-checkpoint-build-cut-event 0 fn2-checkpoint-build) (fn2-csnapshot-cut-event 0 fn2-csnapshot))))
