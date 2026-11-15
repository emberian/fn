; Persistent-in-process C source promises. This is ownership state over the
; existing typed reach graph, not another reachability/selection model.
(in-package "ACL2")
(include-book "checkpoint-source-retention")
(fn2-book-layer :b)
(defcolumns fn2-checkpoint-cbase-holds
 ((phase (:enum fn2-checkpoint-cbase-phase (:idle :protecting :acquiring :held :closing :releasing :released :uncertain)))
  (tag :u60) (checkpoint :u60) (cut-commit :u60) (cut-event :u60)
  (history :u60) (incarnation :u60) (generation :u60)
  (limit :u32) (cursor :u32) (seen :u60) (run-cursor :u32)
  (hash-0 :u32) (hash-1 :u32) (hash-2 :u32) (hash-3 :u32)
  (hash-4 :u32) (hash-5 :u32) (hash-6 :u32) (hash-7 :u32)
  (owner-kind :u8) (owner-slot :u32) (owner-gen :u60)
  (edge-base :u32) (run-limit :u32) (drain-started :bool)))


; The entire existing source region comes first. No C base may borrow a
; free-looking source/root/I/O slot reserved to another lifetime role.
(defun fn2-checkpoint-cbase-edge (c e fn2-extents fn2-ops fn2-checkpoints)
 (declare (xargs :stobjs (fn2-extents fn2-ops fn2-checkpoints)
  :guard (and (fn2-extents-wfp fn2-extents) (fn2-ops-wfp fn2-ops) (fn2-checkpoints-wfp fn2-checkpoints)
              (natp c) (natp e))))
 (+ (fn2-checkpoint-source-edge c e fn2-extents fn2-ops fn2-checkpoints)
    (* (fn2-checkpoints-rows fn2-checkpoints) (fn2-extents-rows fn2-extents))))

; Catalog constructors query this from their actual old c/tag. An incomplete
; acquisition cannot lose its owner merely because it has no query leases yet.
(defun fn2-checkpoint-cbase-catalog-available-p (c tag fn2-checkpoint-cbase-holds)
 (declare (xargs :stobjs fn2-checkpoint-cbase-holds :guard (fn2-checkpoint-cbase-holds-wfp fn2-checkpoint-cbase-holds)))
 (and (natp c) (< c (fn2-checkpoint-cbase-holds-rows fn2-checkpoint-cbase-holds))
      (unsigned-byte-p 60 tag)
      (or (and (equal (fn2-checkpoint-cbase-holds-phase c fn2-checkpoint-cbase-holds) *fn2-checkpoint-cbase-phase-idle*)
               (equal (fn2-checkpoint-cbase-holds-tag c fn2-checkpoint-cbase-holds) 0)
               (equal (fn2-checkpoint-cbase-holds-seen c fn2-checkpoint-cbase-holds) 0))
          (and (equal (fn2-checkpoint-cbase-holds-phase c fn2-checkpoint-cbase-holds) *fn2-checkpoint-cbase-phase-released*)
               (equal (fn2-checkpoint-cbase-holds-cursor c fn2-checkpoint-cbase-holds) (fn2-checkpoint-cbase-holds-limit c fn2-checkpoint-cbase-holds))
               (equal (fn2-checkpoint-cbase-holds-seen c fn2-checkpoint-cbase-holds) 0)))))
