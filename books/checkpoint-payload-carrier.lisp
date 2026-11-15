; Shared concrete payload continuation, independent of live source authority.
(in-package "ACL2")
(include-book "payload-workspace")
(include-book "source-manifest-codec")
(fn2-book-layer :b)
(defcolumns fn2-checkpoint-payload
 ((mode (:enum fn2-checkpoint-payload-mode (:live :cold)))
  (phase (:enum fn2-checkpoint-payload-phase (:idle :manifest-read :wait-manifest :header :entry :block-read :wait-block :block-verify :hash :final :complete :uncertain :location-verify :claim)))
  (verify-next :u8) (location-units :u32)
  (original-slot :u32) (original-gen :u60) (original-off :u32)
  (stored-slot :u32) (stored-gen :u60) (stored-off :u32)
  (vector-slot :u32) (vector-gen :u60) (vector-off :u32) (vector-length :u32)
  (source-tag :u60) (parent-unit :u60) (parent-epoch :u60) (parent-allocation :u60)
  (entry-serial :u60) (token :u60) (owner-kind :u8) (owner-slot :u32) (owner-gen :u60)
  (candidate :u32) (checkpoint :u60) (entry-base :u32) (article :u60) (location-kind :u8)
  (total :u60) (position :u60) (source-unit :u60) (source-epoch :u60) (source-allocation :u60)
  (manifest-position :u32) (loaded-unit :u32) (manifest-slot :u32) (manifest-gen :u60)
  (data-slot :u32) (data-gen :u60) (field-base :u32) (hash-row :u32)
  (block-unit :u60) (block-epoch :u60) (block-allocation :u60) (block-length :u32) (hash-cursor :u32)
  (hash-offset :u32) (cv-offset :u32) (op-slot :u32) (op-gen :u60) (pending :bool)))


; A new semantic owner may bind only after the previous physical operation
; and stream have settled. Uncertain/pending state never changes variant.
(defun fn2-checkpoint-payload-rebindablep (fn2-checkpoint-payload)
 (declare (xargs :stobjs fn2-checkpoint-payload :guard (fn2-checkpoint-payload-wfp fn2-checkpoint-payload)))
 (and (< 0 (fn2-checkpoint-payload-rows fn2-checkpoint-payload))
      (equal (fn2-checkpoint-payload-pending 0 fn2-checkpoint-payload) 0)
      (member (fn2-checkpoint-payload-phase 0 fn2-checkpoint-payload)
       (list *fn2-checkpoint-payload-phase-idle* *fn2-checkpoint-payload-phase-complete*))))
