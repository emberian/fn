; One actual master BIND/CONSUME surface for directory, inventory and frontier.
; Every page uses the shared owned-buffer pipeline and exact physical harvest.
(in-package "ACL2")
(include-book "event-producer")
(fn2-book-layer :c)
(defun fn2-event-inventory-subject-p (fn2-event-build fn2-release-inventory-build fn2-csnapshot fn2-checkpoints)
 (declare (xargs :stobjs (fn2-event-build fn2-release-inventory-build fn2-csnapshot fn2-checkpoints) :verify-guards nil
  :guard (and (fn2-event-buildp fn2-event-build) (fn2-event-build-wfp fn2-event-build)
   (fn2-release-inventory-buildp fn2-release-inventory-build) (fn2-release-inventory-build-wfp fn2-release-inventory-build)
   (fn2-csnapshotp fn2-csnapshot) (fn2-csnapshot-wfp fn2-csnapshot) (fn2-checkpointsp fn2-checkpoints) (fn2-checkpoints-wfp fn2-checkpoints))))
 (and (fn2-event-producer-ownerp fn2-event-build fn2-csnapshot fn2-checkpoints)
      (fn2-release-inventory-subject-p fn2-release-inventory-build fn2-csnapshot fn2-checkpoints)
      (= (fn2-event-build-token 0 fn2-event-build) (fn2-release-inventory-build-token 0 fn2-release-inventory-build))
      (= (fn2-event-build-candidate 0 fn2-event-build) (fn2-release-inventory-build-candidate 0 fn2-release-inventory-build))))
(defmacro fn2-event-inventory-page-operation (name inputs outputs body)
 (let* ((typed (fn2-columns-carrier-hyps (pairlis$ inputs nil)))
        (carriers (fn2-release-inventory-output-carriers (cdr outputs) 2)))
 `(progn
   (defun ,name ,inputs
    (declare (xargs :stobjs ,inputs :verify-guards nil :guard (and ,@typed))) ,body)
   (fn2-event-build-preserves ,name ,inputs :position 1 :hyps ,typed
    :specs ,(append (fn2-columns-carrier-specs carriers) (fn2-release-inventory-row-specs (cdr outputs) 2))))))
(fn2-event-inventory-page-operation fn2-event-producer-bind-page
 (fn2-event-build fn2-release-inventory-build fn2-csnapshot fn2-checkpoints fn2-checkpoint-construction fn2-extents
  fn2-checkpoint-page fn2-checkpoint-page-verified fn2-pool fn2-fc fn2-fields)
 (fn2-event-build fn2-release-inventory-build fn2-checkpoint-page)
 (if (and (< 0 (fn2-event-build-rows fn2-event-build))
          (= (fn2-event-build-phase 0 fn2-event-build) *fn2-event-build-phase-inventory*))
  (if (not (fn2-event-inventory-subject-p fn2-event-build fn2-release-inventory-build fn2-csnapshot fn2-checkpoints))
      (mv :source fn2-event-build fn2-release-inventory-build fn2-checkpoint-page)
   (mv-let (code fn2-release-inventory-build fn2-checkpoint-page)
    (fn2-release-inventory-bind fn2-release-inventory-build fn2-checkpoint-page fn2-checkpoint-page-verified
     fn2-checkpoint-construction fn2-csnapshot fn2-checkpoints fn2-extents fn2-pool fn2-fc fn2-fields)
    (mv code fn2-event-build fn2-release-inventory-build fn2-checkpoint-page)))
  (mv-let (code fn2-event-build fn2-checkpoint-page)
   (fn2-event-build-bind-page fn2-event-build fn2-csnapshot fn2-checkpoints fn2-checkpoint-construction fn2-extents
    fn2-checkpoint-page fn2-checkpoint-page-verified fn2-pool fn2-fc fn2-fields)
   (mv code fn2-event-build fn2-release-inventory-build fn2-checkpoint-page))))
(fn2-event-inventory-page-operation fn2-event-producer-consume-page
 (fn2-event-build fn2-release-inventory-build fn2-event-read fn2-csnapshot fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
  fn2-checkpoint-page fn2-checkpoint-page-verified fn2-checkpoint-construction fn2-extents fn2-mk fn2-fc fn2-digests fn2-pool)
 (fn2-event-build fn2-release-inventory-build fn2-checkpoint-refs fn2-checkpoint-bytes)
 (if (and (< 0 (fn2-event-build-rows fn2-event-build))
          (= (fn2-event-build-phase 0 fn2-event-build) *fn2-event-build-phase-inventory*))
  (if (not (fn2-event-inventory-subject-p fn2-event-build fn2-release-inventory-build fn2-csnapshot fn2-checkpoints))
      (mv :source fn2-event-build fn2-release-inventory-build fn2-checkpoint-refs fn2-checkpoint-bytes)
   (mv-let (code fn2-release-inventory-build)
    (fn2-release-inventory-consume fn2-release-inventory-build fn2-checkpoint-page fn2-csnapshot fn2-checkpoints
     fn2-checkpoint-construction fn2-extents fn2-checkpoint-page-verified fn2-pool)
    (let ((fn2-event-build (if (eq code :done)
            (fn2-event-build-set-phase 0 *fn2-event-build-phase-reserve* fn2-event-build) fn2-event-build)))
     (mv (if (eq code :done) :more code) fn2-event-build fn2-release-inventory-build fn2-checkpoint-refs fn2-checkpoint-bytes))))
  (mv-let (code fn2-event-build fn2-checkpoint-refs fn2-checkpoint-bytes)
   (fn2-event-build-consume-page fn2-event-build fn2-event-read fn2-csnapshot fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
    fn2-checkpoint-page fn2-checkpoint-page-verified fn2-checkpoint-construction fn2-extents fn2-mk fn2-fc fn2-digests fn2-pool fn2-release-inventory-build)
   (mv code fn2-event-build fn2-release-inventory-build fn2-checkpoint-refs fn2-checkpoint-bytes))))
