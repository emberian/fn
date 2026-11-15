; Actual named sizing functions only. This does not admit or reserve a POST.
(in-package "ACL2")
(include-book "../books/checkpoint-service-geometry")
(defconst *fn2-csg-profile*
 (put-assoc-equal :identity-arena-bytes 4096
  (put-assoc-equal :groups '(("service.group" . 1))
   (put-assoc-equal :authority 1 *fn2-profile-concrete*))))
(defun fn2-csg-body (profile classes fn2-pool)
 (declare (xargs :stobjs fn2-pool :verify-guards nil))
 (let ((fn2-pool (fn2-pool-init classes 1 100 fn2-pool)))
  (mv-let (code vector) (fn2-checkpoint-service-demand-vector profile fn2-pool)
   (mv (list code vector (fn2-pool-wfp fn2-pool)) fn2-pool))))
(defun fn2-csg-run (profile classes)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-pool
  (mv-let (answer fn2-pool) (fn2-csg-body profile classes fn2-pool) answer)))
; The 4K arena profile: retained NAME and one POST overlap in fresh service;
; retained cold root + POST is the independent 64K peak. No completion claim.
(assert-event (equal (fn2-csg-run *fn2-csg-profile* '((1 . 4096) (1 . 65536)))
                     '(:ok (13 4) t)))
; Remove the fresh NAME antecedent: the two arenas are no longer charged.
(assert-event
 (equal (fn2-csg-run (put-assoc-equal :groups nil (put-assoc-equal :authority 0 *fn2-csg-profile*))
                    '((1 . 4096) (1 . 65536))) '(:ok (11 4) t)))
; Actual initializer default remains 64K; it changes arena class, not IDs.
(assert-event
 (equal (fn2-csg-run (remove-assoc-equal :identity-arena-bytes *fn2-csg-profile*)
                    '((1 . 4096) (1 . 65536))) '(:ok (5 15) t)))
(assert-event (equal (fn2-csg-run *fn2-csg-profile* '((1 . 4096))) '(:profile nil t)))
(assert-event (equal (fn2-csg-run *fn2-csg-profile* '((1 . 4096) (1 . 8192))) '(:capacity nil t)))
