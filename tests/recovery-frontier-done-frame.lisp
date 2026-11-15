; Actual scanner→ownership boundary frame leaves, SOURCE-ONLY UNEXECUTED.
(in-package "ACL2")
(include-book "../books/recovery-frontier")
(include-book "event-frontier-done-frame")
; This is a projection of the actual machine declaration's readers, not a
; caller-provided readiness flag. Cursor fields stage/token/left are excluded.
(defun fn2-recovery-init-binding-reads (fields)
 (declare (xargs :verify-guards nil))
 (if (atom fields) nil
  (cons (list (fn2-columns-col-name 'fn2-machine (car fields)) 'id 'fn2-core)
        (fn2-recovery-init-binding-reads (cdr fields)))))
(make-event
 (value `(defun fn2-recovery-frontier-source-binding (id fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (list ,@(fn2-recovery-init-binding-reads '(generation phase rc-mode pending rc-pos rc-commit
          rc-base rc-base-tag rc-chain rc-role rc-filled pool-slot pool-gen
          rc-wslot rc-wgen rc-roff rc-rend))))))
; The scanner can never mutate allocator ownership, the directory or the
; physical prepass chain, on success OR refusal. This also frames any later
; maintained identity-index predicate stored inside the actual extents child.
(defthm fn2-recovery-frontier-frames-ownership-carriers
 (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
  (let ((after (mv-nth 1 (fn2-recovery-frontier-step id fn2-core))))
   (and (equal (fn2-core-extents after) (fn2-core-extents fn2-core))
        (equal (fn2-core-alloc-edges after) (fn2-core-alloc-edges fn2-core))
        (equal (fn2-core-rec-cand after) (fn2-core-rec-cand fn2-core))
        (equal (fn2-core-commit-root after) (fn2-core-commit-root fn2-core))
        (equal (fn2-core-pool after) (fn2-core-pool fn2-core)))))
 :hints (("Goal" :in-theory (enable fn2-recovery-frontier-step)))
 :rule-classes nil)
(defthm fn2-recovery-frontier-done-frames-hash-carriers
 (implies
  (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
       (equal (mv-nth 0 (fn2-recovery-frontier-step id fn2-core)) :done))
  (let ((after (mv-nth 1 (fn2-recovery-frontier-step id fn2-core))))
   (and (equal (fn2-core-mk after) (fn2-core-mk fn2-core))
        (equal (fn2-core-b3 after) (fn2-core-b3 fn2-core))
        (equal (fn2-core-digests after) (fn2-core-digests fn2-core)))))
 :hints (("Goal" :in-theory (enable fn2-recovery-frontier-step)))
 :rule-classes nil)
(defthm fn2-recovery-frontier-done-retains-source-binding
 (implies
  (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
       (equal (mv-nth 0 (fn2-recovery-frontier-step id fn2-core)) :done))
  (equal (fn2-recovery-frontier-source-binding id
           (mv-nth 1 (fn2-recovery-frontier-step id fn2-core)))
         (fn2-recovery-frontier-source-binding id fn2-core)))
 :hints (("Goal" :in-theory (enable fn2-recovery-frontier-step fn2-recovery-frontier-source-binding)))
 :rule-classes nil)
