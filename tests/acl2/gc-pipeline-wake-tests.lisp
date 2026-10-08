(in-package "ACL2")
(include-book "../../books/owner-commit-durability-open")
(include-book "gc-pipeline-tests")
; START-NEXT remains legal after A's fence, before its collector wins O.
(assert-event
 (let ((next (fn-ocp-gc-entry-start-next
              (fn-ocp-gc-entry-syncer *gc-a* :current :ok))))
   (and (equal (nth 4 next) :resolutions) (equal (nth 5 next) :drain)
        (fn-ocp-gc-linkedp next))))
; Never promote a B whose intents or append have not returned.
(assert-event
 (let* ((x (fn-ocp-gc-run *gc-a*
             '((:next) (:member :next (:duplicate t)) (:seal :next)
               (:io :current :ok) (:io :current :ok) (:collect))))
        (y (fn-ocp-gc-entry-reader-advance x)))
   (and (fn-ocp-gc-linkedp x) (equal (nth 4 x) :collected)
        (equal (nth 5 x) :intents) (fn-ocp-gc-linkedp y)
        (equal (nth 4 y) :collected) (null (nth 14 y)))))
(assert-event
 (let ((s (nth 1 *gc-a*)))
   (and (equal (fn-ocp-gc-committer-wake s nil t '(0 0 0 0 0 0) t nil) :start-next)
        (equal (fn-ocp-gc-committer-wake s nil t '(0 0 0 0 0 0) nil t) :wait)
        (equal (fn-ocp-gc-committer-wake s t t '(0 0 0 0 0 0) nil nil) :wait)
        (equal (fn-ocp-gc-committer-wake s t t '(0 0 0 0 0 0) nil t) :collect))))
(value-triple :late-start-promotion-and-two-return-wakes-passed)
