(in-package "ACL2")
(include-book "../../books/runtime-unit-source")
(defun rust-unit (unit source runtime geometry)
 (mv-let (status record) (fn-runtime-unit-source unit source runtime geometry)
  (list status record)))
(defun rust-phase (phase)
 (mv-let (status record) (fn-runtime-phase-source phase) (list status record)))
(assert-event
 (equal (nth 1 (rust-unit :node16
   *fn-runtime-unit-source-coordinate* *fn-srbc-coordinate* *fn-srag-coordinate*))
  *fn-runtime-unit-node16*))
(assert-event
 (equal (nth 0 (rust-unit :node16
   *fn-runtime-unit-source-coordinate* *fn-srbc-coordinate* *fn-srag-coordinate*))
  :conditional-unit))
(assert-event
 (equal (nth 1 (rust-unit :node16 nil
   *fn-srbc-coordinate* *fn-srag-coordinate*)) :source-coordinate-mismatch))
(assert-event
 (equal (nth 1 (rust-unit :node16
   *fn-runtime-unit-source-coordinate* nil *fn-srag-coordinate*))
  :runtime-coordinate-mismatch))
(assert-event
 (equal (nth 1 (rust-unit :node16
   *fn-runtime-unit-source-coordinate* *fn-srbc-coordinate* nil))
  :geometry-coordinate-mismatch))
(assert-event
 (equal (nth 0 (rust-phase :explicit-collector))
  :runtime-phase-unavailable))
