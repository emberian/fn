; Runtime capture only; semantic refinements stay in nov-column-pieces
; and nov-row-facts. Definitions moved verbatim for a narrow cursor world.
(in-package "ACL2")
(include-book "catalog")
(include-book "nov-piece-window")
(include-book "nov-held-row-pieces")

(defun fn-nrf-facts (seq fn-cat)
  (declare (xargs :stobjs fn-cat :guard t))
  (if (and (natp seq) (< seq (fn-cat-count fn-cat)))
      (let* ((row (fn-cat-at seq fn-cat)) (facts (fn-held-facts row)))
        (if (and (natp (fn-record-payload row)) (fn-hf-nov facts)) facts nil))
    nil))

