; Runtime capture only; semantic refinements stay in nov-column-pieces
; and nov-row-facts. Definitions moved verbatim for a narrow cursor world.
(in-package "ACL2")
(include-book "catalog")
(include-book "nov-piece-window")

(defun fn-npw-column-pieces (number facts octets)
  (declare (xargs :guard t))
  (let ((nov (fn-hf-nov facts)))
    (list (fn-nntp-decimal-field number) '(9)
          (fn-hnov-subject nov) '(9)
          (fn-hnov-from nov) '(9)
          (fn-hnov-date nov) '(9)
          (fn-hnov-msgid nov) '(9)
          (fn-hnov-references nov) '(9)
          (list :decimal (nfix octets) nil) '(9)
          (list :decimal (nfix (fn-hf-body-lines facts)) nil) '(13 10))))

(defun fn-nrf-facts (seq fn-cat)
  (declare (xargs :stobjs fn-cat :guard t))
  (if (and (natp seq) (< seq (fn-cat-count fn-cat)))
      (let* ((row (fn-cat-at seq fn-cat)) (facts (fn-held-facts row)))
        (if (and (natp (fn-record-payload row)) (fn-hf-nov facts)) facts nil))
    nil))

