; Decoder guard regression: the segment count is a natural after the actual
; header parser succeeds, even when the rest of the input is refused.
(in-package "ACL2")
(include-book "../../books/store-checkpoint-tables")

(assert-event
 (let* ((segments (fn-sct-run-segments '(1 2 3) 64 7))
        (header (fn-scc-parse-header (car segments))))
   (and (consp segments) header
        (fn-scc-segment-listp segments)
        (natp (cadr header))
        (equal (fn-sct-run-decode segments 7) '(:ok (1 2 3) nil)))))

(assert-event
 (and (equal (fn-sct-run-decode '((1 2 3)) 7) '(:refused :header))
      (equal (fn-sct-run-decode (fn-sct-run-segments '(1 2 3) 64 7) 8)
             '(:refused :sequence))))
