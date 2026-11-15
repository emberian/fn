; Existing commit scratch prefix followed by one complete original seal/header.
; These are work buffers, independent of the number of retained batches.
(in-package "ACL2")
(include-book "commit-format")
(fn2-book-layer :b)
(defconst *fn2-event-witness-prefix-bytes* (* 5 *fn2-commit-digest-bytes*))
(defconst *fn2-event-witness-seal-offset* *fn2-event-witness-prefix-bytes*)
(defconst *fn2-event-witness-header-offset*
 (+ *fn2-event-witness-seal-offset* *fn2-format-sealed-batch-max-size*))
(defconst *fn2-event-witness-work-bytes*
 (+ *fn2-event-witness-header-offset* *fn2-format-frame-header-max-size*))
(assert-event (<= *fn2-event-witness-work-bytes* *fn2-commit-unit-bytes*))
