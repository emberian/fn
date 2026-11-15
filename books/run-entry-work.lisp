; One actual restart decode's declared byte envelope, shared by cold readers.
(in-package "ACL2")
(include-book "runs-served")
(include-book "checkpoint-geometry")
(fn2-book-layer :c)
(defconst *fn2-run-entry-visit-bytes*
 (+ (* 2 *fn2-run-entries-base*) *fn2-run-restart-bytes* 32
    (* *fn2-run-restart-interval* *fn2-run-layout-max-entry-bytes*)))
; Actual schema assembly, not a stored-entry or depth ceiling.
(assert-event (<= *fn2-run-layout-max-entry-bytes* *fn2-format-page-size*))
(assert-event (<= (+ (* 2 *fn2-run-entries-base*) *fn2-run-restart-bytes* 32)
                  (* 2 *fn2-format-page-size*)))
(assert-event (<= *fn2-run-entry-visit-bytes* *fn2-checkpoint-semantic-visit-bytes*))
