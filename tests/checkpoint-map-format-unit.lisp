; Local page-count/shape controls, not complete authenticated-reader evidence.
(in-package "ACL2")
(include-book "../books/checkpoint-map-format")
(assert-event (fn2-checkpoint-map-page-shapep 0 0 0 0 0 *fn2-checkpoint-map-slots*))
(assert-event (fn2-checkpoint-map-page-shapep *fn2-checkpoint-map-slots* 0 0 *fn2-checkpoint-map-slots* 0 *fn2-checkpoint-map-slots*))
(assert-event (fn2-checkpoint-map-page-shapep (+ 1 *fn2-checkpoint-map-slots*) 0 0 *fn2-checkpoint-map-slots* 1 *fn2-checkpoint-map-slots*))
(assert-event (fn2-checkpoint-map-page-shapep (+ 1 *fn2-checkpoint-map-slots*) 1 *fn2-checkpoint-map-slots* 1 0 *fn2-checkpoint-map-slots*))
; Removing completeness, continuity or terminal-link facts must fail.
(assert-event (not (fn2-checkpoint-map-page-shapep (+ 1 *fn2-checkpoint-map-slots*) 0 0 *fn2-checkpoint-map-slots* 0 *fn2-checkpoint-map-slots*)))
(assert-event (not (fn2-checkpoint-map-page-shapep (+ 1 *fn2-checkpoint-map-slots*) 1 (+ 1 *fn2-checkpoint-map-slots*) 1 0 *fn2-checkpoint-map-slots*)))
(assert-event (not (fn2-checkpoint-map-page-shapep (+ 1 *fn2-checkpoint-map-slots*) 1 *fn2-checkpoint-map-slots* 0 0 *fn2-checkpoint-map-slots*)))
(assert-event (not (fn2-checkpoint-map-page-shapep 0 1 0 0 0 *fn2-checkpoint-map-slots*)))
