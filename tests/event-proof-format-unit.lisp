(in-package "ACL2")
(include-book "../books/event-proof-format")
; Fixed slots preserve every commit on both sides of a linked-page boundary.
(assert-event
 (let ((n *fn2-event-proof-slots*))
  (and (= (fn2-checkpoint-map-page-count n n) 1)
       (= (fn2-checkpoint-map-page-count (+ n 1) n) 2)
       (= (fn2-checkpoint-map-page-entries (+ n 1) 0 n) n)
       (= (fn2-checkpoint-map-page-entries (+ n 1) 1 n) 1)
       (fn2-checkpoint-map-page-shapep (+ n 1) 0 0 n 1 n)
       (fn2-checkpoint-map-page-shapep (+ n 1) 1 n 1 0 n)
       (not (fn2-checkpoint-map-page-shapep (+ n 1) 1 n 0 0 n))
       (not (fn2-checkpoint-map-page-shapep (+ n 1) 0 0 n 0 n)))))
(assert-event
 (and (= *fn2-event-proof-entry-num-fields* 7)
      (< *fn2-event-frontier-header-num-fields* 128)
      (<= (+ *fn2-event-frontier-peaks-start* (* 60 32)) *fn2-format-page-size*)))
