; Arithmetic controls for actual size-step's ticket demand, not complete
; C/constructor/allocator-closure witnesses. These source fixtures await ACL2.
(in-package "ACL2")
(include-book "../books/checkpoint-plan")
(assert-event (equal (fn2-checkpoint-ticket-demand 1 1 1) 2))
(assert-event (equal (fn2-checkpoint-ticket-demand 1 1 2) 2))
; Crossing an arena-page boundary feeds back into allocation-record demand.
; An omitted arena allocation would incorrectly produce S+1 tickets here.
(assert-event
 (let* ((s *fn2-checkpoint-arena-slots*) (c *fn2-checkpoint-allocation-records-per-ticket*)
        (base (- (* c s) 1)) (next (fn2-checkpoint-ticket-demand base 1 1)))
  (and (< 1 s) (equal next (+ s 2))
       (equal (fn2-checkpoint-map-page-count next s) 2)
       (equal (fn2-checkpoint-ticket-demand base 1 next) next)
       (not (equal next (+ 1 (ceiling (+ base 1) c)))))))
