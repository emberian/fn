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

; Protocol eligibility is not a bound on nonempty metadata or retained journal.
(assert-event (equal (fn2-checkpoint-capacity-required *fn2-checkpoint-minimum-base-pages* 16) 8))
(assert-event (fn2-checkpoint-minimum-capacityp 8))
(assert-event (not (fn2-checkpoint-minimum-capacityp 7)))
(assert-event (not (fn2-checkpoint-minimum-capacityp -1)))
(assert-event (not (fn2-checkpoint-minimum-capacityp nil)))
; Increased actual base construction feeds the same planner demand, rather
; than being hidden by the minimum-profile check.
(assert-event (< (fn2-checkpoint-capacity-required 4 128)
                 (fn2-checkpoint-capacity-required 64 128)))
(assert-event
 (let* ((extents (+ 1 *fn2-checkpoint-map-slots*))
        (need (fn2-checkpoint-capacity-required 4 extents))
        (maps (fn2-checkpoint-map-page-count extents *fn2-checkpoint-map-slots*)))
  (and (equal maps 2) (posp need)
       (not (equal need (fn2-checkpoint-capacity-required 4 16))))))
