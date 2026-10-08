; Teeth for books/decision-trace-reservation.lisp: the ring is held by the
; launcher's reservation, exactly once, and a machine that cannot hold it is
; refused by name; no ring leaves the reservation as it was.

(in-package "ACL2")
(include-book "../../books/decision-trace-reservation")
(include-book "../../books/connection-budget")
(include-book "../../books/owner-credits")
(include-book "must-fail-checked")

(defconst *fn-dtrr-base* '(:heap 200 16 nil 1024 8))
(defconst *fn-dtrr-big* (list (* 64 1024 1048576)))   ; a 64 GiB machine
(defconst *fn-dtrr-core* 143232000)

; the default: no ring, no change (a byte-identical reservation)
(assert-event (equal (fn-dtrace-extend-reservation *fn-dtrr-base* 0 *fn-dtrr-core* *fn-dtrr-big*)
                     *fn-dtrr-base*))
(assert-event (equal (fn-dtrace-config-ring-octets
                      (fn-record-string-octets "[store]
path = \"/s\"
") :production)
                     0))

; a ring of the small preset's capacity grows the heap by at least its octets
(assert-event
 (let ((ring (fn-dtrace-ring-octets (fn-dtrace-admit '(nil 1024 nil nil nil) :production))))
   (and (equal ring (+ 4096 (* 1024 1024)))
        (let ((r (fn-dtrace-extend-reservation *fn-dtrr-base* ring *fn-dtrr-core* *fn-dtrr-big*)))
          (and (equal (car r) :heap)
               (<= (+ (* 1048576 200) ring) (* 1048576 (cadr r)))
               (< 200 (cadr r))
               ;; the rest of the decision is the base's
               (equal (cddr r) (cddr *fn-dtrr-base*)))))))

; the largest ring on a machine too small for it: refused by name
(assert-event
 (let ((r (fn-dtrace-extend-reservation *fn-dtrr-base* 68157440 *fn-dtrr-core*
                                        (list (* 256 1048576)))))
   (and (equal (car r) :refused)
        (equal (cadr r) :machine-cannot-hold-trace-ring))))

; a refused base is not extended
(assert-event (equal (fn-dtrace-extend-reservation '(:refused :x 1 nil) 4096 *fn-dtrr-core* *fn-dtrr-big*)
                     '(:refused :x 1 nil)))

; THE CONNECTION BUDGET (host/native/mux.lisp fnn-mux-budget-install passes
; the core file and the ring, ACL2's sum, as the budget's core): on the small
; preset at 8 MiB nursery, 2 GiB machine, 1,536 MiB dynamic space, 34 threads,
; 1 MiB stacks, the largest ring (capacity 65,536) takes the admitted
; connection count from 2,744 (no [trace]) to 2,435; no ring leaves it alone.
(defun fn-dtrr-limit (ring)
  (let ((core (fn-dtrace-core-with-ring 143232000 ring)))
    (fn-cbud-limit (* 2048 1048576) (* 1536 1048576)
                   (fn-mca-figure-octets *fn-heap-small-profile* core 8388608 nil)
                   core 34 1048576 0 32768 nil)))
(assert-event (equal (fn-dtrr-limit 0) 2744))
(assert-event (equal (fn-dtrr-limit
                      (fn-dtrace-ring-octets (fn-dtrace-admit '(nil 65536 nil nil nil) :production)))
                     2435))
(assert-event (< (fn-dtrr-limit 67112960) (fn-dtrr-limit 0)))
; a smaller ring costs less than a larger one
(assert-event (<= (fn-dtrr-limit 67112960) (fn-dtrr-limit 1052672)))
(assert-event (<= (fn-dtrr-limit 1052672) (fn-dtrr-limit 0)))

; MUTATION of fn-dtrace-config-ring-octets-is-the-plans-ring: a ring-octets
; function missing the 4,096 header.  The theorem's statement, with this
; function in place of fn-dtrace-ring-octets, is not provable.
(defun fn-dtrr-headerless-ring (plan)
  (declare (xargs :guard t))
  (if (fn-dtrace-planp plan) (* 1024 (fn-dtrace-plan-capacity plan)) 0))
(must-fail-checked
 (thm (equal (fn-dtrr-headerless-ring (fn-dtrace-config-plan octets image))
             (let ((plan (fn-dtrace-config-plan octets image)))
               (if (equal (fn-dtrace-plan-kind plan) :plan)
                   (+ 4096 (* 1024 (fn-dtrace-plan-capacity plan)))
                 0)))
      :hints (("Goal" :in-theory (enable fn-dtrr-headerless-ring fn-dtrace-plan-kind))))
 :unchecked "a refused proof is the claim")
