; Teeth for books/decision-trace-reservation.lisp: the ring is held by the
; launcher's reservation, exactly once, and a machine that cannot hold it is
; refused by name; no ring leaves the reservation as it was.

(in-package "ACL2")
(include-book "../../books/decision-trace-reservation")

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
