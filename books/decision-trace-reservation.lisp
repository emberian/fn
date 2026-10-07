; fn: the decision trace ring's memory in the launcher's reservation (lane
; obs-decision-trace; observability program section 2a, N's "the ring is
; charged").
;
; A node that may trace holds a ring of CAPACITY rows (books/decision-trace.lisp
; fn-dtrace-ring-octets: a header and 1,024 octets a row) from the moment
; `trace on' allocates it, so the heap the launcher reserves must already hold
; it, whether tracing starts on or off.  The ring depends on the node's
; [trace] plan, not on the store's profile, so it extends the reservation the
; way the cold and output pools do (books/output-reservation.lisp): after the
; store figure (books/heap-figure.lisp, whose arguments are the store's and
; unchanged) and the other extensions.  No [trace] table: no ring, and the
; reservation is the base, equal.
;
; `fn-dtrace-config-ring-octets' is what the host asks for a configuration's
; octets: the plan's ring, 0 for no table.  A refused table is 0 here; the
; start refuses it by name (host/native/trace.lisp fnn-trace-decide-plan).
;
; Prefix `fn-dtrace-' (docs/prefixes.md).

(in-package "ACL2")
(include-book "decision-trace-config")
(include-book "output-reservation")

(defun fn-dtrace-config-ring-octets (octets image)
  (declare (xargs :guard (fn-cbor-octet-listp octets)))
  (fn-dtrace-ring-octets (fn-dtrace-config-plan octets image)))

; Extend the already composed decision exactly once with the ring.
(defun fn-dtrace-extend-reservation (base ring-octets core observations)
  (declare (xargs :guard t))
  (cond ((not (posp ring-octets)) base)
        ((not (equal (fn-crv-nth 0 base) :heap)) base)
        (t
         (let* ((mb (fn-heap-mb-of
                     (fn-heap-grow-runtime-dynamic
                      (* *fn-heap-mib* (nfix (fn-crv-nth 1 base)))
                      ring-octets
                      (* *fn-heap-mib* (fn-profile-limit :gc-nursery-mib)))))
                (stack (nfix (fn-crv-nth 4 base)))
                (threads (nfix (fn-crv-nth 5 base)))
                (total (fn-heap-reservation-octets mb core stack threads)))
           (if (<= total (fn-heap-machine-octets observations))
               (list :heap mb (fn-crv-nth 2 base) (fn-crv-nth 3 base) stack threads)
             (list :refused :machine-cannot-hold-trace-ring (fn-heap-mb-of total)
                   (fn-crv-nth 3 base)))))))

; KEYSTONE: no ring, no change.
(defthm fn-dtrace-no-ring-leaves-the-reservation
  (equal (fn-dtrace-extend-reservation base 0 core observations) base))

; KEYSTONE: a ring that fits is held: the extended reservation, in octets, covers
; the base's and the ring.
(defthm fn-dtrace-extended-reservation-holds-the-ring
  (let ((r (fn-dtrace-extend-reservation base ring core observations)))
    (implies (and (posp ring)
                  (equal (fn-crv-nth 0 base) :heap)
                  (equal (fn-crv-nth 0 r) :heap))
             (<= (+ (* *fn-heap-mib* (nfix (fn-crv-nth 1 base))) ring)
                 (* *fn-heap-mib* (nfix (fn-crv-nth 1 r))))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-heap-grow-runtime-dynamic-covers-addition
                                   (dynamic (* *fn-heap-mib* (nfix (fn-crv-nth 1 base))))
                                   (extra ring)
                                   (nursery-cap (* *fn-heap-mib* (fn-profile-limit :gc-nursery-mib))))
                        (:instance fn-heap-mb-of-covers
                                   (octets (fn-heap-grow-runtime-dynamic
                                            (* *fn-heap-mib* (nfix (fn-crv-nth 1 base)))
                                            ring
                                            (* *fn-heap-mib* (fn-profile-limit :gc-nursery-mib))))))
           :in-theory (e/d (fn-dtrace-extend-reservation fn-crv-nth fn-ncfg-nth)
                           (fn-heap-grow-runtime-dynamic-covers-addition fn-heap-mb-of-covers
                            fn-heap-grow-runtime-dynamic fn-heap-mb-of)))))
