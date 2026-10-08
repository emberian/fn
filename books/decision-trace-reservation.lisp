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

; KEYSTONE (general): for every configuration and either image profile, what
; the host asks is 0 when the plan is (:off) or a refusal, and otherwise a
; 4,096-octet header and 1,024 octets a row of the plan's capacity.  The
; numbers are written out, not read from the constants, so a change to the
; ring's accounting must change this statement.
(defthm fn-dtrace-ring-octets-by-kind
  (equal (fn-dtrace-ring-octets plan)
         (if (equal (fn-dtrace-plan-kind plan) :plan)
             (+ 4096 (* 1024 (fn-dtrace-plan-capacity plan)))
           0))
  :hints (("Goal" :in-theory (enable fn-dtrace-ring-octets fn-dtrace-plan-kind))))

(defthm fn-dtrace-config-ring-octets-is-the-plans-ring
  (equal (fn-dtrace-config-ring-octets octets image)
         (let ((plan (fn-dtrace-config-plan octets image)))
           (if (equal (fn-dtrace-plan-kind plan) :plan)
               (+ 4096 (* 1024 (fn-dtrace-plan-capacity plan)))
             0)))
  ;; the plan stays one term: expanding the configuration reader here explodes
  :hints (("Goal" :use ((:instance fn-dtrace-ring-octets-by-kind
                                   (plan (fn-dtrace-config-plan octets image))))
                  :in-theory (union-theories (theory 'minimal-theory)
                                             '(fn-dtrace-config-ring-octets)))))

; Its positive witnesses (the theorem is not vacuous): no table is no ring on
; either image; a table of capacity 8 on a developer image holds 12,288 octets.
(defthm fn-dtrace-config-ring-octets-witnesses
  (and (equal (fn-dtrace-config-ring-octets (fn-record-string-octets "[store]
path = \"/s\"
") :production)
              0)
       (equal (fn-dtrace-config-ring-octets (fn-record-string-octets "[store]
path = \"/s\"
") :developer)
              0)
       (equal (fn-dtrace-config-ring-octets (fn-record-string-octets "[store]
path = \"/s\"
[trace]
capacity = 8
") :developer)
              12288))
  :rule-classes nil)

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

; The connection budget divides the machine by the resident figure of a
; connection (books/connection-budget.lisp), whose fixed part counts the
; image's core.  The ring is fixed resident content the run holds as soon as
; `trace on' allocates it, so the core the budget is given is the core file's
; octets and the ring's: ACL2 adds them, the host passes the sum on.
(defun fn-dtrace-core-with-ring (core ring-octets)
  (declare (xargs :guard t))
  (if (natp core) (+ core (nfix ring-octets)) core))

(defthm fn-dtrace-core-with-ring-keeps-the-core
  (and (equal (fn-dtrace-core-with-ring core 0) core)
       (implies (natp core) (<= core (fn-dtrace-core-with-ring core ring)))
       (implies (and (natp core) (natp ring))
                (equal (fn-dtrace-core-with-ring core ring) (+ core ring))))
  :rule-classes nil)
