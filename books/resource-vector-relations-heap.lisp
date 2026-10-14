; fn: ONE accounting, the heap and connection projections (lane
; resource-ledger, 2026-10-01): the launcher's reservation (PRF-198,
; HST-013) and the run's connection capacity (PRF-223: the memory gate's C'
; since L-RUN-LAUNCH) as funded roots of the
; resource vector.  Split from books/resource-vector-relations.lisp because
; these two books' include closure is the owner's (fifty-odd books), which
; the farm certifies; the relations the served path will cite first (Codex's
; gate and PRF-380) stay in the light book.

(in-package "ACL2")
(include-book "resource-vector")
(include-book "heap-reservation")
(include-book "admission-memory")

(local (include-book "arithmetic-5/top" :dir :system))

; -----------------------------------------------------------------------------
; PRF-198's heap reservation funds the root's :resident and :workers.

(defun fn-rv-heap-root (r core observations)
  (declare (xargs :guard t))
  (let ((octets (+ (* *fn-heap-mib* (fn-heap-decision-mb r))
                   (fn-heap-core-file core)
                   (* (fn-heap-reserve-threads r)
                      (+ (* 1024 (fn-heap-reserve-stack-kib r))
                         *fn-heap-thread-runtime-octets*)))))
    (fn-rv-make (list (fn-heap-machine-octets observations) 0 0 (fn-heap-reserve-threads r)
                      0 0 0 0 0)
                (list octets 0 0 (fn-heap-reserve-threads r) 0 0 0 0 0)
                (list (list* 1 0 (list octets 0 0 (fn-heap-reserve-threads r) 0 0 0 0 0))))))

(defthm fn-rv-heap-reservation-funds-the-root
  (let ((r (fn-heap-reserve-decide profile core nursery observations connections)))
    (implies (and (fn-bs-profile-admittedp profile)
                  (equal (car r) :heap))
             (and (fn-rv-okp (fn-rv-heap-root r core observations))
                  (fn-rv-fundedp (fn-rv-heap-root r core observations)))))
  :hints (("Goal" :use fn-heap-reserve-decide-holds-every-thread-the-node-runs
           :in-theory (e/d (fn-rv-okp fn-rv-bankp fn-rv-fundedp fn-rv-outstanding
                            fn-rv-row-demand fn-rv-rowsp fn-rv-rowp fn-rv-vectorp
                            fn-rv-nats-p fn-rv-below fn-rv-plus fn-rv-keep fn-rv-drop)
                           (fn-heap-reserve-decide-holds-every-thread-the-node-runs
                            fn-heap-reserve-decide fn-heap-decide fn-heap-machine-octets
                            fn-heap-decision-mb fn-heap-reserve-threads
                            fn-heap-reserve-stack-kib fn-heap-core-file
                            fn-bs-profile-admittedp)))))

; -----------------------------------------------------------------------------
; PRF-223: the run's capacity C' (books/admission-memory.lisp fn-adm-capacity,
; the most connections at which the memory gate holds at the resident LIMIT)
; funds the root's :resident coordinate: the serving sum at C' is within LIMIT.

(defun fn-rv-connections-root (profile img cfg limit tot)
  (declare (xargs :guard t :verify-guards nil))
  (let ((octets (fn-mm-sum profile img
                           (fn-adm-cfg-at cfg (nfix (fn-adm-capacity profile img cfg limit tot)))
                           tot)))
    (fn-rv-make (list (nfix limit) 0 0 0 0 0 0 0 0)
                (list octets 0 0 0 0 0 0 0 0)
                (list (list* 1 0 (list octets 0 0 0 0 0 0 0 0))))))

(defthm fn-rv-connection-capacity-funds-the-root
  (implies (posp (fn-adm-capacity profile img cfg limit tot))
           (and (fn-rv-okp (fn-rv-connections-root profile img cfg limit tot))
                (fn-rv-fundedp (fn-rv-connections-root profile img cfg limit tot))))
  :hints (("Goal" :use (fn-adm-capacity-fits fn-adm-public-capacity-fits)
           :in-theory (e/d (fn-rv-okp fn-rv-bankp fn-rv-fundedp fn-rv-outstanding
                            fn-rv-row-demand fn-rv-rowsp fn-rv-rowp fn-rv-vectorp
                            fn-rv-nats-p fn-rv-below fn-rv-plus fn-rv-keep fn-rv-drop
                            fn-mm-gate-p)
                           (fn-adm-public-capacity-fits fn-adm-capacity fn-adm-cfg-at fn-mm-sum
                            fn-mm-reopen-need)))))
