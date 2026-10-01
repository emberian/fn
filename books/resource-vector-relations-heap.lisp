; fn: ONE accounting, the heap and connection projections (lane
; resource-ledger, 2026-10-01): the launcher's reservation (PRF-198,
; HST-013) and the connection budget (PRF-223) as funded roots of the
; resource vector.  Split from books/resource-vector-relations.lisp because
; these two books' include closure is the owner's (fifty-odd books), which
; the farm certifies; the relations the served path will cite first (Codex's
; gate and PRF-380) stay in the light book.

(in-package "ACL2")
(include-book "resource-vector")
(include-book "heap-reservation")
(include-book "connection-budget")

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
                (list (cons 1 (list octets 0 0 (fn-heap-reserve-threads r) 0 0 0 0 0))))))

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
; PRF-223's connection budget funds the root's :resident coordinate for
; CAPACITY connections.

(defun fn-rv-connections-root (capacity machine dynamic hneed core threads stack hs article tlsp)
  (declare (xargs :guard t))
  (let ((octets (fn-cbud-resident-octets dynamic hneed core threads stack hs article tlsp
                                         capacity)))
    (fn-rv-make (list (nfix machine) 0 0 0 0 0 0 0 0)
                (list octets 0 0 0 0 0 0 0 0)
                (list (cons 1 (list octets 0 0 0 0 0 0 0 0))))))

(defthm fn-rv-connection-budget-funds-the-root
  (let ((d (fn-cbud-run-decide capacity machine dynamic hneed core threads stack hs
                               article tlsp)))
    (implies (equal (car d) :hold)
             (and (fn-rv-okp (fn-rv-connections-root capacity machine dynamic hneed core threads
                                                     stack hs article tlsp))
                  (fn-rv-fundedp (fn-rv-connections-root capacity machine dynamic hneed core
                                                         threads stack hs article tlsp)))))
  :hints (("Goal" :use fn-cbud-run-decide-holds-the-capacity
           :in-theory (e/d (fn-rv-okp fn-rv-bankp fn-rv-fundedp fn-rv-outstanding
                            fn-rv-row-demand fn-rv-rowsp fn-rv-rowp fn-rv-vectorp
                            fn-rv-nats-p fn-rv-below fn-rv-plus fn-rv-keep fn-rv-drop)
                           (fn-cbud-run-decide-holds-the-capacity fn-cbud-run-decide
                            fn-cbud-resident-octets fn-cbud-limit fn-cbud-held-bound
                            fn-cbud-base-fitsp)))))
