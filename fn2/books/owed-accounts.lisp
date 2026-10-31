; D7 4/n-a's keystones (fn2/docs/d-machines-nntp.md section 13.8), statement
; first: the ledger's grant source over the request FIFO. Their subject is
; the served core's own operations (fn2-account-request-core,
; fn2-account-request-park, fn2-account-request-release and the attached
; grant fn2-account-grant-take) on any core; no machine arm requests yet
; (4/n-b is the connection's, at its port in the machine form). Teeth are in
; tests/request-unit.lisp. fn2-account-request-no-barging is proved in
; accounts.lisp; fn2-account-grant-take-live in accounts-core.lisp.
(in-package "ACL2")
(include-book "executor")
(fn2-book-layer :d)

(make-event (value (fn2-declare '(:operation-set fn2-account-requests) nil nil nil)))

; Whether H, waiting at the head of P's FIFO with a fitting request, is
; granted within N grants: true at once if H no longer heads P's FIFO with
; a fitting request (the premise left), or once the core stopped.
(defun fn2-account-granted-within (n p h fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix n)))
  (cond ((not (equal (fn2-core-stop-reason fn2-core) *fn2-stop-reason-none*)) (mv t fn2-core))
        ((not (fn2-account-core-headed-fits p h fn2-core)) (mv t fn2-core))
        ((zp n) (mv nil fn2-core))
        (t (mv-let (id fn2-core) (fn2-account-grant-take fn2-core)
             (if (equal id h) (mv t fn2-core) (fn2-account-granted-within (- n 1) p h fn2-core))))))

; The grant is exact: unless it stopped the core (its FIFO and the ledger
; disagreed), the granted id was P's head for the principal the cursor
; chose, its reservation is acquired, it left the FIFO (P's head is its
; successor) and its wait is cleared.
(defthm-owed fn2-account-grant-exact (fn2-core)
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core) (fn2-account-grant-ready fn2-core))
           (let* ((p (fn2-account-core-grant-next fn2-core))
                  (head (mv-nth 1 (fn2-account-core-ends p fn2-core)))
                  (next (fn2-machine-ready-next head fn2-core))
                  (d *fn2-account-request-dim*)
                  (id (mv-nth 0 (fn2-account-grant-take fn2-core)))
                  (c2 (mv-nth 1 (fn2-account-grant-take fn2-core))))
             (or (equal (fn2-core-stop-reason c2) *fn2-stop-reason-machine-write*)
                 (and (equal id head)
                      (equal (fn2-account-core-hold p d c2) (+ 1 (fn2-account-core-hold p d fn2-core)))
                      (equal (mv-nth 1 (fn2-account-core-ends p c2)) next)
                      (equal (fn2-machine-wait-reason id c2) *fn2-wait-none*)))))
  :schema :assertion :from (:operation-set fn2-account-requests)
  :teeth (fn2-account-test-grant-exact fn2-account-test-grant-exact-negative)
  :doc "D7 4/n-a: the ledger's grant acquires the reservation of the FIFO head of the principal its cursor chose, dequeues it and clears its wait in one transition, or stops the core (:machine-write) when the FIFO and the ledger disagree; nothing else is granted.")

; The bounded wait (the liveness statement): a head whose request fits, and
; keeps fitting, is granted within as many grants as the ledger has rows,
; because each grant to another principal moves the cursor strictly toward
; P. With A's weighted starvation bound (the grant service is visited within
; L calendar entries) a fitting head waits at most rows * L entries.
(defthm-owed fn2-account-request-bounded-wait (p h fn2-core)
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
           (mv-nth 0 (fn2-account-granted-within (fn2-account-core-rows fn2-core) p h fn2-core)))
  :schema :invariant :from (:operation-set fn2-account-requests)
  :teeth (fn2-account-test-bounded-wait fn2-account-test-bounded-wait-negative)
  :doc "D7 4/n-a: a request at the head of its principal's FIFO whose reservation fits is granted within P+1 grants (the ledger's rows) while it keeps fitting; a visit bound, not request completion.")

; Settled once: a granted request is not granted again before it parks
; again (its wait is cleared and it left the FIFO).
(defthm-owed fn2-account-request-once (fn2-core)
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core) (fn2-account-grant-ready fn2-core))
           (let* ((id (mv-nth 0 (fn2-account-grant-take fn2-core)))
                  (c2 (mv-nth 1 (fn2-account-grant-take fn2-core))))
             (or (not (equal (fn2-core-stop-reason c2) *fn2-stop-reason-none*))
                 (not (equal (mv-nth 0 (fn2-account-grant-take c2)) id)))))
  :schema :assertion :from (:operation-set fn2-account-requests)
  :teeth (fn2-account-test-once fn2-account-test-once-negative)
  :doc "D7 4/n-a: each parked request is granted at most once per park; a second grant returns another row or none.")
