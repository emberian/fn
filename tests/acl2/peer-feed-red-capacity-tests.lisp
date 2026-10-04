; Red-before/green-after witness for rp-feed-dropped-holds-capacity (lane peer-feed, 2026-10-04).
; The assertion is the fixed behaviour, in vocabulary the base and the fix
; share: RED at lane/read-peer@9ab11e8ee (certify-20261004T171953Z-23799),
; green on lane/peer-feed.
(in-package "ACL2")
(include-book "../../books/owner-feed")

(defconst *pfr-peer* '(105 110 110))
(defconst *pfr-a* '(60 97 64 102 110 62))
(defconst *pfr-b* '(60 98 64 102 110 62))
(defconst *pfr-contact* (fn-sched-contact "inn" 0 1000000))
(defconst *pfr-obs* (fn-clock-observation 10 0 0 nil))

; rp-feed-dropped-holds-capacity: a max-queue-one feed that gave its only
; entry up at the bound (one loss) takes the next enqueue.
(defconst *pfr-one-lost*
  (fn-feed-lost (nth 0 (mv-list 2 (fn-feed-tick-step
                           (fn-feed-enqueue (fn-feed-open *pfr-peer* (fn-feed-limits 1 1000 1 t)
                                                          *pfr-contact* 7)
                                            *pfr-a* 1)
                           *pfr-obs*)))
                *pfr-obs*))
(assert-event (consp (fn-feed-find *pfr-b* (fn-feed-queue (fn-feed-enqueue *pfr-one-lost* *pfr-b* 2)))))

