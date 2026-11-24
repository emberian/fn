; The adapter post and the core harvest preserve the peer record consumed
; by the listener's Accept observation.
(in-package "ACL2")
(include-book "owed-host")
(include-book "host-ops")
(include-book "accept-peer-transfer")

(defthm fn2-finish-keeps-observed-peer
  (equal (fn2-ops-observed-peer (mv-nth 1 (fn2-op-finish slot gen ops)))
         (fn2-ops-observed-peer ops))
  :hints (("Goal" :in-theory (e/d (fn2-op-finish fn2-op-recycle fn2-ops-clear-row fn2-ops-observed-peer)
                                  (fn2-op-phase-code fn2-op-slotp)))))
(defthm fn2-harvest-one-retains-observation
  (equal (fn2-ops-observed-peer (fn2-core-ops (mv-nth 10 (fn2-harvest-one c))))
         (fn2-ops-observed-peer (mv-nth 4 (fn2-harvest-next (fn2-core-ops c)))))
  :hints (("Goal" :in-theory (e/d (fn2-harvest-one fn2-core-stop)
                                   (fn2-core-harvest-hooks fn2-ops-observed-peer fn2-op-finish
                                    fn2-harvest-next fn2-op-slotp fn2-op-phase fn2-op-cell fn2-op-range
                                    fn2-pool-complete-in fn2-pool-release-out fn2-terminal-releases-borrow-p)))))

(defthm fn2-accept-host-post-to-core-harvest
  (let ((ops (fn2-core-ops c)))
    (implies (and (fn2-accept-postable-p slot gen ops)
                  (equal (fn2-ops-post-count ops) 0)
                  (natp (fn2-ops-post-head ops))
                  (equal (fn2-ops-post-head ops) (fn2-ops-post-tail ops))
                  (fn2-peer-recordp *fn2-outcome-done* family port w0 w1 w2 w3))
             (let* ((posted (fn2-host-post-accept-result slot gen *fn2-outcome-done* *fn2-reason-none*
                                                         5 9 family port w0 w1 w2 w3 c))
                    (after (mv-nth 10 (fn2-harvest-one posted))))
               (and (equal (fn2-ops-stray (fn2-core-ops posted)) (fn2-ops-stray ops))
                    (equal (fn2-core-observed-peer after) (list family port w0 w1 w2 w3))))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn2-accept-post-and-harvest (fn2-ops (fn2-core-ops c))))
           :in-theory (e/d (fn2-host-post-accept-result fn2-core-observed-peer)
                           (fn2-post-accept-result fn2-accept-postable-p fn2-harvest-one fn2-harvest-next
                            fn2-ops-observed-peer fn2-peer-recordp fn2-ops-stray fn2-core-ops
                            fn2-ops-post-head fn2-ops-post-tail fn2-ops-post-count)))))
