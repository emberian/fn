; fn: the runtime contract's T10: every emitted action is well formed and recorded in the outstanding-use table.
;
; Part of the runtime contract (books/runtime-contract.lisp states it and its
; statements; this book carries the proofs named below).  Split from that book
; so each certifies under the per-book time limit.

(in-package "ACL2")
(include-book "runtime-contract-requests")
(defthm fn-rtc-req-pre-of-frames
  (and (equal (fn-rtc-req-pre id inc (fn-rtc-with-mstate j m s)) (fn-rtc-req-pre id inc s))
       (equal (fn-rtc-req-pre id inc (fn-rtc-with-uses u s))
              (and (natp id) (natp inc) (fn-rtc-action-argp (fn-rtc-s-res (fn-rtc-slot id s)))
                   (fn-rtc-uses-ops-natp u))))
  :hints (("Goal" :in-theory (disable fn-rtc-action-argp fn-rtc-s-res))))

(defthm fn-rtc-deliver-actions-ok
  (implies (fn-rtc-req-pre id inc s)
           (and (fn-rtc-actions-okp (mv-nth 1 (fn-rtc-deliver s id inc ev q)) (mv-nth 0 (fn-rtc-deliver s id inc ev q)))
                (fn-rtc-actions-kinded-p (mv-nth 1 (fn-rtc-deliver s id inc ev q)))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-deliver) (fn-rtc-requests mv-nth fn-rtc-req-pre fn-rtc-actions-okp
                                                    fn-rtc-actions-kinded-p)))))

(defthm fn-rtc-rearm-actions-ok
  (and (fn-rtc-actions-okp (mv-nth 1 (fn-rtc-rearm s)) (mv-nth 0 (fn-rtc-rearm s)))
       (fn-rtc-actions-kinded-p (mv-nth 1 (fn-rtc-rearm s))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-rearm) (fn-rtc-b-gen fn-rtc-b-bytes fn-rtc-h-buf fn-rtc-h-gen fn-rtc-h-off fn-rtc-h-len fn-rtc-s-res fn-rtc-s-inc fn-rtc-slot fn-rtc-next-op fn-rtc-use-bound fn-rtc-submit-okp fn-rtc-kind-out-p fn-rtc-live-p fn-rtc-current-p fn-rtc-extrap fn-rtc-buffered-kind-p member-equal fn-rtc-kind-op fn-rtc-free-slot fn-rtc-kind-out-p)))))

(defthm fn-rtc-actions-okp-through-rearm
  (implies (and (fn-rtc-actions-okp acts s) (fn-rtc-actions-kinded-p acts))
           (fn-rtc-actions-okp acts (mv-nth 0 (fn-rtc-rearm s))))
  :hints (("Goal" :in-theory (disable fn-rtc-actions-okp fn-rtc-actions-kinded-p fn-rtc-actions-okp-of-subset)
                  :use ((:instance fn-rtc-actions-okp-of-subset (s1 s) (s2 (mv-nth 0 (fn-rtc-rearm s))))))))

(defthm fn-rtc-free-slot-natp
  (implies (fn-rtc-free-slot i slots) (natp (fn-rtc-free-slot i slots)))
  :hints (("Goal" :in-theory (disable fn-rtc-s-status))))

(defthm fn-rtc-free-slot-in-range
  (implies (and (fn-rtc-free-slot i slots) (natp i))
           (< (fn-rtc-free-slot i slots) (+ i (len slots))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fn-rtc-s-status))))

(defthm fn-rtc-req-pre-at-accept
  (implies (and (fn-rtc-free-slot 0 (fn-rtc-slots s1)) (natp r) (< r 18446744073709551616)
                (fn-rtc-uses-ops-natp (fn-rtc-uses s1)) (natp inc))
           (fn-rtc-req-pre (fn-rtc-free-slot 0 (fn-rtc-slots s1)) inc
                           (fn-rtc-with-mstate (fn-rtc-free-slot 0 (fn-rtc-slots s1)) m
                             (fn-rtc-with-slot (fn-rtc-free-slot 0 (fn-rtc-slots s1)) (list inc :live r) s1))))
  :hints (("Goal" :in-theory (disable fn-rtc-free-slot))))

(defun fn-rtc-accept-slot (s1) (declare (xargs :guard t)) (fn-rtc-free-slot 0 (fn-rtc-slots s1)))
(defun fn-rtc-accept-inc (s1) (declare (xargs :guard t))
  (+ 1 (fn-rtc-s-inc (fn-rtc-slot (fn-rtc-free-slot 0 (fn-rtc-slots s1)) s1))))
(defun fn-rtc-accept-go-p (s1 out) (declare (xargs :guard t))
  (and (eq (fn-rtc-get 0 out) :done) (fn-rtc-free-slot 0 (fn-rtc-slots s1))
       (natp (fn-rtc-get 1 out)) (< (fn-rtc-get 1 out) (expt 2 64))))
(defun fn-rtc-accept-prepared (s1 out) (declare (xargs :guard t))
  (fn-rtc-with-mstate (fn-rtc-accept-slot s1) (fn-rtc-m-init)
    (fn-rtc-with-slot (fn-rtc-accept-slot s1) (list (fn-rtc-accept-inc s1) :live (fn-rtc-get 1 out)) s1)))

(defthm fn-rtc-accept-branch-parts
  (and (equal (mv-nth 1 (fn-rtc-accept-branch s1 out q))
              (if (fn-rtc-accept-go-p s1 out)
                  (append (mv-nth 1 (fn-rtc-deliver (fn-rtc-accept-prepared s1 out) (fn-rtc-accept-slot s1)
                                                    (fn-rtc-accept-inc s1) (list :accept out) q))
                          (mv-nth 1 (fn-rtc-rearm (mv-nth 0 (fn-rtc-deliver (fn-rtc-accept-prepared s1 out)
                                                                            (fn-rtc-accept-slot s1)
                                                                            (fn-rtc-accept-inc s1)
                                                                            (list :accept out) q)))))
                (mv-nth 1 (fn-rtc-rearm s1))))
       (equal (mv-nth 0 (fn-rtc-accept-branch s1 out q))
              (if (fn-rtc-accept-go-p s1 out)
                  (mv-nth 0 (fn-rtc-rearm (mv-nth 0 (fn-rtc-deliver (fn-rtc-accept-prepared s1 out)
                                                                    (fn-rtc-accept-slot s1)
                                                                    (fn-rtc-accept-inc s1)
                                                                    (list :accept out) q))))
                (mv-nth 0 (fn-rtc-rearm s1)))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-accept-branch) (fn-rtc-deliver fn-rtc-rearm fn-rtc-free-slot)))))

(defthm fn-rtc-accept-branch-actions-ok
  (implies (fn-rtc-uses-ops-natp (fn-rtc-uses s1))
           (and (fn-rtc-actions-okp (mv-nth 1 (fn-rtc-accept-branch s1 out q)) (mv-nth 0 (fn-rtc-accept-branch s1 out q)))
                (fn-rtc-actions-kinded-p (mv-nth 1 (fn-rtc-accept-branch s1 out q)))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-accept-go-p fn-rtc-accept-slot fn-rtc-accept-prepared)
                                  (fn-rtc-accept-branch fn-rtc-deliver fn-rtc-rearm fn-rtc-actions-okp
                                   fn-rtc-actions-kinded-p fn-rtc-free-slot fn-rtc-accept-inc mv-nth
                                   fn-rtc-req-pre fn-rtc-with-mstate fn-rtc-with-slot)))))


(defun fn-rtc-close-prepared (s1 id inc)
  (declare (xargs :guard t))
  (let* ((s2 (fn-rtc-make (fn-rtc-config s1) (fn-rtc-slots s1)
                          (fn-rtc-release-all (fn-rtc-pool s1) id inc)
                          (fn-rtc-uses s1) (fn-rtc-mstates s1) (fn-rtc-next-op s1)))
         (status (if (fn-rtc-uses-of-slot-p id inc (fn-rtc-uses s2)) :draining :free)))
    (fn-rtc-with-mstate
     id (fn-rtc-m-init)
     (fn-rtc-with-slot id (list inc status (if (eq status :free) nil
                                             (fn-rtc-s-res (fn-rtc-slot id s2))))
                       s2))))

(defthm fn-rtc-close-branch-is-rearm
  (equal (fn-rtc-close-branch s1 id inc) (fn-rtc-rearm (fn-rtc-close-prepared s1 id inc)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-close-branch) (fn-rtc-rearm fn-rtc-uses-of-slot-p)))))

(defthm fn-rtc-close-branch-actions-ok
  (and (fn-rtc-actions-okp (mv-nth 1 (fn-rtc-close-branch s1 id inc)) (mv-nth 0 (fn-rtc-close-branch s1 id inc)))
       (fn-rtc-actions-kinded-p (mv-nth 1 (fn-rtc-close-branch s1 id inc))))
  :hints (("Goal" :in-theory (disable fn-rtc-close-prepared fn-rtc-rearm mv-nth))))

(defthm fn-rtc-actions-okp-member
  (implies (and (fn-rtc-actions-okp acts s) (member-equal a acts))
           (and (fn-rtc-actionp a)
                (fn-rtc-find-use (fn-rtc-recorded-key a) (fn-rtc-uses s))))
  :hints (("Goal" :in-theory (disable fn-rtc-actionp fn-rtc-recorded-key))))

(defthm fn-rtc-ops-natp-of-remove-use
  (implies (fn-rtc-uses-ops-natp uses) (fn-rtc-uses-ops-natp (fn-rtc-remove-use k uses))))

(defthm fn-rtc-use-okp-op-natp
  (implies (fn-rtc-use-okp u s) (natp (fn-rtc-get 3 u)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-use-okp) (fn-rtc-current-p fn-rtc-holders fn-rtc-handlep fn-rtc-buffer
                                                   fn-rtc-slot fn-rtc-u-hd fn-rtc-usep))
                  :expand ((fn-rtc-usep u)))))

(defthm fn-rtc-uses-okp-ops-natp
  (implies (fn-rtc-uses-okp uses s) (fn-rtc-uses-ops-natp uses))
  :hints (("Goal" :in-theory (disable fn-rtc-use-okp fn-rtc-kind-out-p fn-rtc-op-used-p fn-rtc-get)
           :induct (fn-rtc-uses-okp uses s))))

(defthm fn-rtc-ops-natp-of-end-use
  (implies (fn-rtc-uses-ops-natp (fn-rtc-uses s)) (fn-rtc-uses-ops-natp (fn-rtc-uses (fn-rtc-end-use s e)))))

(defthm fn-rtc-slots-okp-res
  (implies (and (fn-rtc-slots-okp i slots) (natp i))
           (fn-rtc-action-argp (fn-rtc-s-res (fn-rtc-get k slots))))
  :hints (("Goal" :induct (fn-rtc-ind-free i k slots))))

(defthm fn-rtc-invp-slot-res
  (implies (fn-rtc-invp s) (fn-rtc-action-argp (fn-rtc-s-res (fn-rtc-slot id s))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-slot) (fn-rtc-uses-okp fn-rtc-pool-okp fn-rtc-draining-okp
                                                fn-rtc-free-slot fn-rtc-kind-out-p fn-rtc-mstates-okp
                                                fn-rtc-slots-is-slot fn-rtc-action-argp fn-rtc-slots-okp-res fn-rtc-slots-okp))
                  :use ((:instance fn-rtc-slots-okp-res (i 0) (k id) (slots (fn-rtc-slots s)))))))

(defthm fn-rtc-slot-res-of-retire-drained
  (implies (fn-rtc-action-argp (fn-rtc-s-res (fn-rtc-slot id s)))
           (fn-rtc-action-argp (fn-rtc-s-res (fn-rtc-slot id (fn-rtc-retire-drained k s)))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-retire-drained) (fn-rtc-action-argp fn-rtc-uses-of-slot-p)))))

(defthm fn-rtc-slot-res-of-end-use
  (implies (fn-rtc-action-argp (fn-rtc-s-res (fn-rtc-slot id s)))
           (fn-rtc-action-argp (fn-rtc-s-res (fn-rtc-slot id (fn-rtc-end-use s e)))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-end-use) (fn-rtc-action-argp fn-rtc-uses-of-slot-p fn-rtc-retire-drained
                                                   fn-rtc-end-lease fn-rtc-s-res fn-rtc-completionp fn-rtc-find-use)))))

(defthm fn-rtc-invp-ops-natp
  (implies (fn-rtc-invp s) (fn-rtc-uses-ops-natp (fn-rtc-uses s)))
  :hints (("Goal" :in-theory (disable fn-rtc-invp fn-rtc-uses-okp-ops-natp)
                  :use (fn-rtc-invp-uses-okp (:instance fn-rtc-uses-okp-ops-natp (uses (fn-rtc-uses s)))))))

(defthm fn-rtc-step-actions-ok
  (implies (fn-rtc-invp s)
           (fn-rtc-actions-okp (fn-rtc-step-actions s e q) (fn-rtc-step-state s e q)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-step-actions fn-rtc-step-state fn-rtc-req-pre)
                                  (fn-rtc-invp mv-nth fn-rtc-acts-on-p fn-rtc-e-id fn-rtc-e-inc fn-rtc-e-kind
                                   fn-rtc-delivered-outcome fn-rtc-find-use fn-rtc-key fn-rtc-end-use
                                   fn-rtc-rearm fn-rtc-deliver fn-rtc-accept-branch fn-rtc-close-branch
                                   fn-rtc-actions-okp fn-rtc-action-argp fn-rtc-s-res fn-rtc-slot
                                   fn-rtc-accept-branch-actions-ok fn-rtc-ops-natp-of-end-use fn-rtc-invp-ops-natp
                                   fn-rtc-uses-of-end-use))
           :use (fn-rtc-invp-uses-okp
                 (:instance fn-rtc-uses-okp-ops-natp (uses (fn-rtc-uses s)))
                 (:instance fn-rtc-invp-slot-res (id (fn-rtc-e-id e)))
                 (:instance fn-rtc-accept-branch-actions-ok (s1 (fn-rtc-end-use s e))
                            (out (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e)))
                 (:instance fn-rtc-ops-natp-of-end-use)
                 fn-rtc-invp-ops-natp))))

; T10
(defthm fn-rtc-every-action-is-outstanding
  (implies (and (fn-rtc-invp s)
                (member-equal a (mv-nth 1 (fn-rtc-step s e q))))
           (and (fn-rtc-actionp a)
                (if (equal (fn-rtc-get 0 a) :cancel)
                    (fn-rtc-find-use (list (fn-rtc-get 0 (fn-rtc-get 4 a))
                                           (fn-rtc-get 1 a) (fn-rtc-get 2 a) (fn-rtc-get 3 a))
                                     (fn-rtc-uses (mv-nth 0 (fn-rtc-step s e q))))
                  (fn-rtc-find-use (fn-rtc-key a)
                                   (fn-rtc-uses (mv-nth 0 (fn-rtc-step s e q)))))))
  :hints (("Goal" :in-theory (disable fn-rtc-invp fn-rtc-actionp fn-rtc-actions-okp-member fn-rtc-step-actions-ok)
                  :use (fn-rtc-step-actions-ok
                        (:instance fn-rtc-actions-okp-member (acts (fn-rtc-step-actions s e q))
                                   (s (fn-rtc-step-state s e q)))))))

