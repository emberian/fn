; fn: the runtime contract's T10: every emitted action is well formed and recorded in the outstanding-use table.
;
; Part of the runtime contract (books/runtime-contract.lisp states it and its
; statements; this book carries the proofs named below).  Split from that book
; so each certifies under the per-book time limit.

(in-package "ACL2")
(include-book "runtime-contract-requests")
(include-book "runtime-contract-invariant")
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
                                                    (fn-rtc-accept-inc s1) (fn-rtc-ev :accept out (fn-rtc-accept-slot s1) (fn-rtc-accept-inc s1) nil) q))
                          (mv-nth 1 (fn-rtc-rearm (mv-nth 0 (fn-rtc-deliver (fn-rtc-accept-prepared s1 out)
                                                                            (fn-rtc-accept-slot s1)
                                                                            (fn-rtc-accept-inc s1)
                                                                            (fn-rtc-ev :accept out (fn-rtc-accept-slot s1) (fn-rtc-accept-inc s1) nil) q)))))
                (mv-nth 1 (fn-rtc-rearm s1))))
       (equal (mv-nth 0 (fn-rtc-accept-branch s1 out q))
              (if (fn-rtc-accept-go-p s1 out)
                  (mv-nth 0 (fn-rtc-rearm (mv-nth 0 (fn-rtc-deliver (fn-rtc-accept-prepared s1 out)
                                                                    (fn-rtc-accept-slot s1)
                                                                    (fn-rtc-accept-inc s1)
                                                                    (fn-rtc-ev :accept out (fn-rtc-accept-slot s1) (fn-rtc-accept-inc s1) nil) q))))
                (mv-nth 0 (fn-rtc-rearm s1)))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-accept-branch) (fn-rtc-deliver fn-rtc-rearm fn-rtc-free-slot)))))

(defthm fn-rtc-accept-branch-actions-ok
  (implies (fn-rtc-uses-ops-natp (fn-rtc-uses s1))
           (and (fn-rtc-actions-okp (mv-nth 1 (fn-rtc-accept-branch s1 out q)) (mv-nth 0 (fn-rtc-accept-branch s1 out q)))
                (fn-rtc-actions-kinded-p (mv-nth 1 (fn-rtc-accept-branch s1 out q)))))
  :hints (("Goal" :in-theory
           (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
             '(fn-rtc-accept-go-p fn-rtc-accept-slot fn-rtc-accept-prepared
               fn-rtc-accept-branch-parts fn-rtc-actions-okp-append fn-rtc-actions-kinded-append
               fn-rtc-deliver-actions-ok fn-rtc-rearm-actions-ok fn-rtc-actions-okp-through-rearm
               fn-rtc-req-pre-at-accept (:type-prescription fn-rtc-accept-inc)
               (:executable-counterpart expt) natp)))))


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
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
             '(fn-rtc-retire-drained fn-rtc-slot-of-with fn-rtc-slot-accessors
               (:executable-counterpart fn-rtc-action-argp))))))

(defthm fn-rtc-slot-res-of-end-use
  (implies (fn-rtc-action-argp (fn-rtc-s-res (fn-rtc-slot id s)))
           (fn-rtc-action-argp (fn-rtc-s-res (fn-rtc-slot id (fn-rtc-end-use s e)))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-end-use) (fn-rtc-action-argp fn-rtc-uses-of-slot-p fn-rtc-retire-drained
                                                   fn-rtc-end-lease fn-rtc-s-res fn-rtc-completionp fn-rtc-find-use)))))

(defthm fn-rtc-invp-ops-natp
  (implies (fn-rtc-invp s) (fn-rtc-uses-ops-natp (fn-rtc-uses s)))
  :hints (("Goal" :in-theory (disable fn-rtc-invp fn-rtc-uses-okp-ops-natp)
                  :use (fn-rtc-invp-uses-okp (:instance fn-rtc-uses-okp-ops-natp (uses (fn-rtc-uses s)))))))

(defthm fn-rtc-req-pre-after-end-use
  (implies (and (fn-rtc-invp s) (natp id) (natp inc))
           (fn-rtc-req-pre id inc (fn-rtc-end-use s e)))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
             '(fn-rtc-req-pre fn-rtc-slot-res-of-end-use fn-rtc-invp-slot-res
               fn-rtc-ops-natp-of-end-use fn-rtc-invp-ops-natp)))))

(defthm fn-rtc-hand-target-inc-natp
  (implies (fn-rtc-hand-delivers-p s e)
           (natp (fn-rtc-get 4 (fn-rtc-b-owner
             (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd
               (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))) s)))))
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-hand-delivers-p fn-rtc-handed-to-live-p fn-rtc-live-p)
                (fn-rtc-find-use fn-rtc-key fn-rtc-buffer fn-rtc-u-hd fn-rtc-h-buf
                 fn-rtc-b-owner fn-rtc-slot fn-rtc-s-inc fn-rtc-s-status
                 fn-rtc-delivered-outcome fn-rtc-completionp fn-rtc-handlep)))))

(defun fn-rtc-pool-actions-p (acts)
  (declare (xargs :guard t))
  (if (consp acts) (and (equal (fn-rtc-get 0 (car acts)) :pool) (fn-rtc-pool-actions-p (cdr acts))) t))
(local (defthm fn-rtc-pool-actions-append
  (equal (fn-rtc-pool-actions-p (append a b)) (and (fn-rtc-pool-actions-p a) (fn-rtc-pool-actions-p b)))))
(local (defthm fn-rtc-pool-actions-kinded
  (implies (fn-rtc-pool-actions-p acts) (fn-rtc-actions-kinded-p acts))
  :hints (("Goal" :induct (fn-rtc-pool-actions-p acts) :in-theory (disable fn-rtc-get)))))
(local (defthm fn-rtc-grant-one-pool-actions
  (fn-rtc-pool-actions-p (mv-nth 1 (fn-rtc-grant-one s)))
  :hints (("Goal" :in-theory (disable fn-rtc-free-pool-buf fn-rtc-oldest-wait fn-rtc-b-gen fn-rtc-s-res fn-rtc-get)))))
(local (defthm fn-rtc-grant-pool-actions
  (fn-rtc-pool-actions-p (mv-nth 1 (fn-rtc-grant n s)))
  :hints (("Goal" :induct (fn-rtc-grant n s)
           :in-theory (e/d (fn-rtc-grant) (mv-nth fn-rtc-grant-one fn-rtc-pool-actions-p))))))
(local (defthm fn-rtc-find-use-of-replace-other-kind
  (implies (and (fn-rtc-find-use k uses) (fn-rtc-get 0 k)
                (not (equal (fn-rtc-get 0 k) (fn-rtc-get 0 key))))
           (fn-rtc-find-use k (fn-rtc-replace-use key v uses)))
  :hints (("Goal" :induct (fn-rtc-replace-use key v uses)))))
(local (defthm fn-rtc-grant-one-keeps-pool-action
  (implies (and (equal (fn-rtc-get 0 a) :pool)
                (fn-rtc-find-use (fn-rtc-recorded-key a) (fn-rtc-uses s)))
           (fn-rtc-find-use (fn-rtc-recorded-key a) (fn-rtc-uses (mv-nth 0 (fn-rtc-grant-one s)))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-recorded-key)
    (mv-nth fn-rtc-grant-one fn-rtc-pool-grant-state fn-rtc-pool-grant-use fn-rtc-free-pool-buf
     fn-rtc-oldest-wait fn-rtc-find-use fn-rtc-replace-use fn-rtc-get))))))
(local (defthm fn-rtc-pool-actions-ok-through-grant-one
  (implies (and (fn-rtc-actions-okp acts s) (fn-rtc-pool-actions-p acts))
           (fn-rtc-actions-okp acts (mv-nth 0 (fn-rtc-grant-one s))))
  :hints (("Goal" :induct (fn-rtc-pool-actions-p acts)
           :in-theory (e/d (fn-rtc-pool-actions-p fn-rtc-actions-okp)
            (mv-nth fn-rtc-grant-one fn-rtc-grant-one-is-pool-grant-state
             fn-rtc-actionp fn-rtc-recorded-key fn-rtc-find-use fn-rtc-get))))))
(local (defthm fn-rtc-pool-actions-ok-through-grant
  (implies (and (fn-rtc-actions-okp acts s) (fn-rtc-pool-actions-p acts))
           (fn-rtc-actions-okp acts (mv-nth 0 (fn-rtc-grant n s))))
  :hints (("Goal" :induct (fn-rtc-grant n s)
           :in-theory (e/d (fn-rtc-grant)
            (mv-nth fn-rtc-grant-one fn-rtc-grant-one-is-pool-grant-state
             fn-rtc-actions-okp fn-rtc-pool-actions-p))))))
(local (defthm fn-rtc-core-invp-slot-res
  (implies (fn-rtc-core-invp s) (fn-rtc-action-argp (fn-rtc-s-res (fn-rtc-slot id s))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-core-invp fn-rtc-slot)
           (fn-rtc-configp fn-rtc-slots-okp fn-rtc-uses-okp fn-rtc-pool-okp-unfolds
            fn-rtc-statics-okp fn-rtc-mstates-okp fn-rtc-draining-okp fn-rtc-action-argp
            fn-rtc-slots-is-slot fn-rtc-slots-okp-res))
           :use ((:instance fn-rtc-slots-okp-res (i 0) (k id) (slots (fn-rtc-slots s))))))))
(local (defthm fn-rtc-replace-use-has-new
  (implies (fn-rtc-find-use key uses) (member-equal v (fn-rtc-replace-use key v uses)))
  :hints (("Goal" :induct (fn-rtc-replace-use key v uses) :in-theory (disable fn-rtc-key)))))

(defun fn-rtc-pool-grant-action (w h s)
  (declare (xargs :guard t))
  (list :pool (nfix (fn-rtc-get 1 w)) (fn-rtc-get 2 w) (fn-rtc-get 3 w)
        (list (list h (+ 1 (fn-rtc-b-gen (fn-rtc-buffer h s))) 0 0)
              (fn-rtc-s-res (fn-rtc-slot (nfix (fn-rtc-get 1 w)) s)))))
(local (defthm fn-rtc-pool-grant-action-well-formed
  (implies (and (fn-rtc-core-invp s) (fn-rtc-use-okp w s) (natp h))
           (fn-rtc-actionp (fn-rtc-pool-grant-action w h s)))
  :hints (("Goal" :in-theory
           (disable fn-rtc-core-invp fn-rtc-use-okp fn-rtc-slot fn-rtc-s-res fn-rtc-b-gen)
           :use (fn-rtc-use-okp-natural-fields
                 (:instance fn-rtc-core-invp-slot-res (id (nfix (fn-rtc-get 1 w)))))))))
(local (defthm fn-rtc-pool-grant-action-key
  (equal (fn-rtc-recorded-key (fn-rtc-pool-grant-action w h s))
         (fn-rtc-key (fn-rtc-pool-grant-use w h s)))))
(local (defthm fn-rtc-pool-grant-action-recorded
  (implies (and (member-equal w (fn-rtc-uses s)) (equal (fn-rtc-get 0 w) :wait))
           (fn-rtc-find-use (fn-rtc-recorded-key (fn-rtc-pool-grant-action w h s))
                            (fn-rtc-uses (fn-rtc-pool-grant-state w h s))))
  :hints (("Goal" :in-theory
           (disable fn-rtc-pool-grant-action fn-rtc-pool-grant-use fn-rtc-pool-grant-state fn-rtc-recorded-key
                    fn-rtc-find-use fn-rtc-replace-use fn-rtc-key fn-rtc-get)
           :use ((:instance fn-rtc-replace-use-has-new (key (fn-rtc-key w)) (v (fn-rtc-pool-grant-use w h s)) (uses (fn-rtc-uses s)))
                 (:instance fn-rtc-find-use-key-of-member (u w) (e w) (uses (fn-rtc-uses s)))
                 (:instance fn-rtc-find-use-of-member-key
                   (x (fn-rtc-pool-grant-use w h s)) (k (fn-rtc-key (fn-rtc-pool-grant-use w h s)))
                   (uses (fn-rtc-replace-use (fn-rtc-key w) (fn-rtc-pool-grant-use w h s) (fn-rtc-uses s)))))))))
(local (defthm fn-rtc-grant-one-actions-is
  (equal (mv-nth 1 (fn-rtc-grant-one s))
         (let ((h (fn-rtc-free-pool-buf 0 (fn-rtc-pool s) (fn-rtc-config s)))
               (w (fn-rtc-oldest-wait (fn-rtc-uses s))))
           (if (and h w) (list (fn-rtc-pool-grant-action w h s)) nil)))
  :hints (("Goal" :in-theory (disable fn-rtc-free-pool-buf fn-rtc-oldest-wait fn-rtc-b-gen fn-rtc-get fn-rtc-s-res)))))
(local (defthm fn-rtc-grant-one-actions-ok
  (implies (fn-rtc-core-invp s)
           (fn-rtc-actions-okp (mv-nth 1 (fn-rtc-grant-one s)) (mv-nth 0 (fn-rtc-grant-one s))))
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-actions-okp)
             (fn-rtc-pool-grant-action-recorded mv-nth fn-rtc-core-invp fn-rtc-use-okp fn-rtc-uses-okp fn-rtc-grant-one fn-rtc-actionp
              fn-rtc-pool-grant-action fn-rtc-pool-grant-state fn-rtc-pool-grant-use
              fn-rtc-free-pool-buf fn-rtc-oldest-wait fn-rtc-get fn-rtc-recorded-key fn-rtc-find-use))
           :use ((:instance fn-rtc-pool-grant-action-recorded
                   (w (fn-rtc-oldest-wait (fn-rtc-uses s)))
                   (h (fn-rtc-free-pool-buf 0 (fn-rtc-pool s) (fn-rtc-config s))))
                 (:instance fn-rtc-uses-okp-member
                   (u (fn-rtc-oldest-wait (fn-rtc-uses s))) (uses (fn-rtc-uses s))))))))
(local (defthm fn-rtc-grant-actions-ok
  (implies (fn-rtc-core-invp s)
           (and (fn-rtc-actions-okp (mv-nth 1 (fn-rtc-grant n s)) (mv-nth 0 (fn-rtc-grant n s)))
                (fn-rtc-actions-kinded-p (mv-nth 1 (fn-rtc-grant n s)))))
  :hints (("Goal" :induct (fn-rtc-grant n s)
           :in-theory (e/d (fn-rtc-grant)
             (mv-nth fn-rtc-core-invp fn-rtc-grant-one fn-rtc-grant-one-is-pool-grant-state
              fn-rtc-grant-one-actions-is fn-rtc-actions-okp fn-rtc-actions-kinded-p fn-rtc-pool-actions-p))))))

(defthm fn-rtc-step-actions-ok
  (implies (fn-rtc-invp s)
           (fn-rtc-actions-okp (fn-rtc-step-actions s e q) (fn-rtc-step-state s e q)))
  :hints (("Goal" :in-theory
           (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
             '(fn-rtc-step-actions fn-rtc-step* fn-rtc-step-state
               fn-rtc-grant-actions-ok (:executable-counterpart member-equal)
               fn-rtc-rearm-actions-ok fn-rtc-actions-okp-append fn-rtc-actions-okp-through-rearm
               fn-rtc-deliver-actions-ok fn-rtc-accept-branch-actions-ok fn-rtc-close-branch-actions-ok
               fn-rtc-req-pre-after-end-use fn-rtc-ops-natp-of-end-use fn-rtc-invp-ops-natp
               (:type-prescription fn-rtc-e-id) (:type-prescription fn-rtc-e-inc)
               (:type-prescription nfix) natp))
           :do-not-induct t
           :use (fn-rtc-hand-target-inc-natp fn-rtc-invp-is-core-and-admission fn-rtc-end-use-preserves-core-invp))))

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
  :hints (("Goal" :in-theory
           (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
             '(fn-rtc-recorded-key fn-rtc-step-actions-is fn-rtc-step-is-step-state))
                  :use (fn-rtc-step-actions-ok
                        (:instance fn-rtc-actions-okp-member (acts (fn-rtc-step-actions s e q))
                                   (s (fn-rtc-step-state s e q)))))))
