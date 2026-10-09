; fn: the runtime contract's step keystones: T7 machine changes only on its own completion, T8 other workspaces untouched, T9 generations monotone, T11 commit only on own barrier, T13 draining slots retire, T14 borrow hides in-flight input, T15 machine states bounded.
;
; Part of the runtime contract (books/runtime-contract.lisp states it and its
; statements; this book carries the proofs named below).  Split from that book
; so each certifies under the per-book time limit.

(in-package "ACL2")
(include-book "runtime-contract")

; The state half of a step, one function of its four branches.
(defun fn-rtc-step-state (s e q)
  (declare (xargs :guard t))
  (if (not (fn-rtc-acts-on-p s e))
      (mv-let (s2 acts) (fn-rtc-rearm (fn-rtc-end-use s e)) (declare (ignore acts)) s2)
    (let* ((s1 (fn-rtc-end-use s e))
           (kind (fn-rtc-e-kind e)) (id (fn-rtc-e-id e)) (inc (fn-rtc-e-inc e))
           (u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))
           (out (fn-rtc-delivered-outcome u e)))
      (cond
       ((fn-rtc-hand-delivers-p s e)
        (let* ((h (fn-rtc-h-buf (fn-rtc-u-hd u))) (b (fn-rtc-buffer h s))
               (o (fn-rtc-b-owner b)) (to (nfix (fn-rtc-get 3 o))) (tinc (fn-rtc-get 4 o))
               (hd2 (list h (+ 1 (fn-rtc-b-gen b)) 0 (len (fn-rtc-b-bytes b)))))
          (mv-let (s2 acts refused cost)
            (fn-rtc-deliver s1 to tinc (fn-rtc-ev :handed out to tinc (list id inc hd2)) q)
            (declare (ignore acts refused cost))
            (mv-let (s3 acts2) (fn-rtc-rearm s2) (declare (ignore acts2)) s3))))
       ((eq kind :accept) (mv-let (s2 a r c) (fn-rtc-accept-branch s1 out q) (declare (ignore a r c)) s2))
       ((eq kind :close) (mv-let (s2 a) (fn-rtc-close-branch s1 id inc) (declare (ignore a)) s2))
       ((eq kind :hand)
        (let* ((h (fn-rtc-h-buf (fn-rtc-u-hd u))) (b (fn-rtc-buffer h s))
               (hd2 (list h (+ 1 (fn-rtc-b-gen b)) 0 (len (fn-rtc-b-bytes b)))))
          (mv-let (s2 a r c)
            (fn-rtc-deliver s1 id inc
              (fn-rtc-ev kind (if (eq (fn-rtc-get 0 out) :done) '(:failed :gone) out)
                         id inc (list hd2)) q)
            (declare (ignore a r c)) s2)))
       (t (mv-let (s2 a r c)
            (fn-rtc-deliver s1 id inc (fn-rtc-ev kind out id inc nil) q)
            (declare (ignore a r c)) s2))))))

(defthm fn-rtc-step-is-step-state
  (equal (mv-nth 0 (fn-rtc-step s e q)) (fn-rtc-step-state s e q))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
             '(fn-rtc-step fn-rtc-step* fn-rtc-step-state)))))
(defthm fn-rtc-gen-le-of-step-state
  (fn-rtc-gen-le h s (fn-rtc-step-state s e q))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
             '(fn-rtc-step-state fn-rtc-gen-le-refl
               fn-rtc-gen-le-chain-end-use fn-rtc-gen-le-chain-rearm
               fn-rtc-gen-le-chain-deliver fn-rtc-gen-le-chain-accept-branch
               fn-rtc-gen-le-chain-close-branch)))))

(in-theory (disable fn-rtc-step-state fn-rtc-step fn-rtc-step*))

; T9
(defthm fn-rtc-generation-is-monotone
  (implies (fn-rtc-invp s)
           (<= (fn-rtc-gen h s) (fn-rtc-gen h (mv-nth 0 (fn-rtc-step s e q)))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-gen-le) (fn-rtc-invp fn-rtc-gen-le-of-step-state fn-rtc-gen))
           :use fn-rtc-gen-le-of-step-state)))

; T14
; T14 is proved over fn-rtc-view in runtime-contract-isolation.

(defthm fn-rtc-mstates-okp-get
  (implies (and (fn-rtc-mstates-okp ms) (< (nfix j) (len ms)))
           (<= (fn-rtc-size (fn-rtc-get j ms)) (fn-rtc-m-max-state))))

(defthm fn-rtc-m-max-state-positive
  (<= 1 (fn-rtc-m-max-state))
  :rule-classes :linear
  :hints (("Goal" :use fn-rtc-m-init-is-bounded :in-theory (disable fn-rtc-m-init-is-bounded))))

; T15
(defthm fn-rtc-machine-states-are-bounded
  (implies (and (fn-rtc-invp s) (natp j))
           (<= (fn-rtc-size (fn-rtc-mstate j s)) (fn-rtc-m-max-state)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-mstate) (fn-rtc-mstates-okp-get))
           :cases ((< j (len (fn-rtc-mstates s))))
           :use ((:instance fn-rtc-mstates-okp-get (ms (fn-rtc-mstates s)))))))


; Machine states, operation by operation.
(defthm fn-rtc-request-keeps-mstates
  (equal (fn-rtc-mstate j (mv-nth 0 (fn-rtc-request r id inc s))) (fn-rtc-mstate j s))
  :hints (("Goal" :in-theory (e/d (fn-rtc-request fn-rtc-req-acquire fn-rtc-req-write fn-rtc-req-release
                                   fn-rtc-req-close fn-rtc-req-cancel fn-rtc-req-submit)
                                  (fn-rtc-b-gen fn-rtc-b-bytes fn-rtc-h-buf fn-rtc-h-gen fn-rtc-h-off fn-rtc-h-len fn-rtc-s-res fn-rtc-s-inc fn-rtc-slot fn-rtc-next-op fn-rtc-use-bound fn-rtc-submit-okp fn-rtc-kind-out-p fn-rtc-live-p fn-rtc-current-p fn-rtc-extrap fn-rtc-buffered-kind-p member-equal fn-rtc-kind-op fn-rtc-submit-okp fn-rtc-kind-out-p fn-rtc-live-p fn-rtc-current-p
                                   fn-rtc-extrap fn-rtc-kind-op fn-rtc-splice)))))
(defthm fn-rtc-requests-keeps-mstates
  (equal (fn-rtc-mstate j (mv-nth 0 (fn-rtc-requests reqs id inc s))) (fn-rtc-mstate j s))
  :hints (("Goal" :in-theory (e/d (fn-rtc-requests) (mv-nth fn-rtc-request))
           :induct (fn-rtc-requests reqs id inc s))))
(defthm fn-rtc-mstate-of-deliver
  (equal (fn-rtc-mstate j (mv-nth 0 (fn-rtc-deliver s id inc ev q)))
         (if (and (equal (nfix j) (nfix id)) (< (nfix id) (len (fn-rtc-mstates s))))
             (mv-nth 0 (fn-rtc-m-step (fn-rtc-mstate id s) ev (fn-rtc-view id inc s) (nfix q)))
           (fn-rtc-mstate j s)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-deliver) (fn-rtc-requests mv-nth)))))
(defthm fn-rtc-mstate-of-end-use
  (equal (fn-rtc-mstate j (fn-rtc-end-use s e)) (fn-rtc-mstate j s))
  :hints (("Goal" :in-theory (enable fn-rtc-end-use))))
(defthm fn-rtc-mstate-of-accept-branch
  (implies (not (equal (nfix j) (nfix (fn-rtc-free-slot 0 (fn-rtc-slots s1)))))
           (equal (fn-rtc-mstate j (mv-nth 0 (fn-rtc-accept-branch s1 out q))) (fn-rtc-mstate j s1)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-accept-branch) (fn-rtc-b-gen fn-rtc-b-bytes fn-rtc-h-buf fn-rtc-h-gen fn-rtc-h-off fn-rtc-h-len fn-rtc-s-res fn-rtc-s-inc fn-rtc-slot fn-rtc-next-op fn-rtc-use-bound fn-rtc-submit-okp fn-rtc-kind-out-p fn-rtc-live-p fn-rtc-current-p fn-rtc-extrap fn-rtc-buffered-kind-p member-equal fn-rtc-kind-op mv-nth fn-rtc-free-slot fn-rtc-deliver fn-rtc-rearm)))))
(defthm fn-rtc-mstates-is-mstate
  (equal (fn-rtc-get j (fn-rtc-mstates s)) (fn-rtc-mstate j s))
  :hints (("Goal" :in-theory (enable fn-rtc-mstate))))
(defthm fn-rtc-slots-is-slot
  (equal (fn-rtc-get j (fn-rtc-slots s)) (fn-rtc-slot j s))
  :hints (("Goal" :in-theory (enable fn-rtc-slot))))
(defthm fn-rtc-mstate-of-close-branch
  (implies (not (equal (nfix j) (nfix id)))
           (equal (fn-rtc-mstate j (mv-nth 0 (fn-rtc-close-branch s1 id inc))) (fn-rtc-mstate j s1)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-close-branch) (fn-rtc-b-gen fn-rtc-b-bytes fn-rtc-h-buf fn-rtc-h-gen fn-rtc-h-off fn-rtc-h-len fn-rtc-s-res fn-rtc-s-inc fn-rtc-slot fn-rtc-next-op fn-rtc-use-bound fn-rtc-submit-okp fn-rtc-kind-out-p fn-rtc-live-p fn-rtc-current-p fn-rtc-extrap fn-rtc-buffered-kind-p member-equal fn-rtc-kind-op mv-nth fn-rtc-uses-of-slot-p fn-rtc-rearm)))))
(defthm fn-rtc-mstate-of-accept-branch-not-done
  (implies (not (eq (fn-rtc-get 0 out) :done))
           (equal (fn-rtc-mstate j (mv-nth 0 (fn-rtc-accept-branch s1 out q))) (fn-rtc-mstate j s1)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-accept-branch) (mv-nth fn-rtc-free-slot fn-rtc-deliver fn-rtc-rearm)))))

(defthm fn-rtc-invp-listener
  (implies (fn-rtc-invp s) (equal (fn-rtc-slot 0 s) '(0 :live nil)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-slot) (fn-rtc-uses-okp fn-rtc-pool-okp fn-rtc-draining-okp fn-rtc-free-slot
                                                fn-rtc-kind-out-p fn-rtc-mstates-okp fn-rtc-slots-is-slot))
                  :expand ((fn-rtc-slots-okp 0 (fn-rtc-slots s))))))

(defthm fn-rtc-slots-of-end-lease
  (equal (fn-rtc-slots (fn-rtc-end-lease u e s)) (fn-rtc-slots s))
  :hints (("Goal" :in-theory (e/d (fn-rtc-end-lease) (fn-rtc-lease-return fn-rtc-holds-p fn-rtc-handlep)))))

(defthm fn-rtc-slots-of-end-use-at-live-slot
  (implies (not (eq (fn-rtc-s-status (fn-rtc-slot (fn-rtc-e-id e) s)) :draining))
           (equal (fn-rtc-slots (fn-rtc-end-use s e)) (fn-rtc-slots s)))
  :hints (("Goal" :in-theory (enable fn-rtc-end-use fn-rtc-retire-drained))))

(defthm fn-rtc-delivered-outcome-done
  (implies (eq (fn-rtc-get 0 (fn-rtc-delivered-outcome u e)) :done)
           (eq (fn-rtc-get 0 (fn-rtc-e-outcome e)) :done))
  :hints (("Goal" :in-theory (enable fn-rtc-delivered-outcome))))

(defthm fn-rtc-use-okp-accept-is-listener
  (implies (and (fn-rtc-use-okp u s) (equal (fn-rtc-get 0 u) :accept))
           (equal (fn-rtc-get 1 u) 0))
  :hints (("Goal" :in-theory (e/d (fn-rtc-use-okp) (fn-rtc-usep fn-rtc-current-p fn-rtc-holders fn-rtc-handlep
                                                   fn-rtc-buffer fn-rtc-slot fn-rtc-u-hd))
                  :expand ((fn-rtc-usep u)))))

(defthm fn-rtc-acts-on-accept-id
  (implies (and (fn-rtc-invp s) (fn-rtc-acts-on-p s e) (eq (fn-rtc-e-kind e) :accept))
           (equal (fn-rtc-e-id e) 0))
  :hints (("Goal" :in-theory (e/d (fn-rtc-acts-on-p fn-rtc-e-kind fn-rtc-e-id)
                                  (fn-rtc-invp fn-rtc-uses-okp-member fn-rtc-find-use fn-rtc-use-okp
                                   fn-rtc-use-okp-accept-is-listener fn-rtc-completionp fn-rtc-slot))
           :use (fn-rtc-invp-uses-okp
                 (:instance fn-rtc-uses-okp-member (uses (fn-rtc-uses s))
                            (u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))))
                 (:instance fn-rtc-use-okp-accept-is-listener (u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))))
                 (:instance fn-rtc-find-use-is-member (k (fn-rtc-key e)) (uses (fn-rtc-uses s)))
                 (:instance fn-rtc-key-of-find-use (k (fn-rtc-key e)) (uses (fn-rtc-uses s)))))))
(defthm fn-rtc-hand-delivers-kind
  (implies (fn-rtc-hand-delivers-p s e) (equal (fn-rtc-e-kind e) :hand))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                           '(fn-rtc-hand-delivers-p)))))

(defthm fn-rtc-acts-on-id-natp
  (implies (fn-rtc-acts-on-p s e) (natp (fn-rtc-e-id e)))
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-acts-on-p fn-rtc-hand-delivers-p fn-rtc-completionp fn-rtc-e-id)
                (fn-rtc-find-use fn-rtc-key fn-rtc-slot fn-rtc-outcomep
                 fn-rtc-handed-to-live-p fn-rtc-delivered-outcome))))
  :rule-classes :forward-chaining)

; T7
(defthm fn-rtc-machine-changes-only-when-delivered-to
  (implies (and (fn-rtc-invp s)
                (not (equal (fn-rtc-mstate j (mv-nth 0 (fn-rtc-step s e q)))
                            (fn-rtc-mstate j s))))
           (and (fn-rtc-acts-on-p s e)
                (equal (nfix j) (fn-rtc-target s e))))
  :hints (("Goal"
           :in-theory (union-theories (theory 'minimal-theory)
                        '(fn-rtc-step-is-step-state fn-rtc-step-state fn-rtc-target
                          fn-rtc-hand-to fn-rtc-mstate-of-deliver fn-rtc-rearm-frame
                          fn-rtc-mstate-of-end-use fn-rtc-mstate-of-accept-branch
                          fn-rtc-mstate-of-accept-branch-not-done fn-rtc-mstate-of-close-branch
                          fn-rtc-slots-of-end-use-at-live-slot fn-rtc-s-status nfix natp
                          (:executable-counterpart fn-rtc-get)))
           :do-not-induct t
           :use (fn-rtc-invp-listener fn-rtc-acts-on-accept-id fn-rtc-hand-delivers-kind fn-rtc-acts-on-id-natp
                 (:instance fn-rtc-delivered-outcome-done
                   (u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))))))))

(defthm fn-rtc-m-step-uncommitted-when-nonbarrier
  (implies (and (not (fn-rtc-m-committedp m)) (not (fn-rtc-fsync-done-p ev)))
           (not (fn-rtc-m-committedp (mv-nth 0 (fn-rtc-m-step m ev pool q)))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use fn-rtc-m-commits-only-on-fsync-done)))

(defthm fn-rtc-accept-branch-commits-nothing
  (implies (not (fn-rtc-m-committedp (fn-rtc-mstate j s1)))
           (not (fn-rtc-m-committedp (fn-rtc-mstate j (mv-nth 0 (fn-rtc-accept-branch s1 out q))))))
  :hints (("Goal" :in-theory
           (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
             '(fn-rtc-accept-branch fn-rtc-rearm-frame fn-rtc-mstate-of-deliver
               fn-rtc-mstate-of-with fn-rtc-m-init-is-uncommitted
               fn-rtc-m-step-uncommitted-when-nonbarrier fn-rtc-fsync-done-p fn-rtc-ev
               fn-rtc-get nfix zp natp fn-rtc-with-accessors fn-rtc-len-of-set car-cons cdr-cons
               (:executable-counterpart nfix) (:executable-counterpart zp))))))

(defthm fn-rtc-close-branch-commits-nothing
  (implies (not (fn-rtc-m-committedp (fn-rtc-mstate j s1)))
           (not (fn-rtc-m-committedp (fn-rtc-mstate j (mv-nth 0 (fn-rtc-close-branch s1 id inc))))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-close-branch) (mv-nth fn-rtc-uses-of-slot-p fn-rtc-rearm)))))

(defthm fn-rtc-deliver-commits-only-on-fsync-done
  (implies (and (not (fn-rtc-m-committedp (fn-rtc-mstate j s)))
                (fn-rtc-m-committedp (fn-rtc-mstate j (mv-nth 0 (fn-rtc-deliver s id inc ev q)))))
           (fn-rtc-fsync-done-p ev))
  :hints (("Goal" :in-theory (disable fn-rtc-m-commits-only-on-fsync-done fn-rtc-fsync-done-p mv-nth)
           :use ((:instance fn-rtc-m-commits-only-on-fsync-done
                  (m (fn-rtc-mstate id s)) (pool (fn-rtc-view id inc s)) (q (nfix q)))))))

(defthm fn-rtc-deliver-commit-implies-barrier
  (implies (and (not (fn-rtc-m-committedp (fn-rtc-mstate j s)))
                (fn-rtc-m-committedp (fn-rtc-mstate j (mv-nth 0 (fn-rtc-deliver s id inc ev q)))))
           (fn-rtc-fsync-done-p ev))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use fn-rtc-deliver-commits-only-on-fsync-done)))

(defthm fn-rtc-deliver-preserves-uncommitted
  (implies (and (not (fn-rtc-m-committedp (fn-rtc-mstate j s)))
                (not (fn-rtc-fsync-done-p ev)))
           (not (fn-rtc-m-committedp
                 (fn-rtc-mstate j (mv-nth 0 (fn-rtc-deliver s id inc ev q))))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use fn-rtc-deliver-commits-only-on-fsync-done)))

(defthm fn-rtc-fsync-done-p-of-ev
  (equal (fn-rtc-fsync-done-p (fn-rtc-ev kind out id inc extra))
         (and (equal kind :fsync) (equal (fn-rtc-get 0 out) :done))))

; T11
(defthm fn-rtc-commit-only-on-own-barrier-completion
  (implies (and (fn-rtc-invp s)
                (not (fn-rtc-m-committedp (fn-rtc-mstate j s)))
                (fn-rtc-m-committedp (fn-rtc-mstate j (mv-nth 0 (fn-rtc-step s e q)))))
           (and (fn-rtc-acts-on-p s e)
                (equal (fn-rtc-e-kind e) :fsync)
                (equal (nfix j) (fn-rtc-e-id e))
                (equal (fn-rtc-get 0 (fn-rtc-e-outcome e)) :done)))
  :hints (("Goal" :in-theory
           (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
             '(fn-rtc-step-is-step-state fn-rtc-step-state fn-rtc-target
               fn-rtc-rearm-frame fn-rtc-mstate-of-end-use
               fn-rtc-accept-branch-commits-nothing fn-rtc-close-branch-commits-nothing
               fn-rtc-deliver-preserves-uncommitted fn-rtc-deliver-commit-implies-barrier
               fn-rtc-fsync-done-p-of-ev nfix zp car-cons cdr-cons
               (:executable-counterpart nfix) (:executable-counterpart zp)))
           :do-not-induct t
           :use (fn-rtc-machine-changes-only-when-delivered-to
                 (:instance fn-rtc-delivered-outcome-done
                   (u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))))))))


; Another instance's workspace, operation by operation.
; Another instance's workspace: a buffer owned (:workspace j ij) with j not the
; acting instance.
(defun fn-rtc-foreign-ws-p (h id s)
  (declare (xargs :guard t))
  (let ((o (fn-rtc-b-owner (fn-rtc-buffer h s))))
    (and (eq (fn-rtc-get 0 o) :workspace)
         (not (equal (fn-rtc-get 1 o) id)))))

(defthm fn-rtc-req-acquire-keeps-foreign
  (implies (fn-rtc-foreign-ws-p h id s)
           (equal (fn-rtc-buffer h (mv-nth 0 (fn-rtc-req-acquire r id inc s))) (fn-rtc-buffer h s))))
(defthm fn-rtc-req-write-keeps-foreign
  (implies (fn-rtc-foreign-ws-p h id s)
           (equal (fn-rtc-buffer h (mv-nth 0 (fn-rtc-req-write r id inc s))) (fn-rtc-buffer h s)))
  :hints (("Goal" :in-theory (disable fn-rtc-splice))))
(defthm fn-rtc-req-release-keeps-foreign
  (implies (fn-rtc-foreign-ws-p h id s)
           (equal (fn-rtc-buffer h (mv-nth 0 (fn-rtc-req-release r id inc s))) (fn-rtc-buffer h s))))
(defthm fn-rtc-req-submit-keeps-foreign
  (implies (fn-rtc-foreign-ws-p h id s)
           (equal (fn-rtc-buffer h (mv-nth 0 (fn-rtc-req-submit r id inc s))) (fn-rtc-buffer h s)))
  :hints (("Goal" :in-theory (disable fn-rtc-b-gen fn-rtc-b-bytes fn-rtc-h-buf fn-rtc-h-gen fn-rtc-h-off fn-rtc-h-len fn-rtc-s-res fn-rtc-s-inc fn-rtc-slot fn-rtc-next-op fn-rtc-use-bound fn-rtc-submit-okp fn-rtc-kind-out-p fn-rtc-live-p fn-rtc-current-p fn-rtc-extrap fn-rtc-buffered-kind-p member-equal fn-rtc-kind-op fn-rtc-submit-okp fn-rtc-kind-out-p fn-rtc-live-p fn-rtc-extrap))))
(defthm fn-rtc-request-keeps-foreign
  (implies (fn-rtc-foreign-ws-p h id s)
           (equal (fn-rtc-buffer h (mv-nth 0 (fn-rtc-request r id inc s))) (fn-rtc-buffer h s)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-request)
                                  (mv-nth fn-rtc-foreign-ws-p fn-rtc-req-acquire fn-rtc-req-write fn-rtc-req-release
                                   fn-rtc-req-close fn-rtc-req-cancel fn-rtc-req-submit)))))
(defthm fn-rtc-requests-keeps-foreign
  (implies (fn-rtc-foreign-ws-p h id s)
           (equal (fn-rtc-buffer h (mv-nth 0 (fn-rtc-requests reqs id inc s))) (fn-rtc-buffer h s)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-requests) (mv-nth fn-rtc-request))
           :induct (fn-rtc-requests reqs id inc s))))
(defthm fn-rtc-deliver-keeps-foreign
  (implies (fn-rtc-foreign-ws-p h id s)
           (equal (fn-rtc-buffer h (mv-nth 0 (fn-rtc-deliver s id inc ev q))) (fn-rtc-buffer h s)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-deliver) (fn-rtc-requests mv-nth)))))
(defthm fn-rtc-accept-branch-keeps-foreign
  (implies (fn-rtc-foreign-ws-p h (fn-rtc-free-slot 0 (fn-rtc-slots s1)) s1)
           (equal (fn-rtc-buffer h (mv-nth 0 (fn-rtc-accept-branch s1 out q))) (fn-rtc-buffer h s1)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-accept-branch) (fn-rtc-b-gen fn-rtc-b-bytes fn-rtc-h-buf fn-rtc-h-gen fn-rtc-h-off fn-rtc-h-len fn-rtc-s-res fn-rtc-s-inc fn-rtc-slot fn-rtc-next-op fn-rtc-use-bound fn-rtc-submit-okp fn-rtc-kind-out-p fn-rtc-live-p fn-rtc-current-p fn-rtc-extrap fn-rtc-buffered-kind-p member-equal fn-rtc-kind-op mv-nth fn-rtc-free-slot fn-rtc-deliver fn-rtc-rearm)))))
(defthm fn-rtc-close-branch-keeps-foreign
  (implies (fn-rtc-foreign-ws-p h id s1)
           (equal (fn-rtc-buffer h (mv-nth 0 (fn-rtc-close-branch s1 id inc))) (fn-rtc-buffer h s1)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-close-branch) (mv-nth fn-rtc-uses-of-slot-p fn-rtc-rearm)))))
(defthm fn-rtc-end-use-keeps-workspaces
  (implies (and (fn-rtc-invp s)
                (eq (fn-rtc-get 0 (fn-rtc-b-owner (fn-rtc-buffer h s))) :workspace))
           (equal (fn-rtc-buffer h (fn-rtc-end-use s e)) (fn-rtc-buffer h s)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-end-use fn-rtc-leasedp)
                                  (fn-rtc-invp fn-rtc-use-okp fn-rtc-completionp fn-rtc-find-use
                                   fn-rtc-remove-use fn-rtc-holds-p fn-rtc-handlep fn-rtc-key
                                   fn-rtc-h-buf fn-rtc-h-gen fn-rtc-u-hd fn-rtc-use-okp-lease
                                   fn-rtc-uses-okp-member fn-rtc-end-lease-buffer-unchanged))
           :do-not-induct t
           :use ((:instance fn-rtc-invp-uses-okp)
                 (:instance fn-rtc-uses-okp-member (uses (fn-rtc-uses s))
                            (u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))))
                 (:instance fn-rtc-use-okp-lease (u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))))
                 (:instance fn-rtc-find-use-is-member (k (fn-rtc-key e)) (uses (fn-rtc-uses s)))
                 (:instance fn-rtc-end-lease-buffer-unchanged
                            (u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))
                            (s (fn-rtc-with-uses (fn-rtc-remove-use (fn-rtc-key e) (fn-rtc-uses s)) s)))))))

(defthm fn-rtc-accept-branch-not-done-keeps-buffers
  (implies (not (eq (fn-rtc-get 0 out) :done))
           (equal (fn-rtc-buffer h (mv-nth 0 (fn-rtc-accept-branch s1 out q))) (fn-rtc-buffer h s1)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-accept-branch) (mv-nth fn-rtc-free-slot fn-rtc-deliver fn-rtc-rearm)))))

(defthm fn-rtc-accept-branch-no-slot-keeps-buffers
  (implies (not (fn-rtc-free-slot 0 (fn-rtc-slots s1)))
           (equal (fn-rtc-buffer h (mv-nth 0 (fn-rtc-accept-branch s1 out q))) (fn-rtc-buffer h s1)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-accept-branch) (mv-nth fn-rtc-free-slot fn-rtc-deliver fn-rtc-rearm)))))

(defthm fn-rtc-free-slot-result-natp
  (implies (fn-rtc-free-slot i slots) (natp (fn-rtc-free-slot i slots)))
  :hints (("Goal" :in-theory (disable fn-rtc-s-status))))

; T8
(defthm fn-rtc-other-workspaces-are-untouched
  (implies (and (fn-rtc-invp s)
                (equal (fn-rtc-get 0 (fn-rtc-b-owner (fn-rtc-buffer h s))) :workspace)
                (not (equal (fn-rtc-get 1 (fn-rtc-b-owner (fn-rtc-buffer h s)))
                            (fn-rtc-target s e))))
           (equal (fn-rtc-buffer h (mv-nth 0 (fn-rtc-step s e q)))
                  (fn-rtc-buffer h s)))
  :hints (("Goal" :in-theory
           (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
             '(fn-rtc-step-is-step-state fn-rtc-step-state fn-rtc-target fn-rtc-hand-to
               fn-rtc-foreign-ws-p fn-rtc-rearm-frame fn-rtc-end-use-keeps-workspaces
               fn-rtc-deliver-keeps-foreign fn-rtc-close-branch-keeps-foreign
               fn-rtc-accept-branch-keeps-foreign fn-rtc-accept-branch-not-done-keeps-buffers
               fn-rtc-accept-branch-no-slot-keeps-buffers
               fn-rtc-slots-of-end-use-at-live-slot fn-rtc-s-status nfix natp
               (:executable-counterpart fn-rtc-get)))
           :do-not-induct t
           :use ((:instance fn-rtc-free-slot-result-natp (i 0) (slots (fn-rtc-slots s)))
                 fn-rtc-invp-listener fn-rtc-acts-on-accept-id fn-rtc-hand-delivers-kind
                 (:instance fn-rtc-delivered-outcome-done
                   (u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))))))))

; Draining slots retire.
(defun fn-rtc-ind-free (i k slots)
  (declare (xargs :guard t :measure (len slots)) (irrelevant i))
  (if (consp slots)
      (if (zp (nfix k)) t (fn-rtc-ind-free (+ 1 (nfix i)) (- (nfix k) 1) (cdr slots)))
    t))

(defthm fn-rtc-free-slot-found
  (implies (and (natp i) (natp k) (< k (len slots)) (< 0 (+ i k))
                (eq (fn-rtc-s-status (fn-rtc-get k slots)) :free))
           (fn-rtc-free-slot i slots))
  :hints (("Goal" :induct (fn-rtc-ind-free i k slots)
                  :in-theory (disable fn-rtc-s-status))))

(defthm fn-rtc-rearm-arms-when-free
  (implies (fn-rtc-free-slot 0 (fn-rtc-slots s))
           (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses (mv-nth 0 (fn-rtc-rearm s)))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-rearm) (fn-rtc-free-slot)))))

(defthm fn-rtc-retire-drained-retires
  (implies (and (eq (fn-rtc-s-status (fn-rtc-slot id s)) :draining)
                (not (fn-rtc-uses-of-slot-p id (fn-rtc-s-inc (fn-rtc-slot id s)) (fn-rtc-uses s)))
                (< (nfix id) (len (fn-rtc-slots s))))
           (equal (fn-rtc-s-status (fn-rtc-slot id (fn-rtc-retire-drained id s))) :free))
  :hints (("Goal" :in-theory (e/d (fn-rtc-retire-drained) (fn-rtc-b-gen fn-rtc-b-bytes fn-rtc-h-buf fn-rtc-h-gen fn-rtc-h-off fn-rtc-h-len fn-rtc-s-res fn-rtc-s-inc fn-rtc-slot fn-rtc-next-op fn-rtc-use-bound fn-rtc-submit-okp fn-rtc-kind-out-p fn-rtc-live-p fn-rtc-current-p fn-rtc-extrap fn-rtc-buffered-kind-p member-equal fn-rtc-kind-op)))))
(defthm fn-rtc-use-okp-slot-range
  (implies (fn-rtc-use-okp u s)
           (and (natp (fn-rtc-get 1 u))
                (< (fn-rtc-get 1 u) (fn-rtc-nslots (fn-rtc-config s)))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-use-okp) (fn-rtc-current-p fn-rtc-holders fn-rtc-handlep
                                                   fn-rtc-buffer fn-rtc-slot fn-rtc-u-hd))
                  :expand ((fn-rtc-usep u)))))

(defthm fn-rtc-invp-slots-len
  (implies (fn-rtc-invp s) (equal (len (fn-rtc-slots s)) (fn-rtc-nslots (fn-rtc-config s))))
  :hints (("Goal" :in-theory (disable fn-rtc-uses-okp fn-rtc-pool-okp fn-rtc-draining-okp fn-rtc-free-slot
                                      fn-rtc-kind-out-p fn-rtc-mstates-okp fn-rtc-slots-okp))))

(defthm fn-rtc-end-use-structure
  (implies (and (fn-rtc-completionp e) (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))
           (equal (fn-rtc-end-use s e)
                  (fn-rtc-retire-drained
                   (fn-rtc-e-id e)
                   (fn-rtc-end-lease (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e
                                     (fn-rtc-with-uses (fn-rtc-remove-use (fn-rtc-key e) (fn-rtc-uses s)) s)))))
  :hints (("Goal" :in-theory (enable fn-rtc-end-use))))

(defthm fn-rtc-key-equal-parts
  (implies (equal (fn-rtc-key e) (fn-rtc-key u))
           (and (equal (fn-rtc-get 0 e) (fn-rtc-get 0 u))
                (equal (fn-rtc-get 1 e) (fn-rtc-get 1 u))
                (equal (fn-rtc-get 2 e) (fn-rtc-get 2 u))
                (equal (fn-rtc-get 3 e) (fn-rtc-get 3 u))))
  :rule-classes :forward-chaining)

(defthm fn-rtc-len-slots-of-retire-drained
  (equal (len (fn-rtc-slots (fn-rtc-retire-drained id s))) (len (fn-rtc-slots s)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-retire-drained) (fn-rtc-uses-of-slot-p)))))

(defthm fn-rtc-slot-of-rearm
  (equal (fn-rtc-slot j (mv-nth 0 (fn-rtc-rearm s))) (fn-rtc-slot j s))
  :hints (("Goal" :in-theory (e/d (fn-rtc-rearm) (fn-rtc-free-slot fn-rtc-kind-out-p)))))

(defthm fn-rtc-request-keeps-free-slot
  (implies (equal (fn-rtc-s-status (fn-rtc-slot j s)) :free)
           (equal (fn-rtc-slot j (mv-nth 0 (fn-rtc-request r id inc s)))
                  (fn-rtc-slot j s)))
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-request fn-rtc-req-acquire fn-rtc-req-write fn-rtc-req-release
                 fn-rtc-req-close fn-rtc-req-cancel fn-rtc-req-submit fn-rtc-live-p)
                (fn-rtc-b-gen fn-rtc-b-bytes fn-rtc-h-buf fn-rtc-h-gen fn-rtc-h-off
                 fn-rtc-h-len fn-rtc-s-res fn-rtc-s-inc fn-rtc-slot fn-rtc-next-op
                 fn-rtc-use-bound fn-rtc-submit-okp fn-rtc-kind-out-p fn-rtc-current-p
                 fn-rtc-extrap fn-rtc-buffered-kind-p member-equal fn-rtc-kind-op fn-rtc-splice)))))

(defthm fn-rtc-requests-keep-free-slot
  (implies (equal (fn-rtc-s-status (fn-rtc-slot j s)) :free)
           (equal (fn-rtc-slot j (mv-nth 0 (fn-rtc-requests reqs id inc s)))
                  (fn-rtc-slot j s)))
  :hints (("Goal" :induct (fn-rtc-requests reqs id inc s)
           :in-theory (e/d (fn-rtc-requests) (fn-rtc-request mv-nth fn-rtc-s-status)))))

(defthm fn-rtc-deliver-keeps-free-slot
  (implies (equal (fn-rtc-s-status (fn-rtc-slot j s)) :free)
           (equal (fn-rtc-slot j (mv-nth 0 (fn-rtc-deliver s id inc ev q)))
                  (fn-rtc-slot j s)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-deliver)
                                  (fn-rtc-requests mv-nth fn-rtc-s-status)))))

; T13
(defthm fn-rtc-end-use-retires-last
  (implies (and (fn-rtc-invp s)
                (equal (fn-rtc-s-status (fn-rtc-slot j s)) :draining)
                (member-equal u (fn-rtc-uses s))
                (equal (fn-rtc-get 1 u) j)
                (fn-rtc-ends-use-p e u)
                (not (fn-rtc-uses-of-slot-p j (fn-rtc-s-inc (fn-rtc-slot j s))
                                            (fn-rtc-remove-use (fn-rtc-key u) (fn-rtc-uses s)))))
           (and (equal (fn-rtc-s-status (fn-rtc-slot j (fn-rtc-end-use s e))) :free)
                (natp j)
                (< j (len (fn-rtc-slots (fn-rtc-end-use s e))))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-ends-use-p fn-rtc-e-id)
                                  (fn-rtc-invp mv-nth fn-rtc-end-use fn-rtc-rearm fn-rtc-completionp
                                   fn-rtc-find-use fn-rtc-remove-use fn-rtc-uses-of-slot-p fn-rtc-free-slot
                                   fn-rtc-use-okp fn-rtc-retire-drained fn-rtc-end-lease fn-rtc-key
                                   fn-rtc-free-slot-found fn-rtc-retire-drained-retires fn-rtc-s-status
                                   fn-rtc-s-inc))
           :do-not-induct t
           :use (fn-rtc-invp-uses-okp fn-rtc-invp-listener fn-rtc-invp-slots-len
                 (:instance fn-rtc-uses-okp-member (uses (fn-rtc-uses s)))
                 (:instance fn-rtc-use-okp-slot-range)
                 (:instance fn-rtc-find-use-key-of-member (uses (fn-rtc-uses s)))
                 (:instance fn-rtc-retire-drained-retires
                            (id j)
                            (s (fn-rtc-end-lease (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e
                                                 (fn-rtc-with-uses (fn-rtc-remove-use (fn-rtc-key e) (fn-rtc-uses s)) s))))
                 (:instance fn-rtc-free-slot-found (i 0) (k j)
                            (slots (fn-rtc-slots (fn-rtc-end-use s e))))))))

(defthm fn-rtc-free-record-implies-free-slot
  (implies (and (equal (fn-rtc-s-status (fn-rtc-slot j s)) :free) (posp j))
           (fn-rtc-free-slot 0 (fn-rtc-slots s)))
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-slot fn-rtc-s-status)
                (fn-rtc-free-slot fn-rtc-free-slot-found fn-rtc-slots-is-slot))
           :use ((:instance fn-rtc-free-slot-found (i 0) (k j) (slots (fn-rtc-slots s)))
                 (:instance fn-rtc-get-out-of-range (i j) (l (fn-rtc-slots s)))))))

(defthm fn-rtc-rearm-arms-from-free-record
  (implies (and (equal (fn-rtc-s-status (fn-rtc-slot j s)) :free) (posp j))
           (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses (mv-nth 0 (fn-rtc-rearm s)))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use (fn-rtc-free-record-implies-free-slot fn-rtc-rearm-arms-when-free))))

(defthm fn-rtc-rearm-after-deliver-arms-from-free-record
  (implies (and (equal (fn-rtc-s-status (fn-rtc-slot j s)) :free) (posp j))
           (fn-rtc-kind-out-p :accept 0 0
             (fn-rtc-uses (mv-nth 0 (fn-rtc-rearm
               (mv-nth 0 (fn-rtc-deliver s id inc ev q)))))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use (fn-rtc-deliver-keeps-free-slot
                 (:instance fn-rtc-rearm-arms-from-free-record
                   (s (mv-nth 0 (fn-rtc-deliver s id inc ev q))))))))

(defthm fn-rtc-last-completion-retires-a-draining-slot
  (implies (and (fn-rtc-invp s)
                (equal (fn-rtc-s-status (fn-rtc-slot j s)) :draining)
                (member-equal u (fn-rtc-uses s))
                (equal (fn-rtc-get 1 u) j)
                (fn-rtc-ends-use-p e u)
                (not (fn-rtc-uses-of-slot-p j (fn-rtc-s-inc (fn-rtc-slot j s))
                                            (fn-rtc-remove-use (fn-rtc-key u) (fn-rtc-uses s)))))
           (let ((s2 (mv-nth 0 (fn-rtc-step s e q))))
             (and (equal (fn-rtc-s-status (fn-rtc-slot j s2)) :free)
                  (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses s2)))))
  :hints (("Goal" :in-theory
           (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
             '(fn-rtc-step-is-step-state fn-rtc-step-state fn-rtc-acts-on-p
               fn-rtc-ends-use-p fn-rtc-e-id (:executable-counterpart fn-rtc-s-status)
               fn-rtc-slot-of-rearm fn-rtc-rearm-arms-from-free-record
               fn-rtc-rearm-after-deliver-arms-from-free-record
               fn-rtc-deliver-keeps-free-slot fn-rtc-key-equal-parts
               fn-rtc-free-record-implies-free-slot posp natp nfix
               (:executable-counterpart fn-rtc-get)))
           :do-not-induct t :cases ((equal j 0))
           :use (fn-rtc-invp-listener fn-rtc-end-use-retires-last))))
