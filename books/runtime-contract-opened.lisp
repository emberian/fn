; fn: the runtime contract's store-opened completion (v2.2): KO1 the initial state arms one
; :opened per static slot, KO1b only a static slot holds an :opened use, KO2 it acts at most once,
; KO3 an acting :opened steps exactly its static slot's machine.
;
; Part of the runtime contract (books/runtime-contract.lisp defines `fn-rtc-arm-opened' and the
; :opened arm of `fn-rtc-step*'; this book carries the proofs).

(in-package "ACL2")
(include-book "runtime-contract-invariant-facts")
(include-book "runtime-contract-isolation")

(local (defthm fn-rtc-opened-use-is-static-lemma
  (implies (and (fn-rtc-uses-okp uses s) (fn-rtc-kind-out-p :opened id inc uses))
           (and (<= 1 id) (<= id (fn-rtc-nstatic (fn-rtc-config s)))))
  :hints (("Goal" :induct (fn-rtc-uses-okp uses s)
           :in-theory (union-theories (theory 'minimal-theory)
                        '(fn-rtc-use-okp fn-rtc-uses-okp fn-rtc-kind-out-p fn-rtc-usep nfix natp
                          fn-rtc-get-of-non-natp))))))

(defthm fn-rtc-opened-use-is-static
  (implies (and (fn-rtc-invp s) (fn-rtc-kind-out-p :opened id inc (fn-rtc-uses s)))
           (and (<= 1 id) (<= id (fn-rtc-nstatic (fn-rtc-config s)))))
  :hints (("Goal" :use ((:instance fn-rtc-opened-use-is-static-lemma (uses (fn-rtc-uses s)))
                        (:instance fn-rtc-invp-uses-okp))
           :in-theory (theory 'minimal-theory))))

(local (defthm fn-rtc-uses-of-arm-opened
  (implies (and (natp j) (natp i))
           (iff (fn-rtc-kind-out-p :opened j 1 (fn-rtc-uses (mv-nth 0 (fn-rtc-arm-opened i n s))))
                (or (fn-rtc-kind-out-p :opened j 1 (fn-rtc-uses s))
                    (and (<= i j) (< j (+ i (nfix n)))))))
  :hints (("Goal" :induct (fn-rtc-arm-opened i n s)
           :in-theory (e/d (fn-rtc-arm-opened fn-rtc-issue fn-rtc-make fn-rtc-uses fn-rtc-kind-out-cons)
                           (fn-rtc-kind-out-p))))))

(local (defthm fn-rtc-opened-out-of-rearm
  (iff (fn-rtc-kind-out-p :opened j inc (fn-rtc-uses (mv-nth 0 (fn-rtc-rearm s))))
       (fn-rtc-kind-out-p :opened j inc (fn-rtc-uses s)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-rearm fn-rtc-arm-accept fn-rtc-arm-grant fn-rtc-issue fn-rtc-make fn-rtc-uses fn-rtc-kind-out-cons)
                                  (fn-rtc-kind-out-p fn-rtc-free-slot fn-rtc-free-pool-buf fn-rtc-oldest-wait))))))

(local (defthm fn-rtc-kind-out-of-nil (not (fn-rtc-kind-out-p k id inc nil))
  :hints (("Goal" :in-theory (enable fn-rtc-kind-out-p)))))

(defthm fn-rtc-init-arms-the-opened
  (implies (and (fn-rtc-configp cfg) (natp j) (< j (fn-rtc-nslots cfg)))
           (iff (fn-rtc-kind-out-p :opened j 1 (fn-rtc-uses (mv-nth 0 (fn-rtc-init cfg))))
                (and (<= 1 j) (<= j (fn-rtc-nstatic cfg)))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-init-is-base)
                                  (fn-rtc-rearm fn-rtc-arm-opened fn-rtc-init-base fn-rtc-init mv-nth fn-rtc-kind-out-p))
           :use ((:instance fn-rtc-uses-of-arm-opened (i 1) (n (fn-rtc-nstatic cfg)) (s (fn-rtc-init-base cfg)))
                 (:instance fn-rtc-opened-out-of-rearm (inc 1) (s (mv-nth 0 (fn-rtc-arm-opened 1 (fn-rtc-nstatic cfg) (fn-rtc-init-base cfg)))))
                 (:instance fn-rtc-init-base-facts)))))

(local (defthm fn-rtc-opened-pool-of-end-use
  (implies (not (fn-rtc-handlep (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))))
           (equal (fn-rtc-pool (fn-rtc-end-use s e)) (fn-rtc-pool s)))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
             '(fn-rtc-end-use fn-rtc-end-lease fn-rtc-retire-drained fn-rtc-with-accessors))))))

(local (defthm fn-rtc-opened-view-of-end-use
  (implies (not (fn-rtc-handlep (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))))
           (equal (fn-rtc-view id inc (fn-rtc-end-use s e)) (fn-rtc-view id inc s)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-view) (fn-rtc-find-use fn-rtc-key fn-rtc-end-use fn-rtc-handlep fn-rtc-u-hd))
           :use fn-rtc-opened-pool-of-end-use))))

(local (defthm fn-rtc-opened-step-is
  (implies (and (fn-rtc-acts-on-p s e) (eq (fn-rtc-get 0 e) :opened))
           (equal (mv-nth 0 (fn-rtc-step s e q))
                  (mv-nth 0 (fn-rtc-rearm
                              (mv-nth 0 (fn-rtc-deliver (fn-rtc-end-use s e) (fn-rtc-e-id e) (fn-rtc-e-inc e)
                                          (fn-rtc-ev :opened
                                                     (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e)
                                                     (fn-rtc-e-id e) (fn-rtc-e-inc e)
                                                     (if (eq (fn-rtc-get 0 (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e)) :done)
                                                         (list (fn-rtc-e-data e)) nil))
                                          q))))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-step-is-step-state fn-rtc-step-state fn-rtc-hand-delivers-p fn-rtc-e-kind)
                                  (fn-rtc-acts-on-p fn-rtc-end-use fn-rtc-deliver fn-rtc-rearm fn-rtc-delivered-outcome fn-rtc-find-use
                                   fn-rtc-key fn-rtc-get fn-rtc-ev))))))

(local (defthm fn-rtc-member-of-find-use
  (implies (fn-rtc-find-use k uses) (member-equal (fn-rtc-find-use k uses) uses))
  :hints (("Goal" :induct (fn-rtc-find-use k uses)))))

(local (defthm fn-rtc-opened-kind-of-find-use
  (implies (fn-rtc-find-use k uses)
           (equal (fn-rtc-get 0 (fn-rtc-find-use k uses)) (fn-rtc-get 0 k)))
  :hints (("Goal" :in-theory (enable fn-rtc-key) :induct (fn-rtc-find-use k uses)))))

(local (defthm fn-rtc-use-okp-opened
  (implies (and (fn-rtc-use-okp u s) (equal (fn-rtc-get 0 u) :opened))
           (and (fn-rtc-usep u)
                (null (fn-rtc-u-hd u))
                (<= 1 (nfix (fn-rtc-get 1 u))) (<= (nfix (fn-rtc-get 1 u)) (fn-rtc-nstatic (fn-rtc-config s)))
                (fn-rtc-current-p (nfix (fn-rtc-get 1 u)) (fn-rtc-get 2 u) s)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                        '(fn-rtc-use-okp fn-rtc-usep fn-rtc-u-hd nfix natp fn-rtc-get-of-non-natp))))))

(local (defthm fn-rtc-opened-find-use-facts
  (implies (and (fn-rtc-invp s) (fn-rtc-find-use key (fn-rtc-uses s)) (equal (fn-rtc-get 0 key) :opened))
           (let ((u (fn-rtc-find-use key (fn-rtc-uses s))))
             (and (equal (fn-rtc-get 0 u) :opened)
                  (null (fn-rtc-u-hd u))
                  (<= 1 (nfix (fn-rtc-get 1 u))) (<= (nfix (fn-rtc-get 1 u)) (fn-rtc-nstatic (fn-rtc-config s)))
                  (fn-rtc-current-p (nfix (fn-rtc-get 1 u)) (fn-rtc-get 2 u) s))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '())
           :use ((:instance fn-rtc-opened-kind-of-find-use (k key) (uses (fn-rtc-uses s)))
                 (:instance fn-rtc-member-of-find-use (k key) (uses (fn-rtc-uses s)))
                 (:instance fn-rtc-use-okp-opened (u (fn-rtc-find-use key (fn-rtc-uses s))))
                 (:instance fn-rtc-uses-okp-member (uses (fn-rtc-uses s)) (u (fn-rtc-find-use key (fn-rtc-uses s))))
                 fn-rtc-invp-uses-okp)))))

(local (defthm fn-rtc-opened-delivers-done
  (implies (and (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))
                (equal (fn-rtc-get 0 e) :opened)
                (equal (fn-rtc-get 4 e) '(:done 0)))
           (equal (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e) '(:done 0)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-delivered-outcome fn-rtc-e-outcome)
                                  (fn-rtc-find-use fn-rtc-key))
           :use (:instance fn-rtc-opened-kind-of-find-use (k (fn-rtc-key e)) (uses (fn-rtc-uses s)))))))

(local (defthm fn-rtc-opened-acts-facts
  (implies (and (fn-rtc-acts-on-p s e) (equal (fn-rtc-get 0 e) :opened))
           (and (fn-rtc-completionp e)
                (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))
                (equal (fn-rtc-s-inc (fn-rtc-slot (fn-rtc-e-id e) s)) (fn-rtc-e-inc e))
                (equal (fn-rtc-s-status (fn-rtc-slot (fn-rtc-e-id e) s)) :live)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-acts-on-p fn-rtc-hand-delivers-p fn-rtc-e-kind)
                                  (fn-rtc-find-use fn-rtc-key fn-rtc-completionp fn-rtc-slot fn-rtc-s-inc fn-rtc-s-status
                                   fn-rtc-e-id fn-rtc-e-inc))))))



(local (defthm fn-rtc-static-slot-at
  (implies (and (fn-rtc-invp s) (natp k) (<= 1 k) (<= k (fn-rtc-nstatic (fn-rtc-config s))))
           (equal (fn-rtc-slot k s) '(1 :live 0)))
  :hints (("Goal" :use (fn-rtc-invp-has-static-records
                        (:instance fn-rtc-statics-okp-get (j 1) (n (fn-rtc-nstatic (fn-rtc-config s))) (slots (fn-rtc-slots s))))
           :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-slot (:executable-counterpart nfix) (:executable-counterpart natp) fn-rtc-nstatic nfix))))))

(local (defthm fn-rtc-key-get-0
  (equal (fn-rtc-get 0 (fn-rtc-key e)) (fn-rtc-get 0 e))
  :hints (("Goal" :in-theory (enable fn-rtc-key)))))

(local (defthm fn-rtc-key-parts-of-find-use
  (implies (fn-rtc-find-use (fn-rtc-key e) uses)
           (let ((u (fn-rtc-find-use (fn-rtc-key e) uses)))
             (and (equal (fn-rtc-get 1 u) (fn-rtc-get 1 e))
                  (equal (fn-rtc-get 2 u) (fn-rtc-get 2 e)))))
  :hints (("Goal" :use (:instance fn-rtc-key-of-find-use (k (fn-rtc-key e)))
           :in-theory (e/d (fn-rtc-key) (fn-rtc-key-of-find-use fn-rtc-find-use))))))

(local (defthm fn-rtc-opened-acting-facts
  (implies (and (fn-rtc-invp s) (fn-rtc-acts-on-p s e) (equal (fn-rtc-get 0 e) :opened))
           (and (natp (fn-rtc-get 1 e)) (natp (fn-rtc-get 2 e))
                (<= 1 (fn-rtc-get 1 e)) (<= (fn-rtc-get 1 e) (fn-rtc-nstatic (fn-rtc-config s)))
                (equal (fn-rtc-get 2 e) 1)
                (null (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-completionp fn-rtc-current-p fn-rtc-s-inc fn-rtc-e-id fn-rtc-e-inc)
                                  (fn-rtc-invp fn-rtc-invp-is-core-and-admission fn-rtc-core-invp fn-rtc-acts-on-p
                                   fn-rtc-find-use fn-rtc-key fn-rtc-slot fn-rtc-nstatic fn-rtc-config
                                   fn-rtc-opened-find-use-facts fn-rtc-static-slot-at fn-rtc-opened-acts-facts))
           :use (fn-rtc-opened-acts-facts
                 (:instance fn-rtc-opened-find-use-facts (key (fn-rtc-key e)))
                 (:instance fn-rtc-key-parts-of-find-use (uses (fn-rtc-uses s)))
                 (:instance fn-rtc-static-slot-at (k (nfix (fn-rtc-get 1 e)))))))))

(local (defthm fn-rtc-opened-step-simplified
  (implies (and (fn-rtc-invp s) (fn-rtc-acts-on-p s e) (eq (fn-rtc-get 0 e) :opened)
                (equal (fn-rtc-get 4 e) '(:done 0)))
           (equal (mv-nth 0 (fn-rtc-step s e q))
                  (mv-nth 0 (fn-rtc-rearm
                              (mv-nth 0 (fn-rtc-deliver (fn-rtc-end-use s e) (fn-rtc-get 1 e) 1
                                          (list :opened '(:done 0) (fn-rtc-get 1 e) 1 (fn-rtc-get 5 e))
                                          q))))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-ev fn-rtc-e-id fn-rtc-e-inc fn-rtc-e-data)
                                  (fn-rtc-step fn-rtc-rearm fn-rtc-deliver fn-rtc-end-use fn-rtc-find-use fn-rtc-key
                                   fn-rtc-acts-on-p fn-rtc-invp fn-rtc-delivered-outcome fn-rtc-opened-step-is
                                   fn-rtc-slot fn-rtc-config fn-rtc-nstatic fn-rtc-current-p fn-rtc-invp-is-core-and-admission fn-rtc-core-invp
                                   fn-rtc-opened-acting-facts fn-rtc-opened-delivers-done fn-rtc-opened-acts-facts))
           :use (fn-rtc-opened-step-is fn-rtc-opened-acting-facts fn-rtc-opened-delivers-done fn-rtc-opened-acts-facts)))))

(local (defthm fn-rtc-end-use-len-mstates
  (implies (fn-rtc-invp s)
           (equal (len (fn-rtc-mstates (fn-rtc-end-use s e))) (fn-rtc-nslots (fn-rtc-config s))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-invp-is-core-and-admission))
           :use ((:instance fn-rtc-end-use-preserves-core-invp)
                 (:instance fn-rtc-core-invp-shape (s (fn-rtc-end-use s e)))
                 (:instance fn-rtc-end-use-config))))))

(defthm fn-rtc-opened-steps-its-slot
  (implies (and (fn-rtc-invp s) (fn-rtc-acts-on-p s e) (eq (fn-rtc-get 0 e) :opened)
                (equal (fn-rtc-get 4 e) '(:done 0))
                (natp j) (< j (fn-rtc-nslots (fn-rtc-config s))))
           (equal (fn-rtc-mstate j (mv-nth 0 (fn-rtc-step s e q)))
                  (if (equal j (fn-rtc-get 1 e))
                      (mv-nth 0 (fn-rtc-m-step (fn-rtc-mstate j s)
                                               (list :opened '(:done 0) j 1 (fn-rtc-get 5 e))
                                               (fn-rtc-make (fn-rtc-config s) nil (fn-rtc-view j 1 s) nil nil 0)
                                               (nfix q)))
                    (fn-rtc-mstate j s))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-ev)
                                  (fn-rtc-step fn-rtc-rearm fn-rtc-deliver fn-rtc-end-use fn-rtc-find-use fn-rtc-key
                                   fn-rtc-acts-on-p fn-rtc-invp fn-rtc-invp-is-core-and-admission fn-rtc-core-invp
                                   fn-rtc-view fn-rtc-mstate fn-rtc-make fn-rtc-config fn-rtc-nslots fn-rtc-slot
                                   fn-rtc-opened-step-simplified fn-rtc-opened-acting-facts fn-rtc-opened-view-of-end-use
                                   fn-rtc-mstate-of-deliver fn-rtc-rearm-frame fn-rtc-mstate-of-end-use fn-rtc-end-use-config
                                   fn-rtc-end-use-len-mstates))
           :use (fn-rtc-opened-step-simplified fn-rtc-opened-acting-facts
                 (:instance fn-rtc-rearm-frame (j j)
                            (s (mv-nth 0 (fn-rtc-deliver (fn-rtc-end-use s e) (fn-rtc-get 1 e) 1
                                          (list :opened '(:done 0) (fn-rtc-get 1 e) 1 (fn-rtc-get 5 e)) q))))
                 (:instance fn-rtc-mstate-of-deliver (s (fn-rtc-end-use s e)) (id (fn-rtc-get 1 e)) (inc 1)
                            (ev (list :opened '(:done 0) (fn-rtc-get 1 e) 1 (fn-rtc-get 5 e))))
                 (:instance fn-rtc-mstate-of-end-use (j j))
                 (:instance fn-rtc-mstate-of-end-use (j (fn-rtc-get 1 e)))
                 (:instance fn-rtc-opened-view-of-end-use (id (fn-rtc-get 1 e)) (inc 1))
                 (:instance fn-rtc-opened-view-of-end-use (id j) (inc 1))
                 (:instance fn-rtc-end-use-len-mstates)))))

(local (defthm fn-rtc-find-use-cons-other-kind
  (implies (not (equal (fn-rtc-get 0 u) (fn-rtc-get 0 k)))
           (equal (fn-rtc-find-use k (cons u uses)) (fn-rtc-find-use k uses)))
  :hints (("Goal" :expand ((fn-rtc-find-use k (cons u uses)))
           :in-theory (e/d (fn-rtc-key) (fn-rtc-find-use))))))

(local (defthm fn-rtc-machine-kind-not-opened
  (implies (member-equal kind *fn-rtc-machine-kinds*) (not (equal kind :opened)))))

(local (defthm fn-rtc-request-keeps-opened-uses
  (implies (equal (fn-rtc-get 0 k) :opened)
           (equal (fn-rtc-find-use k (fn-rtc-uses (mv-nth 0 (fn-rtc-request r id inc s))))
                  (fn-rtc-find-use k (fn-rtc-uses s))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-request fn-rtc-req-acquire fn-rtc-req-write fn-rtc-req-release
                                   fn-rtc-req-close fn-rtc-req-cancel fn-rtc-req-submit fn-rtc-buffered-kind-p)
                                  (fn-rtc-b-gen fn-rtc-b-bytes fn-rtc-h-buf fn-rtc-h-gen fn-rtc-h-off fn-rtc-h-len fn-rtc-s-res fn-rtc-s-inc fn-rtc-slot fn-rtc-next-op fn-rtc-use-bound fn-rtc-submit-okp fn-rtc-kind-out-p fn-rtc-live-p fn-rtc-current-p fn-rtc-extrap fn-rtc-kind-extrap member-equal fn-rtc-kind-op fn-rtc-splice
                                   fn-rtc-find-use))))))

(local (defthm fn-rtc-requests-keep-opened-uses
  (implies (equal (fn-rtc-get 0 k) :opened)
           (equal (fn-rtc-find-use k (fn-rtc-uses (mv-nth 0 (fn-rtc-requests reqs id inc s))))
                  (fn-rtc-find-use k (fn-rtc-uses s))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-requests) (mv-nth fn-rtc-request fn-rtc-find-use))
           :induct (fn-rtc-requests reqs id inc s)))))

(local (defthm fn-rtc-deliver-keeps-opened-uses
  (implies (equal (fn-rtc-get 0 k) :opened)
           (equal (fn-rtc-find-use k (fn-rtc-uses (mv-nth 0 (fn-rtc-deliver s id inc ev q))))
                  (fn-rtc-find-use k (fn-rtc-uses s))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-deliver) (fn-rtc-requests mv-nth fn-rtc-find-use))))))

(local (defthm fn-rtc-rearm-keeps-opened-uses
  (implies (equal (fn-rtc-get 0 k) :opened)
           (equal (fn-rtc-find-use k (fn-rtc-uses (mv-nth 0 (fn-rtc-rearm s))))
                  (fn-rtc-find-use k (fn-rtc-uses s))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-rearm fn-rtc-arm-accept fn-rtc-arm-grant)
                                  (fn-rtc-free-slot fn-rtc-free-pool-buf fn-rtc-oldest-wait fn-rtc-find-use fn-rtc-kind-out-p fn-rtc-issue))))))

(local (defun fn-rtc-opened-ev (s e)
  (declare (xargs :guard t))
  (let ((out (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e)))
    (fn-rtc-ev :opened out (fn-rtc-e-id e) (fn-rtc-e-inc e)
               (if (eq (fn-rtc-get 0 out) :done) (list (fn-rtc-e-data e)) nil)))))

(local (defthm fn-rtc-opened-step-is-ev
  (implies (and (fn-rtc-acts-on-p s e) (eq (fn-rtc-get 0 e) :opened))
           (equal (mv-nth 0 (fn-rtc-step s e q))
                  (mv-nth 0 (fn-rtc-rearm
                              (mv-nth 0 (fn-rtc-deliver (fn-rtc-end-use s e) (fn-rtc-e-id e) (fn-rtc-e-inc e)
                                          (fn-rtc-opened-ev s e) q))))))
  :hints (("Goal" :use fn-rtc-opened-step-is
           :in-theory (e/d (fn-rtc-opened-ev) (fn-rtc-opened-step-is fn-rtc-step fn-rtc-rearm fn-rtc-deliver fn-rtc-end-use
                                               fn-rtc-acts-on-p fn-rtc-ev fn-rtc-delivered-outcome fn-rtc-find-use fn-rtc-key))))))

(local (defthm fn-rtc-opened-end-use-removes-key
  (implies (and (fn-rtc-invp s) (fn-rtc-acts-on-p s e) (eq (fn-rtc-get 0 e) :opened))
           (not (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses (fn-rtc-end-use s e)))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-ends-use-p))
           :use (fn-rtc-opened-acts-facts
                 (:instance fn-rtc-completion-ends-its-use (u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))))
                 (:instance fn-rtc-key-of-find-use (k (fn-rtc-key e)) (uses (fn-rtc-uses s)))
                 (:instance fn-rtc-member-of-find-use (k (fn-rtc-key e)) (uses (fn-rtc-uses s))))))))

(local (defthm fn-rtc-opened-ends-its-use
  (implies (and (fn-rtc-invp s) (fn-rtc-acts-on-p s e) (eq (fn-rtc-get 0 e) :opened))
           (not (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses (mv-nth 0 (fn-rtc-step s e q))))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use (fn-rtc-opened-step-is-ev fn-rtc-opened-end-use-removes-key
                 (:instance fn-rtc-rearm-keeps-opened-uses (k (fn-rtc-key e))
                            (s (mv-nth 0 (fn-rtc-deliver (fn-rtc-end-use s e) (fn-rtc-e-id e) (fn-rtc-e-inc e) (fn-rtc-opened-ev s e) q))))
                 (:instance fn-rtc-deliver-keeps-opened-uses (k (fn-rtc-key e)) (s (fn-rtc-end-use s e)) (id (fn-rtc-e-id e)) (inc (fn-rtc-e-inc e))
                            (ev (fn-rtc-opened-ev s e)))
                 fn-rtc-key-get-0)))))

(defthm fn-rtc-opened-acts-at-most-once
  (implies (and (fn-rtc-invp s) (fn-rtc-acts-on-p s e) (eq (fn-rtc-get 0 e) :opened))
           (and (equal (mv-nth 0 (fn-rtc-step (mv-nth 0 (fn-rtc-step s e q)) e q))
                       (mv-nth 0 (fn-rtc-step s e q)))
                (null (mv-nth 1 (fn-rtc-step (mv-nth 0 (fn-rtc-step s e q)) e q)))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use (fn-rtc-opened-ends-its-use
                 (:instance fn-rtc-step-preserves-invp)
                 (:instance fn-rtc-unmatched-completion-is-discarded (s (mv-nth 0 (fn-rtc-step s e q))))))))

(defthm fn-rtc-machine-cannot-request-the-opened
  (implies (and (member-eq (fn-rtc-get 0 r) '(:submit :cancel))
                (eq (fn-rtc-get 1 r) :opened))
           (and (equal (mv-nth 0 (fn-rtc-request r id inc s)) s)
                (null (mv-nth 1 (fn-rtc-request r id inc s)))
                (equal (mv-nth 2 (fn-rtc-request r id inc s)) (list r))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-request fn-rtc-req-submit fn-rtc-req-cancel)
                                  (fn-rtc-live-p fn-rtc-kind-out-p fn-rtc-current-p fn-rtc-use-bound fn-rtc-config fn-rtc-hand-target-okp)))))

(local (defthm fn-rtc-actions-of-arm-opened
  (implies (and (natp j) (natp i))
           (iff (fn-rtc-kind-out-p :opened j 1 (mv-nth 1 (fn-rtc-arm-opened i n s)))
                (and (<= i j) (< j (+ i (nfix n))))))
  :hints (("Goal" :induct (fn-rtc-arm-opened i n s)
           :in-theory (e/d (fn-rtc-arm-opened fn-rtc-kind-out-cons) (fn-rtc-kind-out-p fn-rtc-issue))))))

(local (defthm fn-rtc-opened-out-of-rearm-actions
  (not (fn-rtc-kind-out-p :opened j inc (mv-nth 1 (fn-rtc-rearm s))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-rearm fn-rtc-arm-accept fn-rtc-arm-grant fn-rtc-kind-out-cons)
                                  (fn-rtc-kind-out-p fn-rtc-free-slot fn-rtc-free-pool-buf fn-rtc-oldest-wait fn-rtc-issue))))))

(local (defthm fn-rtc-kind-out-of-append
  (iff (fn-rtc-kind-out-p k i n (append a b))
       (or (fn-rtc-kind-out-p k i n a) (fn-rtc-kind-out-p k i n b)))
  :hints (("Goal" :in-theory (enable fn-rtc-kind-out-p)))))

(defthm fn-rtc-init-emits-the-opened
  (implies (and (fn-rtc-configp cfg) (natp j) (< j (fn-rtc-nslots cfg)))
           (iff (fn-rtc-kind-out-p :opened j 1 (mv-nth 1 (fn-rtc-init cfg)))
                (and (<= 1 j) (<= j (fn-rtc-nstatic cfg)))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-init-is-base)
                                  (fn-rtc-rearm fn-rtc-arm-opened fn-rtc-init-base fn-rtc-init mv-nth fn-rtc-kind-out-p))
           :use ((:instance fn-rtc-actions-of-arm-opened (i 1) (n (fn-rtc-nstatic cfg)) (s (fn-rtc-init-base cfg)))
                 (:instance fn-rtc-opened-out-of-rearm-actions (inc 1) (s (mv-nth 0 (fn-rtc-arm-opened 1 (fn-rtc-nstatic cfg) (fn-rtc-init-base cfg)))))))))

(local (defthm fn-rtc-uses-of-with-mstate-eq (equal (fn-rtc-uses (fn-rtc-with-mstate id m s)) (fn-rtc-uses s))
  :hints (("Goal" :in-theory (enable fn-rtc-with-mstate fn-rtc-make fn-rtc-uses)))))

(local (defthm fn-rtc-uses-of-with-slot-eq (equal (fn-rtc-uses (fn-rtc-with-slot id m s)) (fn-rtc-uses s))
  :hints (("Goal" :in-theory (enable fn-rtc-with-slot fn-rtc-make fn-rtc-uses)))))

(local (defthm fn-rtc-uses-of-with-buffer-eq (equal (fn-rtc-uses (fn-rtc-with-buffer h b s)) (fn-rtc-uses s))
  :hints (("Goal" :in-theory (enable fn-rtc-with-buffer fn-rtc-make fn-rtc-uses)))))

(local (defthm fn-rtc-uses-of-with-uses-eq (equal (fn-rtc-uses (fn-rtc-with-uses u s)) u)
  :hints (("Goal" :in-theory (enable fn-rtc-with-uses fn-rtc-make fn-rtc-uses)))))

(local (defthm fn-rtc-uses-of-make-eq (equal (fn-rtc-uses (fn-rtc-make c sl p u m n)) u)
  :hints (("Goal" :in-theory (enable fn-rtc-make fn-rtc-uses)))))

(local (defthm fn-rtc-opened-out-of-remove-use
  (implies (fn-rtc-kind-out-p :opened i n (fn-rtc-remove-use key uses))
           (fn-rtc-kind-out-p :opened i n uses))
  :hints (("Goal" :induct (fn-rtc-remove-use key uses)
           :in-theory (e/d (fn-rtc-remove-use fn-rtc-kind-out-cons) (fn-rtc-kind-out-p)))
          ("Subgoal *1/2" :expand ((fn-rtc-kind-out-p :opened i n uses)))
          ("Subgoal *1/1" :expand ((fn-rtc-kind-out-p :opened i n uses))))))

(local (defthm fn-rtc-opened-out-of-replace-use
  (implies (and (not (equal (fn-rtc-get 0 u2) :opened))
                (fn-rtc-kind-out-p :opened i n (fn-rtc-replace-use key u2 uses)))
           (fn-rtc-kind-out-p :opened i n uses))
  :hints (("Goal" :induct (fn-rtc-replace-use key u2 uses)
           :in-theory (e/d (fn-rtc-replace-use fn-rtc-kind-out-cons) (fn-rtc-kind-out-p)))
          ("Subgoal *1/2" :expand ((fn-rtc-kind-out-p :opened i n uses)))
          ("Subgoal *1/1" :expand ((fn-rtc-kind-out-p :opened i n uses))))))

(local (defthm fn-rtc-opened-out-of-request
  (implies (fn-rtc-kind-out-p :opened i n (fn-rtc-uses (mv-nth 0 (fn-rtc-request r id inc s))))
           (fn-rtc-kind-out-p :opened i n (fn-rtc-uses s)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-request fn-rtc-req-acquire fn-rtc-req-write fn-rtc-req-release
                                   fn-rtc-req-close fn-rtc-req-cancel fn-rtc-req-submit fn-rtc-buffered-kind-p
                                   fn-rtc-kind-out-cons)
                                  (fn-rtc-b-gen fn-rtc-b-bytes fn-rtc-h-buf fn-rtc-h-gen fn-rtc-h-off fn-rtc-h-len fn-rtc-s-res fn-rtc-s-inc fn-rtc-slot fn-rtc-next-op fn-rtc-use-bound fn-rtc-submit-okp fn-rtc-kind-out-p fn-rtc-live-p fn-rtc-current-p fn-rtc-extrap fn-rtc-kind-extrap member-equal fn-rtc-kind-op fn-rtc-splice))))))

(local (defthm fn-rtc-opened-out-of-requests
  (implies (fn-rtc-kind-out-p :opened i n (fn-rtc-uses (mv-nth 0 (fn-rtc-requests reqs id inc s))))
           (fn-rtc-kind-out-p :opened i n (fn-rtc-uses s)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-requests) (mv-nth fn-rtc-request fn-rtc-kind-out-p))
           :induct (fn-rtc-requests reqs id inc s)))))

(local (defthm fn-rtc-opened-out-of-deliver
  (implies (fn-rtc-kind-out-p :opened i n (fn-rtc-uses (mv-nth 0 (fn-rtc-deliver s id inc ev q))))
           (fn-rtc-kind-out-p :opened i n (fn-rtc-uses s)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-deliver) (fn-rtc-requests mv-nth fn-rtc-kind-out-p fn-rtc-opened-out-of-requests))
           :use ((:instance fn-rtc-opened-out-of-requests
                            (reqs (mv-nth 1 (fn-rtc-m-step (fn-rtc-mstate id s) ev
                                     (fn-rtc-make (fn-rtc-config s) nil (fn-rtc-view id inc s) nil nil 0) (nfix q))))
                            (s (fn-rtc-with-mstate id (mv-nth 0 (fn-rtc-m-step (fn-rtc-mstate id s) ev
                                     (fn-rtc-make (fn-rtc-config s) nil (fn-rtc-view id inc s) nil nil 0) (nfix q))) s))))))))

(local (defthm fn-rtc-opened-out-of-rearm-uses
  (implies (fn-rtc-kind-out-p :opened i n (fn-rtc-uses (mv-nth 0 (fn-rtc-rearm s))))
           (fn-rtc-kind-out-p :opened i n (fn-rtc-uses s)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-rearm fn-rtc-arm-accept fn-rtc-arm-grant fn-rtc-kind-out-cons)
                                  (fn-rtc-free-slot fn-rtc-free-pool-buf fn-rtc-oldest-wait fn-rtc-kind-out-p fn-rtc-issue))))))

(local (defthm fn-rtc-opened-out-of-end-use
  (implies (fn-rtc-kind-out-p :opened i n (fn-rtc-uses (fn-rtc-end-use s e)))
           (fn-rtc-kind-out-p :opened i n (fn-rtc-uses s)))
  :hints (("Goal" :in-theory (disable fn-rtc-kind-out-p fn-rtc-remove-use fn-rtc-find-use fn-rtc-key)
           :use (fn-rtc-uses-of-end-use (:instance fn-rtc-opened-out-of-remove-use (key (fn-rtc-key e)) (uses (fn-rtc-uses s))))))))

(local (defthm fn-rtc-opened-out-of-replace-pool-fwd
  (implies (fn-rtc-kind-out-p :opened i n (fn-rtc-replace-use key (cons :pool more) uses))
           (fn-rtc-kind-out-p :opened i n uses))
  :hints (("Goal" :use (:instance fn-rtc-opened-out-of-replace-use (u2 (cons :pool more)))
           :in-theory (disable fn-rtc-opened-out-of-replace-use)))
  :rule-classes :forward-chaining))

(local (defthm fn-rtc-opened-out-of-grant-one
  (implies (fn-rtc-kind-out-p :opened i n (fn-rtc-uses (mv-nth 0 (fn-rtc-grant-one s))))
           (fn-rtc-kind-out-p :opened i n (fn-rtc-uses s)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                               '(fn-rtc-grant-one mv-nth fn-rtc-uses-of-with-buffer-eq fn-rtc-uses-of-with-uses-eq
                                 fn-rtc-opened-out-of-replace-pool-fwd car-cons cdr-cons (:executable-counterpart consp)
                                 (:type-prescription fn-rtc-kind-out-p)))))
  :rule-classes :forward-chaining))

(local (defthm fn-rtc-opened-out-of-grant
  (implies (fn-rtc-kind-out-p :opened i n (fn-rtc-uses (mv-nth 0 (fn-rtc-grant k s))))
           (fn-rtc-kind-out-p :opened i n (fn-rtc-uses s)))
  :hints (("Goal" :induct (fn-rtc-grant k s)
           :in-theory (union-theories (theory 'minimal-theory)
                         '(fn-rtc-grant mv-nth fn-rtc-opened-out-of-grant-one (:type-prescription fn-rtc-kind-out-p)))
           ))))

(local (defthm fn-rtc-opened-out-of-rearm-fwd
  (implies (fn-rtc-kind-out-p :opened i n (fn-rtc-uses (mv-nth 0 (fn-rtc-rearm s))))
           (fn-rtc-kind-out-p :opened i n (fn-rtc-uses s)))
  :hints (("Goal" :by fn-rtc-opened-out-of-rearm-uses))
  :rule-classes :forward-chaining))

(local (defthm fn-rtc-opened-out-of-deliver-fwd
  (implies (fn-rtc-kind-out-p :opened i n (fn-rtc-uses (mv-nth 0 (fn-rtc-deliver s id inc ev q))))
           (fn-rtc-kind-out-p :opened i n (fn-rtc-uses s)))
  :hints (("Goal" :by fn-rtc-opened-out-of-deliver))
  :rule-classes :forward-chaining))

(local (defthm fn-rtc-opened-out-of-accept-branch
  (implies (fn-rtc-kind-out-p :opened i n (fn-rtc-uses (mv-nth 0 (fn-rtc-accept-branch s out q))))
           (fn-rtc-kind-out-p :opened i n (fn-rtc-uses s)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                               '(fn-rtc-accept-branch mv-nth fn-rtc-uses-of-with-mstate-eq fn-rtc-uses-of-with-slot-eq
                                 fn-rtc-opened-out-of-rearm
                                 (:type-prescription fn-rtc-kind-out-p) (:executable-counterpart consp) car-cons cdr-cons))
           :use ((:instance fn-rtc-opened-out-of-deliver
                            (s (fn-rtc-with-mstate (fn-rtc-free-slot 0 (fn-rtc-slots s)) (fn-rtc-m-init)
                                    (fn-rtc-with-slot (fn-rtc-free-slot 0 (fn-rtc-slots s))
                                       (list (+ 1 (fn-rtc-s-inc (fn-rtc-slot (fn-rtc-free-slot 0 (fn-rtc-slots s)) s))) :live (fn-rtc-get 1 out)) s)))
                            (id (fn-rtc-free-slot 0 (fn-rtc-slots s)))
                            (inc (+ 1 (fn-rtc-s-inc (fn-rtc-slot (fn-rtc-free-slot 0 (fn-rtc-slots s)) s))))
                            (ev (fn-rtc-ev :accept out (fn-rtc-free-slot 0 (fn-rtc-slots s))
                                             (+ 1 (fn-rtc-s-inc (fn-rtc-slot (fn-rtc-free-slot 0 (fn-rtc-slots s)) s))) nil))))))))

(local (defthm fn-rtc-opened-out-of-close-branch
  (implies (fn-rtc-kind-out-p :opened i n (fn-rtc-uses (mv-nth 0 (fn-rtc-close-branch s id inc))))
           (fn-rtc-kind-out-p :opened i n (fn-rtc-uses s)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                               '(fn-rtc-close-branch mv-nth fn-rtc-uses-of-with-mstate-eq fn-rtc-uses-of-with-slot-eq fn-rtc-uses-of-make-eq
                                 fn-rtc-opened-out-of-rearm (:type-prescription fn-rtc-kind-out-p) car-cons cdr-cons))))))

(local (defthm fn-rtc-no-opened-after-end-use
  (implies (not (fn-rtc-kind-out-p :opened i n (fn-rtc-uses s)))
           (not (fn-rtc-kind-out-p :opened i n (fn-rtc-uses (fn-rtc-end-use s e)))))
  :hints (("Goal" :use fn-rtc-opened-out-of-end-use :in-theory (theory 'minimal-theory)))))

(local (defthm fn-rtc-no-opened-after-rearm
  (implies (not (fn-rtc-kind-out-p :opened i n (fn-rtc-uses s)))
           (not (fn-rtc-kind-out-p :opened i n (fn-rtc-uses (mv-nth 0 (fn-rtc-rearm s))))))
  :hints (("Goal" :use fn-rtc-opened-out-of-rearm-uses :in-theory (theory 'minimal-theory)))))

(local (defthm fn-rtc-no-opened-after-deliver
  (implies (not (fn-rtc-kind-out-p :opened i n (fn-rtc-uses s)))
           (not (fn-rtc-kind-out-p :opened i n (fn-rtc-uses (mv-nth 0 (fn-rtc-deliver s id inc ev q))))))
  :hints (("Goal" :use fn-rtc-opened-out-of-deliver :in-theory (theory 'minimal-theory)))))

(local (defthm fn-rtc-no-opened-after-grant
  (implies (not (fn-rtc-kind-out-p :opened i n (fn-rtc-uses s)))
           (not (fn-rtc-kind-out-p :opened i n (fn-rtc-uses (mv-nth 0 (fn-rtc-grant k s))))))
  :hints (("Goal" :use fn-rtc-opened-out-of-grant :in-theory (theory 'minimal-theory)))))

(local (defthm fn-rtc-no-opened-after-accept-branch
  (implies (not (fn-rtc-kind-out-p :opened i n (fn-rtc-uses s)))
           (not (fn-rtc-kind-out-p :opened i n (fn-rtc-uses (mv-nth 0 (fn-rtc-accept-branch s out q))))))
  :hints (("Goal" :use fn-rtc-opened-out-of-accept-branch :in-theory (theory 'minimal-theory)))))

(local (defthm fn-rtc-no-opened-after-close-branch
  (implies (not (fn-rtc-kind-out-p :opened i n (fn-rtc-uses s)))
           (not (fn-rtc-kind-out-p :opened i n (fn-rtc-uses (mv-nth 0 (fn-rtc-close-branch s id inc))))))
  :hints (("Goal" :use fn-rtc-opened-out-of-close-branch :in-theory (theory 'minimal-theory)))))

(local (defthm fn-rtc-absent-opened-stays-absent
  (implies (not (fn-rtc-kind-out-p :opened i n (fn-rtc-uses s)))
           (not (fn-rtc-kind-out-p :opened i n (fn-rtc-uses (mv-nth 0 (fn-rtc-step s e q))))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                               '(fn-rtc-step-is-step-state fn-rtc-step-state mv-nth
                                 fn-rtc-no-opened-after-end-use fn-rtc-no-opened-after-rearm fn-rtc-no-opened-after-deliver
                                 fn-rtc-no-opened-after-grant fn-rtc-no-opened-after-accept-branch fn-rtc-no-opened-after-close-branch
                                 (:type-prescription fn-rtc-kind-out-p) car-cons cdr-cons (:executable-counterpart consp)))))))

(local (defthm fn-rtc-find-use-implies-kind-out
  (implies (and (fn-rtc-find-use key uses) (consp key))
           (fn-rtc-kind-out-p (fn-rtc-get 0 key) (fn-rtc-get 1 key) (fn-rtc-get 2 key) uses))
  :hints (("Goal" :induct (fn-rtc-find-use key uses)
           :in-theory (e/d (fn-rtc-find-use fn-rtc-kind-out-p fn-rtc-key) ())))))

(local (defthm fn-rtc-remove-use-clears-opened-kind
  (implies (and (fn-rtc-uses-okp uses s) (fn-rtc-find-use key uses) (equal (fn-rtc-get 0 key) :opened))
           (not (fn-rtc-kind-out-p :opened (fn-rtc-get 1 key) (fn-rtc-get 2 key) (fn-rtc-remove-use key uses))))
  :hints (("Goal" :induct (fn-rtc-remove-use key uses)
           :in-theory (e/d (fn-rtc-remove-use fn-rtc-kind-out-p fn-rtc-uses-okp fn-rtc-find-use fn-rtc-key)
                           (fn-rtc-use-okp fn-rtc-op-used-p)))
          ("Subgoal *1/2'" :use ((:instance fn-rtc-find-use-implies-kind-out (uses (cdr uses))))))))

(local (defthm fn-rtc-key-get-1 (equal (fn-rtc-get 1 (fn-rtc-key e)) (fn-rtc-get 1 e)) :hints (("Goal" :in-theory (enable fn-rtc-key)))))

(local (defthm fn-rtc-key-get-2 (equal (fn-rtc-get 2 (fn-rtc-key e)) (fn-rtc-get 2 e)) :hints (("Goal" :in-theory (enable fn-rtc-key)))))

(local (defthm fn-rtc-opened-absent-after-end-use
  (implies (and (fn-rtc-invp s) (fn-rtc-acts-on-p s e) (eq (fn-rtc-get 0 e) :opened))
           (not (fn-rtc-kind-out-p :opened (fn-rtc-get 1 e) (fn-rtc-get 2 e) (fn-rtc-uses (fn-rtc-end-use s e)))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                               '(fn-rtc-key-get-0 fn-rtc-key-get-1 fn-rtc-key-get-2 (:type-prescription fn-rtc-kind-out-p) fn-rtc-uses-of-end-use))
           :use (fn-rtc-opened-acts-facts fn-rtc-invp-uses-okp
                 (:instance fn-rtc-remove-use-clears-opened-kind (key (fn-rtc-key e)) (uses (fn-rtc-uses s)))
                 (:instance fn-rtc-key-parts-of-find-use (uses (fn-rtc-uses s))))))))

(local (defthm fn-rtc-opened-absent-after-acting-step
  (implies (and (fn-rtc-invp s) (fn-rtc-acts-on-p s e) (eq (fn-rtc-get 0 e) :opened))
           (not (fn-rtc-kind-out-p :opened (fn-rtc-get 1 e) (fn-rtc-get 2 e)
                                   (fn-rtc-uses (mv-nth 0 (fn-rtc-step s e q))))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                               '(fn-rtc-opened-step-is-ev fn-rtc-no-opened-after-rearm fn-rtc-no-opened-after-deliver
                                 fn-rtc-opened-absent-after-end-use (:type-prescription fn-rtc-kind-out-p)))))))

(local (defthm fn-rtc-absent-opened-stays-absent-run
  (implies (not (fn-rtc-kind-out-p :opened i n (fn-rtc-uses s)))
           (not (fn-rtc-kind-out-p :opened i n (fn-rtc-uses (fn-rtc-run s events q)))))
  :hints (("Goal" :induct (fn-rtc-run s events q)
           :in-theory (union-theories (theory 'minimal-theory)
                         '(fn-rtc-run mv-nth (:type-prescription fn-rtc-kind-out-p)
                           fn-rtc-absent-opened-stays-absent))))))

(local (defthm fn-rtc-key-consp (consp (fn-rtc-key e)) :hints (("Goal" :in-theory (enable fn-rtc-key)))))

(local (defthm fn-rtc-acts-opened-needs-kind-out
  (implies (and (fn-rtc-acts-on-p s e2) (eq (fn-rtc-get 0 e2) :opened))
           (fn-rtc-kind-out-p :opened (fn-rtc-get 1 e2) (fn-rtc-get 2 e2) (fn-rtc-uses s)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                               '(fn-rtc-key-get-0 fn-rtc-key-get-1 fn-rtc-key-get-2 fn-rtc-key-consp (:type-prescription fn-rtc-kind-out-p)))
           :use ((:instance fn-rtc-opened-acts-facts (e e2))
                 (:instance fn-rtc-find-use-implies-kind-out (key (fn-rtc-key e2)) (uses (fn-rtc-uses s))))))))

(defthm fn-rtc-opened-acts-once-per-incarnation
  (implies (and (fn-rtc-invp s) (fn-rtc-acts-on-p s e) (eq (fn-rtc-get 0 e) :opened)
                (eq (fn-rtc-get 0 e2) :opened)
                (equal (fn-rtc-get 1 e2) (fn-rtc-get 1 e))
                (equal (fn-rtc-get 2 e2) (fn-rtc-get 2 e)))
           (not (fn-rtc-acts-on-p (fn-rtc-run (mv-nth 0 (fn-rtc-step s e q)) events q2) e2)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '((:type-prescription fn-rtc-kind-out-p)))
           :use (fn-rtc-opened-absent-after-acting-step
                 (:instance fn-rtc-absent-opened-stays-absent-run (s (mv-nth 0 (fn-rtc-step s e q)))
                            (i (fn-rtc-get 1 e)) (n (fn-rtc-get 2 e)) (q q2))
                 (:instance fn-rtc-acts-opened-needs-kind-out (s (fn-rtc-run (mv-nth 0 (fn-rtc-step s e q)) events q2)))))))
