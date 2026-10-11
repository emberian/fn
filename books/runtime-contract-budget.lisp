; fn: the runtime contract's T12: the work budget, the action count and the retained output of one step.
;
; Part of the runtime contract (books/runtime-contract.lisp states it and its
; statements; this book carries the proofs named below).  Split from that book
; so each certifies under the per-book time limit.

(in-package "ACL2")
(include-book "runtime-contract-actions")
(include-book "runtime-contract-invariant")

(local (in-theory (disable fn-rtc-buf-cap fn-rtc-home fn-rtc-hand-target-okp)))

; The work budget.
(defun fn-rtc-req-octets (r)
  (declare (xargs :guard t))
  (if (eq (fn-rtc-get 0 r) :write) (len (fn-rtc-get 4 r)) 0))

(defthm fn-rtc-reqs-octets-def
  (equal (fn-rtc-reqs-octets reqs)
         (if (consp reqs) (+ (fn-rtc-req-octets (car reqs)) (fn-rtc-reqs-octets (cdr reqs))) 0))
  :rule-classes :definition)

(defun fn-rtc-pool-bytes-okp (pool cap)
  (declare (xargs :guard (natp cap)))
  (if (consp pool)
      (and (fn-cbor-octet-listp (fn-rtc-b-bytes (car pool)))
           (<= (len (fn-rtc-b-bytes (car pool))) cap)
           (fn-rtc-pool-bytes-okp (cdr pool) cap))
    t))

(defthm fn-rtc-pool-bytes-okp-get
  (implies (and (fn-rtc-pool-bytes-okp pool cap) (natp cap))
           (and (fn-cbor-octet-listp (fn-rtc-b-bytes (fn-rtc-get h pool)))
                (<= (len (fn-rtc-b-bytes (fn-rtc-get h pool))) cap)))
  :hints (("Goal" :induct (fn-rtc-get h pool)
           :in-theory (disable fn-rtc-b-bytes fn-cbor-octet-listp))))

(defthm fn-rtc-pool-bytes-okp-set
  (implies (and (fn-rtc-pool-bytes-okp pool cap)
                (fn-cbor-octet-listp (fn-rtc-b-bytes b))
                (<= (len (fn-rtc-b-bytes b)) cap))
           (fn-rtc-pool-bytes-okp (fn-rtc-set h b pool) cap))
  :hints (("Goal" :induct (fn-rtc-set h b pool)
           :in-theory (disable fn-rtc-b-bytes fn-cbor-octet-listp))))

(defthm fn-rtc-bounded-pool-buffer-bytes
  (implies (fn-rtc-pool-bytes-okp (fn-rtc-pool s) (fn-rtc-cap (fn-rtc-config s)))
           (and (fn-cbor-octet-listp (fn-rtc-b-bytes (fn-rtc-buffer h s)))
                (<= (len (fn-rtc-b-bytes (fn-rtc-buffer h s)))
                    (fn-rtc-cap (fn-rtc-config s)))))
  :hints (("Goal" :in-theory (disable fn-rtc-pool-bytes-okp fn-rtc-b-bytes
                                      fn-cbor-octet-listp fn-rtc-cap)
           :use ((:instance fn-rtc-pool-bytes-okp-get
                   (pool (fn-rtc-pool s)) (cap (fn-rtc-cap (fn-rtc-config s))))))))

(defthm fn-rtc-pool-bytes-okp-splice
  (implies (and (fn-rtc-pool-bytes-okp pool cap)
                (fn-cbor-octet-listp bytes) (<= (len bytes) cap)
                (fn-cbor-octet-listp data) (natp off) (<= off (len bytes))
                (<= (+ off (len data)) cap))
           (fn-rtc-pool-bytes-okp (fn-rtc-set h (list g o (fn-rtc-splice bytes off data)) pool) cap))
  :hints (("Goal" :use (fn-rtc-splice-length fn-rtc-splice-octets
                        (:instance fn-rtc-pool-bytes-okp-set (b (list g o (fn-rtc-splice bytes off data)))))
           :in-theory
           (e/d (fn-cbor-octet-listp-implies-true-listp)
                (fn-rtc-pool-bytes-okp fn-rtc-splice fn-cbor-octet-listp
                 fn-rtc-pool-bytes-okp-set fn-rtc-splice-length fn-rtc-splice-octets)))))

(defthm fn-rtc-request-preserves-pool-bytes
  (implies (fn-rtc-pool-bytes-okp (fn-rtc-pool s) (fn-rtc-cap (fn-rtc-config s)))
           (fn-rtc-pool-bytes-okp
             (fn-rtc-pool (mv-nth 0 (fn-rtc-request r id inc s)))
             (fn-rtc-cap (fn-rtc-config s))))
  :hints (("Goal" :in-theory
           (e/d (fn-cbor-octet-listp-implies-true-listp fn-rtc-splice-octets fn-rtc-splice-length
                 fn-rtc-request fn-rtc-req-acquire fn-rtc-req-write fn-rtc-req-release
                 fn-rtc-req-close fn-rtc-req-cancel fn-rtc-req-submit)
                (fn-rtc-pool-bytes-okp fn-rtc-bounded-pool-buffer-bytes fn-rtc-b-gen fn-rtc-b-owner fn-rtc-b-bytes
                 fn-rtc-h-buf fn-rtc-h-gen fn-rtc-h-off fn-rtc-h-len fn-rtc-s-res fn-rtc-s-inc
                 fn-rtc-slot fn-rtc-next-op fn-rtc-use-bound fn-rtc-submit-okp
                 fn-rtc-kind-out-p fn-rtc-live-p fn-rtc-current-p fn-rtc-extrap
                 fn-rtc-buffered-kind-p member-equal fn-rtc-kind-op fn-rtc-splice
                 fn-cbor-octet-listp fn-rtc-cap fn-rtc-nbufs fn-rtc-nstatic))
           :use ((:instance fn-rtc-bounded-pool-buffer-bytes (h (fn-rtc-get 1 r)))
                 (:instance fn-rtc-bounded-pool-buffer-bytes
                   (h (fn-rtc-h-buf (fn-rtc-get 2 r))))))))

(defthm fn-rtc-submit-okp-within-bounded-cap
  (implies (and (fn-rtc-pool-bytes-okp (fn-rtc-pool s) (fn-rtc-cap (fn-rtc-config s)))
                (fn-rtc-submit-okp kind hd id inc s))
           (<= (fn-rtc-h-len hd) (fn-rtc-cap (fn-rtc-config s))))
  :hints (("Goal" :use ((:instance fn-rtc-bounded-pool-buffer-bytes (h (fn-rtc-h-buf hd))))
           :in-theory (disable fn-rtc-pool-bytes-okp fn-rtc-bounded-pool-buffer-bytes
                               fn-rtc-b-bytes fn-cbor-octet-listp)))
  :rule-classes :linear)

(local (in-theory (disable fn-rtc-cap fn-rtc-pool-bytes-okp)))

(defun fn-rtc-act-octets (a)
  (declare (xargs :guard t))
  (let ((hd (fn-rtc-get 0 (fn-rtc-get 4 a))))
    (if (and (fn-rtc-buffered-kind-p (fn-rtc-get 0 a)) (fn-rtc-handlep hd)) (fn-rtc-h-len hd) 0)))

(defthm fn-rtc-actions-octets-def
  (equal (fn-rtc-actions-octets acts)
         (if (consp acts) (+ (fn-rtc-act-octets (car acts)) (fn-rtc-actions-octets (cdr acts))) 0))
  :rule-classes :definition)

(defthm fn-rtc-actions-octets-append
  (equal (fn-rtc-actions-octets (append a b)) (+ (fn-rtc-actions-octets a) (fn-rtc-actions-octets b))))

(defthm fn-rtc-req-acquire-budget
  (let ((x (fn-rtc-req-acquire r id inc s)) (u (fn-rtc-use-bound (fn-rtc-config s))))
   (implies (equal (fn-rtc-get 0 r) :acquire)
    (and (<= (mv-nth 3 x) (+ 1 u (fn-rtc-req-octets r)))
         (<= (len (mv-nth 1 x)) 1)
         (<= (fn-rtc-actions-octets (mv-nth 1 x)) (fn-rtc-cap (fn-rtc-config s)))
         (equal (fn-rtc-config (mv-nth 0 x)) (fn-rtc-config s)))))
  :hints (("Goal" :in-theory (disable fn-rtc-b-bytes fn-rtc-h-buf fn-rtc-h-gen fn-rtc-h-off fn-rtc-s-inc fn-rtc-buffered-kind-p fn-rtc-b-gen fn-rtc-splice fn-rtc-b-owner fn-rtc-nbufs fn-cbor-octet-listp fn-rtc-buffer fn-rtc-live-p fn-rtc-current-p fn-rtc-slot fn-rtc-s-res fn-rtc-extrap fn-rtc-kind-out-p fn-rtc-kind-op member-equal fn-rtc-next-op))))

(defthm fn-rtc-req-write-budget
  (let ((x (fn-rtc-req-write r id inc s)) (u (fn-rtc-use-bound (fn-rtc-config s))))
   (implies (equal (fn-rtc-get 0 r) :write)
    (and (<= (mv-nth 3 x) (+ 1 u (fn-rtc-req-octets r)))
         (<= (len (mv-nth 1 x)) 1)
         (<= (fn-rtc-actions-octets (mv-nth 1 x)) (fn-rtc-cap (fn-rtc-config s)))
         (equal (fn-rtc-config (mv-nth 0 x)) (fn-rtc-config s)))))
  :hints (("Goal" :in-theory (disable fn-rtc-b-bytes fn-rtc-h-buf fn-rtc-h-gen fn-rtc-h-off fn-rtc-s-inc fn-rtc-buffered-kind-p fn-rtc-b-gen fn-rtc-splice fn-rtc-b-owner fn-rtc-nbufs fn-cbor-octet-listp fn-rtc-buffer fn-rtc-live-p fn-rtc-current-p fn-rtc-slot fn-rtc-s-res fn-rtc-extrap fn-rtc-kind-out-p fn-rtc-kind-op member-equal fn-rtc-next-op))))

(defthm fn-rtc-req-release-budget
  (let ((x (fn-rtc-req-release r id inc s)) (u (fn-rtc-use-bound (fn-rtc-config s))))
   (implies (equal (fn-rtc-get 0 r) :release)
    (and (<= (mv-nth 3 x) (+ 1 u (fn-rtc-req-octets r)))
         (<= (len (mv-nth 1 x)) 1)
         (<= (fn-rtc-actions-octets (mv-nth 1 x)) (fn-rtc-cap (fn-rtc-config s)))
         (equal (fn-rtc-config (mv-nth 0 x)) (fn-rtc-config s)))))
  :hints (("Goal" :in-theory (disable fn-rtc-b-bytes fn-rtc-h-buf fn-rtc-h-gen fn-rtc-h-off fn-rtc-s-inc fn-rtc-buffered-kind-p fn-rtc-b-gen fn-rtc-splice fn-rtc-b-owner fn-rtc-nbufs fn-cbor-octet-listp fn-rtc-buffer fn-rtc-live-p fn-rtc-current-p fn-rtc-slot fn-rtc-s-res fn-rtc-extrap fn-rtc-kind-out-p fn-rtc-kind-op member-equal fn-rtc-next-op))))

(defthm fn-rtc-req-close-budget
  (let ((x (fn-rtc-req-close r id inc s)) (u (fn-rtc-use-bound (fn-rtc-config s))))
   (implies (equal (fn-rtc-get 0 r) :close)
    (and (<= (mv-nth 3 x) (+ 1 u (fn-rtc-req-octets r)))
         (<= (len (mv-nth 1 x)) 1)
         (<= (fn-rtc-actions-octets (mv-nth 1 x)) (fn-rtc-cap (fn-rtc-config s)))
         (equal (fn-rtc-config (mv-nth 0 x)) (fn-rtc-config s)))))
  :hints (("Goal" :in-theory (disable fn-rtc-b-bytes fn-rtc-h-buf fn-rtc-h-gen fn-rtc-h-off fn-rtc-s-inc fn-rtc-buffered-kind-p fn-rtc-b-gen fn-rtc-splice fn-rtc-b-owner fn-rtc-nbufs fn-cbor-octet-listp fn-rtc-buffer fn-rtc-live-p fn-rtc-current-p fn-rtc-slot fn-rtc-s-res fn-rtc-extrap fn-rtc-kind-out-p fn-rtc-kind-op member-equal fn-rtc-next-op))))

(defthm fn-rtc-req-cancel-budget
  (let ((x (fn-rtc-req-cancel r id inc s)) (u (fn-rtc-use-bound (fn-rtc-config s))))
   (implies (equal (fn-rtc-get 0 r) :cancel)
    (and (<= (mv-nth 3 x) (+ 1 u (fn-rtc-req-octets r)))
         (<= (len (mv-nth 1 x)) 1)
         (<= (fn-rtc-actions-octets (mv-nth 1 x)) (fn-rtc-cap (fn-rtc-config s)))
         (equal (fn-rtc-config (mv-nth 0 x)) (fn-rtc-config s)))))
  :hints (("Goal" :in-theory (disable fn-rtc-b-bytes fn-rtc-h-buf fn-rtc-h-gen fn-rtc-h-off fn-rtc-s-inc fn-rtc-buffered-kind-p fn-rtc-b-gen fn-rtc-splice fn-rtc-b-owner fn-rtc-nbufs fn-cbor-octet-listp fn-rtc-buffer fn-rtc-live-p fn-rtc-current-p fn-rtc-slot fn-rtc-s-res fn-rtc-extrap fn-rtc-kind-out-p fn-rtc-kind-op member-equal fn-rtc-next-op))))

(defthm fn-rtc-req-submit-budget
  (implies (fn-rtc-pool-bytes-okp (fn-rtc-pool s) (fn-rtc-cap (fn-rtc-config s)))
    (let ((x (fn-rtc-req-submit r id inc s)) (u (fn-rtc-use-bound (fn-rtc-config s))))
   (implies (equal (fn-rtc-get 0 r) :submit)
    (and (<= (mv-nth 3 x) (+ 1 u (fn-rtc-req-octets r)))
         (<= (len (mv-nth 1 x)) 1)
         (<= (fn-rtc-actions-octets (mv-nth 1 x)) (fn-rtc-cap (fn-rtc-config s)))
         (equal (fn-rtc-config (mv-nth 0 x)) (fn-rtc-config s))))))
  :hints (("Goal" :in-theory (disable fn-rtc-b-gen fn-rtc-b-bytes fn-rtc-h-buf fn-rtc-h-gen fn-rtc-h-off fn-rtc-h-len fn-rtc-s-res fn-rtc-s-inc fn-rtc-slot fn-rtc-next-op fn-rtc-use-bound fn-rtc-submit-okp fn-rtc-kind-out-p fn-rtc-live-p fn-rtc-current-p fn-rtc-extrap fn-rtc-buffered-kind-p member-equal fn-rtc-kind-op fn-rtc-b-bytes fn-rtc-h-buf fn-rtc-h-gen fn-rtc-h-off fn-rtc-s-inc fn-rtc-buffered-kind-p fn-rtc-b-gen fn-rtc-splice fn-rtc-b-owner fn-rtc-nbufs fn-cbor-octet-listp fn-rtc-buffer fn-rtc-live-p fn-rtc-current-p fn-rtc-slot fn-rtc-s-res fn-rtc-extrap fn-rtc-kind-out-p fn-rtc-kind-op member-equal fn-rtc-next-op))))

(defthm fn-rtc-request-budget
  (implies (fn-rtc-pool-bytes-okp (fn-rtc-pool s) (fn-rtc-cap (fn-rtc-config s)))
    (let ((x (fn-rtc-request r id inc s)) (u (fn-rtc-use-bound (fn-rtc-config s))))
    (and (<= (mv-nth 3 x) (+ 1 u (fn-rtc-req-octets r)))
         (<= (len (mv-nth 1 x)) 1)
         (<= (fn-rtc-actions-octets (mv-nth 1 x)) (fn-rtc-cap (fn-rtc-config s)))
         (equal (fn-rtc-config (mv-nth 0 x)) (fn-rtc-config s)))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-request)
                                  (mv-nth fn-rtc-req-acquire fn-rtc-req-write fn-rtc-req-release fn-rtc-req-close
                                   fn-rtc-req-cancel fn-rtc-req-submit fn-rtc-req-octets fn-rtc-use-bound
                                   fn-rtc-actions-octets fn-rtc-cap)))))

(defthm fn-rtc-request-budget-linear
  (implies (fn-rtc-pool-bytes-okp (fn-rtc-pool s) (fn-rtc-cap (fn-rtc-config s)))
    (and (<= (mv-nth 3 (fn-rtc-request r id inc s))
           (+ 1 (fn-rtc-use-bound (fn-rtc-config s)) (fn-rtc-req-octets r)))
       (<= (len (mv-nth 1 (fn-rtc-request r id inc s))) 1)
       (<= (fn-rtc-actions-octets (mv-nth 1 (fn-rtc-request r id inc s))) (fn-rtc-cap (fn-rtc-config s)))))
  :rule-classes :linear
  :hints (("Goal" :use fn-rtc-request-budget :in-theory (disable fn-rtc-request-budget fn-rtc-request))))

(defthm fn-rtc-len-append (equal (len (append a b)) (+ (len a) (len b))))

(defthm fn-rtc-requests-budget
  (implies (fn-rtc-pool-bytes-okp (fn-rtc-pool s) (fn-rtc-cap (fn-rtc-config s)))
    (let ((x (fn-rtc-requests reqs id inc s)) (u (fn-rtc-use-bound (fn-rtc-config s))))
    (and (<= (mv-nth 3 x) (+ (* (len reqs) (+ 1 u)) (fn-rtc-reqs-octets reqs)))
         (<= (len (mv-nth 1 x)) (len reqs))
         (<= (fn-rtc-actions-octets (mv-nth 1 x)) (* (len reqs) (fn-rtc-cap (fn-rtc-config s))))
         (equal (fn-rtc-config (mv-nth 0 x)) (fn-rtc-config s)))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-requests)
                                  (mv-nth fn-rtc-request fn-rtc-req-octets fn-rtc-use-bound fn-rtc-actions-octets
                                   fn-rtc-cap))
           :induct (fn-rtc-requests reqs id inc s))
          ("Subgoal *1/1'" :nonlinearp t)))

(defthm fn-rtc-deliver-budget
  (implies (fn-rtc-pool-bytes-okp (fn-rtc-pool s) (fn-rtc-cap (fn-rtc-config s)))
    (implies (natp q)
           (let ((x (fn-rtc-deliver s id inc ev q)) (u (fn-rtc-use-bound (fn-rtc-config s))))
             (and (<= (mv-nth 3 x) (+ q (fn-rtc-m-c) (* (fn-rtc-m-max-reqs) (+ 1 u))))
                  (<= (len (mv-nth 1 x)) (fn-rtc-m-max-reqs))
                  (<= (fn-rtc-actions-octets (mv-nth 1 x)) (* (fn-rtc-m-max-reqs) (fn-rtc-cap (fn-rtc-config s))))))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-deliver)
                                  (fn-rtc-requests mv-nth fn-rtc-use-bound fn-rtc-actions-octets fn-rtc-cap
                                   fn-rtc-m-step-is-charged fn-rtc-m-step-requests-are-bounded fn-rtc-requests-budget))
           :use ((:instance fn-rtc-m-step-is-charged (m (fn-rtc-mstate id s)) (pool (fn-rtc-make (fn-rtc-config s) nil (fn-rtc-view id inc s) nil nil 0)))
                 (:instance fn-rtc-m-step-requests-are-bounded (m (fn-rtc-mstate id s))
                            (pool (fn-rtc-make (fn-rtc-config s) nil (fn-rtc-view id inc s) nil nil 0)) (q (nfix q)))
                 (:instance fn-rtc-requests-budget
                            (reqs (mv-nth 1 (fn-rtc-m-step (fn-rtc-mstate id s) ev (fn-rtc-make (fn-rtc-config s) nil (fn-rtc-view id inc s) nil nil 0) q)))
                            (s (fn-rtc-with-mstate id (mv-nth 0 (fn-rtc-m-step (fn-rtc-mstate id s) ev
                                                                                (fn-rtc-make (fn-rtc-config s) nil (fn-rtc-view id inc s) nil nil 0) q))
                                                   s))))
           :nonlinearp t)))

(defthm fn-rtc-rearm-budget
  (and (<= (len (mv-nth 1 (fn-rtc-rearm s))) 2)
       (equal (fn-rtc-actions-octets (mv-nth 1 (fn-rtc-rearm s))) 0))
  :hints (("Goal" :in-theory (e/d (fn-rtc-rearm) (fn-rtc-free-slot fn-rtc-kind-out-p)))))

(defun fn-rtc-step-cost-of (s e q)
  (declare (xargs :guard t))
  (mv-let (s2 a r c) (fn-rtc-step* s e q)
    (declare (ignore s2 a r)) c))

(defthm fn-rtc-step-cost-is
  (equal (fn-rtc-step-cost s e q) (fn-rtc-step-cost-of s e q))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory) '(fn-rtc-step-cost fn-rtc-step-cost-of)))))

(in-theory (disable fn-rtc-step-cost-of fn-rtc-step-cost))

(defthm fn-rtc-config-of-end-use
  (equal (fn-rtc-config (fn-rtc-end-use s e)) (fn-rtc-config s))
  :hints (("Goal" :in-theory (enable fn-rtc-end-use))))

(defthm fn-rtc-config-of-accept-prepared
  (equal (fn-rtc-config (fn-rtc-accept-prepared s1 out)) (fn-rtc-config s1)))

(defthm fn-rtc-accept-branch-cost-part
  (equal (mv-nth 3 (fn-rtc-accept-branch s1 out q))
         (if (fn-rtc-accept-go-p s1 out)
             (mv-nth 3 (fn-rtc-deliver (fn-rtc-accept-prepared s1 out) (fn-rtc-accept-slot s1)
                                       (fn-rtc-accept-inc s1) (fn-rtc-ev :accept out (fn-rtc-accept-slot s1) (fn-rtc-accept-inc s1) nil) q))
           0))
  :hints (("Goal" :in-theory (e/d (fn-rtc-accept-branch) (fn-rtc-deliver fn-rtc-rearm fn-rtc-free-slot)))))

(defthm fn-rtc-rearm-budget-linear
  (<= (len (mv-nth 1 (fn-rtc-rearm s))) 2)
  :rule-classes :linear
  :hints (("Goal" :use fn-rtc-rearm-budget :in-theory (disable fn-rtc-rearm-budget fn-rtc-rearm))))

(defthm fn-rtc-pool-of-accept-prepared
  (equal (fn-rtc-pool (fn-rtc-accept-prepared s1 out)) (fn-rtc-pool s1))
  :hints (("Goal" :in-theory (enable fn-rtc-accept-prepared))))

(defthm fn-rtc-accept-branch-budget
  (implies (fn-rtc-pool-bytes-okp (fn-rtc-pool s1) (fn-rtc-cap (fn-rtc-config s1)))
    (implies (natp q)
           (let ((x (fn-rtc-accept-branch s1 out q)) (u (fn-rtc-use-bound (fn-rtc-config s1))))
             (and (<= (nfix (mv-nth 3 x)) (+ q (fn-rtc-m-c) (* (fn-rtc-m-max-reqs) (+ 1 u))))
                  (<= (len (mv-nth 1 x)) (+ 2 (fn-rtc-m-max-reqs)))
                  (<= (fn-rtc-actions-octets (mv-nth 1 x)) (* (fn-rtc-m-max-reqs) (fn-rtc-cap (fn-rtc-config s1))))))))
  :hints (("Goal" :in-theory (disable fn-rtc-b-gen fn-rtc-b-bytes fn-rtc-h-buf fn-rtc-h-gen fn-rtc-h-off fn-rtc-h-len fn-rtc-s-res fn-rtc-s-inc fn-rtc-slot fn-rtc-next-op fn-rtc-use-bound fn-rtc-submit-okp fn-rtc-kind-out-p fn-rtc-live-p fn-rtc-current-p fn-rtc-extrap fn-rtc-buffered-kind-p member-equal fn-rtc-kind-op fn-rtc-accept-branch fn-rtc-deliver fn-rtc-rearm mv-nth fn-rtc-use-bound
                                      fn-rtc-actions-octets fn-rtc-cap fn-rtc-deliver-budget fn-rtc-accept-go-p
                                      fn-rtc-accept-prepared fn-rtc-accept-slot fn-rtc-accept-inc)
           :use ((:instance fn-rtc-deliver-budget
                  (s (fn-rtc-accept-prepared s1 out)) (id (fn-rtc-accept-slot s1)) (inc (fn-rtc-accept-inc s1))
                  (ev (fn-rtc-ev :accept out (fn-rtc-accept-slot s1) (fn-rtc-accept-inc s1) nil)))))))

(defthm fn-rtc-close-branch-budget
  (and (<= (len (mv-nth 1 (fn-rtc-close-branch s1 id inc))) 2)
       (equal (fn-rtc-actions-octets (mv-nth 1 (fn-rtc-close-branch s1 id inc))) 0))
  :hints (("Goal" :in-theory (disable fn-rtc-close-prepared fn-rtc-rearm))))

(defthm fn-rtc-in-use-within-cap
  (implies (and (fn-rtc-invp s)
                (fn-rtc-find-use k (fn-rtc-uses s))
                (member-equal (fn-rtc-get 0 (fn-rtc-find-use k (fn-rtc-uses s))) *fn-rtc-in-kinds*))
           (<= (fn-rtc-h-len (fn-rtc-u-hd (fn-rtc-find-use k (fn-rtc-uses s))))
               (fn-rtc-cap (fn-rtc-config s))))
  :rule-classes :linear
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
             '(fn-rtc-use-okp fn-rtc-usep fn-rtc-u-hd fn-rtc-handlep fn-rtc-h-off
               fn-rtc-h-len nfix natp (:executable-counterpart member-equal)))
           :use ((:instance fn-rtc-buf-cap-at-most-cap
                   (h (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use k (fn-rtc-uses s)))))
                   (cfg (fn-rtc-config s)))
                 fn-rtc-invp-uses-okp
                 (:instance fn-rtc-find-use-is-member (uses (fn-rtc-uses s)))
                 (:instance fn-rtc-uses-okp-member (uses (fn-rtc-uses s))
                   (u (fn-rtc-find-use k (fn-rtc-uses s))))))))

(defthm fn-rtc-deliver-budget-linear
  (implies (fn-rtc-pool-bytes-okp (fn-rtc-pool s) (fn-rtc-cap (fn-rtc-config s)))
    (implies (natp q)
           (and (<= (mv-nth 3 (fn-rtc-deliver s id inc ev q))
                    (+ q (fn-rtc-m-c) (* (fn-rtc-m-max-reqs) (+ 1 (fn-rtc-use-bound (fn-rtc-config s))))))
                (<= (len (mv-nth 1 (fn-rtc-deliver s id inc ev q))) (fn-rtc-m-max-reqs))
                (<= (fn-rtc-actions-octets (mv-nth 1 (fn-rtc-deliver s id inc ev q)))
                    (* (fn-rtc-m-max-reqs) (fn-rtc-cap (fn-rtc-config s)))))))
  :rule-classes :linear
  :hints (("Goal" :use fn-rtc-deliver-budget :in-theory (disable fn-rtc-deliver-budget fn-rtc-deliver))))

(defthm fn-rtc-accept-branch-budget-linear
  (implies (fn-rtc-pool-bytes-okp (fn-rtc-pool s1) (fn-rtc-cap (fn-rtc-config s1)))
    (implies (natp q)
           (and (<= (nfix (mv-nth 3 (fn-rtc-accept-branch s1 out q)))
                    (+ q (fn-rtc-m-c) (* (fn-rtc-m-max-reqs) (+ 1 (fn-rtc-use-bound (fn-rtc-config s1))))))
                (<= (len (mv-nth 1 (fn-rtc-accept-branch s1 out q))) (+ 2 (fn-rtc-m-max-reqs)))
                (<= (fn-rtc-actions-octets (mv-nth 1 (fn-rtc-accept-branch s1 out q)))
                    (* (fn-rtc-m-max-reqs) (fn-rtc-cap (fn-rtc-config s1)))))))
  :rule-classes :linear
  :hints (("Goal" :use fn-rtc-accept-branch-budget :in-theory (disable fn-rtc-accept-branch-budget fn-rtc-accept-branch))))

(defthm fn-rtc-close-branch-budget-linear
  (and (<= (len (mv-nth 1 (fn-rtc-close-branch s1 id inc))) 2)
       (<= (fn-rtc-actions-octets (mv-nth 1 (fn-rtc-close-branch s1 id inc))) 0))
  :rule-classes :linear
  :hints (("Goal" :use fn-rtc-close-branch-budget :in-theory (disable fn-rtc-close-branch-budget fn-rtc-close-branch))))

(defthm fn-rtc-completionp-consp
  (implies (fn-rtc-completionp e) (consp e))
  :rule-classes :forward-chaining)

(defthm fn-rtc-invp-found-use-consp
  (implies (and (fn-rtc-invp s) (fn-rtc-find-use k (fn-rtc-uses s)))
           (consp (fn-rtc-find-use k (fn-rtc-uses s))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-rtc-use-okp fn-rtc-usep))
 :use (fn-rtc-invp-uses-okp
       (:instance fn-rtc-find-use-is-member (uses (fn-rtc-uses s)))
       (:instance fn-rtc-uses-okp-member (uses (fn-rtc-uses s))
         (u (fn-rtc-find-use k (fn-rtc-uses s))))))))

(defthm fn-rtc-pool-okp-implies-pool-bytes-okp
  (implies (fn-rtc-pool-okp i pool s)
           (fn-rtc-pool-bytes-okp pool (fn-rtc-cap (fn-rtc-config s))))
  :hints (("Goal" :induct (fn-rtc-pool-induct i pool)
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-rtc-pool-induct fn-rtc-pool-okp-unfolds fn-rtc-pool-bytes-okp fn-rtc-buffer-okp-bytes
   car-cons cdr-cons (:executable-counterpart fn-rtc-pool-bytes-okp))))))

(defthm fn-rtc-core-invp-pool-bytes
  (implies (fn-rtc-core-invp s)
           (fn-rtc-pool-bytes-okp (fn-rtc-pool s) (fn-rtc-cap (fn-rtc-config s))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use (fn-rtc-core-invp-pool
                 (:instance fn-rtc-pool-okp-implies-pool-bytes-okp (i 0) (pool (fn-rtc-pool s)))))))

(local (defthm fn-rtc-grant-one-budget
  (and (<= (len (mv-nth 1 (fn-rtc-grant-one s))) 1)
       (equal (fn-rtc-actions-octets (mv-nth 1 (fn-rtc-grant-one s))) 0))
  :hints (("Goal" :in-theory
    (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
      '(fn-rtc-grant-one fn-rtc-actions-octets fn-rtc-buffered-kind-p fn-rtc-handlep
        fn-rtc-h-len fn-rtc-get nfix natp zp len car-cons cdr-cons
        (:executable-counterpart equal) (:executable-counterpart member-equal)
        (:executable-counterpart zp) (:executable-counterpart binary-+)
        (:executable-counterpart unary--)))))))
(local (defthm fn-rtc-grant-one-budget-linear
  (<= (len (mv-nth 1 (fn-rtc-grant-one s))) 1)
  :rule-classes :linear
  :hints (("Goal" :in-theory (theory 'minimal-theory) :use fn-rtc-grant-one-budget))))
(local (defthm fn-rtc-grant-budget
  (and (<= (len (mv-nth 1 (fn-rtc-grant n s))) (nfix n))
       (equal (fn-rtc-actions-octets (mv-nth 1 (fn-rtc-grant n s))) 0))
  :hints (("Goal" :induct (fn-rtc-grant n s)
    :in-theory
    (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
      '(fn-rtc-grant fn-rtc-grant-one-budget-linear fn-rtc-grant-one-budget fn-rtc-actions-octets-append
        fn-rtc-len-append nfix natp zp len car-cons cdr-cons
        (:executable-counterpart fn-rtc-actions-octets)
        (:executable-counterpart binary-+) (:executable-counterpart unary--)
        (:type-prescription fn-rtc-actions-octets)))))))

(local (defthm fn-rtc-grant-budget-linear
  (<= (len (mv-nth 1 (fn-rtc-grant n s))) (nfix n))
  :rule-classes ((:linear :trigger-terms ((len (mv-nth 1 (fn-rtc-grant n s))))))
  :hints (("Goal" :in-theory (theory 'minimal-theory) :use fn-rtc-grant-budget))))

(defthm fn-rtc-invp-implies-core-invp
  (implies (fn-rtc-invp s) (fn-rtc-core-invp s))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use fn-rtc-invp-is-core-and-admission)))

(local (defthm fn-rtc-acts-on-has-use
  (implies (fn-rtc-acts-on-p s e)
           (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                 '(fn-rtc-acts-on-p fn-rtc-hand-delivers-p))))))

(local (defthm fn-rtc-deliver-end-use-budget
  (implies (and (fn-rtc-invp s) (natp q))
           (and (<= (mv-nth 3 (fn-rtc-deliver (fn-rtc-end-use s e) id inc ev q))
                    (+ q (fn-rtc-m-c) (* (fn-rtc-m-max-reqs) (+ 1 (fn-rtc-use-bound (fn-rtc-config s))))))
                (<= (len (mv-nth 1 (fn-rtc-deliver (fn-rtc-end-use s e) id inc ev q))) (fn-rtc-m-max-reqs))
                (<= (fn-rtc-actions-octets (mv-nth 1 (fn-rtc-deliver (fn-rtc-end-use s e) id inc ev q)))
                    (* (fn-rtc-m-max-reqs) (fn-rtc-cap (fn-rtc-config s))))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-config-of-end-use))
    :use (fn-rtc-invp-implies-core-invp fn-rtc-end-use-preserves-core-invp
          (:instance fn-rtc-core-invp-pool-bytes (s (fn-rtc-end-use s e)))
          (:instance fn-rtc-deliver-budget (s (fn-rtc-end-use s e))))))))

(local (defthm fn-rtc-accept-end-use-budget
  (implies (fn-rtc-invp s)
    (implies (natp q)
           (and (<= (nfix (mv-nth 3 (fn-rtc-accept-branch (fn-rtc-end-use s e) out q)))
                    (+ q (fn-rtc-m-c) (* (fn-rtc-m-max-reqs) (+ 1 (fn-rtc-use-bound (fn-rtc-config s))))))
                (<= (len (mv-nth 1 (fn-rtc-accept-branch (fn-rtc-end-use s e) out q))) (+ 2 (fn-rtc-m-max-reqs)))
                (<= (fn-rtc-actions-octets (mv-nth 1 (fn-rtc-accept-branch (fn-rtc-end-use s e) out q)))
                    (* (fn-rtc-m-max-reqs) (fn-rtc-cap (fn-rtc-config s)))))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-config-of-end-use))
    :use (fn-rtc-invp-implies-core-invp fn-rtc-end-use-preserves-core-invp
          (:instance fn-rtc-core-invp-pool-bytes (s (fn-rtc-end-use s e)))
          (:instance fn-rtc-accept-branch-budget (s1 (fn-rtc-end-use s e))))))))

; T12
(defthm fn-rtc-step-is-charged
  (implies (and (fn-rtc-invp s) (natp q))
           (and (<= (fn-rtc-step-cost s e q)
                    (+ q (fn-rtc-step-c (fn-rtc-config s))))
                (<= (len (mv-nth 1 (fn-rtc-step s e q)))
                    (fn-rtc-step-actions-bound (fn-rtc-config s)))
                (<= (fn-rtc-actions-octets (mv-nth 1 (fn-rtc-step s e q)))
                    (* (fn-rtc-m-max-reqs) (fn-rtc-cap (fn-rtc-config s))))))
  :hints (("Goal" :nonlinearp t :in-theory
 (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
 '(fn-rtc-step-cost-is fn-rtc-step-cost-of fn-rtc-step-actions-is fn-rtc-step-actions
   fn-rtc-step* fn-rtc-step-c fn-rtc-step-actions-bound
   fn-rtc-config-of-end-use fn-rtc-end-use-config
   fn-rtc-deliver-end-use-budget fn-rtc-accept-end-use-budget
   fn-rtc-grant-budget-linear fn-rtc-close-branch-budget-linear fn-rtc-rearm-budget-linear
   fn-rtc-rearm-budget
   fn-rtc-actions-octets-append fn-rtc-len-append
   fn-rtc-actions-octets-def fn-rtc-act-octets len binary-append
   nfix natp car-cons cdr-cons fn-rtc-e-kind
   fn-rtc-m-max-reqs-natp fn-rtc-m-c-natp
   fn-rtc-invp-implies-core-invp fn-rtc-end-use-preserves-core-invp
   fn-rtc-core-invp-pool-bytes
   (:type-prescription fn-rtc-use-bound) (:type-prescription fn-rtc-cap)
   (:type-prescription fn-rtc-grant-unit)
   (:type-prescription fn-rtc-npool) (:type-prescription fn-rtc-nslots) (:type-prescription fn-rtc-nbufs)
   (:executable-counterpart equal) (:executable-counterpart member-equal)))
 :use ((:instance fn-rtc-accept-end-use-budget (out (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e)))
       (:instance fn-rtc-grant-budget (n (fn-rtc-npool (fn-rtc-config s))) (s (fn-rtc-end-use s e)))
       fn-rtc-acts-on-has-use fn-rtc-hand-delivers-kind
       (:instance fn-rtc-in-use-within-cap (k (fn-rtc-key e)))
       (:instance fn-rtc-key-of-find-use (k (fn-rtc-key e)) (uses (fn-rtc-uses s)))
       (:instance fn-rtc-key-equal-parts (e (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))) (u e))))))
