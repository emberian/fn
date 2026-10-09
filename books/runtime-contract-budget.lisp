; fn: the runtime contract's T12: the work budget, the action count and the retained output of one step.
;
; Part of the runtime contract (books/runtime-contract.lisp states it and its
; statements; this book carries the proofs named below).  Split from that book
; so each certifies under the per-book time limit.

(in-package "ACL2")
(include-book "runtime-contract-actions")

; The work budget.
(defun fn-rtc-req-octets (r)
  (declare (xargs :guard t))
  (if (eq (fn-rtc-get 0 r) :write) (len (fn-rtc-get 4 r)) 0))

(defthm fn-rtc-reqs-octets-def
  (equal (fn-rtc-reqs-octets reqs)
         (if (consp reqs) (+ (fn-rtc-req-octets (car reqs)) (fn-rtc-reqs-octets (cdr reqs))) 0))
  :rule-classes :definition)

(defthm fn-rtc-submit-okp-within-cap
  (implies (fn-rtc-submit-okp kind hd id inc s)
           (<= (fn-rtc-h-len hd) (fn-rtc-cap (fn-rtc-config s))))
  :rule-classes :linear)

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
  (let ((x (fn-rtc-req-submit r id inc s)) (u (fn-rtc-use-bound (fn-rtc-config s))))
   (implies (equal (fn-rtc-get 0 r) :submit)
    (and (<= (mv-nth 3 x) (+ 1 u (fn-rtc-req-octets r)))
         (<= (len (mv-nth 1 x)) 1)
         (<= (fn-rtc-actions-octets (mv-nth 1 x)) (fn-rtc-cap (fn-rtc-config s)))
         (equal (fn-rtc-config (mv-nth 0 x)) (fn-rtc-config s)))))
  :hints (("Goal" :in-theory (disable fn-rtc-b-gen fn-rtc-b-bytes fn-rtc-h-buf fn-rtc-h-gen fn-rtc-h-off fn-rtc-h-len fn-rtc-s-res fn-rtc-s-inc fn-rtc-slot fn-rtc-next-op fn-rtc-use-bound fn-rtc-submit-okp fn-rtc-kind-out-p fn-rtc-live-p fn-rtc-current-p fn-rtc-extrap fn-rtc-buffered-kind-p member-equal fn-rtc-kind-op fn-rtc-b-bytes fn-rtc-h-buf fn-rtc-h-gen fn-rtc-h-off fn-rtc-s-inc fn-rtc-buffered-kind-p fn-rtc-b-gen fn-rtc-splice fn-rtc-b-owner fn-rtc-nbufs fn-cbor-octet-listp fn-rtc-buffer fn-rtc-live-p fn-rtc-current-p fn-rtc-slot fn-rtc-s-res fn-rtc-extrap fn-rtc-kind-out-p fn-rtc-kind-op member-equal fn-rtc-next-op))))

(defthm fn-rtc-request-budget
  (let ((x (fn-rtc-request r id inc s)) (u (fn-rtc-use-bound (fn-rtc-config s))))
    (and (<= (mv-nth 3 x) (+ 1 u (fn-rtc-req-octets r)))
         (<= (len (mv-nth 1 x)) 1)
         (<= (fn-rtc-actions-octets (mv-nth 1 x)) (fn-rtc-cap (fn-rtc-config s)))
         (equal (fn-rtc-config (mv-nth 0 x)) (fn-rtc-config s))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-request)
                                  (mv-nth fn-rtc-req-acquire fn-rtc-req-write fn-rtc-req-release fn-rtc-req-close
                                   fn-rtc-req-cancel fn-rtc-req-submit fn-rtc-req-octets fn-rtc-use-bound
                                   fn-rtc-actions-octets fn-rtc-cap)))))

(defthm fn-rtc-request-budget-linear
  (and (<= (mv-nth 3 (fn-rtc-request r id inc s))
           (+ 1 (fn-rtc-use-bound (fn-rtc-config s)) (fn-rtc-req-octets r)))
       (<= (len (mv-nth 1 (fn-rtc-request r id inc s))) 1)
       (<= (fn-rtc-actions-octets (mv-nth 1 (fn-rtc-request r id inc s))) (fn-rtc-cap (fn-rtc-config s))))
  :rule-classes :linear
  :hints (("Goal" :use fn-rtc-request-budget :in-theory (disable fn-rtc-request-budget fn-rtc-request))))

(defthm fn-rtc-len-append (equal (len (append a b)) (+ (len a) (len b))))

(defthm fn-rtc-requests-budget
  (let ((x (fn-rtc-requests reqs id inc s)) (u (fn-rtc-use-bound (fn-rtc-config s))))
    (and (<= (mv-nth 3 x) (+ (* (len reqs) (+ 1 u)) (fn-rtc-reqs-octets reqs)))
         (<= (len (mv-nth 1 x)) (len reqs))
         (<= (fn-rtc-actions-octets (mv-nth 1 x)) (* (len reqs) (fn-rtc-cap (fn-rtc-config s))))
         (equal (fn-rtc-config (mv-nth 0 x)) (fn-rtc-config s))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-requests)
                                  (mv-nth fn-rtc-request fn-rtc-req-octets fn-rtc-use-bound fn-rtc-actions-octets
                                   fn-rtc-cap))
           :induct (fn-rtc-requests reqs id inc s))
          ("Subgoal *1/1'" :nonlinearp t)))

(defthm fn-rtc-deliver-budget
  (implies (natp q)
           (let ((x (fn-rtc-deliver s id inc ev q)) (u (fn-rtc-use-bound (fn-rtc-config s))))
             (and (<= (mv-nth 3 x) (+ q (fn-rtc-m-c) (* (fn-rtc-m-max-reqs) (+ 1 u))))
                  (<= (len (mv-nth 1 x)) (fn-rtc-m-max-reqs))
                  (<= (fn-rtc-actions-octets (mv-nth 1 x)) (* (fn-rtc-m-max-reqs) (fn-rtc-cap (fn-rtc-config s)))))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-deliver)
                                  (fn-rtc-requests mv-nth fn-rtc-use-bound fn-rtc-actions-octets fn-rtc-cap
                                   fn-rtc-m-step-is-charged fn-rtc-m-step-requests-are-bounded fn-rtc-requests-budget))
           :use ((:instance fn-rtc-m-step-is-charged (m (fn-rtc-mstate id s)) (pool (fn-rtc-borrow (fn-rtc-pool s))))
                 (:instance fn-rtc-m-step-requests-are-bounded (m (fn-rtc-mstate id s))
                            (pool (fn-rtc-borrow (fn-rtc-pool s))) (q (nfix q)))
                 (:instance fn-rtc-requests-budget
                            (reqs (mv-nth 1 (fn-rtc-m-step (fn-rtc-mstate id s) ev (fn-rtc-borrow (fn-rtc-pool s)) q)))
                            (s (fn-rtc-with-mstate id (mv-nth 0 (fn-rtc-m-step (fn-rtc-mstate id s) ev
                                                                                (fn-rtc-borrow (fn-rtc-pool s)) q))
                                                   s))))
           :nonlinearp t)))

(defthm fn-rtc-rearm-budget
  (and (<= (len (mv-nth 1 (fn-rtc-rearm s))) 1)
       (equal (fn-rtc-actions-octets (mv-nth 1 (fn-rtc-rearm s))) 0))
  :hints (("Goal" :in-theory (e/d (fn-rtc-rearm) (fn-rtc-free-slot fn-rtc-kind-out-p)))))

(defun fn-rtc-step-cost-of (s e q)
  (declare (xargs :guard t))
  (let* ((cfg (fn-rtc-config s))
         (base (+ 4 (* 6 (fn-rtc-use-bound cfg)) (* 2 (fn-rtc-nslots cfg)))))
    (if (not (fn-rtc-acts-on-p s e))
        base
      (let* ((s1 (fn-rtc-end-use s e))
             (kind (fn-rtc-e-kind e))
             (u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))
             (out (fn-rtc-delivered-outcome u e))
             (base (+ base (if (member-eq kind *fn-rtc-in-kinds*) (fn-rtc-h-len (fn-rtc-u-hd u)) 0))))
        (cond ((eq kind :accept)
               (mv-let (s2 a r c) (fn-rtc-accept-branch s1 out q) (declare (ignore s2 a r)) (+ base (nfix c))))
              ((eq kind :close) (+ base (fn-rtc-nbufs cfg)))
              (t (mv-let (s2 a r c) (fn-rtc-deliver s1 (fn-rtc-e-id e) (fn-rtc-e-inc e) (list kind out) q)
                   (declare (ignore s2 a r)) (+ base c))))))))

(defthm fn-rtc-step-cost-idle
  (implies (not (fn-rtc-acts-on-p s e))
           (equal (mv-nth 3 (fn-rtc-step* s e q)) (+ 4 (* 6 (fn-rtc-use-bound (fn-rtc-config s))) (* 2 (fn-rtc-nslots (fn-rtc-config s))))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-step*) (fn-rtc-acts-on-p fn-rtc-e-kind fn-rtc-e-id fn-rtc-e-inc
                                   fn-rtc-delivered-outcome fn-rtc-find-use fn-rtc-key fn-rtc-end-use
                                   fn-rtc-rearm fn-rtc-deliver fn-rtc-accept-branch fn-rtc-close-branch
                                   fn-rtc-use-bound fn-rtc-nslots fn-rtc-nbufs fn-rtc-h-len fn-rtc-u-hd
                                   member-equal fn-rtc-config fn-rtc-cap fn-rtc-uses nfix fn-rtc-step-is-step-state
                                   fn-rtc-step-actions-is fn-rtc-close-branch-is-rearm)))))

(defthm fn-rtc-step-cost-accept
  (implies (and (fn-rtc-acts-on-p s e) (eq (fn-rtc-e-kind e) :accept))
           (equal (mv-nth 3 (fn-rtc-step* s e q)) (+ (+ 4 (* 6 (fn-rtc-use-bound (fn-rtc-config s))) (* 2 (fn-rtc-nslots (fn-rtc-config s)))) (if (member-equal (fn-rtc-e-kind e) *fn-rtc-in-kinds*) (fn-rtc-h-len (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))) 0) (nfix (mv-nth 3 (fn-rtc-accept-branch (fn-rtc-end-use s e) (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e) q))))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-step*) (fn-rtc-acts-on-p fn-rtc-e-kind fn-rtc-e-id fn-rtc-e-inc
                                   fn-rtc-delivered-outcome fn-rtc-find-use fn-rtc-key fn-rtc-end-use
                                   fn-rtc-rearm fn-rtc-deliver fn-rtc-accept-branch fn-rtc-close-branch
                                   fn-rtc-use-bound fn-rtc-nslots fn-rtc-nbufs fn-rtc-h-len fn-rtc-u-hd
                                   member-equal fn-rtc-config fn-rtc-cap fn-rtc-uses nfix fn-rtc-step-is-step-state
                                   fn-rtc-step-actions-is fn-rtc-close-branch-is-rearm)))))

(defthm fn-rtc-step-cost-close
  (implies (and (fn-rtc-acts-on-p s e) (eq (fn-rtc-e-kind e) :close))
           (equal (mv-nth 3 (fn-rtc-step* s e q)) (+ (+ 4 (* 6 (fn-rtc-use-bound (fn-rtc-config s))) (* 2 (fn-rtc-nslots (fn-rtc-config s)))) (if (member-equal (fn-rtc-e-kind e) *fn-rtc-in-kinds*) (fn-rtc-h-len (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))) 0) (fn-rtc-nbufs (fn-rtc-config s)))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-step*) (fn-rtc-acts-on-p fn-rtc-e-kind fn-rtc-e-id fn-rtc-e-inc
                                   fn-rtc-delivered-outcome fn-rtc-find-use fn-rtc-key fn-rtc-end-use
                                   fn-rtc-rearm fn-rtc-deliver fn-rtc-accept-branch fn-rtc-close-branch
                                   fn-rtc-use-bound fn-rtc-nslots fn-rtc-nbufs fn-rtc-h-len fn-rtc-u-hd
                                   member-equal fn-rtc-config fn-rtc-cap fn-rtc-uses nfix fn-rtc-step-is-step-state
                                   fn-rtc-step-actions-is fn-rtc-close-branch-is-rearm)))))

(defthm fn-rtc-step-cost-deliver
  (implies (and (fn-rtc-acts-on-p s e) (not (eq (fn-rtc-e-kind e) :accept)) (not (eq (fn-rtc-e-kind e) :close)))
           (equal (mv-nth 3 (fn-rtc-step* s e q)) (+ (+ 4 (* 6 (fn-rtc-use-bound (fn-rtc-config s))) (* 2 (fn-rtc-nslots (fn-rtc-config s)))) (if (member-equal (fn-rtc-e-kind e) *fn-rtc-in-kinds*) (fn-rtc-h-len (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))) 0) (mv-nth 3 (fn-rtc-deliver (fn-rtc-end-use s e) (fn-rtc-e-id e) (fn-rtc-e-inc e) (list (fn-rtc-e-kind e) (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e)) q)))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-step*) (fn-rtc-acts-on-p fn-rtc-e-kind fn-rtc-e-id fn-rtc-e-inc
                                   fn-rtc-delivered-outcome fn-rtc-find-use fn-rtc-key fn-rtc-end-use
                                   fn-rtc-rearm fn-rtc-deliver fn-rtc-accept-branch fn-rtc-close-branch
                                   fn-rtc-use-bound fn-rtc-nslots fn-rtc-nbufs fn-rtc-h-len fn-rtc-u-hd
                                   member-equal fn-rtc-config fn-rtc-cap fn-rtc-uses nfix fn-rtc-step-is-step-state
                                   fn-rtc-step-actions-is fn-rtc-close-branch-is-rearm)))))

(defthm fn-rtc-step-cost-is
  (equal (fn-rtc-step-cost s e q) (fn-rtc-step-cost-of s e q))
  :hints (("Goal" :in-theory (e/d (fn-rtc-step-cost fn-rtc-step-cost-of) (fn-rtc-step* fn-rtc-acts-on-p fn-rtc-e-kind fn-rtc-e-id fn-rtc-e-inc
                                   fn-rtc-delivered-outcome fn-rtc-find-use fn-rtc-key fn-rtc-end-use
                                   fn-rtc-rearm fn-rtc-deliver fn-rtc-accept-branch fn-rtc-close-branch
                                   fn-rtc-use-bound fn-rtc-nslots fn-rtc-nbufs fn-rtc-h-len fn-rtc-u-hd
                                   member-equal fn-rtc-config fn-rtc-cap fn-rtc-uses nfix fn-rtc-step-is-step-state
                                   fn-rtc-step-actions-is fn-rtc-close-branch-is-rearm))))
)

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
                                       (fn-rtc-accept-inc s1) (list :accept out) q))
           0))
  :hints (("Goal" :in-theory (e/d (fn-rtc-accept-branch) (fn-rtc-deliver fn-rtc-rearm fn-rtc-free-slot)))))

(defthm fn-rtc-rearm-budget-linear
  (<= (len (mv-nth 1 (fn-rtc-rearm s))) 1)
  :rule-classes :linear
  :hints (("Goal" :use fn-rtc-rearm-budget :in-theory (disable fn-rtc-rearm-budget fn-rtc-rearm))))

(defthm fn-rtc-accept-branch-budget
  (implies (natp q)
           (let ((x (fn-rtc-accept-branch s1 out q)) (u (fn-rtc-use-bound (fn-rtc-config s1))))
             (and (<= (nfix (mv-nth 3 x)) (+ q (fn-rtc-m-c) (* (fn-rtc-m-max-reqs) (+ 1 u))))
                  (<= (len (mv-nth 1 x)) (+ 1 (fn-rtc-m-max-reqs)))
                  (<= (fn-rtc-actions-octets (mv-nth 1 x)) (* (fn-rtc-m-max-reqs) (fn-rtc-cap (fn-rtc-config s1)))))))
  :hints (("Goal" :in-theory (disable fn-rtc-b-gen fn-rtc-b-bytes fn-rtc-h-buf fn-rtc-h-gen fn-rtc-h-off fn-rtc-h-len fn-rtc-s-res fn-rtc-s-inc fn-rtc-slot fn-rtc-next-op fn-rtc-use-bound fn-rtc-submit-okp fn-rtc-kind-out-p fn-rtc-live-p fn-rtc-current-p fn-rtc-extrap fn-rtc-buffered-kind-p member-equal fn-rtc-kind-op fn-rtc-accept-branch fn-rtc-deliver fn-rtc-rearm mv-nth fn-rtc-use-bound
                                      fn-rtc-actions-octets fn-rtc-cap fn-rtc-deliver-budget fn-rtc-accept-go-p
                                      fn-rtc-accept-prepared fn-rtc-accept-slot fn-rtc-accept-inc)
           :use ((:instance fn-rtc-deliver-budget
                  (s (fn-rtc-accept-prepared s1 out)) (id (fn-rtc-accept-slot s1)) (inc (fn-rtc-accept-inc s1))
                  (ev (list :accept out)))))))

(defthm fn-rtc-close-branch-budget
  (and (<= (len (mv-nth 1 (fn-rtc-close-branch s1 id inc))) 1)
       (equal (fn-rtc-actions-octets (mv-nth 1 (fn-rtc-close-branch s1 id inc))) 0))
  :hints (("Goal" :in-theory (disable fn-rtc-close-prepared fn-rtc-rearm))))

(defthm fn-rtc-in-use-within-cap
  (implies (and (fn-rtc-invp s)
                (fn-rtc-find-use k (fn-rtc-uses s))
                (member-equal (fn-rtc-get 0 (fn-rtc-find-use k (fn-rtc-uses s))) *fn-rtc-in-kinds*))
           (<= (fn-rtc-h-len (fn-rtc-u-hd (fn-rtc-find-use k (fn-rtc-uses s))))
               (fn-rtc-cap (fn-rtc-config s))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (fn-rtc-use-okp) (fn-rtc-invp fn-rtc-uses-okp-member fn-rtc-current-p fn-rtc-holders
                                                   fn-rtc-buffer fn-rtc-slot fn-rtc-find-use))
                  :use (fn-rtc-invp-uses-okp
                        (:instance fn-rtc-find-use-is-member (uses (fn-rtc-uses s)))
                        (:instance fn-rtc-uses-okp-member (uses (fn-rtc-uses s))
                                   (u (fn-rtc-find-use k (fn-rtc-uses s)))))
                  :expand ((fn-rtc-usep (fn-rtc-find-use k (fn-rtc-uses s)))))))

(defthm fn-rtc-deliver-budget-linear
  (implies (natp q)
           (and (<= (mv-nth 3 (fn-rtc-deliver s id inc ev q))
                    (+ q (fn-rtc-m-c) (* (fn-rtc-m-max-reqs) (+ 1 (fn-rtc-use-bound (fn-rtc-config s))))))
                (<= (len (mv-nth 1 (fn-rtc-deliver s id inc ev q))) (fn-rtc-m-max-reqs))
                (<= (fn-rtc-actions-octets (mv-nth 1 (fn-rtc-deliver s id inc ev q)))
                    (* (fn-rtc-m-max-reqs) (fn-rtc-cap (fn-rtc-config s))))))
  :rule-classes :linear
  :hints (("Goal" :use fn-rtc-deliver-budget :in-theory (disable fn-rtc-deliver-budget fn-rtc-deliver))))

(defthm fn-rtc-accept-branch-budget-linear
  (implies (natp q)
           (and (<= (nfix (mv-nth 3 (fn-rtc-accept-branch s1 out q)))
                    (+ q (fn-rtc-m-c) (* (fn-rtc-m-max-reqs) (+ 1 (fn-rtc-use-bound (fn-rtc-config s1))))))
                (<= (len (mv-nth 1 (fn-rtc-accept-branch s1 out q))) (+ 1 (fn-rtc-m-max-reqs)))
                (<= (fn-rtc-actions-octets (mv-nth 1 (fn-rtc-accept-branch s1 out q)))
                    (* (fn-rtc-m-max-reqs) (fn-rtc-cap (fn-rtc-config s1))))))
  :rule-classes :linear
  :hints (("Goal" :use fn-rtc-accept-branch-budget :in-theory (disable fn-rtc-accept-branch-budget fn-rtc-accept-branch))))

(defthm fn-rtc-close-branch-budget-linear
  (and (<= (len (mv-nth 1 (fn-rtc-close-branch s1 id inc))) 1)
       (<= (fn-rtc-actions-octets (mv-nth 1 (fn-rtc-close-branch s1 id inc))) 0))
  :rule-classes :linear
  :hints (("Goal" :use fn-rtc-close-branch-budget :in-theory (disable fn-rtc-close-branch-budget fn-rtc-close-branch))))

(defthm fn-rtc-completionp-consp
  (implies (fn-rtc-completionp e) (consp e))
  :rule-classes :forward-chaining)

(defthm fn-rtc-invp-found-use-consp
  (implies (and (fn-rtc-invp s) (fn-rtc-find-use k (fn-rtc-uses s)))
           (consp (fn-rtc-find-use k (fn-rtc-uses s))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-use-okp) (fn-rtc-invp fn-rtc-uses-okp-member fn-rtc-current-p fn-rtc-holders
                                                   fn-rtc-buffer fn-rtc-slot fn-rtc-find-use))
                  :use (fn-rtc-invp-uses-okp
                        (:instance fn-rtc-find-use-is-member (uses (fn-rtc-uses s)))
                        (:instance fn-rtc-uses-okp-member (uses (fn-rtc-uses s))
                                   (u (fn-rtc-find-use k (fn-rtc-uses s)))))
                  :expand ((fn-rtc-usep (fn-rtc-find-use k (fn-rtc-uses s)))))))

; T12
(defthm fn-rtc-step-is-charged
  (implies (and (fn-rtc-invp s) (natp q))
           (and (<= (fn-rtc-step-cost s e q)
                    (+ q (fn-rtc-step-c (fn-rtc-config s))))
                (<= (len (mv-nth 1 (fn-rtc-step s e q)))
                    (+ 1 (fn-rtc-m-max-reqs)))
                (<= (fn-rtc-actions-octets (mv-nth 1 (fn-rtc-step s e q)))
                    (* (fn-rtc-m-max-reqs) (fn-rtc-cap (fn-rtc-config s))))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-step-cost-of fn-rtc-step-actions fn-rtc-step-c fn-rtc-acts-on-p)
                                  (fn-rtc-invp mv-nth fn-rtc-e-id fn-rtc-e-inc
                                   fn-rtc-delivered-outcome fn-rtc-find-use fn-rtc-key fn-rtc-end-use
                                   fn-rtc-rearm fn-rtc-deliver fn-rtc-accept-branch fn-rtc-close-branch
                                   fn-rtc-use-bound fn-rtc-actions-octets fn-rtc-cap fn-rtc-h-len fn-rtc-u-hd
                                   fn-rtc-config fn-rtc-nslots fn-rtc-nbufs fn-rtc-end-use-structure
                                   fn-rtc-delivered-outcome fn-rtc-completionp))
           :use ((:instance fn-rtc-in-use-within-cap (k (fn-rtc-key e)))
                 (:instance fn-rtc-key-of-find-use (k (fn-rtc-key e)) (uses (fn-rtc-uses s)))
                 (:instance fn-rtc-key-equal-parts (e (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))) (u e))))))

