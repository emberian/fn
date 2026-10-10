; fn: the runtime contract's T10, request layer: each request's actions are well formed and recorded in the state it
; leaves, the outstanding-use table only grows under requests and re-arming.
;
; Part of the runtime contract (books/runtime-contract.lisp states it and its
; statements; this book carries the proofs named below).  Split from that book
; so each certifies under the per-book time limit.

(in-package "ACL2")
(include-book "runtime-contract-keystones")

; Emitted actions are well formed and recorded.
(defun fn-rtc-step-actions (s e q)
  (declare (xargs :guard t))
  (if (not (fn-rtc-acts-on-p s e))
      (mv-let (s2 a) (fn-rtc-rearm (fn-rtc-end-use s e)) (declare (ignore s2)) a)
    (let ((s1 (fn-rtc-end-use s e))
          (kind (fn-rtc-e-kind e))
          (out (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e)))
      (cond ((eq kind :accept)
             (mv-let (s2 a r c) (fn-rtc-accept-branch s1 out q) (declare (ignore s2 r c)) a))
            ((eq kind :close)
             (mv-let (s2 a) (fn-rtc-close-branch s1 (fn-rtc-e-id e) (fn-rtc-e-inc e)) (declare (ignore s2)) a))
            (t (mv-let (s2 a r c) (fn-rtc-deliver s1 (fn-rtc-e-id e) (fn-rtc-e-inc e) (list kind out) q)
                 (declare (ignore s2 r c)) a))))))

(defthm fn-rtc-step-actions-is
  (equal (mv-nth 1 (fn-rtc-step s e q)) (fn-rtc-step-actions s e q))
  :hints (("Goal" :in-theory (e/d (fn-rtc-step fn-rtc-step* fn-rtc-step-actions)
                                  (fn-rtc-acts-on-p fn-rtc-e-kind fn-rtc-e-id fn-rtc-e-inc
                                   fn-rtc-delivered-outcome fn-rtc-find-use fn-rtc-key fn-rtc-end-use
                                   fn-rtc-rearm fn-rtc-deliver fn-rtc-accept-branch fn-rtc-close-branch
                                   fn-rtc-use-bound fn-rtc-nslots fn-rtc-nbufs fn-rtc-h-len fn-rtc-u-hd
                                   member-equal fn-rtc-config nfix fn-rtc-cap fn-rtc-uses)))))

(in-theory (disable fn-rtc-step-actions))

(defun fn-rtc-recorded-key (a)
  (declare (xargs :guard t))
  (if (equal (fn-rtc-get 0 a) :cancel)
      (list (fn-rtc-get 0 (fn-rtc-get 4 a)) (fn-rtc-get 1 a) (fn-rtc-get 2 a) (fn-rtc-get 3 a))
    (fn-rtc-key a)))

(defun fn-rtc-actions-okp (acts s)
  (declare (xargs :guard t))
  (if (consp acts)
      (and (fn-rtc-actionp (car acts))
           (fn-rtc-find-use (fn-rtc-recorded-key (car acts)) (fn-rtc-uses s))
           (fn-rtc-actions-okp (cdr acts) s))
    t))

(defthm fn-rtc-find-use-of-member-key
  (implies (and (member-equal x uses) (equal (fn-rtc-key x) k) (fn-rtc-get 0 x))
           (fn-rtc-find-use k uses))
  :hints (("Goal" :in-theory (disable fn-rtc-key))))

(defthm fn-rtc-member-of-subset
  (implies (and (member-equal x u1) (subsetp-equal u1 u2))
           (member-equal x u2)))

(defthm fn-rtc-find-use-of-subset
  (implies (and (fn-rtc-find-use k u1) (subsetp-equal u1 u2) (fn-rtc-get 0 k))
           (fn-rtc-find-use k u2))
  :hints (("Goal" :in-theory (disable fn-rtc-find-use-of-member-key fn-rtc-find-use-is-member
                                      fn-rtc-key-of-find-use fn-rtc-member-of-subset)
                  :use ((:instance fn-rtc-find-use-is-member (uses u1))
                        (:instance fn-rtc-key-of-find-use (uses u1))
                        (:instance fn-rtc-member-of-subset (x (fn-rtc-find-use k u1)))
                        (:instance fn-rtc-find-use-of-member-key (x (fn-rtc-find-use k u1)) (uses u2))))))

(defun fn-rtc-actions-kinded-p (acts)
  (declare (xargs :guard t))
  (if (consp acts)
      (and (fn-rtc-get 0 (fn-rtc-recorded-key (car acts)))
           (fn-rtc-actions-kinded-p (cdr acts)))
    t))

(defthm fn-rtc-subsetp-cons (implies (subsetp-equal x y) (subsetp-equal x (cons a y))))

(defthm fn-rtc-subsetp-refl (subsetp-equal x x))

(defthm fn-rtc-subsetp-trans
  (implies (and (subsetp-equal x y) (subsetp-equal y z)) (subsetp-equal x z)))

(defthm fn-rtc-actions-okp-of-subset
  (implies (and (fn-rtc-actions-okp acts s1) (fn-rtc-actions-kinded-p acts)
                (subsetp-equal (fn-rtc-uses s1) (fn-rtc-uses s2)))
           (fn-rtc-actions-okp acts s2))
  :hints (("Goal" :in-theory (disable fn-rtc-actionp fn-rtc-recorded-key))))

(defthm fn-rtc-actions-okp-append
  (equal (fn-rtc-actions-okp (append a b) s)
         (and (fn-rtc-actions-okp a s) (fn-rtc-actions-okp b s)))
  :hints (("Goal" :in-theory (disable fn-rtc-actionp fn-rtc-recorded-key))))

(defthm fn-rtc-actions-kinded-append
  (equal (fn-rtc-actions-kinded-p (append a b))
         (and (fn-rtc-actions-kinded-p a) (fn-rtc-actions-kinded-p b)))
  :hints (("Goal" :in-theory (disable fn-rtc-recorded-key))))

(defthm fn-rtc-request-grows-uses
  (subsetp-equal (fn-rtc-uses s) (fn-rtc-uses (mv-nth 0 (fn-rtc-request r id inc s))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-request fn-rtc-req-acquire fn-rtc-req-write fn-rtc-req-release
                                   fn-rtc-req-close fn-rtc-req-cancel fn-rtc-req-submit)
                                  (fn-rtc-b-bytes fn-rtc-h-buf fn-rtc-h-gen fn-rtc-h-off fn-rtc-h-len fn-rtc-s-res
                                   fn-rtc-s-inc fn-rtc-slot fn-rtc-next-op fn-rtc-use-bound fn-rtc-submit-okp
                                   fn-rtc-kind-out-p fn-rtc-live-p fn-rtc-current-p fn-rtc-extrap
                                   fn-rtc-buffered-kind-p fn-rtc-kind-op fn-rtc-b-gen fn-rtc-splice)))))

(defthm fn-rtc-requests-grows-uses
  (subsetp-equal (fn-rtc-uses s) (fn-rtc-uses (mv-nth 0 (fn-rtc-requests reqs id inc s))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-requests) (mv-nth fn-rtc-request))
           :induct (fn-rtc-requests reqs id inc s))
          ("Subgoal *1/1'" :use ((:instance fn-rtc-subsetp-trans
                                  (x (fn-rtc-uses s))
                                  (y (fn-rtc-uses (mv-nth 0 (fn-rtc-request (car reqs) id inc s))))
                                  (z (fn-rtc-uses (mv-nth 0 (fn-rtc-requests (cdr reqs) id inc
                                                              (mv-nth 0 (fn-rtc-request (car reqs) id inc s)))))))))))

(defthm fn-rtc-rearm-grows-uses
  (subsetp-equal (fn-rtc-uses s) (fn-rtc-uses (mv-nth 0 (fn-rtc-rearm s))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-rearm) (fn-rtc-free-slot fn-rtc-kind-out-p)))))

(defun fn-rtc-uses-ops-natp (uses)
  (declare (xargs :guard t))
  (if (consp uses)
      (and (natp (fn-rtc-get 3 (car uses))) (fn-rtc-uses-ops-natp (cdr uses)))
    t))

(defthm fn-rtc-kind-op-is-recorded
  (implies (and (fn-rtc-kind-out-p kind id inc uses) kind (fn-rtc-uses-ops-natp uses))
           (fn-rtc-find-use (list kind id inc (fn-rtc-kind-op kind id inc uses)) uses)))

(defthm fn-rtc-buffer-reqs-shape
  (and (equal (mv-nth 1 (fn-rtc-req-acquire r id inc s)) nil)
       (equal (fn-rtc-uses (mv-nth 0 (fn-rtc-req-acquire r id inc s))) (fn-rtc-uses s))
       (equal (fn-rtc-slots (mv-nth 0 (fn-rtc-req-acquire r id inc s))) (fn-rtc-slots s))
       (equal (mv-nth 1 (fn-rtc-req-write r id inc s)) nil)
       (equal (fn-rtc-uses (mv-nth 0 (fn-rtc-req-write r id inc s))) (fn-rtc-uses s))
       (equal (fn-rtc-slots (mv-nth 0 (fn-rtc-req-write r id inc s))) (fn-rtc-slots s))
       (equal (mv-nth 1 (fn-rtc-req-release r id inc s)) nil)
       (equal (fn-rtc-uses (mv-nth 0 (fn-rtc-req-release r id inc s))) (fn-rtc-uses s))
       (equal (fn-rtc-slots (mv-nth 0 (fn-rtc-req-release r id inc s))) (fn-rtc-slots s)))
  :hints (("Goal" :in-theory (disable fn-rtc-b-bytes fn-rtc-b-gen fn-rtc-b-owner fn-rtc-splice fn-rtc-cap
                                      fn-rtc-nbufs fn-rtc-config fn-cbor-octet-listp fn-rtc-buffer))))

(defthm fn-rtc-req-close-keeps-res
  (equal (fn-rtc-s-res (fn-rtc-slot id (mv-nth 0 (fn-rtc-req-close r id inc s))))
         (fn-rtc-s-res (fn-rtc-slot id s)))
  :hints (("Goal" :in-theory (disable fn-rtc-b-bytes fn-rtc-h-buf fn-rtc-h-gen fn-rtc-h-off fn-rtc-h-len fn-rtc-s-inc fn-rtc-use-bound fn-rtc-buffered-kind-p fn-rtc-b-gen fn-rtc-splice fn-rtc-b-owner fn-rtc-cap fn-rtc-nbufs fn-rtc-config fn-cbor-octet-listp fn-rtc-buffer fn-rtc-submit-okp fn-rtc-kind-out-p fn-rtc-live-p fn-rtc-current-p fn-rtc-extrap fn-rtc-kind-op))))

(defthm fn-rtc-req-close-ops-natp
  (implies (fn-rtc-uses-ops-natp (fn-rtc-uses s))
           (fn-rtc-uses-ops-natp (fn-rtc-uses (mv-nth 0 (fn-rtc-req-close r id inc s)))))
  :hints (("Goal" :in-theory (disable fn-rtc-b-bytes fn-rtc-h-buf fn-rtc-h-gen fn-rtc-h-off fn-rtc-h-len fn-rtc-s-inc fn-rtc-use-bound fn-rtc-buffered-kind-p fn-rtc-b-gen fn-rtc-splice fn-rtc-b-owner fn-rtc-cap fn-rtc-nbufs fn-rtc-config fn-cbor-octet-listp fn-rtc-buffer fn-rtc-submit-okp fn-rtc-kind-out-p fn-rtc-live-p fn-rtc-current-p fn-rtc-extrap fn-rtc-kind-op fn-rtc-slot fn-rtc-s-res))))

(defthm fn-rtc-req-cancel-keeps-res
  (equal (fn-rtc-s-res (fn-rtc-slot id (mv-nth 0 (fn-rtc-req-cancel r id inc s))))
         (fn-rtc-s-res (fn-rtc-slot id s)))
  :hints (("Goal" :in-theory (disable fn-rtc-b-bytes fn-rtc-h-buf fn-rtc-h-gen fn-rtc-h-off fn-rtc-h-len fn-rtc-s-inc fn-rtc-use-bound fn-rtc-buffered-kind-p fn-rtc-b-gen fn-rtc-splice fn-rtc-b-owner fn-rtc-cap fn-rtc-nbufs fn-rtc-config fn-cbor-octet-listp fn-rtc-buffer fn-rtc-submit-okp fn-rtc-kind-out-p fn-rtc-live-p fn-rtc-current-p fn-rtc-extrap fn-rtc-kind-op))))

(defthm fn-rtc-req-cancel-ops-natp
  (implies (fn-rtc-uses-ops-natp (fn-rtc-uses s))
           (fn-rtc-uses-ops-natp (fn-rtc-uses (mv-nth 0 (fn-rtc-req-cancel r id inc s)))))
  :hints (("Goal" :in-theory (disable fn-rtc-b-bytes fn-rtc-h-buf fn-rtc-h-gen fn-rtc-h-off fn-rtc-h-len fn-rtc-s-inc fn-rtc-use-bound fn-rtc-buffered-kind-p fn-rtc-b-gen fn-rtc-splice fn-rtc-b-owner fn-rtc-cap fn-rtc-nbufs fn-rtc-config fn-cbor-octet-listp fn-rtc-buffer fn-rtc-submit-okp fn-rtc-kind-out-p fn-rtc-live-p fn-rtc-current-p fn-rtc-extrap fn-rtc-kind-op fn-rtc-slot fn-rtc-s-res))))

(defthm fn-rtc-req-submit-keeps-res
  (equal (fn-rtc-s-res (fn-rtc-slot id (mv-nth 0 (fn-rtc-req-submit r id inc s))))
         (fn-rtc-s-res (fn-rtc-slot id s)))
  :hints (("Goal" :in-theory (disable fn-rtc-b-bytes fn-rtc-h-buf fn-rtc-h-gen fn-rtc-h-off fn-rtc-h-len fn-rtc-s-inc fn-rtc-use-bound fn-rtc-buffered-kind-p fn-rtc-b-gen fn-rtc-splice fn-rtc-b-owner fn-rtc-cap fn-rtc-nbufs fn-rtc-config fn-cbor-octet-listp fn-rtc-buffer fn-rtc-submit-okp fn-rtc-kind-out-p fn-rtc-live-p fn-rtc-current-p fn-rtc-extrap fn-rtc-kind-op))))

(defthm fn-rtc-req-submit-ops-natp
  (implies (fn-rtc-uses-ops-natp (fn-rtc-uses s))
           (fn-rtc-uses-ops-natp (fn-rtc-uses (mv-nth 0 (fn-rtc-req-submit r id inc s)))))
  :hints (("Goal" :in-theory (disable fn-rtc-b-bytes fn-rtc-h-buf fn-rtc-h-gen fn-rtc-h-off fn-rtc-h-len fn-rtc-s-inc fn-rtc-use-bound fn-rtc-buffered-kind-p fn-rtc-b-gen fn-rtc-splice fn-rtc-b-owner fn-rtc-cap fn-rtc-nbufs fn-rtc-config fn-cbor-octet-listp fn-rtc-buffer fn-rtc-submit-okp fn-rtc-kind-out-p fn-rtc-live-p fn-rtc-current-p fn-rtc-extrap fn-rtc-kind-op fn-rtc-slot fn-rtc-s-res))))

(defthm fn-rtc-extrap-args-0
  (implies (fn-rtc-extrap x) (fn-rtc-action-argsp x))
  :hints (("Goal" :expand ((fn-rtc-action-argsp x) (fn-rtc-action-argsp (cdr x)) (fn-rtc-action-argsp (cddr x)))
                  :in-theory (disable fn-rtc-action-argsp))))

(defthm fn-rtc-extrap-args-1
  (implies (and (fn-rtc-extrap x) (fn-rtc-action-argp a)) (fn-rtc-action-argsp (cons a x)))
  :hints (("Goal" :expand ((fn-rtc-action-argsp (cons a x)) (fn-rtc-action-argsp x) (fn-rtc-action-argsp (cdr x))
                           (fn-rtc-action-argsp (list a))
                           (fn-rtc-action-argsp (cddr x)))
                  :in-theory (disable fn-rtc-action-argsp fn-rtc-action-argp))))

(defthm fn-rtc-extrap-args-2
  (implies (and (fn-rtc-extrap x) (fn-rtc-action-argp a) (fn-rtc-action-argp b))
           (fn-rtc-action-argsp (cons a (cons b x))))
  :hints (("Goal" :expand ((fn-rtc-action-argsp (cons a (cons b x))) (fn-rtc-action-argsp (cons b x))
                           (fn-rtc-action-argsp (list b)) (fn-rtc-action-argsp (list a b))
                           (fn-rtc-action-argsp x) (fn-rtc-action-argsp (cdr x)) (fn-rtc-action-argsp (cddr x)))
                  :in-theory (disable fn-rtc-action-argsp fn-rtc-action-argp))))

(defthm fn-rtc-submit-okp-handlep
  (implies (fn-rtc-submit-okp kind hd id inc s) (fn-rtc-handlep hd))
  :rule-classes :forward-chaining)

(defthm fn-rtc-kind-classes
  (implies (member-equal k *fn-rtc-machine-kinds*)
           (and (member-equal k *fn-rtc-action-kinds*)
                (member-equal k *fn-rtc-kinds*))))

(defthm fn-rtc-nil-not-machine-kind (not (member-equal nil *fn-rtc-machine-kinds*)))

(defthm fn-rtc-req-submit-actions-ok-fast
  (implies (and (natp id) (natp inc) (fn-rtc-action-argp (fn-rtc-s-res (fn-rtc-slot id s)))
                (fn-rtc-uses-ops-natp (fn-rtc-uses s)))
           (and (fn-rtc-actions-okp (mv-nth 1 (fn-rtc-req-submit r id inc s)) (mv-nth 0 (fn-rtc-req-submit r id inc s)))
                (fn-rtc-actions-kinded-p (mv-nth 1 (fn-rtc-req-submit r id inc s)))))
  :hints (("Goal" :in-theory (disable fn-rtc-b-bytes fn-rtc-h-buf fn-rtc-h-gen fn-rtc-h-off fn-rtc-h-len fn-rtc-s-inc
                                      fn-rtc-use-bound fn-rtc-buffered-kind-p fn-rtc-b-gen fn-rtc-splice fn-rtc-b-owner
                                      fn-rtc-cap fn-rtc-nbufs fn-rtc-config fn-cbor-octet-listp fn-rtc-buffer
                                      fn-rtc-submit-okp fn-rtc-live-p fn-rtc-current-p fn-rtc-slot fn-rtc-s-res
                                      fn-rtc-extrap fn-rtc-action-argsp member-equal fn-rtc-kind-out-p fn-rtc-handlep))
          ("Goal'" :use ((:instance fn-rtc-submit-okp-handlep (kind (fn-rtc-get 1 r)) (hd (fn-rtc-get 2 r)))))))

(defthm fn-rtc-req-cancel-actions-ok-fast
  (implies (and (natp id) (natp inc) (fn-rtc-uses-ops-natp (fn-rtc-uses s)))
           (and (fn-rtc-actions-okp (mv-nth 1 (fn-rtc-req-cancel r id inc s)) (mv-nth 0 (fn-rtc-req-cancel r id inc s)))
                (fn-rtc-actions-kinded-p (mv-nth 1 (fn-rtc-req-cancel r id inc s)))))
  :hints (("Goal" :in-theory (disable fn-rtc-current-p fn-rtc-kind-out-p fn-rtc-kind-op member-equal fn-rtc-use-bound)
                  :cases ((fn-rtc-get 1 r)))))

(defthm fn-rtc-req-close-actions-ok-fast
  (implies (and (natp id) (natp inc) (fn-rtc-action-argp (fn-rtc-s-res (fn-rtc-slot id s))))
           (and (fn-rtc-actions-okp (mv-nth 1 (fn-rtc-req-close r id inc s)) (mv-nth 0 (fn-rtc-req-close r id inc s)))
                (fn-rtc-actions-kinded-p (mv-nth 1 (fn-rtc-req-close r id inc s)))))
  :hints (("Goal" :in-theory (disable fn-rtc-live-p fn-rtc-slot fn-rtc-s-res fn-rtc-use-bound fn-rtc-action-argp))))

(defthm fn-rtc-buffer-reqs-actions-ok
  (and (fn-rtc-actions-okp (mv-nth 1 (fn-rtc-req-acquire r id inc s)) x)
       (fn-rtc-actions-kinded-p (mv-nth 1 (fn-rtc-req-acquire r id inc s)))
       (fn-rtc-actions-okp (mv-nth 1 (fn-rtc-req-write r id inc s)) x)
       (fn-rtc-actions-kinded-p (mv-nth 1 (fn-rtc-req-write r id inc s)))
       (fn-rtc-actions-okp (mv-nth 1 (fn-rtc-req-release r id inc s)) x)
       (fn-rtc-actions-kinded-p (mv-nth 1 (fn-rtc-req-release r id inc s))))
  :hints (("Goal" :in-theory (disable fn-rtc-req-acquire fn-rtc-req-write fn-rtc-req-release))))

(defthm fn-rtc-buffer-reqs-preconditions
  (and (equal (fn-rtc-s-res (fn-rtc-slot j (mv-nth 0 (fn-rtc-req-acquire r id inc s)))) (fn-rtc-s-res (fn-rtc-slot j s)))
       (equal (fn-rtc-s-res (fn-rtc-slot j (mv-nth 0 (fn-rtc-req-write r id inc s)))) (fn-rtc-s-res (fn-rtc-slot j s)))
       (equal (fn-rtc-s-res (fn-rtc-slot j (mv-nth 0 (fn-rtc-req-release r id inc s)))) (fn-rtc-s-res (fn-rtc-slot j s))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-slot) (fn-rtc-req-acquire fn-rtc-req-write fn-rtc-req-release fn-rtc-slots-is-slot)))))

(defun fn-rtc-req-pre (id inc s)
  (declare (xargs :guard t))
  (and (natp id) (natp inc)
       (fn-rtc-action-argp (fn-rtc-s-res (fn-rtc-slot id s)))
       (fn-rtc-uses-ops-natp (fn-rtc-uses s))))

(defthm fn-rtc-actions-okp-nil
  (and (fn-rtc-actions-okp nil s) (fn-rtc-actions-kinded-p nil)))

(defthm fn-rtc-req-cancel-actions-ok-s
  (implies (and (natp id) (natp inc) (fn-rtc-uses-ops-natp (fn-rtc-uses s)))
           (fn-rtc-actions-okp (mv-nth 1 (fn-rtc-req-cancel r id inc s)) s))
  :hints (("Goal" :use fn-rtc-req-cancel-actions-ok-fast
                  :in-theory (disable fn-rtc-req-cancel-actions-ok-fast fn-rtc-req-cancel))))

(defthm fn-rtc-request-actions-ok
  (implies (fn-rtc-req-pre id inc s)
           (and (fn-rtc-actions-okp (mv-nth 1 (fn-rtc-request r id inc s)) (mv-nth 0 (fn-rtc-request r id inc s)))
                (fn-rtc-actions-kinded-p (mv-nth 1 (fn-rtc-request r id inc s)))
                (fn-rtc-req-pre id inc (mv-nth 0 (fn-rtc-request r id inc s)))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-request)
                                  (mv-nth fn-rtc-req-acquire fn-rtc-req-write fn-rtc-req-release
                                   fn-rtc-req-close fn-rtc-req-cancel fn-rtc-req-submit fn-rtc-action-argp
                                   fn-rtc-uses-ops-natp fn-rtc-actions-okp fn-rtc-actions-kinded-p
                                   fn-rtc-s-res fn-rtc-slot)))))

(defthm fn-rtc-requests-actions-ok
  (implies (fn-rtc-req-pre id inc s)
           (and (fn-rtc-actions-okp (mv-nth 1 (fn-rtc-requests reqs id inc s)) (mv-nth 0 (fn-rtc-requests reqs id inc s)))
                (fn-rtc-actions-kinded-p (mv-nth 1 (fn-rtc-requests reqs id inc s)))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-requests)
                                  (mv-nth fn-rtc-request fn-rtc-req-pre fn-rtc-actions-okp fn-rtc-actions-kinded-p))
           :induct (fn-rtc-requests reqs id inc s))
          ("Subgoal *1/1'" :use ((:instance fn-rtc-actions-okp-of-subset
                                  (acts (mv-nth 1 (fn-rtc-request (car reqs) id inc s)))
                                  (s1 (mv-nth 0 (fn-rtc-request (car reqs) id inc s)))
                                  (s2 (mv-nth 0 (fn-rtc-requests (cdr reqs) id inc
                                                                 (mv-nth 0 (fn-rtc-request (car reqs) id inc s))))))
                                 (:instance fn-rtc-requests-grows-uses (reqs (cdr reqs))
                                  (s (mv-nth 0 (fn-rtc-request (car reqs) id inc s))))))))

