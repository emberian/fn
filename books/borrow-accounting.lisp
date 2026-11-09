; A2's accounting: the borrow count over the pool and ops children, and
; the per-operation lemmas (every pool writer, every ops writer, the issue,
; harvest and pool-writer children) the core-level keystone in
; borrow-conservation.lisp is assembled from. Only the children and the ops
; invariant are needed here, not the core stobj or the machines.
(in-package "ACL2")
(include-book "arm-children")
(include-book "ops-conservation")


(defun fn2-borrow-valsp (kind phase h0 p1 h1 aux0)
  (declare (xargs :guard t))
  (and (or (equal kind *fn2-action-send*) (equal kind *fn2-action-write*))
       (or (equal phase *fn2-op-phase-queued*) (equal phase *fn2-op-phase-submitted*)
           (equal phase *fn2-op-phase-release-pending*))
       (not (equal h1 1))
       (not (and (equal h0 1) (equal p1 0)
                 (not (and (equal kind *fn2-action-send*) (equal aux0 1)))))))
(defun fn2-op-borrowp (i fn2-ops)
  (declare (xargs :stobjs fn2-ops :verify-guards nil))
  (fn2-borrow-valsp (fn2-ops-kind i fn2-ops) (fn2-ops-phase i fn2-ops) (fn2-ops-c0-harvested i fn2-ops)
                    (fn2-ops-c1-posted i fn2-ops) (fn2-ops-c1-harvested i fn2-ops) (fn2-ops-c0-aux0 i fn2-ops)))
(defun fn2-op-borrow-on (i r fn2-ops)
  (declare (xargs :stobjs fn2-ops :verify-guards nil))
  (if (and (fn2-op-borrowp i fn2-ops) (equal (fn2-ops-range-slot i fn2-ops) r)) 1 0))
(defun fn2-ops-borrow-count (n r fn2-ops)
  (declare (xargs :stobjs fn2-ops :verify-guards nil :measure (nfix n)))
  (if (zp n) 0
    (+ (fn2-op-borrow-on (- n 1) r fn2-ops) (fn2-ops-borrow-count (- n 1) r fn2-ops))))
(defun-sk fn2-pool-borrows-countedp (pool ops)
  (forall r
    (implies (and (natp r) (< r (fn2-pool-rows pool)))
             (and (equal (fn2-pool-out-count r pool)
                         (fn2-ops-borrow-count (fn2-ops-rows ops) r ops))
                  (implies (< 0 (fn2-pool-out-count r pool))
                           (equal (fn2-pool-state r pool) *fn2-pool-state-leased-out*)))))
  :rewrite :direct)
(defun-sk fn2-ops-borrows-namedp (pool ops)
  (forall i
    (implies (and (natp i) (< i (fn2-ops-rows ops)))
             (and (implies (equal (fn2-ops-may-release i ops) 1)
                           (equal (fn2-ops-kind i ops) *fn2-action-send*))
                  (implies (fn2-op-borrowp i ops)
                           (and (natp (fn2-ops-range-slot i ops))
                                (< (fn2-ops-range-slot i ops) (fn2-pool-rows pool))
                                (equal (fn2-ops-range-gen i ops)
                                       (fn2-pool-gen (fn2-ops-range-slot i ops) pool)))))))
  :rewrite :direct)
(defun-nx fn2-borrows-accountedp (pool ops)
  (and (fn2-pool-borrows-countedp pool ops) (fn2-ops-borrows-namedp pool ops)))
(defun-nx fn2-op-borrow-key (i ops)
  (list (fn2-op-borrowp i ops) (fn2-ops-range-slot i ops) (fn2-ops-range-gen i ops)
        (fn2-ops-may-release i ops) (fn2-ops-kind i ops)))
(defun-sk fn2-ops-keys-except (s a b)
  (forall i (implies (and (natp i) (not (equal i s)))
                     (equal (fn2-op-borrow-key i b) (fn2-op-borrow-key i a))))
  :rewrite :direct)
(defthm fn2-ops-keys-except-reads
  (implies (and (fn2-ops-keys-except s a b) (natp i) (not (equal i s)))
           (and (equal (fn2-op-borrowp i b) (fn2-op-borrowp i a))
                (equal (fn2-ops-range-slot i b) (fn2-ops-range-slot i a))
                (equal (fn2-ops-range-gen i b) (fn2-ops-range-gen i a))
                (equal (fn2-ops-may-release i b) (fn2-ops-may-release i a))
                (equal (fn2-ops-kind i b) (fn2-ops-kind i a))
                (equal (fn2-op-borrow-on i r b) (fn2-op-borrow-on i r a))))
  :hints (("Goal" :use fn2-ops-keys-except-necc
           :in-theory (e/d (fn2-op-borrow-on) (fn2-ops-keys-except-necc fn2-op-borrowp fn2-ops-keys-except
                            fn2-ops-range-slot fn2-ops-range-gen fn2-ops-may-release fn2-ops-kind)))))
(in-theory (disable fn2-op-borrow-key))
(defthm fn2-ops-borrow-count-except
  (implies (and (fn2-ops-keys-except s a b) (natp s))
           (equal (fn2-ops-borrow-count n r b)
                  (if (< s (nfix n))
                      (+ (fn2-ops-borrow-count n r a)
                         (- (fn2-op-borrow-on s r b) (fn2-op-borrow-on s r a)))
                    (fn2-ops-borrow-count n r a))))
  :hints (("Goal" :induct (fn2-ops-borrow-count n r a)
           :in-theory (disable fn2-op-borrow-on fn2-ops-keys-except))))
(defthm fn2-ops-keys-except-trans
  (implies (and (fn2-ops-keys-except s a b) (fn2-ops-keys-except s b c))
           (fn2-ops-keys-except s a c))
  :hints (("Goal" :expand ((fn2-ops-keys-except s a c))
           :in-theory (disable fn2-ops-keys-except))))
(defthm fn2-ops-keys-except-refl
  (fn2-ops-keys-except s a a))
(defun-sk fn2-pool-keys-except (s a b)
  (forall r (implies (and (natp r) (not (equal r s)))
                     (and (equal (fn2-pool-out-count r b) (fn2-pool-out-count r a))
                          (equal (fn2-pool-state r b) (fn2-pool-state r a))
                          (equal (fn2-pool-gen r b) (fn2-pool-gen r a)))))
  :rewrite :direct)
(defthm fn2-pool-keys-except-refl (fn2-pool-keys-except s a a))
(deftheory fn2-borrow-readers
  '(fn2-ops-kind fn2-ops-phase fn2-ops-range-slot fn2-ops-range-gen fn2-ops-may-release
    fn2-ops-c0-harvested fn2-ops-c1-harvested fn2-ops-c1-posted fn2-ops-c0-aux0 fn2-ops-rows
    fn2-pool-out-count fn2-pool-state fn2-pool-gen fn2-pool-rows))
(in-theory (disable fn2-borrow-readers fn2-op-borrowp fn2-op-borrow-on fn2-borrow-valsp))
(defthm fn2-pool-borrows-countedp-transfer
  (implies (and (fn2-pool-borrows-countedp pool ops)
                (fn2-pool-keys-except ps pool pool2) (fn2-ops-keys-except j ops ops2)
                (natp j) (natp ps)
                (equal (fn2-pool-rows pool2) (fn2-pool-rows pool))
                (equal (fn2-ops-rows ops2) (fn2-ops-rows ops))
                (< j (fn2-ops-rows ops)) (natp (fn2-ops-rows ops))
                (implies (fn2-op-borrowp j ops) (equal (fn2-ops-range-slot j ops) ps))
                (implies (fn2-op-borrowp j ops2) (equal (fn2-ops-range-slot j ops2) ps))
                (implies (< ps (fn2-pool-rows pool))
                         (and (equal (fn2-pool-out-count ps pool2)
                                     (+ (fn2-pool-out-count ps pool)
                                        (- (fn2-op-borrow-on j ps ops2) (fn2-op-borrow-on j ps ops))))
                              (implies (< 0 (fn2-pool-out-count ps pool2))
                                       (equal (fn2-pool-state ps pool2) *fn2-pool-state-leased-out*)))))
           (fn2-pool-borrows-countedp pool2 ops2))
  :hints (("Goal" :in-theory (e/d (fn2-op-borrow-on) (fn2-pool-borrows-countedp fn2-pool-keys-except fn2-ops-keys-except))
           :expand ((fn2-pool-borrows-countedp pool2 ops2))
           :use ((:instance fn2-pool-borrows-countedp-necc
                            (r (fn2-pool-borrows-countedp-witness pool2 ops2)))
                 (:instance fn2-pool-keys-except-necc (s ps) (a pool) (b pool2)
                            (r (fn2-pool-borrows-countedp-witness pool2 ops2))))
           :cases ((equal (fn2-pool-borrows-countedp-witness pool2 ops2) ps)))))
(defthm fn2-ops-borrows-namedp-transfer
  (implies (and (fn2-ops-borrows-namedp pool ops)
                (fn2-pool-keys-except ps pool pool2) (fn2-ops-keys-except j ops ops2)
                (natp j)
                (equal (fn2-pool-rows pool2) (fn2-pool-rows pool))
                (equal (fn2-ops-rows ops2) (fn2-ops-rows ops))
                (equal (fn2-pool-gen ps pool2) (fn2-pool-gen ps pool))
                (implies (equal (fn2-ops-may-release j ops2) 1)
                         (equal (fn2-ops-kind j ops2) *fn2-action-send*))
                (implies (fn2-op-borrowp j ops2)
                         (and (natp (fn2-ops-range-slot j ops2))
                              (< (fn2-ops-range-slot j ops2) (fn2-pool-rows pool))
                              (equal (fn2-ops-range-gen j ops2)
                                     (fn2-pool-gen (fn2-ops-range-slot j ops2) pool2)))))
           (fn2-ops-borrows-namedp pool2 ops2))
  :hints (("Goal" :in-theory (disable fn2-ops-borrows-namedp fn2-pool-keys-except fn2-ops-keys-except)
           :expand ((fn2-ops-borrows-namedp pool2 ops2))
           :use ((:instance fn2-ops-borrows-namedp-necc
                            (i (fn2-ops-borrows-namedp-witness pool2 ops2)))
                 (:instance fn2-pool-keys-except-necc (s ps) (a pool) (b pool2)
                            (r (fn2-ops-range-slot (fn2-ops-borrows-namedp-witness pool2 ops2) ops))))
           :cases ((equal (fn2-ops-borrows-namedp-witness pool2 ops2) j)
                   (and (not (equal (fn2-ops-borrows-namedp-witness pool2 ops2) j))
                        (equal (fn2-ops-range-slot (fn2-ops-borrows-namedp-witness pool2 ops2) ops) ps))))))

(deftheory fn2-ops-writers '(fn2-ops-set-gen fn2-ops-set-phase fn2-ops-set-kind fn2-ops-set-owner-kind fn2-ops-set-owner-slot fn2-ops-set-owner-gen fn2-ops-set-principal fn2-ops-set-range-slot fn2-ops-set-range-gen fn2-ops-set-range-off fn2-ops-set-range-len fn2-ops-set-cap-index fn2-ops-set-cap-nonce fn2-ops-set-storage-offset fn2-ops-set-fua fn2-ops-set-may-release fn2-ops-set-cancel-slot fn2-ops-set-cancel-gen fn2-ops-set-cancel-requested fn2-ops-set-c0-posted fn2-ops-set-c0-harvested fn2-ops-set-c0-event fn2-ops-set-c0-outcome fn2-ops-set-c0-reason fn2-ops-set-c0-count fn2-ops-set-c0-aux0 fn2-ops-set-c0-aux1 fn2-ops-set-peer-family fn2-ops-set-peer-port fn2-ops-set-peer-w0 fn2-ops-set-peer-w1 fn2-ops-set-peer-w2 fn2-ops-set-peer-w3 fn2-ops-set-c1-posted fn2-ops-set-c1-harvested fn2-ops-set-c1-event fn2-ops-set-c1-outcome fn2-ops-set-c1-reason fn2-ops-set-c1-count fn2-ops-set-c1-aux0 fn2-ops-set-c1-aux1 fn2-ops-set-next-free fn2-ops-set-wake-deadline fn2-ops-set-wake-observation-gen update-fn2-ops-gen$ai update-fn2-ops-phase$ai update-fn2-ops-kind$ai update-fn2-ops-owner-kind$ai update-fn2-ops-owner-slot$ai update-fn2-ops-owner-gen$ai update-fn2-ops-principal$ai update-fn2-ops-range-slot$ai update-fn2-ops-range-gen$ai update-fn2-ops-range-off$ai update-fn2-ops-range-len$ai update-fn2-ops-cap-index$ai update-fn2-ops-cap-nonce$ai update-fn2-ops-storage-offset$ai update-fn2-ops-fua$ai update-fn2-ops-may-release$ai update-fn2-ops-cancel-slot$ai update-fn2-ops-cancel-gen$ai update-fn2-ops-cancel-requested$ai update-fn2-ops-c0-posted$ai update-fn2-ops-c0-harvested$ai update-fn2-ops-c0-event$ai update-fn2-ops-c0-outcome$ai update-fn2-ops-c0-reason$ai update-fn2-ops-c0-count$ai update-fn2-ops-c0-aux0$ai update-fn2-ops-c0-aux1$ai update-fn2-ops-peer-family$ai update-fn2-ops-peer-port$ai update-fn2-ops-peer-w0$ai update-fn2-ops-peer-w1$ai update-fn2-ops-peer-w2$ai update-fn2-ops-peer-w3$ai update-fn2-ops-c1-posted$ai update-fn2-ops-c1-harvested$ai update-fn2-ops-c1-event$ai update-fn2-ops-c1-outcome$ai update-fn2-ops-c1-reason$ai update-fn2-ops-c1-count$ai update-fn2-ops-c1-aux0$ai update-fn2-ops-c1-aux1$ai update-fn2-ops-next-free$ai update-fn2-ops-wake-deadline$ai update-fn2-ops-wake-observation-gen$ai update-fn2-ops-out-head update-fn2-ops-out-tail update-fn2-ops-queued update-fn2-ops-reserved-credits update-fn2-ops-post-head update-fn2-ops-post-tail update-fn2-ops-post-count update-fn2-ops-clock-posted update-fn2-ops-clock-seen update-fn2-ops-clock-mono update-fn2-ops-clock-real update-fn2-ops-clock-flags update-fn2-ops-clock-coalesced update-fn2-ops-clock-rejected update-fn2-ops-signals update-fn2-ops-stray update-fn2-ops-seen-peer-family update-fn2-ops-seen-peer-port update-fn2-ops-seen-peer-w0 update-fn2-ops-seen-peer-w1 update-fn2-ops-seen-peer-w2 update-fn2-ops-seen-peer-w3 update-fn2-ops-free-head update-fn2-ops-free-count update-fn2-ops-gen-limit update-fn2-ops-retired-count update-fn2-ops-out-sloti update-fn2-ops-out-geni update-fn2-ops-posted-fifoi))
(defthm fn2-bc-nth-of-update-nth-array
  (equal (nth j (update-nth-array k i v l))
         (if (equal (nfix j) (nfix k)) (update-nth i v (nth k l)) (nth j l))))
(defthm fn2-ops-peek-posted-slot
  (implies (equal (car (fn2-ops-peek-posted ops)) t)
           (and (natp (mv-nth 1 (fn2-ops-peek-posted ops)))
                (< (mv-nth 1 (fn2-ops-peek-posted ops)) (fn2-ops-rows ops))
                (or (equal (mv-nth 2 (fn2-ops-peek-posted ops)) 0)
                    (equal (mv-nth 2 (fn2-ops-peek-posted ops)) 1))))
  :rule-classes ((:rewrite) (:forward-chaining :trigger-terms ((fn2-ops-peek-posted ops))))
  :hints (("Goal" :in-theory (enable fn2-ops-peek-posted fn2-op-slotp fn2-borrow-readers))))
(defthm fn2-ops-peek-posted-cell
  (implies (equal (car (fn2-ops-peek-posted ops)) t)
           (let ((j (mv-nth 1 (fn2-ops-peek-posted ops))))
             (if (equal (mv-nth 2 (fn2-ops-peek-posted ops)) 0)
                 (and (equal (fn2-ops-c0-posted j ops) 1) (equal (fn2-ops-c0-harvested j ops) 0))
               (and (equal (fn2-ops-c1-posted j ops) 1) (equal (fn2-ops-c1-harvested j ops) 0)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn2-ops-peek-posted fn2-op-slotp fn2-borrow-readers))))
(defthm fn2-op-borrow-key-of-update-nth-array-other
  (implies (and (natp i) (natp s) (not (equal i s)))
           (equal (fn2-op-borrow-key i (update-nth-array k s v x)) (fn2-op-borrow-key i x)))
  :hints (("Goal" :in-theory (e/d (fn2-borrow-readers fn2-op-borrowp fn2-op-borrow-key) (update-nth-array)))))
(defthm fn2-op-borrow-key-of-update-nth-array-scalar
  (implies (and (natp k) (<= 44 k))
           (equal (fn2-op-borrow-key i (update-nth-array k s v x)) (fn2-op-borrow-key i x)))
  :hints (("Goal" :in-theory (e/d (fn2-borrow-readers fn2-op-borrowp fn2-op-borrow-key) ()))))
(defthm fn2-op-borrow-key-of-update-nth-scalar
  (implies (and (natp k) (<= 44 k))
           (equal (fn2-op-borrow-key i (update-nth k v x)) (fn2-op-borrow-key i x)))
  :hints (("Goal" :in-theory (e/d (fn2-borrow-readers fn2-op-borrowp fn2-op-borrow-key) ()))))
(defun fn2-harvest-phase-of (h0 h1 p1 kind aux0)
  (cond ((equal h0 0) *fn2-op-phase-submitted*)
        ((and (equal h1 0) (or (equal p1 1) (and (equal kind *fn2-action-send*) (equal aux0 1))))
         *fn2-op-phase-release-pending*)
        (t *fn2-op-phase-done*)))
(defthm fn2-bc-latch-peer-columns
  (implies (and (natp c) (< c 64))
           (equal (nth c (fn2-ops-latch-peer cell slot x)) (nth c x)))
  :hints (("Goal" :in-theory (enable fn2-ops-latch-peer fn2-ops-writers))))
(defthm fn2-bc-latch-peer-scalars
  (implies (and (natp c) (<= 70 c))
           (equal (nth c (fn2-ops-latch-peer cell slot x)) (nth c x)))
  :hints (("Goal" :in-theory (enable fn2-ops-latch-peer fn2-ops-writers))))
(defthm fn2-bc-harvest-phase-by-vals
  (equal (fn2-op-harvest-phase slot x)
         (fn2-harvest-phase-of (nth slot (nth 20 x)) (nth slot (nth 34 x)) (nth slot (nth 33 x))
                               (nth slot (nth 2 x)) (nth slot (nth 25 x))))
  :hints (("Goal" :in-theory (enable fn2-op-harvest-phase fn2-borrow-readers fn2-harvest-phase-of))))
(defthm fn2-op-borrow-key-of-latch-peer
  (equal (fn2-op-borrow-key i (fn2-ops-latch-peer cell slot x)) (fn2-op-borrow-key i x))
  :hints (("Goal" :in-theory (e/d (fn2-borrow-readers fn2-op-borrowp fn2-op-borrow-key) (fn2-ops-latch-peer)))))
(defthm fn2-harvest-next-keys-other
  (implies (and (natp i) (not (equal i (mv-nth 1 (fn2-harvest-next ops)))))
           (equal (fn2-op-borrow-key i (mv-nth 4 (fn2-harvest-next ops)))
                  (fn2-op-borrow-key i ops)))
  :hints (("Goal" :in-theory (e/d (fn2-ops-writers fn2-harvest-next)
                                  (update-nth-array fn2-ops-peek-posted fn2-ops-latch-peer
                                   fn2-op-harvest-phase)))))
(defthm fn2-harvest-next-keys-except
  (fn2-ops-keys-except (mv-nth 1 (fn2-harvest-next ops)) ops (mv-nth 4 (fn2-harvest-next ops)))
  :hints (("Goal" :in-theory (e/d (fn2-ops-keys-except) (fn2-harvest-next fn2-harvest-next-keys-other))
           :use ((:instance fn2-harvest-next-keys-other
                  (i (fn2-ops-keys-except-witness (mv-nth 1 (fn2-harvest-next ops)) ops
                                                  (mv-nth 4 (fn2-harvest-next ops)))))))))
(defun-nx fn2-bc-row-body (j ops)
  (let* ((slot j) (phase (fn2-ops-phase slot ops))
           (p0 (fn2-ops-c0-posted slot ops))
           (h0 (fn2-ops-c0-harvested slot ops))
           (p1 (fn2-ops-c1-posted slot ops))
           (h1 (fn2-ops-c1-harvested slot ops))
           (may (fn2-ops-may-release slot ops))
           (pending (and (equal (fn2-ops-kind slot ops) *fn2-action-send*)
                         (equal (fn2-ops-c0-aux0 slot ops) 1))))
      (and            (< phase *fn2-op-phase-count*) (< (fn2-ops-kind slot ops) *fn2-action-count*)
           (<= (fn2-ops-gen slot ops) (fn2-ops-gen-limit ops))
           (<= h0 p0) (<= h1 p1) (<= p1 may)
           (implies (equal p0 1)
                    (fn2-post-payloadp 0 slot (fn2-ops-c0-event slot ops)
                      (fn2-ops-c0-outcome slot ops) (fn2-ops-c0-reason slot ops)
                      (fn2-ops-c0-count slot ops) (fn2-ops-c0-aux0 slot ops)
                      (fn2-ops-c0-aux1 slot ops) ops))
           (implies (equal p1 1)
                    (fn2-post-payloadp 1 slot (fn2-ops-c1-event slot ops)
                      (fn2-ops-c1-outcome slot ops) (fn2-ops-c1-reason slot ops)
                      (fn2-ops-c1-count slot ops) (fn2-ops-c1-aux0 slot ops)
                      (fn2-ops-c1-aux1 slot ops) ops))
           (< (fn2-ops-c0-event slot ops) *fn2-event-count*)
           (< (fn2-ops-c1-event slot ops) *fn2-event-count*)
           (< (fn2-ops-c0-outcome slot ops) *fn2-outcome-count*)
           (< (fn2-ops-c1-outcome slot ops) *fn2-outcome-count*)
           (< (fn2-ops-c0-reason slot ops) *fn2-reason-count*)
           (< (fn2-ops-c1-reason slot ops) *fn2-reason-count*)
           (implies (member-equal phase (list *fn2-op-phase-free* *fn2-op-phase-reserved* *fn2-op-phase-queued*))
                    (and (equal p0 0) (equal h0 0) (equal p1 0) (equal h1 0)))
           (implies (equal phase *fn2-op-phase-submitted*) (equal h0 0))
           (implies (equal phase *fn2-op-phase-release-pending*)
                    (and (equal h0 1) (equal h1 0) (equal may 1)
                         (or pending (equal p1 1))))
           (implies (equal phase *fn2-op-phase-done*)
                    (if (fn2-action-completionp (fn2-ops-kind slot ops))
                        (and (equal h0 1) (equal p1 h1)
                             (implies pending (equal h1 1)))
                      (and (equal p0 0) (equal h0 0) (equal p1 0) (equal h1 0))))
           (implies (equal phase *fn2-op-phase-retired*)
                    (and (equal (fn2-ops-gen slot ops) (fn2-ops-gen-limit ops))
                         (equal p0 h0) (equal p1 h1)))
           t)))
(defthm fn2-ops-row-semanticp-by-body
  (equal (fn2-ops-row-semanticp n ops)
         (if (zp n) t
           (and (fn2-ops-row-semanticp (- n 1) ops) (fn2-bc-row-body (- n 1) ops))))
  :rule-classes ((:definition :controller-alist ((fn2-ops-row-semanticp t nil))))
  :hints (("Goal" :expand ((fn2-ops-row-semanticp n ops))
           :in-theory (union-theories '(fn2-bc-row-body) (theory 'minimal-theory)))))
(in-theory (disable fn2-bc-row-body))
(defthm fn2-bc-row-body-cell-facts
  (implies (and (fn2-bc-row-body j ops) (fn2-opsp ops) (fn2-ops-wfp ops)
                (natp j) (< j (fn2-ops-rows ops)))
           (and (implies (and (equal (fn2-ops-c0-posted j ops) 1) (equal (fn2-ops-c0-harvested j ops) 0))
                         (and (equal (fn2-ops-phase j ops) *fn2-op-phase-submitted*)
                              (equal (fn2-ops-c0-event j ops) (fn2-terminal-event (fn2-ops-kind j ops)))
                              (implies (equal (fn2-ops-c0-event j ops) *fn2-event-send-result*)
                                       (unsigned-byte-p 1 (fn2-ops-c0-aux0 j ops)))))
                (implies (and (equal (fn2-ops-c1-posted j ops) 1) (equal (fn2-ops-c1-harvested j ops) 0))
                         (and (or (equal (fn2-ops-phase j ops) *fn2-op-phase-submitted*)
                                  (equal (fn2-ops-phase j ops) *fn2-op-phase-release-pending*))
                              (implies (equal (fn2-ops-phase j ops) *fn2-op-phase-submitted*)
                                       (equal (fn2-ops-c0-harvested j ops) 0))
                              (implies (equal (fn2-ops-phase j ops) *fn2-op-phase-release-pending*)
                                       (equal (fn2-ops-c0-harvested j ops) 1))
                              (equal (fn2-ops-c1-event j ops) *fn2-event-borrow-released*)
                              (equal (fn2-ops-may-release j ops) 1)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-bc-row-body fn2-post-payloadp)
                                  (fn2-event-statusp fn2-terminal-event fn2-action-completionp
                                   fn2-ops-range-len fn2-ops-c0-event fn2-ops-c1-event fn2-ops-c0-posted
                                   fn2-ops-gen fn2-ops-gen-limit fn2-ops-c0-outcome fn2-ops-c1-outcome
                                   fn2-ops-c0-reason fn2-ops-c1-reason fn2-ops-c0-count fn2-ops-c1-count
                                   fn2-ops-c0-aux1 fn2-ops-c1-aux0 fn2-ops-c1-aux1 unsigned-byte-p)))))
(defthm fn2-ops-row-semanticp-body-at
  (implies (and (fn2-ops-row-semanticp n ops) (natp j) (< j n) (natp n))
           (fn2-bc-row-body j ops))
  :hints (("Goal" :induct (fn2-ops-row-semanticp n ops)
           :in-theory (enable fn2-ops-row-semanticp-by-body))))
(deftheory fn2-pool-writers '(fn2-pool-set-gen fn2-pool-set-base fn2-pool-set-cap fn2-pool-set-state fn2-pool-set-owner-kind fn2-pool-set-owner-slot fn2-pool-set-owner-gen fn2-pool-set-lease-op-slot fn2-pool-set-lease-op-gen fn2-pool-set-lease-off fn2-pool-set-lease-len fn2-pool-set-out-count fn2-pool-set-fill fn2-pool-set-hand-to-kind fn2-pool-set-hand-to-slot fn2-pool-set-hand-to-gen fn2-pool-set-next-free fn2-pool-set-class update-fn2-pool-gen$ai update-fn2-pool-base$ai update-fn2-pool-cap$ai update-fn2-pool-state$ai update-fn2-pool-owner-kind$ai update-fn2-pool-owner-slot$ai update-fn2-pool-owner-gen$ai update-fn2-pool-lease-op-slot$ai update-fn2-pool-lease-op-gen$ai update-fn2-pool-lease-off$ai update-fn2-pool-lease-len$ai update-fn2-pool-out-count$ai update-fn2-pool-fill$ai update-fn2-pool-hand-to-kind$ai update-fn2-pool-hand-to-slot$ai update-fn2-pool-hand-to-gen$ai update-fn2-pool-next-free$ai update-fn2-pool-class$ai))
(defthm fn2-pool-keys-except-of-row-write
  (implies (natp s)
           (fn2-pool-keys-except s x (update-nth-array k s v x)))
  :hints (("Goal" :in-theory (e/d (fn2-pool-keys-except fn2-borrow-readers) (update-nth-array)))))
(defthm fn2-pool-release-out-effect
  (let* ((r (fn2-pool-release-out slot gen pool)) (q (mv-nth 1 r)))
    (and (fn2-pool-keys-except slot pool q)
         (equal (fn2-pool-rows q) (fn2-pool-rows pool))
         (equal (fn2-pool-gen slot q) (fn2-pool-gen slot pool))
         (iff (equal (mv-nth 0 r) :ok)
              (and (natp slot) (< slot (fn2-pool-rows pool)) (equal gen (fn2-pool-gen slot pool))
                   (equal (fn2-pool-state slot pool) *fn2-pool-state-leased-out*)
                   (not (equal (fn2-pool-out-count slot pool) 0))))
         (implies (not (equal (mv-nth 0 r) :ok)) (equal q pool))
         (implies (equal (mv-nth 0 r) :ok)
                  (and (equal (fn2-pool-out-count slot q) (- (fn2-pool-out-count slot pool) 1))
                       (equal (fn2-pool-state slot q)
                              (if (equal (fn2-pool-out-count slot pool) 1)
                                  *fn2-pool-state-workspace* *fn2-pool-state-leased-out*))))))
  :hints (("Goal" :in-theory (e/d (fn2-pool-writers fn2-borrow-readers fn2-pool-release-out fn2-pool-handle-code)
                                  (update-nth-array)))))
(defthm fn2-pool-complete-in-effect
  (let* ((r (fn2-pool-complete-in slot gen opslot opgen n pool)) (q (mv-nth 1 r)))
    (and (fn2-pool-keys-except slot pool q)
         (equal (fn2-pool-rows q) (fn2-pool-rows pool))
         (equal (fn2-pool-gen slot q) (fn2-pool-gen slot pool))
         (equal (fn2-pool-out-count slot q) (fn2-pool-out-count slot pool))
         (implies (not (equal (fn2-pool-state slot pool) *fn2-pool-state-leased-in*))
                  (equal (fn2-pool-state slot q) (fn2-pool-state slot pool)))))
  :hints (("Goal" :in-theory (e/d (fn2-pool-writers fn2-borrow-readers fn2-pool-complete-in fn2-pool-input-code
                                   fn2-pool-handle-code)
                                  (update-nth-array)))))
(defthm fn2-pool-lease-out-effect
  (let* ((r (fn2-pool-lease-out slot gen off len okind oslot ogen pool)) (q (mv-nth 1 r)))
    (and (fn2-pool-keys-except slot pool q)
         (equal (fn2-pool-rows q) (fn2-pool-rows pool))
         (equal (fn2-pool-gen slot q) (fn2-pool-gen slot pool))
         (implies (not (equal (mv-nth 0 r) :ok)) (equal q pool))
         (implies (equal (mv-nth 0 r) :ok)
                  (and (natp slot) (< slot (fn2-pool-rows pool)) (equal (fn2-pool-gen slot pool) gen)
                       (equal (fn2-pool-out-count slot q) (+ 1 (fn2-pool-out-count slot pool)))
                       (equal (fn2-pool-state slot q) *fn2-pool-state-leased-out*)))))
  :hints (("Goal" :in-theory (e/d (fn2-pool-writers fn2-borrow-readers fn2-pool-lease-out fn2-pool-readable-code
                                   fn2-pool-handle-code)
                                  (update-nth-array fn2-pool-ownerp)))))
(defthm fn2-pool-lease-in-effect
  (let* ((r (fn2-pool-lease-in slot gen len opslot opgen okind oslot ogen pool)) (q (mv-nth 2 r)))
    (and (fn2-pool-keys-except slot pool q)
         (equal (fn2-pool-rows q) (fn2-pool-rows pool))
         (equal (fn2-pool-gen slot q) (fn2-pool-gen slot pool))
         (equal (fn2-pool-out-count slot q) (fn2-pool-out-count slot pool))
         (implies (not (equal (fn2-pool-state slot pool) *fn2-pool-state-workspace*))
                  (equal (fn2-pool-state slot q) (fn2-pool-state slot pool)))
         (implies (not (equal (mv-nth 0 r) :ok)) (equal q pool))))
  :hints (("Goal" :in-theory (e/d (fn2-pool-writers fn2-borrow-readers fn2-pool-lease-in fn2-pool-workspace-code
                                   fn2-pool-handle-code)
                                  (update-nth-array fn2-pool-ownerp)))))
(defthm fn2-op-finish-keys-other
  (implies (and (natp i) (not (equal i slot)))
           (equal (fn2-op-borrow-key i (mv-nth 1 (fn2-op-finish slot gen ops)))
                  (fn2-op-borrow-key i ops)))
  :hints (("Goal" :in-theory (e/d (fn2-ops-writers fn2-op-finish fn2-op-recycle fn2-ops-clear-row
                                   fn2-op-phase-code fn2-op-handle-code fn2-op-slotp)
                                  (update-nth-array)))))
(defthm fn2-op-finish-keys-except
  (fn2-ops-keys-except slot ops (mv-nth 1 (fn2-op-finish slot gen ops)))
  :hints (("Goal" :in-theory (e/d (fn2-ops-keys-except) (fn2-op-finish fn2-op-finish-keys-other))
           :use ((:instance fn2-op-finish-keys-other
                  (i (fn2-ops-keys-except-witness slot ops (mv-nth 1 (fn2-op-finish slot gen ops)))))))))
(defthm fn2-op-finish-row
  (let* ((r (fn2-op-finish slot gen ops)) (q (mv-nth 1 r)))
    (and (equal (fn2-ops-rows q) (fn2-ops-rows ops))
         (implies (and (natp slot) (equal (fn2-ops-phase slot ops) *fn2-op-phase-done*))
                  (not (fn2-op-borrowp slot q)))
         (implies (equal (fn2-ops-may-release slot q) 1)
                  (and (equal (fn2-ops-may-release slot ops) 1)
                       (equal (fn2-ops-kind slot q) (fn2-ops-kind slot ops))))))
  :hints (("Goal" :in-theory (e/d (fn2-ops-writers fn2-borrow-readers fn2-op-finish fn2-op-recycle
                                   fn2-ops-clear-row fn2-op-phase-code fn2-op-handle-code fn2-op-slotp
                                   fn2-op-borrowp fn2-borrow-valsp)
                                  (update-nth-array)))))
(defthm fn2-ops-semanticp-row-facts
  (implies (fn2-ops-semanticp ops)
           (and (fn2-opsp ops) (fn2-ops-wfp ops) (natp (fn2-ops-rows ops))
                (fn2-ops-row-semanticp (fn2-ops-rows ops) ops)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn2-ops-semanticp fn2-borrow-readers))))
(defthm fn2-harvest-next-not-found
  (implies (not (equal (mv-nth 0 (fn2-harvest-next ops)) t))
           (equal (mv-nth 4 (fn2-harvest-next ops)) ops))
  :hints (("Goal" :in-theory (e/d (fn2-harvest-next) (fn2-ops-peek-posted fn2-ops-latch-peer fn2-ops-writers
                                                      fn2-op-harvest-phase)))))
(defthm fn2-ops-borrow-count-at-least
  (implies (and (natp j) (< j (nfix n)))
           (<= (fn2-op-borrow-on j r ops) (fn2-ops-borrow-count n r ops)))
  :rule-classes :linear
  :hints (("Goal" :induct (fn2-ops-borrow-count n r ops))))
(defthm fn2-harvest-finish-keys-except
  (fn2-ops-keys-except (mv-nth 1 (fn2-harvest-next ops)) ops
                       (mv-nth 1 (fn2-op-finish (mv-nth 1 (fn2-harvest-next ops)) g
                                                (mv-nth 4 (fn2-harvest-next ops)))))
  :hints (("Goal" :in-theory (disable fn2-harvest-next fn2-op-finish fn2-ops-keys-except)
           :use ((:instance fn2-ops-keys-except-trans (s (mv-nth 1 (fn2-harvest-next ops))) (a ops)
                            (b (mv-nth 4 (fn2-harvest-next ops)))
                            (c (mv-nth 1 (fn2-op-finish (mv-nth 1 (fn2-harvest-next ops)) g
                                                        (mv-nth 4 (fn2-harvest-next ops))))))))))

(defun-nx fn2-bc-input-condp (cell j q)
  (let ((ev (mv-nth 2 (fn2-op-cell cell j q))))
    (or (equal ev *fn2-event-receive-result*) (equal ev *fn2-event-read-result*)
        (equal ev *fn2-event-entropy-result*))))
(defun-nx fn2-bc-release-condp (cell j q)
  (let ((ev (mv-nth 2 (fn2-op-cell cell j q))) (aux0 (mv-nth 6 (fn2-op-cell cell j q)))
        (rp (mv-nth 0 (fn2-op-cell 1 j q))) (rh (mv-nth 1 (fn2-op-cell 1 j q))))
    (or (equal ev *fn2-event-borrow-released*)
        (and (equal rh 0) (equal rp 0)
             (or (equal ev *fn2-event-write-result*)
                 (and (equal ev *fn2-event-send-result*) (equal aux0 0)))))))
(defthm fn2-bc-input-not-release
  (implies (fn2-bc-input-condp cell j q) (not (fn2-bc-release-condp cell j q))))
(in-theory (disable fn2-bc-input-condp fn2-bc-release-condp))
(defun-nx fn2-bc-row-vals (j x)
  (list (fn2-ops-kind j x) (fn2-ops-phase j x) (fn2-ops-c0-posted j x) (fn2-ops-c0-harvested j x)
        (fn2-ops-c1-posted j x) (fn2-ops-c1-harvested j x) (fn2-ops-c0-aux0 j x)
        (fn2-ops-c0-event j x) (fn2-ops-c1-event j x) (fn2-ops-c1-aux0 j x)))
(defun fn2-bc-vals-borrowp (v)
  (fn2-borrow-valsp (nth 0 v) (nth 1 v) (nth 3 v) (nth 4 v) (nth 5 v) (nth 6 v)))
(defun fn2-bc-vals-release (cell v)
  (let ((ev (if (equal cell 0) (nth 7 v) (nth 8 v))) (aux (if (equal cell 0) (nth 6 v) (nth 9 v))))
    (or (equal ev *fn2-event-borrow-released*)
        (and (equal (nth 5 v) 0) (equal (nth 4 v) 0)
             (or (equal ev *fn2-event-write-result*)
                 (and (equal ev *fn2-event-send-result*) (equal aux 0)))))))
(defun fn2-bc-vals-after (cell v)
  (let* ((h0 (if (equal cell 0) 1 (nth 3 v))) (h1 (if (equal cell 1) 1 (nth 5 v))))
    (list (nth 0 v) (fn2-harvest-phase-of h0 h1 (nth 4 v) (nth 0 v) (nth 6 v)) (nth 2 v) h0
          (nth 4 v) h1 (nth 6 v) (nth 7 v) (nth 8 v) (nth 9 v))))
(defun fn2-bc-vals-okp (cell v)
  (let ((kind (nth 0 v)) (phase (nth 1 v)) (h0 (nth 3 v)) (p1 (nth 4 v)) (h1 (nth 5 v)))
    (and (or (equal cell 0) (equal cell 1))
         (natp h0) (< h0 2) (natp h1) (< h1 2) (natp p1) (< p1 2)
         (if (equal cell 0)
             (and (equal h0 0) (equal phase *fn2-op-phase-submitted*)
                  (equal (nth 7 v) (fn2-terminal-event kind))
                  (implies (equal (nth 7 v) *fn2-event-send-result*) (unsigned-byte-p 1 (nth 6 v))))
           (and (equal p1 1) (equal h1 0) (equal (nth 8 v) *fn2-event-borrow-released*)
                (equal kind *fn2-action-send*)
                (or (equal phase *fn2-op-phase-submitted*) (equal phase *fn2-op-phase-release-pending*))
                (implies (equal phase *fn2-op-phase-submitted*) (equal h0 0))
                (implies (equal phase *fn2-op-phase-release-pending*) (equal h0 1)))))))
(defthm fn2-bc-vals-harvest
  (implies (fn2-bc-vals-okp cell v)
           (and (implies (fn2-bc-vals-borrowp (fn2-bc-vals-after cell v)) (fn2-bc-vals-borrowp v))
                (iff (and (fn2-bc-vals-borrowp v) (not (fn2-bc-vals-borrowp (fn2-bc-vals-after cell v))))
                     (fn2-bc-vals-release cell (fn2-bc-vals-after cell v)))))
  :hints (("Goal" :in-theory (enable fn2-borrow-valsp fn2-terminal-event unsigned-byte-p))))
(in-theory (disable fn2-bc-vals-borrowp fn2-bc-vals-release fn2-bc-vals-after fn2-bc-vals-okp))
(defthm fn2-op-borrowp-by-vals
  (equal (fn2-op-borrowp j x) (fn2-bc-vals-borrowp (fn2-bc-row-vals j x)))
  :hints (("Goal" :in-theory (enable fn2-op-borrowp fn2-bc-vals-borrowp fn2-bc-row-vals))))
(defthm fn2-bc-release-condp-by-vals
  (equal (fn2-bc-release-condp cell j x) (fn2-bc-vals-release cell (fn2-bc-row-vals j x)))
  :hints (("Goal" :in-theory (enable fn2-bc-release-condp fn2-bc-vals-release fn2-bc-row-vals fn2-op-cell))))
(defthm fn2-bc-nth-cons-const
  (implies (syntaxp (quotep n))
           (equal (nth n (cons a b)) (if (zp n) a (nth (- n 1) b)))))
(defthm fn2-harvest-next-peek
  (implies (equal (mv-nth 0 (fn2-harvest-next ops)) t)
           (and (equal (car (fn2-ops-peek-posted ops)) t)
                (equal (mv-nth 1 (fn2-ops-peek-posted ops)) (mv-nth 1 (fn2-harvest-next ops)))
                (equal (mv-nth 2 (fn2-ops-peek-posted ops)) (mv-nth 3 (fn2-harvest-next ops)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-harvest-next) (fn2-ops-peek-posted fn2-ops-latch-peer fn2-ops-writers
                                                      fn2-op-harvest-phase)))))
(defthm fn2-harvest-next-row-vals-at
  (implies (and (equal (car (fn2-ops-peek-posted ops)) t) (equal (mv-nth 1 (fn2-ops-peek-posted ops)) j)
                (equal (mv-nth 2 (fn2-ops-peek-posted ops)) cell) (natp j) (or (equal cell 0) (equal cell 1)))
           (equal (fn2-bc-row-vals j (mv-nth 4 (fn2-harvest-next ops)))
                  (fn2-bc-vals-after cell (fn2-bc-row-vals j ops))))
  :hints (("Goal" :in-theory (union-theories
                               (union-theories (theory 'fn2-ops-writers) (theory 'fn2-borrow-readers))
                               (union-theories
                                '(fn2-bc-row-vals fn2-bc-vals-after fn2-harvest-next fn2-bc-latch-peer-columns fn2-bc-latch-peer-scalars
                                  fn2-bc-harvest-phase-by-vals fn2-ops-c0-posted fn2-ops-c0-event fn2-ops-c1-event
                                  fn2-ops-c1-aux0 fn2-bc-nth-of-update-nth-array nth-update-nth
                                  fn2-ops-kind$ai fn2-ops-phase$ai fn2-ops-c0-posted$ai fn2-ops-c0-harvested$ai
                                  fn2-ops-c1-posted$ai fn2-ops-c1-harvested$ai fn2-ops-c0-aux0$ai
                                  fn2-ops-c0-event$ai fn2-ops-c1-event$ai fn2-ops-c1-aux0$ai fn2-ops-gen
                                  fn2-ops-gen$ai nfix fn2-harvest-phase-of fn2-bc-nth-cons-const zp natp
                                  (:executable-counterpart nfix) (:executable-counterpart equal)
                                  (:executable-counterpart <) (:executable-counterpart not))
                                (theory 'minimal-theory))))))
(defthm fn2-harvest-next-row-keys-at
  (implies (and (equal (car (fn2-ops-peek-posted ops)) t) (equal (mv-nth 1 (fn2-ops-peek-posted ops)) j)
                (natp j))
           (let ((q (mv-nth 4 (fn2-harvest-next ops))))
             (and (equal (fn2-ops-kind j q) (fn2-ops-kind j ops))
                  (equal (fn2-ops-range-slot j q) (fn2-ops-range-slot j ops))
                  (equal (fn2-ops-range-gen j q) (fn2-ops-range-gen j ops))
                  (equal (fn2-ops-may-release j q) (fn2-ops-may-release j ops))
                  (equal (fn2-ops-rows q) (fn2-ops-rows ops)))))
  :hints (("Goal" :in-theory (union-theories
                               (union-theories (theory 'fn2-ops-writers) (theory 'fn2-borrow-readers))
                               (union-theories
                                '(fn2-harvest-next fn2-bc-latch-peer-columns fn2-bc-latch-peer-scalars
                                  fn2-bc-harvest-phase-by-vals fn2-bc-nth-of-update-nth-array nth-update-nth
                                  fn2-ops-kind$ai fn2-ops-phase$ai fn2-ops-range-slot$ai fn2-ops-range-gen$ai
                                  fn2-ops-may-release$ai fn2-ops-rows fn2-ops-gen fn2-ops-gen$ai nfix zp natp (:executable-counterpart natp)
                                  (:executable-counterpart nfix) (:executable-counterpart equal)
                                  (:executable-counterpart <) (:executable-counterpart not))
                                (theory 'minimal-theory))))))
(defthm fn2-harvest-next-found
  (implies (equal (mv-nth 0 (fn2-harvest-next ops)) t)
           (let ((q (mv-nth 4 (fn2-harvest-next ops))))
             (and (natp (mv-nth 1 (fn2-harvest-next ops))) (< (mv-nth 1 (fn2-harvest-next ops)) (fn2-ops-rows ops))
                  (or (equal (mv-nth 3 (fn2-harvest-next ops)) 0) (equal (mv-nth 3 (fn2-harvest-next ops)) 1))
                  (equal (fn2-ops-kind (mv-nth 1 (fn2-harvest-next ops)) q) (fn2-ops-kind (mv-nth 1 (fn2-harvest-next ops)) ops))
                  (equal (fn2-ops-range-slot (mv-nth 1 (fn2-harvest-next ops)) q) (fn2-ops-range-slot (mv-nth 1 (fn2-harvest-next ops)) ops))
                  (equal (fn2-ops-range-gen (mv-nth 1 (fn2-harvest-next ops)) q) (fn2-ops-range-gen (mv-nth 1 (fn2-harvest-next ops)) ops))
                  (equal (fn2-ops-may-release (mv-nth 1 (fn2-harvest-next ops)) q) (fn2-ops-may-release (mv-nth 1 (fn2-harvest-next ops)) ops))
                  (equal (fn2-ops-rows q) (fn2-ops-rows ops))
                  (equal (fn2-bc-row-vals (mv-nth 1 (fn2-harvest-next ops)) q) (fn2-bc-vals-after (mv-nth 3 (fn2-harvest-next ops)) (fn2-bc-row-vals (mv-nth 1 (fn2-harvest-next ops)) ops))))))
  :hints (("Goal" :in-theory (disable fn2-harvest-next fn2-ops-peek-posted fn2-harvest-next-row-keys-at
                                      fn2-harvest-next-row-vals-at)
           :use (fn2-harvest-next-peek (:instance fn2-ops-peek-posted-slot)
                 (:instance fn2-harvest-next-row-keys-at (j (mv-nth 1 (fn2-harvest-next ops))))
                 (:instance fn2-harvest-next-row-vals-at (j (mv-nth 1 (fn2-harvest-next ops))) (cell (mv-nth 3 (fn2-harvest-next ops))))))))
(defthm fn2-bc-vals-okp-of-row
  (implies (and (fn2-bc-row-body j ops) (fn2-opsp ops) (fn2-ops-wfp ops) (natp j) (< j (fn2-ops-rows ops))
                (or (equal cell 0) (equal cell 1))
                (implies (equal (fn2-ops-may-release j ops) 1) (equal (fn2-ops-kind j ops) *fn2-action-send*))
                (if (equal cell 0)
                    (and (equal (fn2-ops-c0-posted j ops) 1) (equal (fn2-ops-c0-harvested j ops) 0))
                  (and (equal (fn2-ops-c1-posted j ops) 1) (equal (fn2-ops-c1-harvested j ops) 0))))
           (fn2-bc-vals-okp cell (fn2-bc-row-vals j ops)))
  :hints (("Goal" :in-theory (e/d (fn2-bc-row-vals fn2-bc-vals-okp) (fn2-bc-row-body))
           :use ((:instance fn2-bc-row-body-cell-facts)
                 (:instance fn2-ops-c0-harvested-natp (i j) (fn2-ops ops))
                 (:instance fn2-ops-c0-harvested-bound (i j) (fn2-ops ops))
                 (:instance fn2-ops-c1-harvested-natp (i j) (fn2-ops ops))
                 (:instance fn2-ops-c1-harvested-bound (i j) (fn2-ops ops))
                 (:instance fn2-ops-c1-posted-natp (i j) (fn2-ops ops))
                 (:instance fn2-ops-c1-posted-bound (i j) (fn2-ops ops))))))
(defthm fn2-harvest-next-vals-okp
  (implies (and (fn2-ops-semanticp ops) (equal (mv-nth 0 (fn2-harvest-next ops)) t)
                (implies (equal (fn2-ops-may-release (mv-nth 1 (fn2-harvest-next ops)) ops) 1) (equal (fn2-ops-kind (mv-nth 1 (fn2-harvest-next ops)) ops) *fn2-action-send*)))
           (fn2-bc-vals-okp (mv-nth 3 (fn2-harvest-next ops)) (fn2-bc-row-vals (mv-nth 1 (fn2-harvest-next ops)) ops)))
  :hints (("Goal" :in-theory (union-theories '(fn2-ops-semanticp-row-facts) (theory 'minimal-theory))
           :use (fn2-harvest-next-found fn2-harvest-next-peek
                 (:instance fn2-ops-peek-posted-cell)
                 (:instance fn2-ops-row-semanticp-body-at (n (fn2-ops-rows ops)) (j (mv-nth 1 (fn2-harvest-next ops))))
                 (:instance fn2-bc-vals-okp-of-row (j (mv-nth 1 (fn2-harvest-next ops))) (cell (mv-nth 3 (fn2-harvest-next ops))))))))
(in-theory (disable fn2-bc-row-vals))
(defthm fn2-harvest-next-borrow-release
  (implies (and (fn2-ops-semanticp ops) (equal (mv-nth 0 (fn2-harvest-next ops)) t)
                (implies (equal (fn2-ops-may-release (mv-nth 1 (fn2-harvest-next ops)) ops) 1) (equal (fn2-ops-kind (mv-nth 1 (fn2-harvest-next ops)) ops) *fn2-action-send*)))
           (and (implies (fn2-op-borrowp (mv-nth 1 (fn2-harvest-next ops)) (mv-nth 4 (fn2-harvest-next ops))) (fn2-op-borrowp (mv-nth 1 (fn2-harvest-next ops)) ops))
                (iff (and (fn2-op-borrowp (mv-nth 1 (fn2-harvest-next ops)) ops) (not (fn2-op-borrowp (mv-nth 1 (fn2-harvest-next ops)) (mv-nth 4 (fn2-harvest-next ops)))))
                     (fn2-bc-release-condp (mv-nth 3 (fn2-harvest-next ops)) (mv-nth 1 (fn2-harvest-next ops)) (mv-nth 4 (fn2-harvest-next ops))))))
  :hints (("Goal" :in-theory (disable fn2-harvest-next fn2-ops-semanticp)
           :use (fn2-harvest-next-found fn2-harvest-next-vals-okp
                 (:instance fn2-bc-vals-harvest (cell (mv-nth 3 (fn2-harvest-next ops))) (v (fn2-bc-row-vals (mv-nth 1 (fn2-harvest-next ops)) ops)))))))
(defun-nx fn2-bc-harvest-pool-step (pool ops)
  (b* (((mv found j g cell q) (fn2-harvest-next ops))
       ((unless (and (eq found t) (fn2-op-slotp j q) (unsigned-byte-p 1 cell))) (mv :ok pool))
       ((mv ?p ?h ?ev outcome ?r count ?aux0 ?a1) (fn2-op-cell cell j q))
       ((mv slot gen ?off ?len) (fn2-op-range j q)))
    (cond ((fn2-bc-input-condp cell j q)
           (fn2-pool-complete-in slot gen j g
             (if (or (equal outcome *fn2-outcome-failed*) (equal outcome *fn2-outcome-cancelled*)) 0 count)
             pool))
          ((fn2-bc-release-condp cell j q) (fn2-pool-release-out slot gen pool))
          (t (mv :ok pool)))))
(defun-nx fn2-bc-harvest-ops (pool ops)
  (b* (((mv found j g cell q) (fn2-harvest-next ops))
       ((unless (and (eq found t) (fn2-op-slotp j q) (unsigned-byte-p 1 cell))) q)
       ((mv code ?p) (fn2-bc-harvest-pool-step pool ops))
       ((unless (eq code :ok)) q))
    (if (equal (fn2-op-phase j q) *fn2-op-phase-done*) (mv-nth 1 (fn2-op-finish j g q)) q)))
(defthm fn2-bc-harvest-pool-frame
  (and (fn2-pool-keys-except (fn2-ops-range-slot (mv-nth 1 (fn2-harvest-next ops)) ops) pool (mv-nth 1 (fn2-bc-harvest-pool-step pool ops)))
       (equal (fn2-pool-rows (mv-nth 1 (fn2-bc-harvest-pool-step pool ops))) (fn2-pool-rows pool))
       (equal (fn2-pool-gen (fn2-ops-range-slot (mv-nth 1 (fn2-harvest-next ops)) ops) (mv-nth 1 (fn2-bc-harvest-pool-step pool ops))) (fn2-pool-gen (fn2-ops-range-slot (mv-nth 1 (fn2-harvest-next ops)) ops) pool)))
  :hints (("Goal" :cases ((equal (mv-nth 0 (fn2-harvest-next ops)) t))
           :in-theory (e/d (fn2-bc-harvest-pool-step fn2-op-range fn2-op-slotp) (fn2-harvest-next fn2-op-finish fn2-pool-release-out fn2-pool-complete-in
                            fn2-borrows-accountedp fn2-pool-borrows-countedp fn2-op-borrowp-by-vals
                            fn2-bc-release-condp-by-vals
                            fn2-ops-borrows-namedp fn2-ops-semanticp fn2-ops-keys-except fn2-pool-keys-except
                            fn2-op-cell fn2-bc-input-condp fn2-bc-release-condp)))))
(defthm fn2-bc-harvest-ops-frame
  (and (fn2-ops-keys-except (mv-nth 1 (fn2-harvest-next ops)) ops (fn2-bc-harvest-ops pool ops))
       (equal (fn2-ops-rows (fn2-bc-harvest-ops pool ops)) (fn2-ops-rows ops)))
  :hints (("Goal" :cases ((equal (mv-nth 0 (fn2-harvest-next ops)) t))
           :in-theory (e/d (fn2-bc-harvest-ops fn2-op-slotp) (fn2-harvest-next fn2-op-finish fn2-pool-release-out fn2-pool-complete-in
                            fn2-borrows-accountedp fn2-pool-borrows-countedp fn2-op-borrowp-by-vals
                            fn2-bc-release-condp-by-vals
                            fn2-ops-borrows-namedp fn2-ops-semanticp fn2-ops-keys-except fn2-pool-keys-except
                            fn2-op-cell fn2-bc-input-condp fn2-bc-release-condp fn2-bc-harvest-pool-step)))))
(defthm fn2-op-borrowp-when-done
  (implies (equal (fn2-ops-phase j x) *fn2-op-phase-done*) (not (fn2-op-borrowp j x)))
  :hints (("Goal" :in-theory (e/d (fn2-op-borrowp fn2-borrow-valsp) (fn2-op-borrowp-by-vals)))))
(defthm fn2-bc-harvest-ops-row
  (implies (equal (mv-nth 0 (fn2-harvest-next ops)) t)
           (and (iff (fn2-op-borrowp (mv-nth 1 (fn2-harvest-next ops)) (fn2-bc-harvest-ops pool ops)) (fn2-op-borrowp (mv-nth 1 (fn2-harvest-next ops)) (mv-nth 4 (fn2-harvest-next ops))))
                (implies (fn2-op-borrowp (mv-nth 1 (fn2-harvest-next ops)) (fn2-bc-harvest-ops pool ops))
                         (and (equal (fn2-ops-range-slot (mv-nth 1 (fn2-harvest-next ops)) (fn2-bc-harvest-ops pool ops)) (fn2-ops-range-slot (mv-nth 1 (fn2-harvest-next ops)) ops))
                              (equal (fn2-ops-range-gen (mv-nth 1 (fn2-harvest-next ops)) (fn2-bc-harvest-ops pool ops)) (fn2-ops-range-gen (mv-nth 1 (fn2-harvest-next ops)) ops))))
                (implies (equal (fn2-ops-may-release (mv-nth 1 (fn2-harvest-next ops)) (fn2-bc-harvest-ops pool ops)) 1)
                         (and (equal (fn2-ops-may-release (mv-nth 1 (fn2-harvest-next ops)) ops) 1)
                              (equal (fn2-ops-kind (mv-nth 1 (fn2-harvest-next ops)) (fn2-bc-harvest-ops pool ops)) (fn2-ops-kind (mv-nth 1 (fn2-harvest-next ops)) ops))))))
  :hints (("Goal" :in-theory (union-theories '(fn2-bc-harvest-ops fn2-op-phase) (theory 'minimal-theory))
           :use (fn2-harvest-next-found
                 (:instance fn2-op-finish-row (slot (mv-nth 1 (fn2-harvest-next ops))) (gen (mv-nth 2 (fn2-harvest-next ops))) (ops (mv-nth 4 (fn2-harvest-next ops))))
                 (:instance fn2-op-borrowp-when-done (j (mv-nth 1 (fn2-harvest-next ops))) (x (mv-nth 4 (fn2-harvest-next ops))))))))
(defthm fn2-bc-release-out-ok
  (implies (and (fn2-borrows-accountedp pool ops) (fn2-op-borrowp j ops)
                (natp j) (< j (fn2-ops-rows ops)) (natp (fn2-ops-rows ops)))
           (equal (mv-nth 0 (fn2-pool-release-out (fn2-ops-range-slot j ops)
                                                  (fn2-pool-gen (fn2-ops-range-slot j ops) pool) pool))
                  :ok))
  :hints (("Goal" :in-theory (e/d (fn2-borrows-accountedp fn2-op-borrow-on)
                                  (fn2-pool-release-out fn2-pool-borrows-countedp fn2-ops-borrows-namedp
                                   fn2-ops-borrow-count-at-least fn2-op-borrowp-by-vals))
           :use ((:instance fn2-ops-borrows-namedp-necc (i j))
                 (:instance fn2-pool-borrows-countedp-necc (r (fn2-ops-range-slot j ops)))
                 (:instance fn2-ops-borrow-count-at-least (r (fn2-ops-range-slot j ops)) (n (fn2-ops-rows ops)))
                 (:instance fn2-pool-release-out-effect (slot (fn2-ops-range-slot j ops))
                            (gen (fn2-pool-gen (fn2-ops-range-slot j ops) pool)))))))
(defthm fn2-bc-harvest-pool-count
  (implies (and (fn2-ops-semanticp ops) (fn2-borrows-accountedp pool ops) (equal (mv-nth 0 (fn2-harvest-next ops)) t)
                (< (fn2-ops-range-slot (mv-nth 1 (fn2-harvest-next ops)) ops) (fn2-pool-rows pool)))
           (and (equal (fn2-pool-out-count (fn2-ops-range-slot (mv-nth 1 (fn2-harvest-next ops)) ops) (mv-nth 1 (fn2-bc-harvest-pool-step pool ops)))
                       (- (fn2-pool-out-count (fn2-ops-range-slot (mv-nth 1 (fn2-harvest-next ops)) ops) pool) (if (fn2-bc-release-condp (mv-nth 3 (fn2-harvest-next ops)) (mv-nth 1 (fn2-harvest-next ops)) (mv-nth 4 (fn2-harvest-next ops))) 1 0)))
                (implies (< 0 (fn2-pool-out-count (fn2-ops-range-slot (mv-nth 1 (fn2-harvest-next ops)) ops) (mv-nth 1 (fn2-bc-harvest-pool-step pool ops))))
                         (equal (fn2-pool-state (fn2-ops-range-slot (mv-nth 1 (fn2-harvest-next ops)) ops) (mv-nth 1 (fn2-bc-harvest-pool-step pool ops))) *fn2-pool-state-leased-out*))))
  :hints (("Goal" :cases ((fn2-bc-input-condp (mv-nth 3 (fn2-harvest-next ops)) (mv-nth 1 (fn2-harvest-next ops)) (mv-nth 4 (fn2-harvest-next ops))) (fn2-bc-release-condp (mv-nth 3 (fn2-harvest-next ops)) (mv-nth 1 (fn2-harvest-next ops)) (mv-nth 4 (fn2-harvest-next ops))))
           :in-theory (e/d (fn2-bc-harvest-pool-step fn2-op-range fn2-op-slotp fn2-borrows-accountedp
                            fn2-op-borrow-on)
                           (fn2-harvest-next fn2-op-finish fn2-pool-release-out fn2-pool-complete-in
                            fn2-pool-borrows-countedp fn2-op-borrowp-by-vals
                            fn2-bc-release-condp-by-vals
                            fn2-ops-borrows-namedp fn2-ops-semanticp fn2-ops-keys-except fn2-pool-keys-except
                            fn2-op-cell fn2-bc-input-condp fn2-bc-release-condp fn2-harvest-next-borrow-release fn2-ops-borrow-count-at-least))
           :use (fn2-harvest-next-found fn2-harvest-next-borrow-release
                 (:instance fn2-ops-borrows-namedp-necc (i (mv-nth 1 (fn2-harvest-next ops))))
                 (:instance fn2-pool-borrows-countedp-necc (r (fn2-ops-range-slot (mv-nth 1 (fn2-harvest-next ops)) ops)))
                 (:instance fn2-ops-borrow-count-at-least (j (mv-nth 1 (fn2-harvest-next ops))) (r (fn2-ops-range-slot (mv-nth 1 (fn2-harvest-next ops)) ops)) (n (fn2-ops-rows ops)))
                 (:instance fn2-ops-range-slot-natp (i (mv-nth 1 (fn2-harvest-next ops))) (fn2-ops ops))))))
(defthm fn2-bc-harvest-not-found
  (implies (not (equal (mv-nth 0 (fn2-harvest-next ops)) t))
           (and (equal (mv-nth 1 (fn2-bc-harvest-pool-step pool ops)) pool) (equal (fn2-bc-harvest-ops pool ops) ops)))
  :hints (("Goal" :in-theory (e/d (fn2-bc-harvest-pool-step fn2-bc-harvest-ops) (fn2-harvest-next)))))
(defthm fn2-borrows-accountedp-release-transfer
  (implies (and (fn2-borrows-accountedp pool ops)
                (fn2-pool-keys-except rs pool p2) (fn2-ops-keys-except j ops o2)
                (equal (fn2-pool-rows p2) (fn2-pool-rows pool)) (equal (fn2-ops-rows o2) (fn2-ops-rows ops))
                (equal (fn2-pool-gen rs p2) (fn2-pool-gen rs pool))
                (natp j) (< j (fn2-ops-rows ops)) (natp (fn2-ops-rows ops)) (natp rs)
                (equal (fn2-ops-range-slot j ops) rs)
                (implies (fn2-op-borrowp j o2)
                         (and (fn2-op-borrowp j ops) (equal (fn2-ops-range-slot j o2) rs)
                              (equal (fn2-ops-range-gen j o2) (fn2-ops-range-gen j ops))))
                (implies (equal (fn2-ops-may-release j o2) 1)
                         (and (equal (fn2-ops-may-release j ops) 1)
                              (equal (fn2-ops-kind j o2) (fn2-ops-kind j ops))))
                (implies (< rs (fn2-pool-rows pool))
                         (and (equal (fn2-pool-out-count rs p2)
                                     (- (fn2-pool-out-count rs pool)
                                        (if (and (fn2-op-borrowp j ops) (not (fn2-op-borrowp j o2))) 1 0)))
                              (implies (< 0 (fn2-pool-out-count rs p2))
                                       (equal (fn2-pool-state rs p2) *fn2-pool-state-leased-out*)))))
           (fn2-borrows-accountedp p2 o2))
  :hints (("Goal" :in-theory (e/d (fn2-op-borrow-on)
                                  (fn2-borrows-accountedp fn2-pool-borrows-countedp fn2-ops-borrows-namedp
                                   fn2-pool-borrows-countedp-transfer fn2-ops-borrows-namedp-transfer
                                   fn2-ops-keys-except fn2-pool-keys-except fn2-op-borrowp-by-vals))
           :use ((:instance fn2-pool-borrows-countedp-transfer (pool2 p2) (ops2 o2) (ps rs))
                 (:instance fn2-ops-borrows-namedp-transfer (pool2 p2) (ops2 o2) (ps rs))
                 (:instance fn2-borrows-accountedp)
                 (:instance fn2-borrows-accountedp (pool p2) (ops o2))
                 (:instance fn2-ops-borrows-namedp-necc (i j))))))
(defthm fn2-bc-harvest-borrows
  (implies (and (fn2-ops-semanticp ops)
                (fn2-borrows-accountedp pool ops))
           (fn2-borrows-accountedp (mv-nth 1 (fn2-bc-harvest-pool-step pool ops)) (fn2-bc-harvest-ops pool ops)))
  :hints (("Goal"
           :cases ((equal (mv-nth 0 (fn2-harvest-next ops)) t))
           :in-theory (union-theories '(fn2-bc-harvest-not-found fn2-ops-semanticp-row-facts)
                                      (theory 'minimal-theory))
           :use ((:instance fn2-borrows-accountedp-release-transfer (p2 (mv-nth 1 (fn2-bc-harvest-pool-step pool ops))) (o2 (fn2-bc-harvest-ops pool ops)) (j (mv-nth 1 (fn2-harvest-next ops))) (rs (fn2-ops-range-slot (mv-nth 1 (fn2-harvest-next ops)) ops)))
                 (:instance fn2-ops-borrows-namedp-necc (i (mv-nth 1 (fn2-harvest-next ops))))
                 (:instance fn2-borrows-accountedp)
                 fn2-harvest-next-found fn2-harvest-next-borrow-release fn2-bc-harvest-pool-count
                 fn2-bc-harvest-ops-row fn2-bc-harvest-pool-frame fn2-bc-harvest-ops-frame
                 (:instance fn2-ops-range-slot-natp (i (mv-nth 1 (fn2-harvest-next ops))) (fn2-ops ops))))))
(defmacro fn2-bc-ops-row-writer (op args slot &key (keep-range 't))
  ;; One ops writer whose only row write is at SLOT: the other rows' borrow keys,
  ;; the row count, and (unless it writes the range) the row's borrow-relevant fields stay.
  (let ((call `(,op ,@args)))
    `(progn
       (defthm ,(intern-in-package-of-symbol (concatenate 'string (symbol-name op) "-BORROW-KEYS-OTHER") op)
         (implies (and (natp i) (not (equal i ,slot)))
                  (equal (fn2-op-borrow-key i (mv-nth 1 ,call)) (fn2-op-borrow-key i ops)))
         :hints (("Goal" :in-theory (e/d (fn2-ops-writers ,op fn2-op-phase-code fn2-op-handle-code fn2-op-slotp)
                                         (update-nth-array)))))
       (defthm ,(intern-in-package-of-symbol (concatenate 'string (symbol-name op) "-BORROW-KEYS") op)
         (fn2-ops-keys-except ,slot ops (mv-nth 1 ,call))
         :hints (("Goal" :in-theory (e/d (fn2-ops-keys-except) (,op))
                  :use ((:instance ,(intern-in-package-of-symbol (concatenate 'string (symbol-name op) "-BORROW-KEYS-OTHER") op)
                         (i (fn2-ops-keys-except-witness ,slot ops (mv-nth 1 ,call))))))))
       (defthm ,(intern-in-package-of-symbol (concatenate 'string (symbol-name op) "-BORROW-ROW") op)
         (let ((q (mv-nth 1 ,call)))
           (and (equal (fn2-ops-rows q) (fn2-ops-rows ops))
                (equal (fn2-ops-kind ,slot q) (fn2-ops-kind ,slot ops))
                (equal (fn2-ops-phase ,slot q) (fn2-ops-phase ,slot ops))
                (equal (fn2-ops-may-release ,slot q) (fn2-ops-may-release ,slot ops))
                (equal (fn2-ops-gen ,slot q) (fn2-ops-gen ,slot ops))
                (equal (fn2-ops-out-tail q) (fn2-ops-out-tail ops))
                (equal (fn2-ops-out-slot-length q) (fn2-ops-out-slot-length ops))
                (equal (fn2-ops-out-gen-length q) (fn2-ops-out-gen-length ops))
                (equal (fn2-ops-queued q) (fn2-ops-queued ops))
                (equal (fn2-ops-reserved-credits q) (fn2-ops-reserved-credits ops))
                ,@(and keep-range
                       `((equal (fn2-ops-range-slot ,slot q) (fn2-ops-range-slot ,slot ops))
                         (equal (fn2-ops-range-gen ,slot q) (fn2-ops-range-gen ,slot ops))))
                (equal (fn2-bc-row-vals ,slot q) (fn2-bc-row-vals ,slot ops))))
         :hints (("Goal" :in-theory (e/d (fn2-ops-writers fn2-borrow-readers ,op fn2-op-phase-code fn2-op-handle-code
                                          fn2-op-slotp fn2-bc-row-vals fn2-ops-c0-posted fn2-ops-c0-event
                                          fn2-ops-c1-event fn2-ops-c1-aux0 fn2-ops-gen fn2-ops-out-tail
                                          fn2-ops-out-slot-length fn2-ops-out-gen-length fn2-ops-queued
                                          fn2-ops-reserved-credits)
                                         (update-nth-array))))))))
(fn2-bc-ops-row-writer fn2-op-set-range (slot gen rslot rgen off len ops) slot :keep-range nil)
(fn2-bc-ops-row-writer fn2-op-set-capability (slot gen index nonce ops) slot)
(fn2-bc-ops-row-writer fn2-op-set-storage (slot gen offset fua ops) slot)
(fn2-bc-ops-row-writer fn2-op-set-cancel-target (slot gen tslot tgen ops) slot)
(defthm fn2-op-set-range-borrow-code
  (let ((r (fn2-op-set-range slot gen rslot rgen off len ops)))
    (and (iff (equal (mv-nth 0 r) :ok)
              (and (equal (fn2-op-phase-code slot gen *fn2-op-phase-reserved* ops) :ok)
                   (unsigned-byte-p 32 rslot) (unsigned-byte-p 60 rgen)
                   (unsigned-byte-p 32 off) (unsigned-byte-p 32 len)))
         (implies (equal (mv-nth 0 r) :ok)
                  (and (equal (fn2-ops-range-slot slot (mv-nth 1 r)) rslot)
                       (equal (fn2-ops-range-gen slot (mv-nth 1 r)) rgen)))))
  :hints (("Goal" :in-theory (e/d (fn2-ops-writers fn2-borrow-readers fn2-op-set-range fn2-op-phase-code
                                   fn2-op-handle-code fn2-op-slotp)
                                  (update-nth-array unsigned-byte-p)))))
(defthm fn2-op-set-capability-borrow-code
  (iff (equal (mv-nth 0 (fn2-op-set-capability slot gen index nonce ops)) :ok)
       (and (equal (fn2-op-phase-code slot gen *fn2-op-phase-reserved* ops) :ok)
            (unsigned-byte-p 32 index) (unsigned-byte-p 32 nonce)))
  :hints (("Goal" :in-theory (e/d (fn2-op-set-capability) (fn2-op-phase-code unsigned-byte-p)))))
(defthm fn2-op-set-storage-borrow-code
  (iff (equal (mv-nth 0 (fn2-op-set-storage slot gen offset fua ops)) :ok)
       (and (equal (fn2-op-phase-code slot gen *fn2-op-phase-reserved* ops) :ok)
            (unsigned-byte-p 60 offset) (unsigned-byte-p 1 fua)))
  :hints (("Goal" :in-theory (e/d (fn2-op-set-storage) (fn2-op-phase-code unsigned-byte-p)))))
(defthm fn2-op-set-cancel-target-borrow-code
  (iff (equal (mv-nth 0 (fn2-op-set-cancel-target slot gen tslot tgen ops)) :ok)
       (and (equal (fn2-op-phase-code slot gen *fn2-op-phase-reserved* ops) :ok)
            (unsigned-byte-p 32 tslot) (unsigned-byte-p 60 tgen)))
  :hints (("Goal" :in-theory (e/d (fn2-op-set-cancel-target) (fn2-op-phase-code unsigned-byte-p)))))
(defthm fn2-op-phase-code-by-row
  (equal (fn2-op-phase-code slot gen phase x)
         (cond ((not (and (natp slot) (< slot (fn2-ops-rows x)))) :bounds)
               ((not (equal gen (fn2-ops-gen slot x))) :stale)
               ((not (equal phase (nth 1 (fn2-bc-row-vals slot x)))) :state)
               (t :ok)))
  :hints (("Goal" :in-theory (enable fn2-op-phase-code fn2-op-handle-code fn2-op-slotp fn2-bc-row-vals))))
(defthm fn2-op-enqueue-borrow-keys-other
  (implies (and (natp i) (not (equal i slot)))
           (equal (fn2-op-borrow-key i (mv-nth 1 (fn2-op-enqueue slot gen ops))) (fn2-op-borrow-key i ops)))
  :hints (("Goal" :in-theory (e/d (fn2-ops-writers fn2-op-enqueue fn2-op-phase-code fn2-op-handle-code fn2-op-slotp)
                                  (update-nth-array fn2-op-phase-code-by-row)))))
(defthm fn2-op-enqueue-borrow-keys
  (fn2-ops-keys-except slot ops (mv-nth 1 (fn2-op-enqueue slot gen ops)))
  :hints (("Goal" :in-theory (e/d (fn2-ops-keys-except) (fn2-op-enqueue))
           :use ((:instance fn2-op-enqueue-borrow-keys-other
                  (i (fn2-ops-keys-except-witness slot ops (mv-nth 1 (fn2-op-enqueue slot gen ops)))))))))
(defthm fn2-op-enqueue-borrow-row
  (let* ((r (fn2-op-enqueue slot gen ops)) (q (mv-nth 1 r)))
    (and (equal (fn2-ops-rows q) (fn2-ops-rows ops))
         (equal (fn2-ops-kind slot q) (fn2-ops-kind slot ops))
         (equal (fn2-ops-may-release slot q) (fn2-ops-may-release slot ops))
         (equal (fn2-ops-range-slot slot q) (fn2-ops-range-slot slot ops))
         (equal (fn2-ops-range-gen slot q) (fn2-ops-range-gen slot ops))
         (implies (not (equal (mv-nth 0 r) :ok)) (equal q ops))
         (iff (equal (mv-nth 0 r) :ok)
              (and (equal (fn2-op-phase-code slot gen *fn2-op-phase-reserved* ops) :ok)
                   (< (fn2-ops-out-tail ops) (fn2-ops-out-slot-length ops))
                   (< (fn2-ops-out-tail ops) (fn2-ops-out-gen-length ops))
                   (< (fn2-ops-queued ops) (fn2-ops-out-slot-length ops))
                   (< (fn2-ops-queued ops) *fn2-none*)
                   (< 0 (fn2-ops-reserved-credits ops))
                   (< (fn2-ops-out-slot-length ops) 4294967296)))
         (implies (equal (mv-nth 0 r) :ok)
                  (and (equal (fn2-ops-phase slot q) *fn2-op-phase-queued*)
                       (equal (fn2-bc-row-vals slot q)
                              (update-nth 1 *fn2-op-phase-queued* (fn2-bc-row-vals slot ops)))))))
  :hints (("Goal" :in-theory (e/d (fn2-ops-writers fn2-borrow-readers fn2-op-enqueue fn2-op-phase-code
                                   fn2-op-handle-code fn2-op-slotp fn2-bc-row-vals fn2-ops-c0-posted
                                   fn2-ops-c0-event fn2-ops-c1-event fn2-ops-c1-aux0 fn2-ops-gen
                                   fn2-ops-out-tail fn2-ops-out-slot-length fn2-ops-out-gen-length
                                   fn2-ops-queued fn2-ops-reserved-credits)
                                  (update-nth-array fn2-op-phase-code-by-row)))))
(defthm fn2-op-unreserve-borrow-keys-other
  (implies (and (natp i) (not (equal i slot)))
           (equal (fn2-op-borrow-key i (mv-nth 1 (fn2-op-unreserve slot gen ops))) (fn2-op-borrow-key i ops)))
  :hints (("Goal" :in-theory (e/d (fn2-ops-writers fn2-op-unreserve fn2-ops-clear-row fn2-op-phase-code
                                   fn2-op-handle-code fn2-op-slotp)
                                  (update-nth-array fn2-op-phase-code-by-row)))))
(defthm fn2-op-unreserve-borrow-keys
  (fn2-ops-keys-except slot ops (mv-nth 1 (fn2-op-unreserve slot gen ops)))
  :hints (("Goal" :in-theory (e/d (fn2-ops-keys-except) (fn2-op-unreserve))
           :use ((:instance fn2-op-unreserve-borrow-keys-other
                  (i (fn2-ops-keys-except-witness slot ops (mv-nth 1 (fn2-op-unreserve slot gen ops)))))))))
(defthm fn2-op-unreserve-borrow-row
  (let ((q (mv-nth 1 (fn2-op-unreserve slot gen ops))))
    (and (equal (fn2-ops-rows q) (fn2-ops-rows ops))
         (implies (not (equal (mv-nth 0 (fn2-op-unreserve slot gen ops)) :ok)) (equal q ops))
         (implies (equal (mv-nth 0 (fn2-op-unreserve slot gen ops)) :ok)
                  (equal (fn2-ops-may-release slot q) 0))
         (implies (and (natp slot) (equal (fn2-ops-phase slot ops) *fn2-op-phase-reserved*))
                  (and (not (fn2-op-borrowp slot q))
                       (not (fn2-bc-vals-borrowp (fn2-bc-row-vals slot q)))))
         (implies (equal (fn2-ops-may-release slot q) 1)
                  (and (equal (fn2-ops-may-release slot ops) 1)
                       (equal (fn2-ops-kind slot q) (fn2-ops-kind slot ops))))))
  :hints (("Goal" :in-theory (e/d (fn2-ops-writers fn2-borrow-readers fn2-op-unreserve fn2-ops-clear-row
                                   fn2-op-phase-code fn2-op-handle-code fn2-op-slotp fn2-op-borrowp
                                   fn2-borrow-valsp fn2-bc-vals-borrowp fn2-bc-row-vals)
                                  (update-nth-array fn2-op-phase-code-by-row fn2-op-borrowp-by-vals)))))
(defthm fn2-op-reserve-borrow-keys-other
  (implies (and (natp i) (not (equal i (mv-nth 1 (fn2-op-reserve kind okind oslot ogen principal may ops)))))
           (equal (fn2-op-borrow-key i (mv-nth 3 (fn2-op-reserve kind okind oslot ogen principal may ops)))
                  (fn2-op-borrow-key i ops)))
  :hints (("Goal" :in-theory (e/d (fn2-ops-writers fn2-op-reserve fn2-ops-clear-row fn2-op-slotp)
                                  (update-nth-array)))))
(defthm fn2-op-reserve-borrow-keys
  (fn2-ops-keys-except (mv-nth 1 (fn2-op-reserve kind okind oslot ogen principal may ops)) ops
                       (mv-nth 3 (fn2-op-reserve kind okind oslot ogen principal may ops)))
  :hints (("Goal" :in-theory (e/d (fn2-ops-keys-except) (fn2-op-reserve))
           :use ((:instance fn2-op-reserve-borrow-keys-other
                  (i (fn2-ops-keys-except-witness
                      (mv-nth 1 (fn2-op-reserve kind okind oslot ogen principal may ops)) ops
                      (mv-nth 3 (fn2-op-reserve kind okind oslot ogen principal may ops)))))))))
(defthm fn2-op-reserve-borrow-row
  (let* ((r (fn2-op-reserve kind okind oslot ogen principal may ops))
         (j (mv-nth 1 r)) (q (mv-nth 3 r)))
    (and (equal (fn2-ops-rows q) (fn2-ops-rows ops))
         (implies (not (equal (mv-nth 0 r) :ok)) (equal q ops))
         (implies (equal (mv-nth 0 r) :ok)
                  (and (natp j) (< j (fn2-ops-rows ops))
                       (equal (fn2-ops-phase j ops) *fn2-op-phase-free*)
                       (equal (mv-nth 2 r) (fn2-ops-gen j q))
                       (equal (fn2-bc-row-vals j q) (list kind *fn2-op-phase-reserved* 0 0 0 0 0 0 0 0))
                       (equal (fn2-ops-phase j q) *fn2-op-phase-reserved*)
                       (equal (fn2-ops-kind j q) kind)
                       (equal (fn2-ops-may-release j q) may)
                       (or (equal may 0) (equal kind *fn2-action-send*))
                       (equal (fn2-ops-out-tail q) (fn2-ops-out-tail ops))
                       (equal (fn2-ops-out-slot-length q) (fn2-ops-out-slot-length ops))
                       (equal (fn2-ops-out-gen-length q) (fn2-ops-out-gen-length ops))
                       (equal (fn2-ops-queued q) (fn2-ops-queued ops))
                       (equal (fn2-ops-reserved-credits q) (+ 1 (fn2-ops-reserved-credits ops)))
                       (< (+ (fn2-ops-reserved-credits ops) (fn2-ops-queued ops))
                          (fn2-ops-out-slot-length ops))))))
  :hints (("Goal" :in-theory (e/d (fn2-ops-writers fn2-borrow-readers fn2-op-reserve fn2-ops-clear-row
                                   fn2-op-slotp fn2-bc-row-vals fn2-ops-c0-posted fn2-ops-c0-event
                                   fn2-ops-c1-event fn2-ops-c1-aux0 fn2-ops-gen fn2-ops-out-tail
                                   fn2-ops-out-slot-length fn2-ops-out-gen-length fn2-ops-queued
                                   fn2-ops-reserved-credits fn2-ops-free-head fn2-ops-free-count
                                   fn2-op-cleanup-reserve)
                                  (update-nth-array)))))
(defthm fn2-core-lease-borrow
  (let* ((r (fn2-core-lease kind slot gen off len opslot opgen okind oslot ogen pool)) (q (mv-nth 2 r))
         (ok (equal (mv-nth 0 r) :ok))
         (out (or (equal kind *fn2-action-send*) (equal kind *fn2-action-write*))))
    (and (fn2-pool-keys-except slot pool q)
         (equal (fn2-pool-rows q) (fn2-pool-rows pool))
         (equal (fn2-pool-gen slot q) (fn2-pool-gen slot pool))
         (implies (not ok) (equal q pool))
         (equal (fn2-pool-out-count slot q)
                (if (and ok out) (+ 1 (fn2-pool-out-count slot pool)) (fn2-pool-out-count slot pool)))
         (implies (and ok out)
                  (and (natp slot) (< slot (fn2-pool-rows pool)) (equal (fn2-pool-gen slot pool) gen)
                       (equal (fn2-pool-state slot q) *fn2-pool-state-leased-out*)
                       (equal (mv-nth 1 r) off)))
         (implies (and (not (and ok out))
                       (not (equal (fn2-pool-state slot pool) *fn2-pool-state-workspace*)))
                  (equal (fn2-pool-state slot q) (fn2-pool-state slot pool)))))
  :hints (("Goal" :in-theory (e/d (fn2-core-lease)
                                  (fn2-pool-lease-out fn2-pool-lease-in fn2-pool-keys-except))
           :use ((:instance fn2-pool-lease-out-effect)
                 (:instance fn2-pool-lease-in-effect)))))
(defmacro fn2-bc-keys-through (op args slot pos)
  `(defthm ,(intern-in-package-of-symbol (concatenate 'string (symbol-name op) "-KEYS-THROUGH") op)
     (implies (fn2-ops-keys-except ,slot a ops)
              (fn2-ops-keys-except ,slot a (mv-nth ,pos (,op ,@args))))
     :hints (("Goal" :in-theory (disable ,op fn2-ops-keys-except fn2-ops-keys-except-trans)
              :use ((:instance fn2-ops-keys-except-trans (s ,slot) (a a) (b ops) (c (mv-nth ,pos (,op ,@args)))))))))
(fn2-bc-keys-through fn2-op-set-range (slot gen rslot rgen off len ops) slot 1)
(fn2-bc-keys-through fn2-op-set-capability (slot gen index nonce ops) slot 1)
(fn2-bc-keys-through fn2-op-set-storage (slot gen offset fua ops) slot 1)
(fn2-bc-keys-through fn2-op-set-cancel-target (slot gen tslot tgen ops) slot 1)
(fn2-bc-keys-through fn2-op-enqueue (slot gen ops) slot 1)
(fn2-bc-keys-through fn2-op-unreserve (slot gen ops) slot 1)
(defthm fn2-bc-mv-nth-cons-const
  (implies (syntaxp (quotep n))
           (equal (mv-nth n (cons a b)) (if (zp n) a (mv-nth (- n 1) b)))))
(defthm fn2-issue-children-unreserved
  (implies (not (and (and (unsigned-byte-p 32 cap-index) (unsigned-byte-p 32 cap-nonce)
                     (unsigned-byte-p 60 offset) (unsigned-byte-p 1 fua)
                     (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
                     (unsigned-byte-p 32 off) (unsigned-byte-p 32 len)
                     (unsigned-byte-p 32 target-slot) (unsigned-byte-p 60 target-gen)
                     (fn2-core-outbox-ready ops)) (equal (mv-nth 0 (fn2-op-reserve kind okind oslot ogen principal may-release ops)) :ok)))
           (and (equal (mv-nth 3 (fn2-issue-children kind cap-index cap-nonce offset fua slot gen off len may-release target-slot target-gen okind oslot ogen principal pool ops control)) pool) (equal (mv-nth 4 (fn2-issue-children kind cap-index cap-nonce offset fua slot gen off len may-release target-slot target-gen okind oslot ogen principal pool ops control)) ops)))
  :hints (("Goal" :in-theory (e/d (fn2-issue-children) (fn2-op-reserve fn2-core-lease fn2-op-unreserve fn2-op-set-range fn2-op-set-capability
                            fn2-op-set-storage fn2-op-set-cancel-target fn2-op-enqueue fn2-control-record-stop
                            fn2-op-borrowp fn2-ops-keys-except fn2-pool-keys-except fn2-op-phase-code fn2-ops-gen mv-nth)))))
(defthm fn2-issue-children-borrow-row
  (implies (and (fn2-opsp ops) (fn2-ops-wfp ops) (and (unsigned-byte-p 32 cap-index) (unsigned-byte-p 32 cap-nonce)
                     (unsigned-byte-p 60 offset) (unsigned-byte-p 1 fua)
                     (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
                     (unsigned-byte-p 32 off) (unsigned-byte-p 32 len)
                     (unsigned-byte-p 32 target-slot) (unsigned-byte-p 60 target-gen)
                     (fn2-core-outbox-ready ops)) (equal (mv-nth 0 (fn2-op-reserve kind okind oslot ogen principal may-release ops)) :ok))
           (and (iff (fn2-op-borrowp (mv-nth 1 (fn2-op-reserve kind okind oslot ogen principal may-release ops)) (mv-nth 4 (fn2-issue-children kind cap-index cap-nonce offset fua slot gen off len may-release target-slot target-gen okind oslot ogen principal pool ops control))) (and (equal (mv-nth 0 (fn2-core-lease kind slot gen off len (mv-nth 1 (fn2-op-reserve kind okind oslot ogen principal may-release ops)) (mv-nth 2 (fn2-op-reserve kind okind oslot ogen principal may-release ops)) okind oslot ogen pool)) :ok) (or (equal kind *fn2-action-send*) (equal kind *fn2-action-write*))))
                (implies (fn2-op-borrowp (mv-nth 1 (fn2-op-reserve kind okind oslot ogen principal may-release ops)) (mv-nth 4 (fn2-issue-children kind cap-index cap-nonce offset fua slot gen off len may-release target-slot target-gen okind oslot ogen principal pool ops control)))
                         (and (equal (fn2-ops-range-slot (mv-nth 1 (fn2-op-reserve kind okind oslot ogen principal may-release ops)) (mv-nth 4 (fn2-issue-children kind cap-index cap-nonce offset fua slot gen off len may-release target-slot target-gen okind oslot ogen principal pool ops control))) slot)
                              (equal (fn2-ops-range-gen (mv-nth 1 (fn2-op-reserve kind okind oslot ogen principal may-release ops)) (mv-nth 4 (fn2-issue-children kind cap-index cap-nonce offset fua slot gen off len may-release target-slot target-gen okind oslot ogen principal pool ops control))) gen)))
                (implies (equal (fn2-ops-may-release (mv-nth 1 (fn2-op-reserve kind okind oslot ogen principal may-release ops)) (mv-nth 4 (fn2-issue-children kind cap-index cap-nonce offset fua slot gen off len may-release target-slot target-gen okind oslot ogen principal pool ops control))) 1)
                         (equal (fn2-ops-kind (mv-nth 1 (fn2-op-reserve kind okind oslot ogen principal may-release ops)) (mv-nth 4 (fn2-issue-children kind cap-index cap-nonce offset fua slot gen off len may-release target-slot target-gen okind oslot ogen principal pool ops control))) *fn2-action-send*))))
  :hints (("Goal" :in-theory (e/d (fn2-issue-children fn2-core-outbox-ready fn2-bc-vals-borrowp fn2-borrow-valsp)
                                  (fn2-op-reserve fn2-core-lease fn2-op-unreserve fn2-op-set-range fn2-op-set-capability
                            fn2-op-set-storage fn2-op-set-cancel-target fn2-op-enqueue fn2-control-record-stop
                            fn2-op-borrowp fn2-ops-keys-except fn2-pool-keys-except fn2-op-phase-code fn2-ops-gen mv-nth unsigned-byte-p))
           :use ((:instance fn2-op-reserve-borrow-row (may may-release)))
           :cases ((equal (mv-nth 0 (fn2-core-lease kind slot gen off len (mv-nth 1 (fn2-op-reserve kind okind oslot ogen principal may-release ops)) (mv-nth 2 (fn2-op-reserve kind okind oslot ogen principal may-release ops)) okind oslot ogen pool)) :ok)))))
(defthm fn2-op-borrowp-when-free
  (implies (equal (fn2-ops-phase j x) *fn2-op-phase-free*) (not (fn2-op-borrowp j x)))
  :hints (("Goal" :in-theory (e/d (fn2-op-borrowp fn2-borrow-valsp) (fn2-op-borrowp-by-vals)))))
(defthm fn2-issue-children-borrow-frame
  (implies (and (and (unsigned-byte-p 32 cap-index) (unsigned-byte-p 32 cap-nonce)
                     (unsigned-byte-p 60 offset) (unsigned-byte-p 1 fua)
                     (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
                     (unsigned-byte-p 32 off) (unsigned-byte-p 32 len)
                     (unsigned-byte-p 32 target-slot) (unsigned-byte-p 60 target-gen)
                     (fn2-core-outbox-ready ops)) (equal (mv-nth 0 (fn2-op-reserve kind okind oslot ogen principal may-release ops)) :ok))
           (and (fn2-pool-keys-except slot pool (mv-nth 3 (fn2-issue-children kind cap-index cap-nonce offset fua slot gen off len may-release target-slot target-gen okind oslot ogen principal pool ops control)))
                (equal (fn2-pool-rows (mv-nth 3 (fn2-issue-children kind cap-index cap-nonce offset fua slot gen off len may-release target-slot target-gen okind oslot ogen principal pool ops control))) (fn2-pool-rows pool))
                (equal (fn2-pool-gen slot (mv-nth 3 (fn2-issue-children kind cap-index cap-nonce offset fua slot gen off len may-release target-slot target-gen okind oslot ogen principal pool ops control))) (fn2-pool-gen slot pool))
                (equal (fn2-pool-out-count slot (mv-nth 3 (fn2-issue-children kind cap-index cap-nonce offset fua slot gen off len may-release target-slot target-gen okind oslot ogen principal pool ops control)))
                       (if (and (equal (mv-nth 0 (fn2-core-lease kind slot gen off len (mv-nth 1 (fn2-op-reserve kind okind oslot ogen principal may-release ops)) (mv-nth 2 (fn2-op-reserve kind okind oslot ogen principal may-release ops)) okind oslot ogen pool)) :ok) (or (equal kind *fn2-action-send*) (equal kind *fn2-action-write*))) (+ 1 (fn2-pool-out-count slot pool)) (fn2-pool-out-count slot pool)))
                (implies (and (equal (mv-nth 0 (fn2-core-lease kind slot gen off len (mv-nth 1 (fn2-op-reserve kind okind oslot ogen principal may-release ops)) (mv-nth 2 (fn2-op-reserve kind okind oslot ogen principal may-release ops)) okind oslot ogen pool)) :ok) (or (equal kind *fn2-action-send*) (equal kind *fn2-action-write*)))
                         (and (< slot (fn2-pool-rows pool)) (equal (fn2-pool-gen slot pool) gen)
                              (equal (fn2-pool-state slot (mv-nth 3 (fn2-issue-children kind cap-index cap-nonce offset fua slot gen off len may-release target-slot target-gen okind oslot ogen principal pool ops control))) *fn2-pool-state-leased-out*)))
                (implies (and (not (and (equal (mv-nth 0 (fn2-core-lease kind slot gen off len (mv-nth 1 (fn2-op-reserve kind okind oslot ogen principal may-release ops)) (mv-nth 2 (fn2-op-reserve kind okind oslot ogen principal may-release ops)) okind oslot ogen pool)) :ok) (or (equal kind *fn2-action-send*) (equal kind *fn2-action-write*))))
                              (not (equal (fn2-pool-state slot pool) *fn2-pool-state-workspace*)))
                         (equal (fn2-pool-state slot (mv-nth 3 (fn2-issue-children kind cap-index cap-nonce offset fua slot gen off len may-release target-slot target-gen okind oslot ogen principal pool ops control))) (fn2-pool-state slot pool)))
                (fn2-ops-keys-except (mv-nth 1 (fn2-op-reserve kind okind oslot ogen principal may-release ops)) ops (mv-nth 4 (fn2-issue-children kind cap-index cap-nonce offset fua slot gen off len may-release target-slot target-gen okind oslot ogen principal pool ops control)))
                (equal (fn2-ops-rows (mv-nth 4 (fn2-issue-children kind cap-index cap-nonce offset fua slot gen off len may-release target-slot target-gen okind oslot ogen principal pool ops control))) (fn2-ops-rows ops))))
  :hints (("Goal" :in-theory (e/d (fn2-issue-children) (fn2-op-reserve fn2-core-lease fn2-op-unreserve fn2-op-set-range fn2-op-set-capability
                            fn2-op-set-storage fn2-op-set-cancel-target fn2-op-enqueue fn2-control-record-stop
                            fn2-op-borrowp fn2-ops-keys-except fn2-pool-keys-except fn2-op-phase-code fn2-ops-gen mv-nth)))))
(defthm fn2-bc-ops-rows-natp
  (implies (fn2-ops-wfp ops) (natp (fn2-ops-rows ops)))
  :hints (("Goal" :in-theory (enable fn2-ops-wfp fn2-borrow-readers))))
(defthm fn2-bc-ubp-natp
  (implies (unsigned-byte-p n x) (natp x)))
(defthm fn2-borrows-accountedp-lease-transfer
  (implies (and (fn2-borrows-accountedp pool ops)
                (fn2-pool-keys-except slot pool p2) (fn2-ops-keys-except j ops o2)
                (equal (fn2-pool-rows p2) (fn2-pool-rows pool)) (equal (fn2-ops-rows o2) (fn2-ops-rows ops))
                (equal (fn2-pool-gen slot p2) (fn2-pool-gen slot pool))
                (natp j) (< j (fn2-ops-rows ops)) (natp (fn2-ops-rows ops)) (natp slot)
                (not (fn2-op-borrowp j ops))
                (iff (fn2-op-borrowp j o2) b)
                (implies b (and (equal (fn2-ops-range-slot j o2) slot) (< slot (fn2-pool-rows pool))
                                (equal (fn2-ops-range-gen j o2) (fn2-pool-gen slot pool))))
                (implies (equal (fn2-ops-may-release j o2) 1) (equal (fn2-ops-kind j o2) *fn2-action-send*))
                (equal (fn2-pool-out-count slot p2)
                       (if b (+ 1 (fn2-pool-out-count slot pool)) (fn2-pool-out-count slot pool)))
                (implies b (equal (fn2-pool-state slot p2) *fn2-pool-state-leased-out*))
                (implies (and (not b) (not (equal (fn2-pool-state slot pool) *fn2-pool-state-workspace*)))
                         (equal (fn2-pool-state slot p2) (fn2-pool-state slot pool))))
           (fn2-borrows-accountedp p2 o2))
  :hints (("Goal" :in-theory (e/d (fn2-op-borrow-on)
                                  (fn2-borrows-accountedp fn2-pool-borrows-countedp fn2-ops-borrows-namedp
                                   fn2-pool-borrows-countedp-transfer fn2-ops-borrows-namedp-transfer
                                   fn2-ops-keys-except fn2-pool-keys-except fn2-op-borrowp-by-vals))
           :use ((:instance fn2-pool-borrows-countedp-transfer (pool2 p2) (ops2 o2) (ps slot))
                 (:instance fn2-ops-borrows-namedp-transfer (pool2 p2) (ops2 o2) (ps slot))
                 (:instance fn2-borrows-accountedp)
                 (:instance fn2-borrows-accountedp (pool p2) (ops o2))
                 (:instance fn2-pool-borrows-countedp-necc (r slot))))))
(defthm fn2-issue-children-borrows
  (implies (and (fn2-opsp ops) (fn2-ops-wfp ops) (fn2-borrows-accountedp pool ops))
           (fn2-borrows-accountedp (mv-nth 3 (fn2-issue-children kind cap-index cap-nonce offset fua slot gen off len may-release target-slot target-gen okind oslot ogen principal pool ops control)) (mv-nth 4 (fn2-issue-children kind cap-index cap-nonce offset fua slot gen off len may-release target-slot target-gen okind oslot ogen principal pool ops control))))
  :hints (("Goal" :cases ((and (and (unsigned-byte-p 32 cap-index) (unsigned-byte-p 32 cap-nonce)
                     (unsigned-byte-p 60 offset) (unsigned-byte-p 1 fua)
                     (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
                     (unsigned-byte-p 32 off) (unsigned-byte-p 32 len)
                     (unsigned-byte-p 32 target-slot) (unsigned-byte-p 60 target-gen)
                     (fn2-core-outbox-ready ops)) (equal (mv-nth 0 (fn2-op-reserve kind okind oslot ogen principal may-release ops)) :ok)))
           :in-theory (union-theories '(fn2-issue-children-unreserved fn2-op-borrowp-when-free fn2-bc-ops-rows-natp fn2-bc-ubp-natp)
                                      (theory 'minimal-theory))
           :use ((:instance fn2-borrows-accountedp-lease-transfer (p2 (mv-nth 3 (fn2-issue-children kind cap-index cap-nonce offset fua slot gen off len may-release target-slot target-gen okind oslot ogen principal pool ops control))) (o2 (mv-nth 4 (fn2-issue-children kind cap-index cap-nonce offset fua slot gen off len may-release target-slot target-gen okind oslot ogen principal pool ops control))) (j (mv-nth 1 (fn2-op-reserve kind okind oslot ogen principal may-release ops)))
                            (b (and (equal (mv-nth 0 (fn2-core-lease kind slot gen off len (mv-nth 1 (fn2-op-reserve kind okind oslot ogen principal may-release ops)) (mv-nth 2 (fn2-op-reserve kind okind oslot ogen principal may-release ops)) okind oslot ogen pool)) :ok) (or (equal kind *fn2-action-send*) (equal kind *fn2-action-write*)))))
                 (:instance fn2-op-reserve-borrow-row (may may-release))
                 fn2-issue-children-borrow-frame fn2-issue-children-borrow-row))))
(fn2-bc-ops-row-writer fn2-op-set-wake (slot gen deadline observation-gen ops) slot)
(defthm fn2-op-set-wake-keys-through
  (implies (fn2-ops-keys-except slot a ops)
           (fn2-ops-keys-except slot a (mv-nth 1 (fn2-op-set-wake slot gen deadline observation-gen ops))))
  :hints (("Goal" :in-theory (disable fn2-op-set-wake fn2-ops-keys-except fn2-ops-keys-except-trans)
           :use ((:instance fn2-ops-keys-except-trans (s slot) (a a) (b ops)
                            (c (mv-nth 1 (fn2-op-set-wake slot gen deadline observation-gen ops))))))))
(defthm fn2-borrows-accountedp-ops-transfer
  (implies (and (fn2-borrows-accountedp pool ops) (fn2-ops-keys-except j ops ops2)
                (natp j) (< j (fn2-ops-rows ops)) (natp (fn2-ops-rows ops))
                (equal (fn2-ops-rows ops2) (fn2-ops-rows ops))
                (not (fn2-op-borrowp j ops)) (not (fn2-op-borrowp j ops2))
                (implies (equal (fn2-ops-may-release j ops2) 1)
                         (equal (fn2-ops-kind j ops2) *fn2-action-send*)))
           (fn2-borrows-accountedp pool ops2))
  :hints (("Goal" :in-theory (e/d (fn2-op-borrow-on)
                                  (fn2-borrows-accountedp fn2-pool-borrows-countedp fn2-ops-borrows-namedp
                                   fn2-pool-borrows-countedp-transfer fn2-ops-borrows-namedp-transfer
                                   fn2-ops-keys-except fn2-op-borrowp-by-vals))
           :use ((:instance fn2-pool-borrows-countedp-transfer (pool2 pool) (ps 0))
                 (:instance fn2-ops-borrows-namedp-transfer (pool2 pool) (ps 0))
                 (:instance fn2-borrows-accountedp)
                 (:instance fn2-borrows-accountedp (ops ops2))))))
(defthm fn2-op-unreserve-ok-reserved
  (implies (equal (mv-nth 0 (fn2-op-unreserve slot gen ops)) :ok)
           (and (natp slot) (< slot (fn2-ops-rows ops))
                (equal (fn2-ops-phase slot ops) *fn2-op-phase-reserved*)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-op-unreserve fn2-op-phase-code fn2-op-handle-code fn2-op-slotp)
                                  (fn2-op-phase-code-by-row)))))
(defthm fn2-op-borrowp-when-reserved
  (implies (equal (fn2-ops-phase j x) *fn2-op-phase-reserved*) (not (fn2-op-borrowp j x)))
  :hints (("Goal" :in-theory (e/d (fn2-op-borrowp fn2-borrow-valsp) (fn2-op-borrowp-by-vals)))))
(defthm fn2-op-unreserve-borrows-accounted
  (implies (and (fn2-opsp ops) (fn2-ops-wfp ops) (fn2-borrows-accountedp pool ops))
           (fn2-borrows-accountedp pool (mv-nth 1 (fn2-op-unreserve slot gen ops))))
  :hints (("Goal" :cases ((equal (mv-nth 0 (fn2-op-unreserve slot gen ops)) :ok))
           :in-theory (e/d (fn2-op-phase-code fn2-op-handle-code fn2-op-slotp)
                           (fn2-op-unreserve fn2-borrows-accountedp fn2-borrows-accountedp-ops-transfer
                            fn2-ops-keys-except fn2-op-borrowp-by-vals fn2-op-phase-code-by-row))
           :use ((:instance fn2-borrows-accountedp-ops-transfer (j slot)
                            (ops2 (mv-nth 1 (fn2-op-unreserve slot gen ops))))
                 (:instance fn2-op-unreserve-ok-reserved)))))
;; An executable check of the invariant, equal to it: the teeth evaluate it.
(defun fn2-pool-borrows-counted-loop (k fn2-pool fn2-ops)
  (declare (xargs :stobjs (fn2-pool fn2-ops) :verify-guards nil :measure (nfix k)))
  (if (zp k) t
    (let ((r (- k 1)))
      (and (equal (fn2-pool-out-count r fn2-pool)
                  (fn2-ops-borrow-count (fn2-ops-rows fn2-ops) r fn2-ops))
           (implies (< 0 (fn2-pool-out-count r fn2-pool))
                    (equal (fn2-pool-state r fn2-pool) *fn2-pool-state-leased-out*))
           (fn2-pool-borrows-counted-loop (- k 1) fn2-pool fn2-ops)))))
(defun fn2-ops-borrows-named-loop (n fn2-pool fn2-ops)
  (declare (xargs :stobjs (fn2-pool fn2-ops) :verify-guards nil :measure (nfix n)))
  (if (zp n) t
    (let ((i (- n 1)))
      (and (implies (equal (fn2-ops-may-release i fn2-ops) 1)
                    (equal (fn2-ops-kind i fn2-ops) *fn2-action-send*))
           (implies (fn2-op-borrowp i fn2-ops)
                    (and (natp (fn2-ops-range-slot i fn2-ops))
                         (< (fn2-ops-range-slot i fn2-ops) (fn2-pool-rows fn2-pool))
                         (equal (fn2-ops-range-gen i fn2-ops)
                                (fn2-pool-gen (fn2-ops-range-slot i fn2-ops) fn2-pool))))
           (fn2-ops-borrows-named-loop (- n 1) fn2-pool fn2-ops)))))
(defun fn2-borrows-accounted-check (fn2-pool fn2-ops)
  (declare (xargs :stobjs (fn2-pool fn2-ops) :verify-guards nil))
  (and (fn2-pool-borrows-counted-loop (fn2-pool-rows fn2-pool) fn2-pool fn2-ops)
       (fn2-ops-borrows-named-loop (fn2-ops-rows fn2-ops) fn2-pool fn2-ops)))
(defthm fn2-pool-borrows-counted-loop-of-sk
  (implies (and (fn2-pool-borrows-countedp pool ops) (natp k) (<= k (fn2-pool-rows pool)))
           (fn2-pool-borrows-counted-loop k pool ops))
  :hints (("Goal" :induct (fn2-pool-borrows-counted-loop k pool ops)
           :in-theory (disable fn2-pool-borrows-countedp))
          ("Subgoal *1/2" :use ((:instance fn2-pool-borrows-countedp-necc (r (- k 1)))))))
(defthm fn2-pool-borrows-counted-loop-clause
  (implies (and (fn2-pool-borrows-counted-loop k pool ops) (natp k) (natp r) (< r k))
           (and (equal (fn2-pool-out-count r pool) (fn2-ops-borrow-count (fn2-ops-rows ops) r ops))
                (implies (< 0 (fn2-pool-out-count r pool))
                         (equal (fn2-pool-state r pool) *fn2-pool-state-leased-out*))))
  :hints (("Goal" :induct (fn2-pool-borrows-counted-loop k pool ops))))
(defthm fn2-ops-borrows-named-loop-of-sk
  (implies (and (fn2-ops-borrows-namedp pool ops) (natp n) (<= n (fn2-ops-rows ops)))
           (fn2-ops-borrows-named-loop n pool ops))
  :hints (("Goal" :induct (fn2-ops-borrows-named-loop n pool ops)
           :in-theory (disable fn2-ops-borrows-namedp))
          ("Subgoal *1/2" :use ((:instance fn2-ops-borrows-namedp-necc (i (- n 1)))))))
(defthm fn2-ops-borrows-named-loop-clause
  (implies (and (fn2-ops-borrows-named-loop n pool ops) (natp n) (natp i) (< i n))
           (and (implies (equal (fn2-ops-may-release i ops) 1)
                         (equal (fn2-ops-kind i ops) *fn2-action-send*))
                (implies (fn2-op-borrowp i ops)
                         (and (natp (fn2-ops-range-slot i ops))
                              (< (fn2-ops-range-slot i ops) (fn2-pool-rows pool))
                              (equal (fn2-ops-range-gen i ops)
                                     (fn2-pool-gen (fn2-ops-range-slot i ops) pool))))))
  :hints (("Goal" :induct (fn2-ops-borrows-named-loop n pool ops))))
(defthm fn2-borrows-accounted-check-equiv
  (implies (and (natp (fn2-pool-rows pool)) (natp (fn2-ops-rows ops)))
           (equal (fn2-borrows-accounted-check pool ops) (fn2-borrows-accountedp pool ops)))
  :hints (("Goal" :in-theory (e/d (fn2-borrows-accountedp)
                                  (fn2-pool-borrows-counted-loop fn2-ops-borrows-named-loop))
           :expand ((fn2-pool-borrows-countedp pool ops) (fn2-ops-borrows-namedp pool ops))
           :use ((:instance fn2-pool-borrows-counted-loop-clause (k (fn2-pool-rows pool))
                            (r (fn2-pool-borrows-countedp-witness pool ops)))
                 (:instance fn2-ops-borrows-named-loop-clause (n (fn2-ops-rows ops))
                            (i (fn2-ops-borrows-namedp-witness pool ops)))))))
(defun-nx fn2-pool-row-key-same (s a b)
  (and (equal (fn2-pool-out-count s b) (fn2-pool-out-count s a))
       (equal (fn2-pool-state s b) (fn2-pool-state s a))
       (equal (fn2-pool-gen s b) (fn2-pool-gen s a))))
(defun-nx fn2-pool-free-row-writep (s a b)
  (or (fn2-pool-row-key-same s a b)
      (and (not (equal (fn2-pool-state s a) *fn2-pool-state-leased-out*))
           (or (equal (fn2-pool-out-count s b) 0)
               (equal (fn2-pool-out-count s b) (fn2-pool-out-count s a))))))
(defthm fn2-ops-borrow-count-natp
  (natp (fn2-ops-borrow-count n r ops))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn2-op-borrow-on))))
(defthm fn2-ops-borrow-count-positive
  (implies (and (fn2-op-borrowp i ops) (equal (fn2-ops-range-slot i ops) r) (natp i) (< i (nfix n)))
           (< 0 (fn2-ops-borrow-count n r ops)))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-ops-borrow-count n r ops) :in-theory (enable fn2-op-borrow-on))))
(defthm fn2-pool-unleased-row-count
  (implies (and (fn2-pool-borrows-countedp pool ops) (natp s) (< s (fn2-pool-rows pool))
                (not (equal (fn2-pool-state s pool) *fn2-pool-state-leased-out*)))
           (and (equal (fn2-pool-out-count s pool) 0)
                (equal (fn2-ops-borrow-count (fn2-ops-rows ops) s ops) 0)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn2-pool-borrows-countedp-necc (r s)))
           :in-theory (disable fn2-pool-borrows-countedp fn2-pool-borrows-countedp-necc))))
(defthm fn2-pool-borrows-countedp-free-row
  (implies (and (fn2-pool-borrows-countedp pool ops) (fn2-pool-keys-except s pool p2)
                (equal (fn2-pool-rows p2) (fn2-pool-rows pool))
                (fn2-pool-free-row-writep s pool p2))
           (fn2-pool-borrows-countedp p2 ops))
  :hints (("Goal" :in-theory (e/d (fn2-pool-free-row-writep fn2-pool-row-key-same)
                                  (fn2-pool-borrows-countedp fn2-pool-keys-except
                                   fn2-pool-borrows-countedp-necc fn2-pool-keys-except-necc))
           :expand ((fn2-pool-borrows-countedp p2 ops))
           :cases ((equal (fn2-pool-borrows-countedp-witness p2 ops) s))
           :use ((:instance fn2-pool-borrows-countedp-necc (r (fn2-pool-borrows-countedp-witness p2 ops)))
                 (:instance fn2-pool-keys-except-necc (a pool) (b p2) (r (fn2-pool-borrows-countedp-witness p2 ops)))
                 (:instance fn2-pool-unleased-row-count)))))
(defthm fn2-ops-borrows-namedp-free-row
  (implies (and (fn2-pool-borrows-countedp pool ops) (fn2-ops-borrows-namedp pool ops) (natp (fn2-ops-rows ops))
                (fn2-pool-keys-except s pool p2)
                (equal (fn2-pool-rows p2) (fn2-pool-rows pool))
                (fn2-pool-free-row-writep s pool p2))
           (fn2-ops-borrows-namedp p2 ops))
  :hints (("Goal" :in-theory (e/d (fn2-pool-free-row-writep fn2-pool-row-key-same)
                                  (fn2-pool-borrows-countedp fn2-ops-borrows-namedp fn2-pool-keys-except
                                   fn2-ops-borrows-namedp-necc fn2-pool-keys-except-necc))
           :expand ((fn2-ops-borrows-namedp p2 ops))
           :cases ((equal (fn2-ops-range-slot (fn2-ops-borrows-namedp-witness p2 ops) ops) s))
           :use ((:instance fn2-ops-borrows-namedp-necc (i (fn2-ops-borrows-namedp-witness p2 ops)))
                 (:instance fn2-pool-keys-except-necc (a pool) (b p2)
                            (r (fn2-ops-range-slot (fn2-ops-borrows-namedp-witness p2 ops) ops)))
                 (:instance fn2-pool-unleased-row-count)
                 (:instance fn2-ops-borrow-count-positive (i (fn2-ops-borrows-namedp-witness p2 ops))
                            (r s) (n (fn2-ops-rows ops)))))))
(defthm fn2-borrows-accountedp-free-row-transfer
  (implies (and (fn2-borrows-accountedp pool ops) (fn2-pool-keys-except s pool p2) (natp (fn2-ops-rows ops))
                (equal (fn2-pool-rows p2) (fn2-pool-rows pool))
                (fn2-pool-free-row-writep s pool p2))
           (fn2-borrows-accountedp p2 ops))
  :hints (("Goal" :in-theory (union-theories '(fn2-borrows-accountedp fn2-pool-borrows-countedp-free-row
                                               fn2-ops-borrows-namedp-free-row)
                                             (theory 'minimal-theory)))))
(in-theory (disable fn2-pool-free-row-writep fn2-pool-row-key-same))
;; The data column and the loops over it are outside every key.
(defthm fn2-bc-pool-data-write-keys
  (and (equal (fn2-pool-out-count r (update-fn2-pool-datai i v pool)) (fn2-pool-out-count r pool))
       (equal (fn2-pool-state r (update-fn2-pool-datai i v pool)) (fn2-pool-state r pool))
       (equal (fn2-pool-gen r (update-fn2-pool-datai i v pool)) (fn2-pool-gen r pool))
       (equal (fn2-pool-rows (update-fn2-pool-datai i v pool)) (fn2-pool-rows pool)))
  :hints (("Goal" :in-theory (enable fn2-borrow-readers update-fn2-pool-datai))))
(defthm fn2-bc-pool-copy-up-keys
  (and (equal (fn2-pool-out-count r (fn2-pool-copy-up src dst n pool)) (fn2-pool-out-count r pool))
       (equal (fn2-pool-state r (fn2-pool-copy-up src dst n pool)) (fn2-pool-state r pool))
       (equal (fn2-pool-gen r (fn2-pool-copy-up src dst n pool)) (fn2-pool-gen r pool))
       (equal (fn2-pool-rows (fn2-pool-copy-up src dst n pool)) (fn2-pool-rows pool)))
  :hints (("Goal" :induct (fn2-pool-copy-up src dst n pool)
           :in-theory (e/d (fn2-pool-copy-up) (update-fn2-pool-datai fn2-borrow-readers)))))
(defthm fn2-bc-pool-copy-down-keys
  (and (equal (fn2-pool-out-count r (fn2-pool-copy-down src dst n pool)) (fn2-pool-out-count r pool))
       (equal (fn2-pool-state r (fn2-pool-copy-down src dst n pool)) (fn2-pool-state r pool))
       (equal (fn2-pool-gen r (fn2-pool-copy-down src dst n pool)) (fn2-pool-gen r pool))
       (equal (fn2-pool-rows (fn2-pool-copy-down src dst n pool)) (fn2-pool-rows pool)))
  :hints (("Goal" :induct (fn2-pool-copy-down src dst n pool)
           :in-theory (e/d (fn2-pool-copy-down) (update-fn2-pool-datai fn2-borrow-readers)))))
;; A row index that is not a natural reads and writes row 0.
(defthm fn2-bc-nth-of-non-natp
  (implies (not (natp n)) (equal (nth n l) (nth 0 l))))
(defthm fn2-bc-update-nth-of-non-natp
  (implies (not (natp n)) (equal (update-nth n v l) (update-nth 0 v l))))
(defthm fn2-bc-update-nth-array-of-non-natp
  (implies (not (natp i)) (equal (update-nth-array k i v l) (update-nth-array k 0 v l))))
(defthm fn2-bc-nth-of-cons-0
  (implies (and (natp r) (not (equal r 0))) (equal (nth r (cons a (cdr l))) (nth r l))))
(in-theory (disable fn2-bc-nth-of-non-natp fn2-bc-update-nth-of-non-natp fn2-bc-update-nth-array-of-non-natp
                    fn2-bc-nth-of-cons-0))
;; One pool writer: its effect on row SLOT, then the invariant.
(defmacro fn2-bc-pool-writer (name formals position slot &key enable (hyps 't))
  (let* ((call `(,name ,@formals)) (q `(mv-nth ,position ,call)) (slot `(nfix ,slot))
         (effect (intern-in-package-of-symbol (concatenate 'string (symbol-name name) "-FREE-ROW") name)))
    `(progn
       (defthm ,effect
         (implies ,hyps
                  (and (fn2-pool-keys-except ,slot pool ,q)
                       (equal (fn2-pool-rows ,q) (fn2-pool-rows pool))
                       (fn2-pool-free-row-writep ,slot pool ,q)))
         :hints (("Goal" :in-theory (e/d (,name fn2-pool-writers fn2-borrow-readers fn2-pool-handle-code
                                          fn2-pool-workspace-code fn2-pool-input-code fn2-pool-readable-code
                                          fn2-pool-free-row-writep fn2-pool-row-key-same fn2-pool-keys-except
                                          fn2-bc-nth-of-non-natp fn2-bc-update-nth-of-non-natp
                                          fn2-bc-update-nth-array-of-non-natp fn2-bc-nth-of-cons-0 ,@enable)
                                         (update-nth-array fn2-pool-ownerp fn2-pool-copy-up fn2-pool-copy-down
                                          update-fn2-pool-datai)))))
       (defthm ,(intern-in-package-of-symbol (concatenate 'string (symbol-name name) "-BORROWS-ACCOUNTED") name)
         (implies (and (fn2-borrows-accountedp pool ops) (natp (fn2-ops-rows ops)) ,hyps)
                  (fn2-borrows-accountedp ,q ops))
         :hints (("Goal" :in-theory (disable ,name ,effect fn2-borrows-accountedp fn2-borrows-accountedp-free-row-transfer)
                  :use (,effect (:instance fn2-borrows-accountedp-free-row-transfer (s ,slot) (p2 ,q)))))))))
(fn2-bc-pool-writer fn2-pool-reserve (class okind oslot ogen pool) 3 (fn2-pool-class-headsi class pool)
  :enable (update-fn2-pool-class-countsi update-fn2-pool-class-headsi))
(fn2-bc-pool-writer fn2-pool-release (slot gen okind oslot ogen pool) 1 slot)
(fn2-bc-pool-writer fn2-pool-lease-in (slot gen len opslot opgen okind oslot ogen pool) 2 slot)
(fn2-bc-pool-writer fn2-pool-adapter-write (slot gen opslot opgen idx byte pool) 1 slot)
(fn2-bc-pool-writer fn2-pool-complete-in (slot gen opslot opgen n pool) 1 slot)
(fn2-bc-pool-writer fn2-pool-hand (slot gen okind oslot ogen tkind tslot tgen pool) 1 slot)
(fn2-bc-pool-writer fn2-pool-accept-hand (slot gen tkind tslot tgen pool) 1 slot)
(fn2-bc-pool-writer fn2-pool-accept-own (slot gen okind oslot ogen pool) 1 slot :enable (fn2-pool-accept-hand))
(fn2-bc-pool-writer fn2-pool-write (slot gen idx byte okind oslot ogen pool) 1 slot)
(fn2-bc-pool-writer fn2-pool-reset (slot gen okind oslot ogen pool) 1 slot)
(fn2-bc-pool-writer fn2-pool-copy-range (src sgen soff dst dgen doff len okind oslot ogen pool) 1 dst)
(fn2-bc-pool-writer fn2-pool-drop-prefix (slot gen k cursor limit okind oslot ogen pool) 2 slot)
(fn2-bc-pool-writer fn2-pool-truncate (slot gen n okind oslot ogen pool) 1 slot)
(defthm fn2-core-release-children-borrows-accounted
  (implies (and (fn2-borrows-accountedp pool ops) (natp (fn2-ops-rows ops)))
           (fn2-borrows-accountedp (mv-nth 1 (fn2-core-release-children slot gen okind oslot ogen pool control)) ops))
  :hints (("Goal" :in-theory (e/d (fn2-core-release-children) (fn2-pool-release fn2-borrows-accountedp
                                                               fn2-control-record-stop fn2-pool-release-countp)))))
;; Their core faces.
(defun-sk fn2-ops-keys-same (a b)
  (forall i (implies (natp i) (equal (fn2-op-borrow-key i b) (fn2-op-borrow-key i a))))
  :rewrite :direct)
(defthm fn2-ops-keys-same-except
  (implies (fn2-ops-keys-same a b) (fn2-ops-keys-except s a b))
  :hints (("Goal" :in-theory (disable fn2-ops-keys-same fn2-ops-keys-same-necc)
           :expand ((fn2-ops-keys-except s a b))
           :use ((:instance fn2-ops-keys-same-necc (i (fn2-ops-keys-except-witness s a b)))))))
(defthm fn2-ops-keys-same-trans
  (implies (and (fn2-ops-keys-same a b) (fn2-ops-keys-same b c)) (fn2-ops-keys-same a c))
  :hints (("Goal" :in-theory (disable fn2-ops-keys-same fn2-ops-keys-same-necc)
           :expand ((fn2-ops-keys-same a c))
           :use ((:instance fn2-ops-keys-same-necc (i (fn2-ops-keys-same-witness a c)))
                 (:instance fn2-ops-keys-same-necc (a b) (b c) (i (fn2-ops-keys-same-witness a c)))))))
(defthm fn2-ops-keys-same-refl (fn2-ops-keys-same a a))
(defthm fn2-borrows-accountedp-keys-same-transfer
  (implies (and (fn2-borrows-accountedp pool ops) (fn2-ops-keys-same ops ops2)
                (equal (fn2-ops-rows ops2) (fn2-ops-rows ops)))
           (fn2-borrows-accountedp pool ops2))
  :hints (("Goal" :in-theory (e/d (fn2-borrows-accountedp)
                                  (fn2-pool-borrows-countedp fn2-ops-borrows-namedp fn2-ops-keys-same
                                   fn2-ops-keys-except fn2-pool-borrows-countedp-necc fn2-ops-borrows-namedp-necc
                                   fn2-ops-keys-same-except fn2-ops-borrow-count-except fn2-ops-keys-except-reads))
           :expand ((fn2-pool-borrows-countedp pool ops2) (fn2-ops-borrows-namedp pool ops2))
           :use ((:instance fn2-pool-borrows-countedp-necc (r (fn2-pool-borrows-countedp-witness pool ops2)))
                 (:instance fn2-ops-keys-same-except (a ops) (b ops2) (s (nfix (fn2-ops-rows ops))))
                 (:instance fn2-ops-borrow-count-except (s (nfix (fn2-ops-rows ops))) (a ops) (b ops2)
                            (n (fn2-ops-rows ops)) (r (fn2-pool-borrows-countedp-witness pool ops2)))
                 (:instance fn2-ops-borrows-namedp-necc (i (fn2-ops-borrows-namedp-witness pool ops2)))
                 (:instance fn2-ops-keys-same-except (a ops) (b ops2) (s (+ 1 (nfix (fn2-ops-borrows-namedp-witness pool ops2)))))
                 (:instance fn2-ops-keys-except-reads (a ops) (b ops2) (r 0)
                            (s (+ 1 (nfix (fn2-ops-borrows-namedp-witness pool ops2))))
                            (i (fn2-ops-borrows-namedp-witness pool ops2)))))))
;; A write outside the key's columns keeps every key.
(defconst *fn2-bc-key-columns* '(1 2 7 8 15 20 25 33 34))
(defthm fn2-op-borrow-key-of-update-nth-array-nonkey
  (implies (and (natp k) (not (member k *fn2-bc-key-columns*)))
           (equal (fn2-op-borrow-key i (update-nth-array k s v x)) (fn2-op-borrow-key i x)))
  :hints (("Goal" :in-theory (e/d (fn2-borrow-readers fn2-op-borrowp fn2-op-borrow-key) (fn2-op-borrowp-by-vals)))))
(defthm fn2-op-borrow-key-of-update-nth-nonkey
  (implies (and (natp k) (<= 44 k))
           (equal (fn2-op-borrow-key i (update-nth k v x)) (fn2-op-borrow-key i x)))
  :hints (("Goal" :in-theory (e/d (fn2-borrow-readers fn2-op-borrowp fn2-op-borrow-key) (fn2-op-borrowp-by-vals)))))
(defthm fn2-ops-keys-same-of-nonkey-write
  (implies (and (natp k) (not (member k *fn2-bc-key-columns*)))
           (and (fn2-ops-keys-same x (update-nth-array k s v x))
                (implies (<= 44 k) (fn2-ops-keys-same x (update-nth k v x)))))
  :hints (("Goal" :in-theory (disable update-nth-array fn2-op-borrowp-by-vals)
           :expand ((fn2-ops-keys-same x (update-nth-array k s v x)) (fn2-ops-keys-same x (update-nth k v x)))
           :cases ((<= 44 k)))))
(defthm fn2-ops-keys-same-through-nonkey-write
  (implies (and (fn2-ops-keys-same a x) (natp k) (not (member k *fn2-bc-key-columns*)))
           (fn2-ops-keys-same a (update-nth-array k s v x)))
  :hints (("Goal" :in-theory (disable fn2-ops-keys-same update-nth-array fn2-ops-keys-same-trans
                                      fn2-ops-keys-same-of-nonkey-write)
           :use ((:instance fn2-ops-keys-same-trans (b x) (c (update-nth-array k s v x)))
                 fn2-ops-keys-same-of-nonkey-write))))
(defmacro fn2-bc-ops-keys-kept (name formals position &key enable)
  (let ((q (if position `(mv-nth ,position (,name ,@formals)) `(,name ,@formals))))
    `(defthm ,(intern-in-package-of-symbol (concatenate 'string (symbol-name name) "-KEYS-SAME") name)
       (and (fn2-ops-keys-same ops ,q) (equal (fn2-ops-rows ,q) (fn2-ops-rows ops)))
       :hints (("Goal" :in-theory (e/d (,name fn2-ops-writers fn2-ops-keys-same ,@enable)
                                       (update-nth-array fn2-ops-rows fn2-op-borrowp-by-vals)))
               (and stable-under-simplificationp
                    '(:in-theory (e/d (,name fn2-ops-writers fn2-ops-rows fn2-ops-keys-same ,@enable)
                                      (update-nth-array fn2-op-borrowp-by-vals))))))))
(fn2-bc-ops-keys-kept fn2-count-stray (ops) nil)
(fn2-bc-ops-keys-kept fn2-post-clock (mono real flags ops) nil)
(fn2-bc-ops-keys-kept fn2-post-signal (bits ops) nil)
(fn2-bc-ops-keys-kept fn2-op-request-cancel (slot gen ops) 1)
;; Post-result: the posted cell's harvest bit is clear before and after, and
;; a c1 post comes only on a send whose borrow is retained (release-pending)
;; or not yet released (submitted), so the row's borrow is the same.
(defthm fn2-bc-row-cell-order
  (implies (and (fn2-ops-semanticp ops) (natp slot) (< slot (fn2-ops-rows ops)))
           (let ((phase (fn2-ops-phase slot ops)) (h0 (fn2-ops-c0-harvested slot ops))
                 (p0 (fn2-ops-c0-posted slot ops)) (p1 (fn2-ops-c1-posted slot ops))
                 (h1 (fn2-ops-c1-harvested slot ops)))
             (and (<= h0 p0) (<= h1 p1)
                  (implies (equal phase *fn2-op-phase-submitted*) (equal h0 0))
                  (implies (equal phase *fn2-op-phase-release-pending*)
                           (and (equal h0 1) (equal h1 0)
                                (or (and (equal (fn2-ops-kind slot ops) *fn2-action-send*)
                                         (equal (fn2-ops-c0-aux0 slot ops) 1))
                                    (equal p1 1)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-bc-row-body) (fn2-ops-semanticp fn2-post-payloadp))
           :use ((:instance fn2-ops-semanticp-row-facts)
                 (:instance fn2-ops-row-semanticp-body-at (j slot) (n (fn2-ops-rows ops)))))))
(defthm fn2-post-result-keys-same
  (implies (fn2-ops-semanticp ops)
           (and (fn2-ops-keys-same ops (fn2-post-result cell slot gen evkind outcome reason count aux0 aux1 ops))
                (equal (fn2-ops-rows (fn2-post-result cell slot gen evkind outcome reason count aux0 aux1 ops))
                       (fn2-ops-rows ops))))
  :hints (("Goal" :in-theory (e/d (fn2-post-result fn2-ops-writers fn2-post-eligiblep fn2-op-handle-code fn2-op-slotp
                                   fn2-count-stray fn2-ops-keys-same)
                                  (update-nth-array fn2-post-payloadp fn2-ops-semanticp
                                   fn2-op-borrowp-by-vals))
           :cases ((equal (fn2-ops-keys-same-witness ops (fn2-post-result cell slot gen evkind outcome reason count aux0 aux1 ops))
                          slot))
           :use ((:instance fn2-bc-row-cell-order)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (fn2-post-result fn2-ops-writers fn2-post-eligiblep fn2-op-handle-code fn2-op-slotp
                                  fn2-count-stray fn2-op-borrow-key fn2-op-borrowp fn2-borrow-valsp fn2-borrow-readers
                                  fn2-bc-row-body fn2-ops-keys-same)
                                 (update-nth-array fn2-post-payloadp fn2-ops-semanticp
                                  fn2-op-borrowp-by-vals fn2-ops-row-semanticp fn2-ops-semanticp-row-facts))))))
(defthm fn2-post-accept-result-keys-same
  (implies (fn2-ops-semanticp ops)
           (and (fn2-ops-keys-same ops (fn2-post-accept-result slot gen outcome reason cap-index cap-nonce
                                                               family port w0 w1 w2 w3 ops))
                (equal (fn2-ops-rows (fn2-post-accept-result slot gen outcome reason cap-index cap-nonce
                                                             family port w0 w1 w2 w3 ops))
                       (fn2-ops-rows ops))))
  :hints (("Goal" :in-theory (e/d (fn2-post-accept-result fn2-ops-writers)
                                  (update-nth-array fn2-ops-keys-same fn2-post-result fn2-ops-semanticp fn2-ops-keys-same-trans
                                   fn2-count-stray fn2-ops-rows fn2-peer-recordp fn2-op-slotp))
           :use ((:instance fn2-post-result-keys-same (cell 0) (evkind *fn2-event-accept-result*) (count 0)
                            (aux0 cap-index) (aux1 cap-nonce))))))
;; Ack: each acknowledged row is queued (fn2-outbox-prefixp), so a send or
;; write moves only queued -> submitted and keeps its borrow; a row named
;; twice in the prefix is submitted at its second visit and stays so.
(defun-nx fn2-bc-ack-row-okp (slot ops)
  (or (not (or (equal (fn2-ops-kind slot ops) *fn2-action-send*)
               (equal (fn2-ops-kind slot ops) *fn2-action-write*)))
      (equal (fn2-ops-phase slot ops) *fn2-op-phase-queued*)
      (equal (fn2-ops-phase slot ops) *fn2-op-phase-submitted*)))
(defun-nx fn2-bc-ack-okp (n index ops)
  (declare (xargs :measure (nfix n)))
  (if (zp n) t
    (and (fn2-bc-ack-row-okp (fn2-ops-out-sloti index ops) ops)
         (fn2-bc-ack-okp (- n 1) (fn2-ring-next index (fn2-ops-out-slot-length ops)) ops))))
(defthm fn2-bc-ack-okp-of-prefixp
  (implies (fn2-outbox-prefixp n index ops) (fn2-bc-ack-okp n index ops))
  :hints (("Goal" :induct (fn2-outbox-prefixp n index ops)
           :in-theory (e/d (fn2-op-phase-code fn2-op-handle-code fn2-bc-ack-row-okp) (fn2-op-phase-code-by-row)))))
(defun-nx fn2-bc-ack-step (slot ops)
  (update-nth-array 1 slot (fn2-op-ack-phase (fn2-ops-kind slot ops)) ops))
(defthm fn2-bc-ack-step-row-okp
  (implies (and (fn2-bc-ack-row-okp r ops) (natp slot))
           (fn2-bc-ack-row-okp r (fn2-bc-ack-step slot ops)))
  :hints (("Goal" :cases ((natp r)))
          ("Subgoal 2" :in-theory (e/d (fn2-bc-ack-row-okp fn2-bc-ack-step fn2-borrow-readers fn2-op-ack-phase
                                        fn2-action-completionp fn2-bc-nth-of-non-natp)
                                       (update-nth-array)))
          ("Subgoal 1" :in-theory (e/d (fn2-bc-ack-row-okp fn2-bc-ack-step fn2-borrow-readers fn2-op-ack-phase
                                        fn2-action-completionp)
                                       (update-nth-array)))))
(defthm fn2-bc-ack-row-okp-of-update-nth
  (implies (and (natp k) (not (equal k 1)) (not (equal k 2)))
           (equal (fn2-bc-ack-row-okp r (update-nth k v ops)) (fn2-bc-ack-row-okp r ops)))
  :hints (("Goal" :in-theory (enable fn2-bc-ack-row-okp fn2-borrow-readers))))
(defthm fn2-bc-out-slot-frames
  (and (implies (and (natp k) (not (equal k 45)))
                (and (equal (fn2-ops-out-sloti i (update-nth k v ops)) (fn2-ops-out-sloti i ops))
                     (equal (fn2-ops-out-slot-length (update-nth k v ops)) (fn2-ops-out-slot-length ops))))
       (equal (fn2-ops-out-sloti i (fn2-bc-ack-step slot ops)) (fn2-ops-out-sloti i ops))
       (equal (fn2-ops-out-slot-length (fn2-bc-ack-step slot ops)) (fn2-ops-out-slot-length ops)))
  :hints (("Goal" :in-theory (e/d (fn2-ops-out-sloti fn2-ops-out-slot-length fn2-bc-ack-step) (update-nth-array)))))
(defthm fn2-bc-ack-okp-of-step
  (implies (and (fn2-bc-ack-okp n index ops) (natp slot))
           (fn2-bc-ack-okp n index (fn2-bc-ack-step slot ops)))
  :hints (("Goal" :induct (fn2-bc-ack-okp n index ops)
           :in-theory (disable fn2-bc-ack-row-okp fn2-bc-ack-step fn2-ops-out-sloti fn2-ops-out-slot-length))))
(defthm fn2-bc-ack-okp-of-update-nth
  (implies (and (natp k) (not (equal k 1)) (not (equal k 2)) (not (equal k 45)))
           (equal (fn2-bc-ack-okp n index (update-nth k v ops)) (fn2-bc-ack-okp n index ops)))
  :hints (("Goal" :induct (fn2-bc-ack-okp n index ops)
           :in-theory (disable fn2-bc-ack-row-okp fn2-ops-out-sloti fn2-ops-out-slot-length))))
(defthm fn2-bc-ack-step-keys-same
  (implies (and (fn2-bc-ack-row-okp slot ops) (natp slot))
           (fn2-ops-keys-same ops (fn2-bc-ack-step slot ops)))
  :hints (("Goal" :in-theory (e/d (fn2-ops-keys-same fn2-bc-ack-step fn2-bc-ack-row-okp fn2-op-borrow-key
                                   fn2-op-borrowp fn2-borrow-valsp fn2-borrow-readers fn2-op-ack-phase
                                   fn2-action-completionp)
                                  (update-nth-array fn2-op-borrowp-by-vals)))))
(defthm fn2-ops-keys-same-through-scalar
  (implies (and (fn2-ops-keys-same a x) (natp k) (<= 44 k))
           (fn2-ops-keys-same a (update-nth k v x)))
  :hints (("Goal" :in-theory (disable fn2-ops-keys-same fn2-ops-keys-same-trans fn2-ops-keys-same-of-nonkey-write)
           :use ((:instance fn2-ops-keys-same-trans (b x) (c (update-nth k v x)))
                 (:instance fn2-ops-keys-same-of-nonkey-write (s 0))))))
(defthm fn2-ops-keys-same-trans-back
  (implies (and (fn2-ops-keys-same b c) (fn2-ops-keys-same a b)) (fn2-ops-keys-same a c))
  :hints (("Goal" :use fn2-ops-keys-same-trans :in-theory (disable fn2-ops-keys-same fn2-ops-keys-same-trans))))
(defthm fn2-bc-submit-step-is-ack-step
  (equal (fn2-ops-set-phase slot (fn2-op-ack-phase (fn2-ops-kind slot ops)) ops) (fn2-bc-ack-step slot ops))
  :hints (("Goal" :in-theory (enable fn2-ops-writers fn2-bc-ack-step))))
(defthm fn2-bc-ack-step-rows
  (equal (fn2-ops-rows (fn2-bc-ack-step slot ops)) (fn2-ops-rows ops))
  :hints (("Goal" :in-theory (e/d (fn2-bc-ack-step fn2-ops-rows) (update-nth-array)))))
(defthm fn2-outbox-submit-prefix-keys-same
  (implies (fn2-bc-ack-okp n (fn2-ops-out-head ops) ops)
           (and (fn2-ops-keys-same ops (fn2-outbox-submit-prefix n ops))
                (equal (fn2-ops-rows (fn2-outbox-submit-prefix n ops)) (fn2-ops-rows ops))))
  :hints (("Goal" :induct (fn2-outbox-submit-prefix n ops)
           :in-theory (e/d ((:induction fn2-outbox-submit-prefix) update-fn2-ops-out-head update-fn2-ops-queued
                            fn2-ops-out-head fn2-ops-rows fn2-op-slotp)
                           (fn2-ops-keys-same fn2-bc-ack-okp fn2-bc-ack-row-okp update-nth-array
                            fn2-bc-ack-step fn2-ops-out-sloti fn2-ops-out-slot-length fn2-ops-kind
                            fn2-ops-keys-same-trans fn2-op-ack-phase fn2-action-completionp)))
          (and stable-under-simplificationp
               '(:expand ((fn2-outbox-submit-prefix n ops) (fn2-bc-ack-okp n (fn2-ops-out-head ops) ops)
                          (fn2-bc-ack-okp n (nth 48 ops) ops))))))
(defthm fn2-outbox-ack-keys-same
  (and (fn2-ops-keys-same ops (mv-nth 1 (fn2-outbox-ack n ops)))
       (equal (fn2-ops-rows (mv-nth 1 (fn2-outbox-ack n ops))) (fn2-ops-rows ops)))
  :hints (("Goal" :in-theory (e/d (fn2-outbox-ack) (fn2-ops-keys-same fn2-outbox-prefixp fn2-outbox-submit-prefix)))))
(fn2-bc-ops-keys-kept fn2-take-clock (ops) 4)
(fn2-bc-ops-keys-kept fn2-take-signal (ops) 1)
(defmacro fn2-bc-ops-kept-accounted (name formals position &key semantic)
  (let* ((q (if position `(mv-nth ,position (,name ,@formals)) `(,name ,@formals)))
         (keys (intern-in-package-of-symbol (concatenate 'string (symbol-name name) "-KEYS-SAME") name)))
    `(defthm ,(intern-in-package-of-symbol (concatenate 'string (symbol-name name) "-BORROWS-ACCOUNTED") name)
       (implies (and (fn2-borrows-accountedp pool ops) ,@(and semantic '((fn2-ops-semanticp ops))))
                (fn2-borrows-accountedp pool ,q))
       :hints (("Goal" :in-theory (disable ,name fn2-borrows-accountedp ,keys fn2-borrows-accountedp-keys-same-transfer
                                          fn2-ops-semanticp)
                :use (,keys (:instance fn2-borrows-accountedp-keys-same-transfer (ops2 ,q))))))))
(fn2-bc-ops-kept-accounted fn2-count-stray (ops) nil)
(fn2-bc-ops-kept-accounted fn2-post-clock (mono real flags ops) nil)
(fn2-bc-ops-kept-accounted fn2-post-signal (bits ops) nil)
(fn2-bc-ops-kept-accounted fn2-take-clock (ops) 4)
(fn2-bc-ops-kept-accounted fn2-take-signal (ops) 1)
(fn2-bc-ops-kept-accounted fn2-op-request-cancel (slot gen ops) 1)
(fn2-bc-ops-kept-accounted fn2-outbox-ack (n ops) 1)
(fn2-bc-ops-kept-accounted fn2-post-result (cell slot gen evkind outcome reason count aux0 aux1 ops) nil :semantic t)
(fn2-bc-ops-kept-accounted fn2-post-accept-result
  (slot gen outcome reason cap-index cap-nonce family port w0 w1 w2 w3 ops) nil :semantic t)
;; Finish recycles a done row, which holds no borrow before or after.
(defthm fn2-op-finish-refused
  (implies (not (and (natp slot) (< slot (fn2-ops-rows ops)) (equal (fn2-ops-phase slot ops) *fn2-op-phase-done*)))
           (equal (mv-nth 1 (fn2-op-finish slot gen ops)) ops))
  :hints (("Goal" :in-theory (e/d (fn2-op-finish fn2-op-phase-code fn2-op-handle-code fn2-op-slotp fn2-op-recycle)
                                  (fn2-op-phase-code-by-row)))))
(defthm fn2-op-borrowp-when-done
  (implies (equal (fn2-ops-phase j x) *fn2-op-phase-done*) (not (fn2-op-borrowp j x)))
  :hints (("Goal" :in-theory (e/d (fn2-op-borrowp fn2-borrow-valsp) (fn2-op-borrowp-by-vals)))))
(defthm fn2-op-finish-borrows-accounted
  (implies (and (fn2-borrows-accountedp pool ops) (natp (fn2-ops-rows ops)))
           (fn2-borrows-accountedp pool (mv-nth 1 (fn2-op-finish slot gen ops))))
  :hints (("Goal" :cases ((and (natp slot) (< slot (fn2-ops-rows ops))
                               (equal (fn2-ops-phase slot ops) *fn2-op-phase-done*)))
           :in-theory (e/d (fn2-borrows-accountedp)
                           (fn2-op-finish fn2-pool-borrows-countedp fn2-ops-borrows-namedp fn2-ops-keys-except
                            fn2-borrows-accountedp-ops-transfer fn2-op-borrowp-by-vals fn2-op-finish-row
                            fn2-ops-borrows-namedp-necc))
           :use ((:instance fn2-borrows-accountedp-ops-transfer (j slot) (ops2 (mv-nth 1 (fn2-op-finish slot gen ops))))
                 fn2-op-finish-row
                 (:instance fn2-ops-borrows-namedp-necc (i slot))
                 (:instance fn2-op-borrowp-when-done (j slot) (x ops))))))
