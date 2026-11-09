; A2, the borrow count: every pool row's out-count is the number of live
; send/write operations on that row that have not released their borrow.
(in-package "ACL2")
(include-book "assembly-core")
(include-book "ops-conservation")

(defun fn2-borrow-valsp (kind phase h0 p1 h1 aux0)
  (declare (xargs :guard t))
  (and (or (equal kind *fn2-action-send*) (equal kind *fn2-action-write*))
       (or (equal phase *fn2-op-phase-queued*) (equal phase *fn2-op-phase-submitted*)
           (equal phase *fn2-op-phase-release-pending*))
       (not (equal h1 1))
       (not (and (equal h0 1) (equal p1 0)
                 (not (and (equal kind *fn2-action-send*) (equal aux0 1)))))))
(defun-nx fn2-op-borrowp (i ops)
  (fn2-borrow-valsp (fn2-ops-kind i ops) (fn2-ops-phase i ops) (fn2-ops-c0-harvested i ops)
                    (fn2-ops-c1-posted i ops) (fn2-ops-c1-harvested i ops) (fn2-ops-c0-aux0 i ops)))
(defun-nx fn2-op-borrow-on (i r ops)
  (if (and (fn2-op-borrowp i ops) (equal (fn2-ops-range-slot i ops) r)) 1 0))
(defun-nx fn2-ops-borrow-count (n r ops)
  (declare (xargs :measure (nfix n)))
  (if (zp n) 0
    (+ (fn2-op-borrow-on (- n 1) r ops) (fn2-ops-borrow-count (- n 1) r ops))))
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
(defthm fn2-core-stop-children
  (and (equal (fn2-core-ops (fn2-core-stop reason core)) (fn2-core-ops core))
       (equal (fn2-core-pool (fn2-core-stop reason core)) (fn2-core-pool core)))
  :hints (("Goal" :in-theory (enable fn2-core-stop))))
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
(defthm fn2-harvest-one-children
  (and (equal (fn2-core-pool (mv-nth 10 (fn2-harvest-one core)))
              (mv-nth 1 (fn2-bc-harvest-pool-step (fn2-core-pool core) (fn2-core-ops core))))
       (equal (fn2-core-ops (mv-nth 10 (fn2-harvest-one core)))
              (fn2-bc-harvest-ops (fn2-core-pool core) (fn2-core-ops core))))
  :hints (("Goal" :in-theory (e/d (fn2-harvest-one fn2-bc-harvest-pool-step fn2-bc-harvest-ops
                                   fn2-bc-input-condp fn2-bc-release-condp)
                                  (fn2-harvest-next fn2-op-finish fn2-pool-release-out fn2-pool-complete-in
                                   fn2-core-stop fn2-op-cell fn2-op-range fn2-op-slotp fn2-op-phase
                                   fn2-bc-release-condp-by-vals fn2-op-borrowp-by-vals)))))
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
  :hints (("Goal" :in-theory (e/d (fn2-bc-harvest-ops fn2-op-slotp fn2-op-phase)
                                  (fn2-harvest-next fn2-op-finish fn2-pool-release-out fn2-pool-complete-in
                            fn2-borrows-accountedp fn2-pool-borrows-countedp fn2-op-borrowp-by-vals
                            fn2-bc-release-condp-by-vals
                            fn2-ops-borrows-namedp fn2-ops-semanticp fn2-ops-keys-except fn2-pool-keys-except
                            fn2-op-cell fn2-bc-input-condp fn2-bc-release-condp fn2-bc-harvest-pool-step fn2-harvest-next-found fn2-op-finish-row))
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
(defthm fn2-bc-harvest-borrows
  (implies (and (fn2-ops-semanticp ops)
                (fn2-borrows-accountedp pool ops))
           (fn2-borrows-accountedp (mv-nth 1 (fn2-bc-harvest-pool-step pool ops)) (fn2-bc-harvest-ops pool ops)))
  :hints (("Goal"
           :cases ((equal (mv-nth 0 (fn2-harvest-next ops)) t))
           :in-theory (e/d (fn2-op-borrow-on)
                           (fn2-harvest-next fn2-bc-harvest-pool-step fn2-bc-harvest-ops
                            fn2-borrows-accountedp fn2-pool-borrows-countedp fn2-op-borrowp-by-vals
                            fn2-bc-release-condp-by-vals fn2-pool-borrows-countedp-transfer
                            fn2-ops-borrows-namedp-transfer fn2-harvest-next-borrow-release
                            fn2-ops-borrows-namedp fn2-ops-semanticp fn2-ops-keys-except fn2-pool-keys-except
                            fn2-bc-harvest-pool-count fn2-bc-harvest-ops-row))
           :use ((:instance fn2-pool-borrows-countedp-transfer (pool2 (mv-nth 1 (fn2-bc-harvest-pool-step pool ops))) (ops2 (fn2-bc-harvest-ops pool ops)) (j (mv-nth 1 (fn2-harvest-next ops))) (ps (fn2-ops-range-slot (mv-nth 1 (fn2-harvest-next ops)) ops)))
                 (:instance fn2-ops-borrows-namedp-transfer (pool2 (mv-nth 1 (fn2-bc-harvest-pool-step pool ops))) (ops2 (fn2-bc-harvest-ops pool ops)) (j (mv-nth 1 (fn2-harvest-next ops))) (ps (fn2-ops-range-slot (mv-nth 1 (fn2-harvest-next ops)) ops)))
                 (:instance fn2-borrows-accountedp)
                 (:instance fn2-borrows-accountedp (pool (mv-nth 1 (fn2-bc-harvest-pool-step pool ops))) (ops (fn2-bc-harvest-ops pool ops)))
                 (:instance fn2-ops-borrows-namedp-necc (i (mv-nth 1 (fn2-harvest-next ops))))
                 fn2-harvest-next-found fn2-harvest-next-borrow-release fn2-bc-harvest-pool-count
                 fn2-bc-harvest-ops-row
                 (:instance fn2-ops-range-slot-natp (i (mv-nth 1 (fn2-harvest-next ops))) (fn2-ops ops))))))
(defun-nx fn2-core-borrows-accountedp (core)
  (fn2-borrows-accountedp (fn2-core-pool core) (fn2-core-ops core)))
(defthm fn2-harvest-one-borrows-accounted
  (implies (and (fn2-ops-semanticp (fn2-core-ops core))
                (fn2-core-borrows-accountedp core))
           (fn2-core-borrows-accountedp (mv-nth 10 (fn2-harvest-one core))))
  :hints (("Goal" :in-theory (e/d (fn2-core-borrows-accountedp)
                                  (fn2-harvest-one fn2-borrows-accountedp fn2-ops-semanticp
                                   fn2-bc-harvest-pool-step fn2-bc-harvest-ops))
           :use ((:instance fn2-bc-harvest-borrows (pool (fn2-core-pool core)) (ops (fn2-core-ops core)))))))
