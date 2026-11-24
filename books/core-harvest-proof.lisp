; Input settlement at the served core's harvest boundary.

(in-package "ACL2")

(include-book "assembly-core")
(include-book "owed-discharge")
(local (include-book "ops-harvest-phase"))

; The even FIFO entry names the pending terminal cell of a submitted row.
(local
 (progn
  (defthm fn2-byte-fill-parity
    (implies (and (integerp a) (integerp b))
             (not (equal (* 2 a) (+ -1 (* 2 b)))))
    :hints (("Goal" :cases ((< a b) (equal a b)))))
  (defthm fn2-byte-fill-double-cancel
    (implies (and (acl2-numberp a) (acl2-numberp b))
             (equal (equal (* 2 a) (+ -2 (* 2 b))) (equal a (+ -1 b)))))
  (defthm fn2-byte-fill-pending-even
    (implies (and (natp s) (member-equal (* 2 s) (fn2-ops-pending-cells n ops)))
             (and (equal (fn2-ops-c0-posted s ops) 1)
                  (equal (fn2-ops-c0-harvested s ops) 0)))
    :rule-classes nil
    :hints (("Goal" :induct (fn2-ops-pending-cells n ops)
             :in-theory (disable fn2-ops-c0-posted fn2-ops-c0-harvested fn2-ops-c1-posted fn2-ops-c1-harvested))))
  (defthm fn2-byte-fill-posted-head
    (implies (posp (fn2-ops-post-count ops))
             (member-equal (fn2-ops-posted-fifoi (fn2-ops-post-head ops) ops)
                           (fn2-ops-posted-list ops)))
    :rule-classes nil
    :hints (("Goal" :in-theory (disable fn2-ops-posted-fifoi fn2-ops-post-head fn2-ops-post-count fn2-ops-posted-fifo-length)
             :expand ((fn2-ops-posted-list-aux (fn2-ops-post-count ops) (fn2-ops-post-head ops) ops)))))
  (defthm fn2-byte-fill-member-of-subsetp
    (implies (and (subsetp-equal a b) (member-equal x a)) (member-equal x b))
    :rule-classes nil)
  (encapsulate ()
    (local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))
    (defthm fn2-byte-fill-floor-mod-double
      (implies (integerp s)
               (and (equal (floor (* 2 s) 2) s) (equal (mod (* 2 s) 2) 0)))))
  (defthm fn2-byte-fill-peek
    (implies (and (fn2-ops-semanticp ops) (fn2-op-slotp s ops)
                  (< 0 (fn2-ops-post-count ops))
                  (equal (fn2-ops-posted-fifoi (fn2-ops-post-head ops) ops) (* 2 s)))
             (and (equal (mv-nth 0 (fn2-ops-peek-posted ops)) t)
                  (equal (mv-nth 1 (fn2-ops-peek-posted ops)) s)
                  (equal (mv-nth 2 (fn2-ops-peek-posted ops)) 0)))
    :rule-classes nil
    :hints (("Goal" :in-theory (e/d (fn2-ops-peek-posted fn2-op-slotp fn2-ops-semanticp fn2-ops-ring-shapep
                                     fn2-ops-same-membersp fn2-completion-phasep)
              (fn2-ops-phase fn2-ops-c0-posted fn2-ops-c0-harvested fn2-ops-c1-posted fn2-ops-c1-harvested
               fn2-ops-posted-fifoi fn2-ops-post-head fn2-ops-post-count fn2-ops-posted-fifo-length
               fn2-ops-posted-list fn2-ops-pending-cells fn2-ops-row-semanticp fn2-ops-rows fn2-ops-wfp fn2-opsp
               fn2-ops-phase-slots fn2-ops-free-chain fn2-ops-outbox-list fn2-ops-queued-refsp
               fn2-ops-outbox-credits fn2-ops-out-slot-length fn2-ops-out-gen-length floor mod))
             :use (fn2-byte-fill-posted-head
                   (:instance fn2-byte-fill-pending-even (n (fn2-ops-rows ops)))
                   (:instance fn2-byte-fill-member-of-subsetp (x (* 2 s)) (a (fn2-ops-posted-list ops))
                              (b (fn2-ops-pending-cells (fn2-ops-rows ops) ops)))
                   (:instance fn2-row-semantic-pending-phase
                              (n (fn2-ops-rows ops)) (fn2-ops ops) (slot s) (cell 0))
                   (:instance fn2-ops-phase-natp (i s) (fn2-ops ops))))))))

; Dequeuing that cell preserves its posted result and input range.
(local
 (defthm fn2-byte-fill-harvest-next
   (implies (and (equal (mv-nth 0 (fn2-ops-peek-posted ops)) t)
                 (equal (mv-nth 1 (fn2-ops-peek-posted ops)) s)
                 (equal (mv-nth 2 (fn2-ops-peek-posted ops)) 0)
                 (natp s))
            (let ((q (mv-nth 4 (fn2-harvest-next ops))))
              (and (equal (mv-nth 0 (fn2-harvest-next ops)) t)
                   (equal (mv-nth 1 (fn2-harvest-next ops)) s)
                   (equal (mv-nth 2 (fn2-harvest-next ops)) (fn2-ops-gen s ops))
                   (equal (mv-nth 3 (fn2-harvest-next ops)) 0)
                   (equal (fn2-ops-rows q) (fn2-ops-rows ops))
                   (equal (fn2-ops-c0-event s q) (fn2-ops-c0-event s ops))
                   (equal (fn2-ops-c0-outcome s q) (fn2-ops-c0-outcome s ops))
                   (equal (fn2-ops-c0-count s q) (fn2-ops-c0-count s ops))
                   (equal (fn2-ops-range-slot s q) (fn2-ops-range-slot s ops))
                   (equal (fn2-ops-range-gen s q) (fn2-ops-range-gen s ops)))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn2-harvest-next fn2-ops-latch-peer fn2-ops-set-c0-harvested fn2-ops-set-phase
                                    fn2-ops-rows update-fn2-ops-phase$ai update-fn2-ops-c0-harvested$ai
                                    update-fn2-ops-seen-peer-family update-fn2-ops-seen-peer-port
                                    update-fn2-ops-seen-peer-w0 update-fn2-ops-seen-peer-w1
                                    update-fn2-ops-seen-peer-w2 update-fn2-ops-seen-peer-w3
                                    update-fn2-ops-post-head update-fn2-ops-post-count)
                                   (fn2-ops-peek-posted fn2-op-harvest-phase fn2-ring-next))))))

; Completing the loan changes the readable extent and preserves the octets.
(local
 (progn
  (defthm fn2-byte-fill-pool-leased-row
    (implies (and (fn2-pool-row-invariantp n pool) (natp i) (< i n) (natp n)
                  (equal (fn2-pool-state i pool) *fn2-pool-state-leased-in*))
             (and (equal (fn2-pool-fill i pool) (fn2-pool-lease-off i pool))
                  (<= (+ (fn2-pool-lease-off i pool) (fn2-pool-lease-len i pool)) (fn2-pool-cap i pool))))
    :rule-classes nil
    :hints (("Goal" :induct (fn2-pool-row-invariantp n pool)
             :in-theory (e/d (fn2-pool-row-invariantp)
                             (fn2-pool-state fn2-pool-fill fn2-pool-lease-off fn2-pool-lease-len fn2-pool-cap
                              fn2-pool-base fn2-pool-class fn2-pool-gen fn2-pool-out-count fn2-pool-capacity-bytes
                              fn2-pool-gen-limit fn2-pool-nclasses fn2-pool-class-sizesi)))))
  (defthm fn2-byte-fill-octets-append
    (implies (and (natp a) (natp b) (acl2-numberp base))
             (equal (fn2-pool-logical-octets (+ a b) base pool)
                    (append (fn2-pool-logical-octets a base pool)
                            (fn2-pool-logical-octets b (+ base a) pool))))
    :hints (("Goal" :induct (fn2-pool-logical-octets a base pool)
             :in-theory (disable fn2-pool-datai))))
  (defthm fn2-byte-fill-octets-of-set-state
    (equal (fn2-pool-logical-octets n b (fn2-pool-set-state j v pool))
           (fn2-pool-logical-octets n b pool))
    :hints (("Goal" :induct (fn2-pool-logical-octets n b pool)
             :in-theory (enable fn2-pool-set-state update-fn2-pool-state$ai fn2-pool-datai))))
  (defthm fn2-byte-fill-pool-wfp-rows
    (implies (fn2-pool-wfp pool) (natp (fn2-pool-rows pool)))
    :rule-classes nil
    :hints (("Goal" :in-theory (union-theories '(fn2-pool-wfp) (theory 'minimal-theory)))))
  (defthm fn2-byte-fill-pool-sem-facts
    (implies (and (fn2-pool-semanticp pool) (fn2-pool-logical-slotp slot pool)
                  (equal (fn2-pool-state slot pool) *fn2-pool-state-leased-in*))
             (and (natp slot) (< slot (fn2-pool-rows pool))
                  (natp (fn2-pool-base slot pool)) (natp (fn2-pool-fill slot pool))
                  (equal (fn2-pool-fill slot pool) (fn2-pool-lease-off slot pool))
                  (<= (+ (fn2-pool-lease-off slot pool) (fn2-pool-lease-len slot pool))
                      (fn2-pool-cap slot pool))))
    :rule-classes nil
    :hints (("Goal" :in-theory (union-theories '(fn2-pool-semanticp fn2-pool-logical-slotp fn2-pool-nslots natp)
                                               (theory 'minimal-theory))
             :use (fn2-byte-fill-pool-wfp-rows
                   (:instance fn2-byte-fill-pool-leased-row (i slot) (n (fn2-pool-rows pool)))
                   (:instance fn2-pool-semanticp-row-bounds (i slot) (fn2-pool pool))))))
  (defthm fn2-byte-fill-complete-in-effect
    (implies (and (natp slot) (< slot (fn2-pool-rows pool))
                  (equal (fn2-pool-input-code slot gen opslot opgen pool) :ok)
                  (natp n) (<= n (fn2-pool-lease-len slot pool))
                  (<= (+ (fn2-pool-lease-off slot pool) n) (fn2-pool-cap slot pool)))
             (let ((q (mv-nth 1 (fn2-pool-complete-in slot gen opslot opgen n pool))))
               (and (equal (fn2-pool-state slot q) *fn2-pool-state-workspace*)
                    (equal (fn2-pool-fill slot q) (+ (fn2-pool-lease-off slot pool) n))
                    (equal (fn2-pool-base slot q) (fn2-pool-base slot pool))
                    (equal (fn2-pool-logical-octets m b q) (fn2-pool-logical-octets m b pool)))))
    :rule-classes nil
    :hints (("Goal" :in-theory (e/d (fn2-pool-complete-in fn2-pool-set-state fn2-pool-set-fill
                                     update-fn2-pool-state$ai update-fn2-pool-fill$ai)
                                    (fn2-pool-input-code fn2-pool-logical-octets fn2-pool-rows
                                     fn2-pool-lease-off fn2-pool-lease-len fn2-pool-cap
                                     fn2-byte-fill-octets-of-set-state fn2-pool-logical-octets-of-set-fill))
             :use ((:instance fn2-byte-fill-octets-of-set-state (n m) (j slot) (v *fn2-pool-state-workspace*))
                   (:instance fn2-pool-logical-octets-of-set-fill (n m) (j slot)
                              (v (+ (fn2-pool-lease-off slot pool) n))
                              (fn2-pool (fn2-pool-set-state slot *fn2-pool-state-workspace* pool)))))))
  (defthm fn2-byte-fill-complete-in
    (implies (and (fn2-pool-semanticp pool) (fn2-pool-logical-slotp slot pool)
                  (equal (fn2-pool-input-code slot gen opslot opgen pool) :ok)
                  (natp n) (<= n (fn2-pool-lease-len slot pool)))
             (let ((q (mv-nth 1 (fn2-pool-complete-in slot gen opslot opgen n pool))))
               (and (equal (fn2-pool-state slot q) *fn2-pool-state-workspace*)
                    (equal (fn2-pool-fill slot q) (+ (fn2-pool-lease-off slot pool) n))
                    (equal (fn2-pool-logical-octets (fn2-pool-fill slot q) (fn2-pool-base slot q) q)
                           (append (fn2-pool-logical-octets (fn2-pool-fill slot pool) (fn2-pool-base slot pool) pool)
                                   (fn2-pool-logical-octets n (+ (fn2-pool-base slot pool) (fn2-pool-lease-off slot pool)) pool))))))
    :rule-classes nil
    :hints (("Goal" :in-theory (union-theories '(fn2-pool-input-code natp fn2-byte-fill-octets-append)
                                               (theory 'minimal-theory))
             :use (fn2-byte-fill-pool-sem-facts
                   (:instance fn2-byte-fill-complete-in-effect (m (+ (fn2-pool-lease-off slot pool) n))
                              (b (fn2-pool-base slot pool)))))))))

; A stop records its reason in control. Completion hooks write only their
; registered extension children, even when a hook reports an error.
(local
 (defthm fn2-byte-fill-pool-of-stop
   (equal (fn2-core-pool (fn2-core-stop reason core)) (fn2-core-pool core))
   :hints (("Goal" :in-theory (enable fn2-core-stop)))))

(local
 (defthm fn2-byte-fill-pool-of-hooks
   (equal (fn2-core-pool
           (mv-nth 1 (fn2-core-harvest-hooks opslot opgen cell evkind outcome
                                             reason count aux0 aux1 core)))
          (fn2-core-pool core))
   :hints (("Goal" :in-theory
            (e/d (fn2-core-harvest-hooks
                  fn2-core-alloc-edges-harvest fn2-core-event-read-harvest
                  fn2-core-cns-sources-harvest)
                 (fn2-b-read-pin-harvest fn2-event-read-harvest
                  fn2-cns-source-harvest))))))

(local
 (defthm fn2-byte-fill-harvest-pool
   (implies (fn2-core-fill-hyps slot gen opslot opgen count written
                                (fn2-core-pool core) (fn2-core-ops core))
            (equal (fn2-core-pool (mv-nth 10 (fn2-harvest-one core)))
                   (mv-nth 1 (fn2-pool-complete-in slot gen opslot opgen count
                                                   (fn2-core-pool core)))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance fn2-byte-fill-peek (s opslot) (ops (fn2-core-ops core)))
                  (:instance fn2-byte-fill-harvest-next (s opslot) (ops (fn2-core-ops core))))
            :in-theory
            (union-theories
             '(fn2-harvest-one fn2-core-fill-hyps fn2-op-gen fn2-op-slotp
               fn2-op-cell fn2-op-range member-equal natp
               fn2-byte-fill-pool-of-hooks fn2-byte-fill-pool-of-stop
               fn2-core-pool-of-update-fn2-core-pool fn2-core-pool-of-update-fn2-core-ops
               fn2-core-ops-of-update-fn2-core-pool fn2-core-ops-of-update-fn2-core-ops
               mv-nth (:executable-counterpart mv-nth)
               (:executable-counterpart unsigned-byte-p) (:executable-counterpart equal))
             (theory 'minimal-theory))))))

(local
 (defthm fn2-byte-fill-harvest-result
   (let* ((before (fn2-core-pool core))
          (after (fn2-core-pool (mv-nth 10 (fn2-harvest-one core)))))
     (implies (fn2-core-fill-hyps slot gen opslot opgen count written before (fn2-core-ops core))
              (fn2-core-fill-resultp
               (fn2-pool-state slot after) (fn2-pool-fill slot after)
               (fn2-pool-lease-off slot before) count
               (fn2-pool-logical-octets (fn2-pool-fill slot before) (fn2-pool-base slot before) before)
               (fn2-pool-logical-octets (fn2-pool-fill slot after) (fn2-pool-base slot after) after)
               written)))
   :rule-classes nil
   :hints (("Goal" :use (fn2-byte-fill-harvest-pool
                         (:instance fn2-byte-fill-complete-in (pool (fn2-core-pool core)) (n count)))
            :in-theory (union-theories '(fn2-core-fill-hyps fn2-core-fill-resultp (:executable-counterpart natp))
                                       (theory 'minimal-theory))))))

; Apply the settlement result to the pool returned by the actual write trace.
(defthm fn2-core-harvest-byte-fill-proved
  (fn2-core-harvest-byte-fill$owed slot gen opslot opgen count written loan-core ready-ops)
  :rule-classes nil
  :hints (("Goal"
           :in-theory (union-theories '(fn2-core-harvest-byte-fill$owed)
                                      (theory 'minimal-theory))
           :use ((:instance fn2-byte-fill-harvest-result
                  (core (update-fn2-core-ops
                         ready-ops
                         (update-fn2-core-pool
                          (mv-nth 1 (fn2-core-evidence-initialize
                                     slot gen opslot opgen
                                     (fn2-pool-lease-off slot (fn2-core-pool loan-core))
                                     written (fn2-core-pool loan-core)))
                          loan-core))))))))

(fn2-owed-discharge fn2-core-harvest-byte-fill fn2-core-harvest-byte-fill-proved)
