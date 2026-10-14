; fn: structural permanent exhaustion and bounded state preservation.
(in-package "ACL2")
(include-book "runtime-contract-invariant-facts")
(local (make-event
  (if (getpropc 'fn-rtc-c-set-is-update-nth 'theorem nil (w state))
      '(in-theory (disable fn-rtc-c-set-is-update-nth))
    '(value-triple :concrete-slot-write-alias-absent))))


(defthm fn-rtc-inc-roomp-monotone-negative
  (implies (and (not (fn-rtc-inc-roomp old))
                (<= (fn-rtc-s-inc old) (fn-rtc-s-inc new)))
           (not (fn-rtc-inc-roomp new)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-inc-roomp) (fn-rtc-s-inc)))))
(defthm fn-rtc-slots-exhaustedp-set-monotone
  (implies (and (natp i) (natp nstatic) (natp k)
                (fn-rtc-slots-exhaustedp i nstatic slots)
                (<= (fn-rtc-s-inc (fn-rtc-get k slots)) (fn-rtc-s-inc slot)))
           (fn-rtc-slots-exhaustedp i nstatic (fn-rtc-set k slot slots)))
  :hints (("Goal" :induct (fn-rtc-index-induct k i slots)
           :do-not '(generalize)
           :expand ((fn-rtc-set k slot slots)
                    (fn-rtc-slots-exhaustedp i nstatic (fn-rtc-set k slot slots)))
           :in-theory (e/d (fn-rtc-slots-exhaustedp fn-rtc-set fn-rtc-get)
                           (fn-rtc-inc-roomp fn-rtc-s-inc)))))
(defthm fn-rtc-slot-write-keeps-exhaustion
  (implies (and (natp id) (natp nstatic)
                (fn-rtc-slots-exhaustedp 0 nstatic (fn-rtc-slots s))
                (<= (fn-rtc-s-inc (fn-rtc-slot id s)) (fn-rtc-s-inc slot)))
           (fn-rtc-slots-exhaustedp 0 nstatic (fn-rtc-slots (fn-rtc-with-slot id slot s))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-slot)
                (fn-rtc-slots-is-slot fn-rtc-slots-exhaustedp fn-rtc-get fn-rtc-s-inc))
           :use ((:instance fn-rtc-slots-exhaustedp-set-monotone
                   (i 0) (k id) (slots (fn-rtc-slots s)))))))
(defthm fn-rtc-retire-keeps-exhaustion
  (implies (and (natp id) (natp nstatic)
                (fn-rtc-slots-exhaustedp 0 nstatic (fn-rtc-slots s)))
           (fn-rtc-slots-exhaustedp 0 nstatic (fn-rtc-slots (fn-rtc-retire-drained id s))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-retire-drained)
       (fn-rtc-slots-exhaustedp fn-rtc-uses-of-slot-p fn-rtc-s-inc fn-rtc-s-status fn-rtc-slot)))))
(defthm fn-rtc-end-use-keeps-exhaustion
  (implies (and (natp nstatic) (fn-rtc-slots-exhaustedp 0 nstatic (fn-rtc-slots s)))
           (fn-rtc-slots-exhaustedp 0 nstatic (fn-rtc-slots (fn-rtc-end-use s e))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-end-use)
     (fn-rtc-slots-exhaustedp fn-rtc-retire-drained fn-rtc-end-lease fn-rtc-find-use fn-rtc-key fn-rtc-completionp)))))
(defthm fn-rtc-req-close-keeps-exhaustion
  (implies (and (natp nstatic) (fn-rtc-slots-exhaustedp 0 nstatic (fn-rtc-slots s)))
           (fn-rtc-slots-exhaustedp 0 nstatic (fn-rtc-slots (mv-nth 0 (fn-rtc-req-close r id inc s)))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-req-close fn-rtc-live-p)
     (fn-rtc-slots-exhaustedp fn-rtc-s-inc fn-rtc-s-status fn-rtc-slot fn-rtc-nstatic fn-rtc-next-op fn-rtc-s-res))
           :cases ((natp id)))))
(defthm fn-rtc-request-keeps-exhaustion
  (implies (and (natp nstatic) (fn-rtc-slots-exhaustedp 0 nstatic (fn-rtc-slots s)))
           (fn-rtc-slots-exhaustedp 0 nstatic (fn-rtc-slots (mv-nth 0 (fn-rtc-request r id inc s)))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-request fn-rtc-req-acquire fn-rtc-req-write fn-rtc-req-release fn-rtc-req-submit fn-rtc-req-cancel)
     (fn-rtc-slots-exhaustedp fn-rtc-req-close fn-rtc-buffered-kind-p fn-rtc-submit-okp fn-rtc-hand-target-okp
      fn-rtc-kind-extrap fn-rtc-kind-out-p fn-rtc-kind-op fn-rtc-live-p fn-rtc-current-p
      fn-rtc-buffer fn-rtc-b-gen fn-rtc-b-owner fn-rtc-b-bytes fn-rtc-h-buf fn-rtc-s-res fn-rtc-slot fn-rtc-get fn-rtc-next-op fn-rtc-splice))
           :use fn-rtc-req-close-keeps-exhaustion)))
(defthm fn-rtc-requests-keep-exhaustion
  (implies (and (natp nstatic) (fn-rtc-slots-exhaustedp 0 nstatic (fn-rtc-slots s)))
           (fn-rtc-slots-exhaustedp 0 nstatic (fn-rtc-slots (mv-nth 0 (fn-rtc-requests reqs id inc s)))))
  :hints (("Goal" :induct (fn-rtc-requests reqs id inc s)
           :in-theory (e/d (fn-rtc-requests) (fn-rtc-slots-exhaustedp fn-rtc-request mv-nth)))))
(defthm fn-rtc-deliver-keeps-exhaustion
  (implies (and (natp nstatic) (fn-rtc-slots-exhaustedp 0 nstatic (fn-rtc-slots s)))
           (fn-rtc-slots-exhaustedp 0 nstatic (fn-rtc-slots (mv-nth 0 (fn-rtc-deliver s id inc ev q)))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-deliver)
                  (fn-rtc-slots-exhaustedp fn-rtc-requests fn-rtc-live-p mv-nth)))))
(defthm fn-rtc-close-branch-keeps-exhaustion
  (implies (and (natp id) (natp nstatic) (equal inc (fn-rtc-s-inc (fn-rtc-slot id s)))
                (fn-rtc-slots-exhaustedp 0 nstatic (fn-rtc-slots s)))
           (fn-rtc-slots-exhaustedp 0 nstatic (fn-rtc-slots (mv-nth 0 (fn-rtc-close-branch s id inc)))))
  :hints (("Goal" :in-theory
           (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
             '(fn-rtc-close-branch fn-rtc-rearm-frame fn-rtc-with-accessors
               fn-rtc-make-accessors fn-rtc-slot fn-rtc-slot-accessors
               fn-rtc-slots-exhaustedp-set-monotone natp nfix
               (:type-prescription fn-rtc-s-inc))))))
(defthm fn-rtc-accept-branch-keeps-exhaustion
  (implies (and (natp nstatic)
                (fn-rtc-slots-exhaustedp 0 nstatic (fn-rtc-slots s)))
           (fn-rtc-slots-exhaustedp 0 nstatic
             (fn-rtc-slots (mv-nth 0 (fn-rtc-accept-branch s out q)))))
  :hints (("Goal" :in-theory
           (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
             '(fn-rtc-accept-branch fn-rtc-deliver-keeps-exhaustion
               fn-rtc-rearm-frame fn-rtc-with-accessors fn-rtc-slot fn-rtc-slot-accessors
               fn-rtc-slots-exhaustedp-set-monotone fn-rtc-free-slot-index-type
               natp nfix fix unicity-of-0 commutativity-of-+
               (:type-prescription fn-rtc-s-inc)
               (:type-prescription fn-rtc-free-slot))))))
(defthm fn-rtc-acting-close-incarnation
  (implies (and (fn-rtc-acts-on-p s e) (not (fn-rtc-hand-delivers-p s e)))
           (equal (fn-rtc-e-inc e)
                  (fn-rtc-s-inc (fn-rtc-slot (fn-rtc-e-id e) s))))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory) '(fn-rtc-acts-on-p)))))
(defthm fn-rtc-step*-state-is-step-state
  (equal (mv-nth 0 (fn-rtc-step* s e q)) (fn-rtc-step-state s e q))
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-step)
                (fn-rtc-step* fn-rtc-step-state fn-rtc-step-is-step-state))
           :use fn-rtc-step-is-step-state)))
(defthm fn-rtc-step*-preserves-invp
  (implies (fn-rtc-invp s)
           (fn-rtc-invp (mv-nth 0 (fn-rtc-step* s e q))))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
             '(fn-rtc-step*-state-is-step-state fn-rtc-step-is-step-state))
           :use fn-rtc-step-preserves-invp)))
(defthm fn-rtc-step*-keeps-slot-incarnation-u64
  (implies (fn-rtc-invp s)
           (fn-rtc-u64p (fn-rtc-s-inc
             (fn-rtc-slot j (mv-nth 0 (fn-rtc-step* s e q))))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use (fn-rtc-step*-preserves-invp
                 (:instance fn-rtc-invp-slot-incarnation-is-u64
                  (s (mv-nth 0 (fn-rtc-step* s e q))))))))
(defthm fn-rtc-step*-keeps-exhaustion
  (implies (and (fn-rtc-invp s)
                (fn-rtc-slots-exhaustedp 0 (fn-rtc-nstatic (fn-rtc-config s))
                                           (fn-rtc-slots s)))
           (fn-rtc-slots-exhaustedp 0 (fn-rtc-nstatic (fn-rtc-config s))
               (fn-rtc-slots (mv-nth 0 (fn-rtc-step* s e q)))))
  :hints (("Goal" :in-theory
    (union-theories (theory 'minimal-theory)
      '(fn-rtc-step*-state-is-step-state fn-rtc-step-state
        fn-rtc-end-use-keeps-exhaustion fn-rtc-deliver-keeps-exhaustion
        fn-rtc-accept-branch-keeps-exhaustion fn-rtc-close-branch-keeps-exhaustion
        fn-rtc-rearm-frame fn-rtc-grant-frame fn-rtc-with-accessors
        fn-rtc-slot-of-end-use-when-acting fn-rtc-acting-close-incarnation
        fn-rtc-nstatic fn-rtc-e-id nfix natp
        (:type-prescription fn-rtc-s-inc)))
    :use fn-rtc-acting-close-incarnation)))
(defthm fn-rtc-exhaustion-selects-only-statics
  (implies (and (natp i) (natp nstatic)
                (fn-rtc-slots-exhaustedp i nstatic slots)
                (fn-rtc-free-slot i slots))
           (<= (fn-rtc-free-slot i slots) nstatic))
  :hints (("Goal" :induct (fn-rtc-free-slot i slots)
           :in-theory (e/d (fn-rtc-free-slot fn-rtc-slots-exhaustedp
                             fn-rtc-slot-selectablep)
                           (fn-rtc-inc-roomp fn-rtc-s-status)))))

(defthm fn-rtc-exhausted-means-no-free-slot
  (implies (and (fn-rtc-invp s)
                (fn-rtc-slots-exhaustedp 0 (fn-rtc-nstatic (fn-rtc-config s))
                                           (fn-rtc-slots s)))
           (not (fn-rtc-free-slot 0 (fn-rtc-slots s))))
  :hints (("Goal" :in-theory
    (union-theories (theory 'minimal-theory)
      '(fn-rtc-slot-selectablep natp posp nfix unicity-of-0 fix commutativity-of-+
        (:type-prescription fn-rtc-free-slot)
        (:type-prescription fn-rtc-nstatic)
        (:executable-counterpart fn-rtc-s-status)))
    :use (fn-rtc-invp-has-static-records
          (:instance fn-rtc-exhaustion-selects-only-statics
                   (i 0) (nstatic (fn-rtc-nstatic (fn-rtc-config s)))
                   (slots (fn-rtc-slots s)))
          (:instance fn-rtc-free-slot-result (i 0) (slots (fn-rtc-slots s)))
          (:instance fn-rtc-free-slot-selects-selectable-record
                   (i 0) (slots (fn-rtc-slots s)))
          (:instance fn-rtc-statics-okp-get
                   (j 1) (n (fn-rtc-nstatic (fn-rtc-config s)))
                   (k (fn-rtc-free-slot 0 (fn-rtc-slots s)))
                   (slots (fn-rtc-slots s)))))))

(defthm fn-rtc-step*-config-frame
  (equal (fn-rtc-config (mv-nth 0 (fn-rtc-step* s e q))) (fn-rtc-config s))
  :hints (("Goal" :in-theory
    (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
      '(fn-rtc-step*-state-is-step-state fn-rtc-step-state fn-rtc-deliver
        fn-rtc-accept-branch fn-rtc-close-branch fn-rtc-grant-frame
        fn-rtc-end-use-config fn-rtc-rearm-frame fn-rtc-make-accessors
        fn-rtc-with-accessors fn-rtc-requests-config-frame car-cons cdr-cons)))))
