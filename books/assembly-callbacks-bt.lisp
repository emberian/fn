; Second half of the commit kind's B-S2 section: checkpoint allocation and
; installation coordinators, txn source reference, block read, and verbatim copy.
(in-package "ACL2")
(include-book "assembly-callbacks-bt0")
(make-event
 (let* ((body (fn2-commit-event-forms-1t))
        (pos-a (position-equal '(fn2-checkpoint-allocation-coordinator-events) body))
        (pos-i (position-equal '(fn2-checkpoint-installation-coordinator-events) body))
        (wrapped
         '(encapsulate ()
            (local
             (in-theory (enable
                         (:forward-chaining fn2-checkpoint-construction-wfp-of-fn2-core-checkpoint-construction)
                         (:forward-chaining fn2-checkpoint-bytes-wfp-of-fn2-core-checkpoint-bytes))))
            (local
             (defthm fn2-checkpoint-builder-claimp-bounds-fc
               (implies (fn2-checkpoint-builder-claimp c token okind oslot ogen fn2-checkpoints)
                        (and (natp c)
                             (< c (fn2-checkpoints-rows fn2-checkpoints))
                             (posp token)))
               :rule-classes :forward-chaining
               :hints (("Goal" :in-theory (enable fn2-checkpoint-builder-claimp)))))
            (local
             (defthm fn2-construction-next-ticket-u60
               (implies (fn2-checkpoint-constructionp x)
                        (and (< (fn2-construction-next-ticket x) 1152921504606846976)
                             (unsigned-byte-p 60 (fn2-construction-next-ticket x))))
               :hints (("Goal" :use ((:instance fn2-construction-next-ticket-natp (fn2-checkpoint-construction x))
                                     (:instance fn2-construction-next-ticket-bound (fn2-checkpoint-construction x)))
                               :in-theory (enable unsigned-byte-p)))))
            (make-event
             (value `(local (in-theory (disable nth
                       remove-weak-inequalities-one
                       remove-weak-inequalities-two
                       fn2-core-wfp
                       fn2-checkpoint-builder-claimp
                       fn2-checkpoint-production-roots-p
                       fn2-alloc-handle-code
                       fn2-checkpoint-future-bind
                       fn2-checkpoint-future-lease
                       fn2-checkpoint-future-staging-return
                       fn2-pool-reset
                       fn2-pool-cap
                       ,@(fn2-columns-getter-runes
                           '(fn2-extents fn2-checkpoint-construction fn2-retirement-control
                             fn2-checkpoint-future fn2-checkpoint-future-windows
                             fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
                             fn2-fields fn2-pool)
                           (w state)))))))
            (local
             (defthm fn2-checkpoint-staging-claim-candidate-u32
               (and (natp (mv-nth 1 (fn2-checkpoint-staging-claim expected-c okind oslot ogen need fn2-core)))
                    (< (mv-nth 1 (fn2-checkpoint-staging-claim expected-c okind oslot ogen need fn2-core)) 4294967296)
                    (unsigned-byte-p 32 (mv-nth 1 (fn2-checkpoint-staging-claim expected-c okind oslot ogen need fn2-core))))
               :rule-classes (:rewrite
                              (:type-prescription :typed-term (mv-nth 1 (fn2-checkpoint-staging-claim expected-c okind oslot ogen need fn2-core))))
               :hints (("Goal" :in-theory (e/d (fn2-checkpoint-staging-claim)
                                               (fn2-checkpoint-future-bind fn2-checkpoint-future-lease
                                                fn2-pool-reset fn2-checkpoint-future-candidate
                                                fn2-checkpoint-future-rows fn2-checkpoint-future-windows-rows
                                                fn2-checkpoint-future-windows-borrowed fn2-alloc-freeze-token))))))
            (local
             (defthm fn2-checkpoint-staging-current-candidate-u32
               (and (natp (mv-nth 1 (fn2-checkpoint-staging-current okind oslot ogen need fn2-core)))
                    (< (mv-nth 1 (fn2-checkpoint-staging-current okind oslot ogen need fn2-core)) 4294967296)
                    (unsigned-byte-p 32 (mv-nth 1 (fn2-checkpoint-staging-current okind oslot ogen need fn2-core))))
               :rule-classes (:rewrite
                              (:type-prescription :typed-term (mv-nth 1 (fn2-checkpoint-staging-current okind oslot ogen need fn2-core))))
               :hints (("Goal" :in-theory (e/d (fn2-checkpoint-staging-current)
                                               (fn2-checkpoint-staging-claim
                                                fn2-checkpoint-future-rows fn2-checkpoint-future-candidate))))))
            (fn2-checkpoint-allocation-coordinator-events)
            (fn2-checkpoint-installation-coordinator-events))))
   (if (and pos-a pos-i (= (+ 1 pos-a) pos-i))
       (value (list* 'progn
                     (fn2-commit-local-theory)
                     (fn2-commit-local-forward)
                     (fn2-commit-local-idp)
                     wrapped
                     (nthcdr (+ 1 pos-i) body)))
     (er soft 'assembly-callbacks-bt "Could not locate adjacent allocation/installation coordinator events in fn2-commit-event-forms-1t."))))
