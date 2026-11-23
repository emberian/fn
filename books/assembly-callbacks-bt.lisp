; The commit kind's B-S2 section: the transaction member's admission, its
; source reference, the block read and the seal's verbatim copy (split from
; assembly-callbacks-b and -b2 under the one-minute rule).
(in-package "ACL2")
(include-book "assembly-callbacks-b")
(make-event
 (let* ((body (fn2-commit-event-forms-1t))
        (pos-a (position-equal '(fn2-checkpoint-allocation-coordinator-events) body))
        (pos-i (position-equal '(fn2-checkpoint-installation-coordinator-events) body))
        (wrapped
         '(encapsulate ()
            (local
             (defthm fn2-checkpoint-builder-claimp-bounds-fc
               (implies (fn2-checkpoint-builder-claimp c token okind oslot ogen fn2-checkpoints)
                        (and (natp c)
                             (< c (fn2-checkpoints-rows fn2-checkpoints))
                             (posp token)))
               :rule-classes :forward-chaining
               :hints (("Goal" :in-theory (enable fn2-checkpoint-builder-claimp)))))
            (make-event
             (value `(local (in-theory (disable nth
                       fn2-checkpoint-builder-claimp
                       fn2-checkpoint-production-roots-p
                       fn2-alloc-handle-code
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
                              (:type-prescription :typed-term (mv-nth 1 (fn2-checkpoint-staging-claim expected-c okind oslot ogen need fn2-core)))
                              (:linear :trigger-terms ((mv-nth 1 (fn2-checkpoint-staging-claim expected-c okind oslot ogen need fn2-core)))))
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
                              (:type-prescription :typed-term (mv-nth 1 (fn2-checkpoint-staging-current okind oslot ogen need fn2-core)))
                              (:linear :trigger-terms ((mv-nth 1 (fn2-checkpoint-staging-current okind oslot ogen need fn2-core)))))
               :hints (("Goal" :in-theory (e/d (fn2-checkpoint-staging-current)
                                               (fn2-checkpoint-staging-claim
                                                fn2-checkpoint-future-rows fn2-checkpoint-future-candidate))))))
            (fn2-checkpoint-allocation-coordinator-events)
            (fn2-checkpoint-installation-coordinator-events))))
   (if (and pos-a pos-i (= (+ 1 pos-a) pos-i))
       (value (append (take pos-a body) (cons wrapped (nthcdr (+ 1 pos-i) body))))
     (er soft 'assembly-callbacks-bt "Could not locate adjacent allocation/installation coordinator events in fn2-commit-event-forms-1t."))))
