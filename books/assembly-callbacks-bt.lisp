; The commit kind's B-S2 section: the transaction member's admission, its
; source reference, the block read and the seal's verbatim copy (split from
; assembly-callbacks-b and -b2 under the one-minute rule).
(in-package "ACL2")
(include-book "assembly-callbacks-b")
(make-event
 (let* ((body (fn2-commit-event-forms-1t))
        (pos (position-equal '(fn2-checkpoint-allocation-coordinator-events) body))
        (lemmas
         '(local
           (progn
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
                                               fn2-checkpoint-future-windows-borrowed fn2-alloc-freeze-token)))))
            (defthm fn2-checkpoint-staging-current-candidate-u32
              (and (natp (mv-nth 1 (fn2-checkpoint-staging-current okind oslot ogen need fn2-core)))
                   (< (mv-nth 1 (fn2-checkpoint-staging-current okind oslot ogen need fn2-core)) 4294967296)
                   (unsigned-byte-p 32 (mv-nth 1 (fn2-checkpoint-staging-current okind oslot ogen need fn2-core))))
              :rule-classes (:rewrite
                             (:type-prescription :typed-term (mv-nth 1 (fn2-checkpoint-staging-current okind oslot ogen need fn2-core)))
                             (:linear :trigger-terms ((mv-nth 1 (fn2-checkpoint-staging-current okind oslot ogen need fn2-core)))))
              :hints (("Goal" :in-theory (e/d (fn2-checkpoint-staging-current)
                                              (fn2-checkpoint-staging-claim
                                               fn2-checkpoint-future-rows fn2-checkpoint-future-candidate)))))))))
   (if pos
       (value (append (take pos body) (cons lemmas (nthcdr pos body))))
     (er soft 'assembly-callbacks-bt "Could not locate (fn2-checkpoint-allocation-coordinator-events) in fn2-commit-events-1t."))))
