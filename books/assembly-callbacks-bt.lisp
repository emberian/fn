; The commit kind's B-S2 section: the transaction member's admission, its
; source reference, the block read and the seal's verbatim copy (split from
; assembly-callbacks-b and -b2 under the one-minute rule).
(in-package "ACL2")
(include-book "assembly-callbacks-b")
(local (in-theory (disable fn2-alloc-frozenp fn2-alloc-snapshot-activep
                           fn2-machine-batch-no fn2-machine-member-count
                           fn2-machine-rec-bytes fn2-machine-first-key)))
(local (defun fn2-bt-mentions-big-put-p (x)
         (declare (xargs :guard t))
         (if (atom x)
             (eq x 'fn2-retirement-control-set-install-offset)
           (or (fn2-bt-mentions-big-put-p (car x))
               (fn2-bt-mentions-big-put-p (cdr x))))))
(local (set-default-hints '((and (consp id)
                                 (null (cadr id))
                                 (eql (cddr id) 0)
                                 (<= (len (car id)) 2)
                                 (fn2-bt-mentions-big-put-p clause)
                                 '(:do-not '(preprocess))))))
(local
 (defthm fn2-bt-retirement-control-rows-natp-rewrite
   (implies (fn2-retirement-controlp x)
            (and (integerp (fn2-retirement-control-rows x))
                 (rationalp (fn2-retirement-control-rows x))
                 (acl2-numberp (fn2-retirement-control-rows x))
                 (<= 0 (fn2-retirement-control-rows x))))))
(make-event
 (value `(local (in-theory (e/d ,(fn2-commit-child-forward-runes *fn2-commit-proof-children*)
                                ,(fn2-columns-getter-runes
                                  '(fn2-extents fn2-checkpoint-construction
                                    fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
                                    fn2-retirement-control fn2-checkpoint-future
                                    fn2-checkpoint-future-windows fn2-fields)
                                  (w state)))))))
(fn2-checkpoint-maintenance-staging-events)
(local
 (defthm fn2-checkpoint-staging-claim-candidate-natp
   (natp (mv-nth 1 (fn2-checkpoint-staging-claim expected-c okind oslot ogen need fn2-core)))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable fn2-checkpoint-staging-claim)))))
(local
 (defthm fn2-checkpoint-staging-claim-candidate-width
   (< (mv-nth 1 (fn2-checkpoint-staging-claim expected-c okind oslot ogen need fn2-core)) 4294967296)
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable fn2-checkpoint-staging-claim)))))
(local
 (defthm fn2-checkpoint-staging-current-candidate-natp
   (natp (mv-nth 1 (fn2-checkpoint-staging-current okind oslot ogen need fn2-core)))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable fn2-checkpoint-staging-current)))))
(local
 (defthm fn2-checkpoint-staging-current-candidate-width
   (< (mv-nth 1 (fn2-checkpoint-staging-current okind oslot ogen need fn2-core)) 4294967296)
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable fn2-checkpoint-staging-current)))))
(fn2-commit-events-1t)
