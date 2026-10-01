; Full captured read result is preserved by actual private page construction.
; Source issuance, runtime pricing and retirement remain owning caller obligations.
(in-package "ACL2")
(include-book "history-page-construction")
(encapsulate ()
 (local (defthm fn-hpc-get-put-other-key
  (implies (not (equal a b))
   (equal (fn-hep-node-children-get a (fn-hep-node-children-put b value node) default)
          (fn-hep-node-children-get a node default)))
  :hints (("Goal" :in-theory (enable fn-hep-node-children-get fn-hep-node-children-put)))))
 (local (defthm fn-hpc-bound-put-other-key
  (implies (not (equal a b))
   (equal (fn-hep-node-children-boundp a (fn-hep-node-children-put b value node))
          (fn-hep-node-children-boundp a node)))
  :hints (("Goal" :in-theory (enable fn-hep-node-children-boundp fn-hep-node-children-put)))))

 (local (defthm fn-hpc-get-put-same-key
  (equal (fn-hep-node-children-get a (fn-hep-node-children-put a value node) default) value)
  :hints (("Goal" :in-theory (enable fn-hep-node-children-get fn-hep-node-children-put)))))
 (local (defthm fn-hpc-bound-put-same-key
  (fn-hep-node-children-boundp a (fn-hep-node-children-put a value node))
  :hints (("Goal" :in-theory (enable fn-hep-node-children-boundp fn-hep-node-children-put)))))
 (local (defthm fn-hpc-row-read-occupied
  (implies (equal (car (fn-hec-read e i c s n page)) :row)
           (< 0 (fn-hec-committed page)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-hec-read)))))
 (local (defthm fn-hpc-occupied-initialize-unchanged
  (implies (< 0 (fn-hec-committed page))
           (equal (fn-hec-initialize e i c b page) (list :stale page)))
  :hints (("Goal" :in-theory (enable fn-hec-initialize)))))
 (local (defthm fn-hpc-natural-half
  (implies (natp x) (natp (floor x 2)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable floor)))))
 (local
  (defun fn-hpc-frame-induct (slot depth fuel old-slot old-depth read-fuel fn-hep-node)
   (declare (xargs :stobjs fn-hep-node :measure (nfix depth) :verify-guards nil))
   (cond ((or (zp depth) (<= fuel depth) (equal slot 0)) (list old-slot old-depth read-fuel))
    ((equal (mod slot 2) 0)
     (if (not (fn-hep-node-presentp 'fn-hep-left fn-hep-node)) nil
      (stobj-let ((fn-hep-left (fn-hep-node-children-get 'fn-hep-left fn-hep-node (create-fn-hep-left))))
       (result)
       (fn-hpc-frame-induct (floor slot 2) (1- depth) (1- fuel)
         (floor old-slot 2) (nfix (1- old-depth)) (nfix (1- read-fuel)) fn-hep-left)
       result)))
    (t (if (not (fn-hep-node-presentp 'fn-hep-right fn-hep-node)) nil
      (stobj-let ((fn-hep-right (fn-hep-node-children-get 'fn-hep-right fn-hep-node (create-fn-hep-right))))
       (result)
       (fn-hpc-frame-induct (floor slot 2) (1- depth) (1- fuel)
         (floor old-slot 2) (nfix (1- old-depth)) (nfix (1- read-fuel)) fn-hep-right)
       result))))))

 (defthm fn-hpc-construction-preserves-current-row-read
  (implies
   (and (natp slot) (natp depth) (posp epoch) (posp id)
        (natp incarnation) (natp base) (natp fuel)
        (natp old-slot) (natp old-depth) (natp ordinal) (natp old-base)
        (natp captured) (natp read-fuel)
        (eq (mv-nth 0 (fn-hep-node-read old-slot old-depth old-epoch old-id old-inc
                           ordinal old-base captured read-fuel fn-hep-node)) :row))
   (equal
    (fn-hep-node-read old-slot old-depth old-epoch old-id old-inc ordinal old-base
                      captured read-fuel
     (mv-nth 2 (fn-hpc-node-one slot depth epoch id incarnation base fuel fn-hep-node)))
    (fn-hep-node-read old-slot old-depth old-epoch old-id old-inc ordinal old-base
                      captured read-fuel fn-hep-node)))
  :hints (("Goal" :induct (fn-hpc-frame-induct slot depth fuel old-slot old-depth read-fuel fn-hep-node)
                  :expand ((:free (node) (fn-hep-node-read old-slot old-depth old-epoch old-id old-inc ordinal old-base captured read-fuel node)))
                  :in-theory (e/d (fn-hpc-node-one fn-hep-node-read
                                     fn-hec-matches)
                                    (fn-hec-initialize fn-hec-read fn-hec-committed floor integer-length create-fn-hep-left create-fn-hep-right
                                     create-fn-history-event-page fn-hep-node-children-get
                                     fn-hep-node-children-put fn-hep-node-children-boundp))))))
