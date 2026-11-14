; The semantic accounting invariant funds the constant-time release guard.
; No served operation calls the enumerations used in this proof.
(in-package "ACL2")
(include-book "pool")

(encapsulate ()
 (local
  (defthm fn2-release-member-remove1-other
    (implies (not (equal a b))
             (iff (member-equal b (remove1-equal a ys)) (member-equal b ys)))
    :hints (("Goal" :induct (remove1-equal a ys)))))
 (local
  (defthm fn2-release-subset-remove1-absent
    (implies (and (subsetp-equal xs ys) (not (member-equal a xs)))
             (subsetp-equal xs (remove1-equal a ys)))
    :hints (("Goal" :induct (len xs)))))
 (local
  (defthm fn2-release-len-remove1-member
    (implies (member-equal a ys)
             (equal (len (remove1-equal a ys)) (- (len ys) 1)))
    :hints (("Goal" :induct (remove1-equal a ys)))))
 (local
  (defun fn2-release-subset-ind (xs ys)
    (declare (xargs :measure (len xs) :verify-guards nil))
    (if (atom xs) ys
      (fn2-release-subset-ind (cdr xs) (remove1-equal (car xs) ys)))))
 (local
  (defthm fn2-release-unique-subset-length
    (implies (and (no-duplicatesp-equal xs) (subsetp-equal xs ys))
             (<= (len xs) (len ys)))
    :rule-classes nil
    :hints (("Goal" :induct (fn2-release-subset-ind xs ys)))))

 (defthm fn2-pool-free-enumeration-length-bound
   (<= (len (fn2-pool-free-slots n class pool)) (nfix n))
   :rule-classes :linear
   :hints (("Goal" :induct (fn2-pool-free-slots n class pool)
            :in-theory (enable fn2-pool-free-slots))))
 (defthm fn2-pool-nonfree-row-makes-free-enumeration-strict
   (implies (and (natp n) (natp slot) (< slot n)
                 (not (equal (fn2-pool-state slot pool) *fn2-pool-state-free*)))
            (< (len (fn2-pool-free-slots n class pool)) n))
   :rule-classes :linear
   :hints (("Goal" :induct (fn2-pool-free-slots n class pool)
            :in-theory (enable fn2-pool-free-slots))))
 (defthm fn2-pool-retired-enumeration-bound
   (<= (fn2-pool-retired-slots n pool) (nfix n))
   :rule-classes :linear
   :hints (("Goal" :induct (fn2-pool-retired-slots n pool)
            :in-theory (enable fn2-pool-retired-slots))))
 (defthm fn2-pool-nonretired-row-makes-retired-enumeration-strict
   (implies (and (natp n) (natp slot) (< slot n)
                 (not (equal (fn2-pool-state slot pool) *fn2-pool-state-retired*)))
            (< (fn2-pool-retired-slots n pool) n))
   :rule-classes :linear
   :hints (("Goal" :induct (fn2-pool-retired-slots n pool)
            :in-theory (enable fn2-pool-retired-slots))))

 (local
  (defthm fn2-release-class-clause
    (implies (and (natp n) (natp class) (< class n)
                  (fn2-pool-class-accountsp n pool))
      (let ((chain (fn2-pool-free-chain (fn2-pool-nslots pool)
                       (fn2-pool-class-headsi class pool) pool))
            (free (fn2-pool-free-slots (fn2-pool-nslots pool) class pool)))
        (and (no-duplicatesp-equal chain) (subsetp-equal chain free)
             (equal (len chain) (fn2-pool-class-countsi class pool)))))
    :rule-classes nil
    :hints (("Goal" :induct (fn2-pool-class-accountsp n pool)
             :in-theory
             (e/d (fn2-pool-class-accountsp)
                  (fn2-pool-free-chain fn2-pool-free-slots fn2-pool-nslots))))))
 (local
  (defthm fn2-release-nclasses-natural
    (implies (fn2-poolp pool) (natp (fn2-pool-nclasses pool)))
    :hints (("Goal" :in-theory (disable fn2-poolp)))))

 (defthm fn2-pool-workspace-has-release-headroom
   (implies (and (fn2-pool-semanticp pool)
                 (fn2-pool-logical-slotp slot pool)
                 (equal (fn2-pool-state slot pool) *fn2-pool-state-workspace*))
     (and (< (fn2-pool-retired-count pool) (fn2-pool-rows pool))
          (implies (< (fn2-pool-class slot pool) (fn2-pool-nclasses pool))
            (< (fn2-pool-class-countsi (fn2-pool-class slot pool) pool)
               (fn2-pool-rows pool)))))
   :rule-classes nil
   :hints (("Goal"
            :in-theory
            (e/d (fn2-pool-semanticp fn2-pool-logical-slotp fn2-pool-nslots)
                 (fn2-pool-class-accountsp fn2-pool-row-invariantp
                  fn2-pool-free-chain fn2-pool-free-slots fn2-pool-retired-slots))
            :use
            ((:instance fn2-release-class-clause
                        (n (fn2-pool-nclasses pool)) (class (fn2-pool-class slot pool)))
             (:instance fn2-release-unique-subset-length
                        (xs (fn2-pool-free-chain (fn2-pool-rows pool)
                              (fn2-pool-class-headsi (fn2-pool-class slot pool) pool) pool))
                        (ys (fn2-pool-free-slots (fn2-pool-rows pool)
                              (fn2-pool-class slot pool) pool)))
             (:instance fn2-pool-nonfree-row-makes-free-enumeration-strict
                        (n (fn2-pool-rows pool)) (class (fn2-pool-class slot pool)))
             (:instance fn2-pool-nonretired-row-makes-retired-enumeration-strict
                        (n (fn2-pool-rows pool)))))))
 (defthm fn2-pool-semantic-workspace-admits-release
   (implies (and (fn2-pool-semanticp pool)
                 (fn2-pool-logical-slotp slot pool)
                 (equal (fn2-pool-state slot pool) *fn2-pool-state-workspace*))
            (fn2-pool-release-countp slot pool))
   :rule-classes nil
   :hints (("Goal" :use fn2-pool-workspace-has-release-headroom
            :in-theory
            (e/d (fn2-pool-release-countp fn2-pool-semanticp
                  fn2-pool-logical-slotp fn2-pool-nslots)
                 (fn2-pool-class-accountsp fn2-pool-row-invariantp
                  fn2-pool-free-chain fn2-pool-free-slots fn2-pool-retired-slots))))))

; A release never changes another row's ownership or contents metadata.
; This is the frame needed to apply admission again to a distinct NS row.
(defthm fn2-pool-release-protects-other-row
  (implies (and (natp other) (natp slot) (not (equal other slot)))
    (equal
     (fn2-pool-slot-view other (mv-nth 1 (fn2-pool-release slot gen okind oslot ogen pool)))
     (fn2-pool-slot-view other pool)))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn2-pool-release fn2-pool-slot-view fn2-pool-row-view
                 fn2-pool-set-gen fn2-pool-set-state fn2-pool-set-fill fn2-pool-set-next-free
                 update-fn2-pool-gen$ai update-fn2-pool-state$ai
                 update-fn2-pool-fill$ai update-fn2-pool-next-free$ai
                 update-fn2-pool-class-headsi update-fn2-pool-class-countsi
                 update-fn2-pool-retired-count)
                (fn2-pool-workspace-code fn2-pool-release-countp)))))

(defthm fn2-pool-distinct-workspace-admits-release-after-release
  (implies (and (fn2-pool-semanticp pool) (natp slot)
                (fn2-pool-logical-slotp other pool) (not (equal other slot))
                (equal (fn2-pool-state other pool) *fn2-pool-state-workspace*))
    (fn2-pool-release-countp other
      (mv-nth 1 (fn2-pool-release slot gen okind oslot ogen pool))))
  :rule-classes nil
  :hints (("Goal"
           :use
           ((:instance fn2-pool-semantic-workspace-admits-release
                        (slot other)
                        (pool (mv-nth 1 (fn2-pool-release slot gen okind oslot ogen pool))))
            (:instance fn2-pool-release-protects-other-row)
            (:instance fn2-pool-release-conservation (fn2-pool pool)))
           :in-theory
           (e/d (fn2-pool-logical-slotp fn2-pool-nslots
                 fn2-pool-slot-view fn2-pool-row-view)
                (fn2-pool-release fn2-pool-release-countp fn2-pool-semanticp)))))
