; UNHOOKED stage 0 (2026-10-01): depends on the reverted acceptance-binding field (planning/design-store-representation-2026-10-01.md section 5, D43): the captured-identity chain over the held binding gate is parked (review 2026-10-01 F01: KEEP-PARKED); not in the Makefile check roots or any image world.
; Proof-only exact retained-group verdict boundary for actual fn-pic-next.
(in-package "ACL2")
(include-book "post-identity-captured")

(defun fn-pic-group-productp (c)
  (let ((s (fn-pic-get group-cursor c)))
    (and (equal (fn-pic-get phase c) :groups)
         (equal (fn-pic-at 0 s) :continue)
         (fn-pic-groups-validp s)
         (equal (fn-pic-groups-value s)
                (equal (fn-pic-get groups c) (fn-record-groups (fn-pic-get held c)))))))
(defun fn-pic-group-outcomep (c)
  (or (fn-pic-group-productp c)
      (and (equal (fn-pic-get phase c) :done)
           (case (fn-pic-get result c)
             (:duplicate (equal (fn-pic-get groups c) (fn-record-groups (fn-pic-get held c))))
             (:conflict (not (equal (fn-pic-get groups c) (fn-record-groups (fn-pic-get held c)))))
             (otherwise nil)))))
(local (defthm fn-pic-gr-at-is-nth
 (implies (natp i) (equal (fn-pic-at i x) (nth i x)))
 :hints (("Goal" :induct (fn-pic-at i x) :in-theory (enable fn-pic-at nth)))))
(local (defthm fn-pic-gr-valid-step-is-supported
 (implies (and (fn-pic-groups-validp s) (equal (fn-pic-at 0 s) :continue))
   (member-eq (fn-pic-at 0 (fn-pic-groups-step s)) '(:continue :equal :different)))
 :hints (("Goal" :expand ((fn-pic-string-listp (fn-pic-at 1 s))
                         (fn-pic-string-listp (fn-pic-at 2 s)))
 :in-theory (e/d (fn-pic-groups-validp fn-pic-groups-step fn-pic-at fn-pic-string-listp)
                                 (length char))))))
(local (defthm fn-pic-gr-feedback-preserves-exact-outcome
 (implies (fn-pic-group-productp c)
   (fn-pic-group-outcomep (mv-nth 1 (fn-pic-feed-funded c :control fuel))))
 :hints (("Goal" :use ((:instance fn-pic-gr-valid-step-is-supported
                              (s (fn-pic-get group-cursor c)))
 (:instance fn-pic-groups-step-preserves-value (s (fn-pic-get group-cursor c)))
 (:instance fn-pic-groups-step-preserves-validp (s (fn-pic-get group-cursor c)))
 (:instance fn-pic-groups-step-equal-is-value (s (fn-pic-get group-cursor c)))
 (:instance fn-pic-groups-step-different-is-not-value (s (fn-pic-get group-cursor c))))
 :in-theory (e/d (fn-pic-group-productp fn-pic-group-outcomep fn-pic-feed-funded
                   fn-pic-feed fn-pic-finish fn-pic-demand fn-pic-observation-okp)
  (fn-pic-at fn-pic-groups-step fn-pic-groups-value fn-pic-groups-validp
   fn-pic-gr-valid-step-is-supported fn-pic-groups-step-preserves-value
   fn-pic-groups-step-preserves-validp fn-pic-groups-step-equal-is-value
   fn-pic-groups-step-different-is-not-value nth update-nth))))))
(defthm fn-pic-next-preserves-exact-group-outcome
 (implies (and (fn-pic-group-productp c)
               (equal (fn-pic-get incoming-n c) (len fn-octets)))
   (fn-pic-group-outcomep (mv-nth 1 (fn-pic-next c fuel fn-octets))))
 :rule-classes nil
 :hints (("Goal" :use fn-pic-gr-feedback-preserves-exact-outcome
 :in-theory (e/d (fn-pic-next fn-pic-group-productp fn-pic-group-outcomep fn-pic-demand)
   (fn-pic-at fn-pic-feed-funded fn-pic-groups-step fn-pic-groups-value
    fn-pic-groups-validp fn-pic-gr-feedback-preserves-exact-outcome nth update-nth)))))
(local (defthm fn-pic-gr-start-establishes-product
 (implies (and (fn-pic-string-listp (fn-pic-get groups c))
               (fn-pic-string-listp (fn-record-groups (fn-pic-get held c))))
   (fn-pic-group-productp (fn-pic-groups-start c)))
 :hints (("Goal" :use ((:instance fn-pic-groups-begin-is-valid
  (left (fn-pic-get groups c)) (right (fn-record-groups (fn-pic-get held c))))
  (:instance fn-pic-groups-begin-denotes-exact-equality
  (left (fn-pic-get groups c)) (right (fn-record-groups (fn-pic-get held c)))))
 :in-theory (e/d (fn-pic-group-productp fn-pic-groups-start fn-pic-groups-begin)
   (fn-pic-at fn-pic-groups-value fn-pic-groups-validp fn-pic-string-listp
    fn-pic-groups-begin-is-valid fn-pic-groups-begin-denotes-exact-equality nth update-nth))))))
(defthm fn-pic-next-establishes-exact-group-product
 (implies (and (fn-pic-string-listp (fn-pic-get groups c))
               (fn-pic-string-listp (fn-record-groups (fn-pic-get held c)))
               (member-eq (fn-pic-get phase c) '(:compare-incoming :digest-compare)))
   (let ((next (mv-nth 1 (fn-pic-next c fuel fn-octets))))
     (implies (equal (fn-pic-get phase next) :groups)
       (fn-pic-group-productp next))))
 :rule-classes nil
 :hints (("Goal" :use fn-pic-gr-start-establishes-product
 :in-theory (e/d (fn-pic-next fn-pic-feed-funded fn-pic-feed fn-pic-finish fn-pic-demand)
   (fn-pic-at fn-pic-group-productp fn-pic-groups-start fn-pic-observation-okp
    fn-pic-observed-byte fn-pic-gr-start-establishes-product fn-pic-span-length
    fn-pic-span-offset fn-octets-get nth update-nth)))))
