; The same dirty, unambiguous recovery evidence under two declared contracts.
; This checks the policy seam; the native crash campaign supplies the image.
(in-package "ACL2")
(include-book "../books/boot-kind")
(include-book "../books/recovery")

(assert-event
 (and (equal (fn2-profile-storage-fault-model *fn2-profile-tiny*) "broad")
      (equal (fn2-profile-recovery-assumptions *fn2-profile-tiny*) 2)
      (fn2-profilep (put-assoc-equal :storage-fault-model "broad" *fn2-profile-tiny*))
      (fn2-profilep (put-assoc-equal :storage-fault-model "crash-only" *fn2-profile-tiny*))
      (not (fn2-profilep (put-assoc-equal :storage-fault-model "crash" *fn2-profile-tiny*)))
      (not (fn2-profilep (put-assoc-equal :storage-fault-model nil *fn2-profile-tiny*)))
      (not (fn2-profilep (put-assoc-equal :storage-fault-model 3 *fn2-profile-tiny*)))))

(defun fn2-storage-policy-class (model dirty ambiguous witness)
 (declare (xargs :guard t))
 (fn2-rec-classify
  (fn2-profile-recovery-assumptions (list (cons :storage-fault-model model)))
  dirty ambiguous witness))

(assert-event
 (and
  (equal (fn2-storage-policy-class "broad" t nil *fn2-rec-witness-none*) *fn2-rec-class-unknown*)
  (equal (fn2-storage-policy-class "crash-only" t nil *fn2-rec-witness-none*) *fn2-rec-class-torn-tail*)
  (equal (fn2-storage-policy-class "broad" nil nil *fn2-rec-witness-none*) *fn2-rec-class-intact*)
  (equal (fn2-storage-policy-class "crash-only" nil nil *fn2-rec-witness-none*) *fn2-rec-class-intact*)
  ; Neither contract erases branching or contradictory independent evidence.
  (equal (fn2-storage-policy-class "crash-only" t t *fn2-rec-witness-none*) *fn2-rec-class-unknown*)
  (equal (fn2-storage-policy-class "crash-only" t nil *fn2-rec-witness-rollback-detected*) *fn2-rec-class-damaged*)))

(defthm fn2-storage-policy-crash-only-classification
 (equal (fn2-storage-policy-class "crash-only" dirty nil *fn2-rec-witness-none*)
        (if dirty *fn2-rec-class-torn-tail* *fn2-rec-class-intact*))
 :hints (("Goal" :in-theory (enable fn2-rec-classify))))

(defthm fn2-storage-policy-broad-dirty-uncertainty
 (equal (fn2-storage-policy-class "broad" t nil *fn2-rec-witness-none*)
        *fn2-rec-class-unknown*)
 :hints (("Goal" :in-theory (enable fn2-rec-classify))))
