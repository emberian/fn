; Entry of the local reservation invariant through the actual registered
; directory initializer. No initialization or profile decision is copied.
(in-package "ACL2")
(include-book "machine-reservations")
(include-book "assembly-index")

(defthm fn2-machines-init-bases-reservation-frame
  (equal
   (fn2-machines-reservation-view ord (fn2-machines-init-bases left profile machines))
   (fn2-machines-reservation-view ord machines))
  :hints (("Goal" :induct (fn2-machines-init-bases left profile machines)
           :in-theory
           (e/d (fn2-machines-init-bases fn2-machines-reservation-view
                 fn2-machines-active-counti fn2-machines-admission-creditsi
                 fn2-machines-connection-counti)
                (fn2-machine-global-id)))))
(defthm fn2-machines-init-rows-reservation-frame
  (equal
   (fn2-machines-reservation-view ord (fn2-machines-init-rows left profile machines))
   (fn2-machines-reservation-view ord machines))
  :hints (("Goal" :induct (fn2-machines-init-rows left profile machines)
           :in-theory
           (e/d (fn2-machines-init-rows fn2-machines-reservation-view
                 fn2-machines-active-counti fn2-machines-admission-creditsi
                 fn2-machines-connection-counti)
                (fn2-machine-local-id)))))

; The recursive initializer writes every earlier ordinal, and frames all
; later ordinals. One exact statement handles both induction branches.
(defthm fn2-machines-init-partitions-reservation-view
  (implies (and (natp left) (<= left *fn2-machine-admitted-max*)
                (natp ord) (< ord *fn2-machine-admitted-max*))
    (equal
     (fn2-machines-reservation-view ord (fn2-machines-init-partitions left profile machines))
     (if (< ord left)
         (let ((capacity (fn2-machine-admitted-capacity ord profile)))
           (list 0 (if (unsigned-byte-p 32 capacity) capacity 0)
                   (if (unsigned-byte-p 32 capacity) capacity 0)))
       (fn2-machines-reservation-view ord machines))))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-machines-init-partitions left profile machines)
           :in-theory
           (e/d (fn2-machines-init-partitions fn2-machines-reservation-view
                 fn2-machines-active-counti fn2-machines-admission-creditsi
                 fn2-machines-connection-counti)
                (fn2-machine-admitted-capacity fn2-machine-admitted-base)))))
(defthm fn2-machines-init-partitions-reserved
  (implies (and (natp left) (<= left *fn2-machine-admitted-max*)
                (natp ord) (< ord left))
    (fn2-machines-partition-reservedp ord
      (fn2-machines-init-partitions left profile machines)))
  :rule-classes nil
  :hints (("Goal" :use fn2-machines-init-partitions-reservation-view
           :in-theory
           (e/d (fn2-machines-partition-reservedp fn2-machines-reservation-valuesp)
                (fn2-machines-init-partitions fn2-machines-reservation-view
                 fn2-machine-admitted-capacity)))))

(defthm fn2-machines-init-reservation-entry
  (implies (and (natp ord) (< ord (len *fn2-machine-partitioned*)))
    (fn2-machines-partition-reservedp ord (fn2-machines-init profile machines)))
  :rule-classes nil
  :hints (("Goal"
           :in-theory
           (e/d (fn2-machines-init fn2-machines-partition-reservedp
                 fn2-machines-reservation-valuesp fn2-machines-reservation-view
                 fn2-machines-active-counti fn2-machines-admission-creditsi
                 fn2-machines-connection-counti)
                (fn2-machines-init-bases fn2-machines-init-rows
                 fn2-machines-init-partitions fn2-machines-columns-init
                 fn2-machine-admitted-capacity))
           :use ((:instance fn2-machines-init-partitions-reservation-view
                            (left (len *fn2-machine-partitioned*))
                            (machines
                             (update-fn2-machines-accept-count (fn2-profile-accept-credits profile)
                               (fn2-machines-init-bases 256 profile
                                 (fn2-machines-columns-init (fn2-machine-index-count profile) machines)))))))))
