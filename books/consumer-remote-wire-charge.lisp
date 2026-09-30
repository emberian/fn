; Logical observation of the exact wire charge carried by the scope producer.
; The recursive observation is proof-only; served ticks inspect one name.
(in-package "ACL2")
(include-book "consumer-remote-scope")

(defun fn-crw-wirep (s)
 (declare (xargs :guard t))
 (and (natp (fn-cp-nth 17 s)) (natp (fn-cp-nth 12 s))
      (equal (fn-cp-nth 12 s) (+ (len (fn-cp-nth 13 s)) (len (fn-cp-nth 15 s))))
      (or (not (eq (fn-cp-nth 3 s) :ready)) (null (fn-cp-nth 13 s)))
      (equal (fn-cp-nth 17 s)
             (+ (fn-crw-groups-charge (fn-cp-nth 13 s))
                (fn-crw-groups-charge (fn-cp-nth 15 s))))
      (or (member-eq (fn-cp-nth 3 s) '(:reverse :ready))
          (not (fn-cp-nth 15 s)))))

(defthm fn-crs-begin-establishes-exact-wire-charge
 (implies (eq (fn-cp-nth 0 ingress) :authenticated)
          (fn-crw-wirep (fn-cp-nth 1 (fn-crs-begin ingress generation config groups))))
 :hints (("Goal" :in-theory (enable fn-crs-begin fn-crs-state fn-crw-wirep fn-crw-groups-charge fn-cp-nth))))

(defthm fn-crs-tick-preserves-exact-wire-charge
 (implies (and (fn-crw-wirep s)
                (member-eq (fn-cp-nth 0 (fn-crs-tick s key g)) '(:yield :ready)))
          (fn-crw-wirep (fn-cp-nth 1 (fn-crs-tick s key g))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
          :in-theory (e/d (fn-crs-tick fn-crs-state fn-crs-wire fn-crw-wirep fn-crw-groups-charge fn-cp-nth len)
                          (fn-crs-namep fn-gac-readablep fn-gac-text-octets
                           fn-nntp-moderated-entryp fn-mod-entry-queue fn-mod-entry-moderators
                           fn-caac-list-cons fn-scs-octets fn-nntp-octets-chars)))))

(in-theory (disable fn-crw-groups-charge fn-crw-wirep))
