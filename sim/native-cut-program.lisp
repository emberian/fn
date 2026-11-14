; Explicit physical microsteps for native death cuts.  The seeded simulator's
; atomic completion schedule is unchanged.  This driver exposes the interval
; after physical I/O and before its terminal post, retaining the raw result.
; Completion uses the native release=nil subset. Atomic-equivalence below is
; deliberately stated for storage; generic send early-release remains separate.
(in-package "ACL2")
(include-book "sim")

(include-book "native-cut-state")

(defthm fn2-sim-find-write-is-pending
  (implies (mv-nth 0 (fn2-sim-find-write left index fn2-sim))
           (equal (fn2-sim-active (mv-nth 1 (fn2-sim-find-write left index fn2-sim)) fn2-sim) 1))
  :hints (("Goal" :induct (fn2-sim-find-write left index fn2-sim)
           :in-theory (enable fn2-sim-find-write))))

(defthm fn2-sim-find-write-does-not-replay-returned
  (implies (and (equal (fn2-sim-active slot fn2-sim) *fn2-sim-native-returned*)
                (mv-nth 0 (fn2-sim-find-write left index fn2-sim)))
           (not (equal (mv-nth 1 (fn2-sim-find-write left index fn2-sim)) slot)))
  :hints (("Goal" :use fn2-sim-find-write-is-pending)))

(defthm fn2-sim-physical-keeps-active
  (equal (fn2-sim-active i (mv-nth 4 (fn2-sim-physical slot fault word fn2-core fn2-sim fn2-own)))
         (fn2-sim-active i fn2-sim))
  :hints (("Goal" :in-theory (e/d (fn2-sim-physical fn2-sim-active fn2-sim-land)
                                  (fn2-sim-physical-act)))))

(defthm fn2-sim-returned-completion-does-not-reissue
  (implies (equal (fn2-sim-active slot fn2-sim) *fn2-sim-native-returned*)
           (equal (fn2-sim-complete slot fault word fn2-core fn2-sim fn2-own)
                  (mv nil fn2-core fn2-sim fn2-own)))
  :hints (("Goal" :in-theory (enable fn2-sim-complete))))

(defun fn2-sim-native-cut (cut slot fault word fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil
                  :guard (and (fn2-core-wfp fn2-core) (fn2-sim-ready fn2-sim)
                              (fn2-own-wfp fn2-own) (unsigned-byte-p 32 word))))
  (if (eq cut :before-physical)
      (mv-let (fn2-core fn2-sim fn2-own)
        (fn2-sim-crash (fn2-sim-profile fn2-sim) fn2-core fn2-sim fn2-own)
        (mv t fn2-core fn2-sim fn2-own))
    (b* (((mv status packet fn2-core fn2-sim fn2-own)
          (fn2-sim-native-stage slot fault word fn2-core fn2-sim fn2-own))
         ((unless (eq status :returned)) (mv (eq status :waiting) fn2-core fn2-sim fn2-own))
         ((when (eq cut :after-physical))
          (mv-let (fn2-core fn2-sim fn2-own)
            (fn2-sim-crash (fn2-sim-profile fn2-sim) fn2-core fn2-sim fn2-own)
            (mv t fn2-core fn2-sim fn2-own)))
         ((mv found fn2-core fn2-sim fn2-own)
          (fn2-sim-native-post packet fn2-core fn2-sim fn2-own)))
      (if (eq cut :after-post)
          (mv-let (fn2-core fn2-sim fn2-own)
            (fn2-sim-crash (fn2-sim-profile fn2-sim) fn2-core fn2-sim fn2-own)
            (mv found fn2-core fn2-sim fn2-own))
        (mv found fn2-core fn2-sim fn2-own)))))

(fn2-sim-preserves fn2-sim-native-cut (cut slot fault word fn2-core fn2-sim fn2-own) :part nil
  :carriers ((fn2-core 1 :prefix "-CORE")
             (fn2-sim 2 :invariant fn2-sim-ready :prefix "-SIM" :suffix "-READY")
             (fn2-own 3 :prefix "-OWN")))
(verify-guards fn2-sim-native-cut)

; The packet is the exact physical return, not a synthetic success.  On the
; supported storage path, exposing and then closing the interval must preserve
; every output of the ordinary atomic completion, including core and OWN.
(defthm fn2-sim-native-finish-is-atomic
  (implies (and (fn2-corep fn2-core) (fn2-simp fn2-sim) (fn2-ownp fn2-own)
                (fn2-core-wfp fn2-core) (fn2-sim-ready fn2-sim)
                (fn2-own-wfp fn2-own) (unsigned-byte-p 32 word)
                (fn2-sim-native-storagep slot fn2-sim) (fn2-sim-native-faultp fault))
           (equal (fn2-sim-native-cut :finish slot fault word fn2-core fn2-sim fn2-own)
                  (fn2-sim-complete slot fault word fn2-core fn2-sim fn2-own)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-sim-native-cut fn2-sim-native-stage fn2-sim-native-post fn2-sim-native-packetp fn2-sim-native-storagep fn2-sim-native-flightp fn2-sim-complete fn2-sim-inject)
                            (fn2-sim-physical fn2-sim-complete-result fn2-sim-crash)))))

; The native "take" cut is before acknowledgement: the copied descriptor is
; volatile and the common ops table still owns its queued head.  "ack" is
; after the model's register/ack transition.  Both positions really invoke
; the same crash program, rather than naming an unreachable internal branch.
(defun fn2-sim-native-take-cut (cut fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil
                  :guard (and (fn2-core-wfp fn2-core) (fn2-sim-ready fn2-sim)
                              (fn2-own-wfp fn2-own)
                              (member-eq cut '(:before-take :after-take)))))
  (b* (((mv found fn2-core fn2-sim fn2-own)
        (if (eq cut :after-take)
            (fn2-sim-take-one fn2-core fn2-sim fn2-own)
          (mv t fn2-core fn2-sim fn2-own)))
       ((mv fn2-core fn2-sim fn2-own)
        (fn2-sim-crash (fn2-sim-profile fn2-sim) fn2-core fn2-sim fn2-own)))
    (mv found fn2-core fn2-sim fn2-own)))
(fn2-sim-preserves fn2-sim-native-take-cut (cut fn2-core fn2-sim fn2-own) :part nil
  :carriers ((fn2-core 1 :prefix "-CORE")
             (fn2-sim 2 :invariant fn2-sim-ready :prefix "-SIM" :suffix "-READY")
             (fn2-own 3 :prefix "-OWN")))
(verify-guards fn2-sim-native-take-cut)
