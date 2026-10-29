; Simulator state and reproducible fault schedule. All row storage and the
; diagnostic ring are preallocated; only init may resize arrays or save metadata.
(in-package "ACL2")
(include-book "../books/profile")
(include-book "network")
(include-book "storage")
(include-book "arithmetic-3/floor-mod/floor-mod" :dir :system)

; Fault IDs are persisted in the observation ring. 26 means no fault.
; 0 fragment, 1 short-send, 2 delay, 3 reset, 4 half-open, 5 nonreading,
; 6 read-io, 7 bitrot, 8 misread, 9 miswrite, 10 lying-flush, 11 tear,
; 12 no-space, 13 dead, 14 fail-slow, 15 crash, 16 monotonic-jump,
; 17 realtime-back, 18 duplicate, 19 stale, 20 forged, 21 overcount,
; 22 malformed, 23 flush-io, 24 short-write, 25 release-order.
(defcolumns fn2-sim
  ((active :u8) (gen :u60) (kind :u8) (due :u60) (range-slot :u32) (range-gen :u60) (range-off :u32) (range-len :u32) (owner-kind :u8) (owner-slot :u32) (owner-gen :u60) (cap-index :u32) (cap-nonce :u32) (storage-offset :u60) (fua :bool) (may-release :bool) (cancel-slot :u32) (cancel-gen :u60) (last-gen :u60) (cancelled :bool) (terminal-outcome :u8) (terminal-reason :u8) (terminal-count :u32) (terminal-aux0 :u32) (terminal-aux1 :u32))
  :init-name fn2-sim-columns-init
  :extra-fields
  ((fn2-sim-net :type fn2-sim-network
    :why "Simulator-only nested network stobj; its own defcolumns schema bounds resident fields.")
   (fn2-sim-disk :type fn2-sim-storage
    :why "Simulator-only nested storage stobj; its own defcolumns schema bounds resident fields.")
   (fn2-sim-profile :type t :initially nil
    :why "Simulator-only immutable initialization profile retained for replay.")
   (fn2-sim-profile-name :type t :initially nil
    :why "Simulator-only diagnostic profile label retained for replay.")
   (fn2-sim-revision :type t :initially nil
    :why "Simulator-only diagnostic source revision retained for replay.")
   (fn2-sim-initial-seed :type t :initially 0
    :why "Simulator-only original seed retained for replay; runtime PRNG uses bounded u32 state.")
   (fn2-sim-seed :type (unsigned-byte 32) :initially 0 :why "Simulator-wide random state, independent of flight rows.")
   (fn2-sim-s0 :type (unsigned-byte 32) :initially 0 :why "Simulator-wide random state, independent of flight rows.")
   (fn2-sim-s1 :type (unsigned-byte 32) :initially 0 :why "Simulator-wide random state, independent of flight rows.")
   (fn2-sim-s2 :type (unsigned-byte 32) :initially 0 :why "Simulator-wide random state, independent of flight rows.")
   (fn2-sim-s3 :type (unsigned-byte 32) :initially 0 :why "Simulator-wide random state, independent of flight rows.")
   (fn2-sim-now :type (unsigned-byte 60) :initially 0 :why "Simulator-wide clock, independent of flight rows.")
   (fn2-sim-real :type (unsigned-byte 60) :initially 0 :why "Simulator-wide clock, independent of flight rows.")
   (fn2-sim-deaths :type (unsigned-byte 32) :initially 0 :why "Simulator-wide control or accumulated evidence, independent of flight rows.")
   (fn2-sim-stamp :type (unsigned-byte 60) :initially 0 :why "Simulator-wide control or accumulated evidence, independent of flight rows.")
   (fn2-sim-fault-budget :type (unsigned-byte 32) :initially 0 :why "Simulator-wide control or accumulated evidence, independent of flight rows.")
   (fn2-sim-forced-fault :type (unsigned-byte 8) :initially 26 :why "Simulator-wide control or accumulated evidence, independent of flight rows.")
   (fn2-sim-digest :type (unsigned-byte 32) :initially 0 :why "Simulator-wide control or accumulated evidence, independent of flight rows.")
   (fn2-sim-ring-head :type (unsigned-byte 8) :initially 0 :why "Simulator-wide control or accumulated evidence, independent of flight rows.")
   (fn2-sim-observations :type (unsigned-byte 60) :initially 0 :why "Simulator-wide control or accumulated evidence, independent of flight rows.")
   (fn2-sim-probabilities :type (array (unsigned-byte 8) (26)) :initially 0 :why "Counters or policy indexed by fault/action kind, not flight rows.")
   (fn2-sim-hits :type (array (unsigned-byte 32) (26)) :initially 0 :why "Counters or policy indexed by fault/action kind, not flight rows.")
   (fn2-sim-action-counts :type (array (unsigned-byte 32) (14)) :initially 0 :why "Counters or policy indexed by fault/action kind, not flight rows.")
   (fn2-sim-ring-op :type (array (unsigned-byte 60) (64)) :initially 0 :why "Bounded diagnostic ring indexed independently of flight rows.")
   (fn2-sim-ring-gen :type (array (unsigned-byte 60) (64)) :initially 0 :why "Bounded diagnostic ring indexed independently of flight rows.")
   (fn2-sim-ring-cell :type (array (unsigned-byte 60) (64)) :initially 0 :why "Bounded diagnostic ring indexed independently of flight rows.")
   (fn2-sim-ring-event :type (array (unsigned-byte 60) (64)) :initially 0 :why "Bounded diagnostic ring indexed independently of flight rows.")
   (fn2-sim-ring-outcome :type (array (unsigned-byte 60) (64)) :initially 0 :why "Bounded diagnostic ring indexed independently of flight rows.")
   (fn2-sim-ring-reason :type (array (unsigned-byte 60) (64)) :initially 0 :why "Bounded diagnostic ring indexed independently of flight rows.")
   (fn2-sim-ring-count :type (array (unsigned-byte 60) (64)) :initially 0 :why "Bounded diagnostic ring indexed independently of flight rows.")
   (fn2-sim-ring-aux0 :type (array (unsigned-byte 60) (64)) :initially 0 :why "Bounded diagnostic ring indexed independently of flight rows.")
   (fn2-sim-ring-aux1 :type (array (unsigned-byte 60) (64)) :initially 0 :why "Bounded diagnostic ring indexed independently of flight rows.")
   (fn2-sim-ring-fault :type (array (unsigned-byte 60) (64)) :initially 0 :why "Bounded diagnostic ring indexed independently of flight rows.")
   (fn2-sim-wake-pending :type (unsigned-byte 1) :initially 0 :why "One adapter wake reservation shared by all flights.")
   (fn2-sim-wake-deadline :type (unsigned-byte 60) :initially 0 :why "One adapter wake reservation shared by all flights.")
   (fn2-sim-wake-observation-gen :type (unsigned-byte 60) :initially 0 :why "One adapter wake reservation shared by all flights.")))

(defthm fn2-sim-net-type
  (implies (fn2-simp fn2-sim) (fn2-sim-networkp (fn2-sim-net fn2-sim)))
  :hints (("Goal" :in-theory (enable fn2-simp))))
(defthm fn2-sim-disk-type
  (implies (fn2-simp fn2-sim) (fn2-sim-storagep (fn2-sim-disk fn2-sim)))
  :hints (("Goal" :in-theory (enable fn2-simp))))
(defthm fn2-sim-update-net-type
  (implies (and (fn2-simp fn2-sim) (fn2-sim-networkp child))
           (fn2-simp (update-fn2-sim-net child fn2-sim)))
  :hints (("Goal" :in-theory (enable fn2-simp))))
(defthm fn2-sim-update-disk-type
  (implies (and (fn2-simp fn2-sim) (fn2-sim-storagep child))
           (fn2-simp (update-fn2-sim-disk child fn2-sim)))
  :hints (("Goal" :in-theory (enable fn2-simp))))
(defthm fn2-sim-update-net-wfp
  (equal (fn2-sim-wfp (update-fn2-sim-net child fn2-sim)) (fn2-sim-wfp fn2-sim))
  :hints (("Goal" :in-theory (enable fn2-sim-wfp))))
(defthm fn2-sim-update-disk-wfp
  (equal (fn2-sim-wfp (update-fn2-sim-disk child fn2-sim)) (fn2-sim-wfp fn2-sim))
  :hints (("Goal" :in-theory (enable fn2-sim-wfp))))

(fn2-sim-preserves update-fn2-sim-profile (v fn2-sim) :disable nil
  :specs (("-TYPE" fn2-simp nil :hyps ((fn2-simp fn2-sim)) :hints (("Goal" :in-theory (enable fn2-simp))))
          ("-WFP" fn2-sim-wfp nil :frame fn2-sim :hints (("Goal" :in-theory (enable fn2-sim-wfp))))))
(fn2-sim-preserves update-fn2-sim-profile-name (v fn2-sim) :disable nil
  :specs (("-TYPE" fn2-simp nil :hyps ((fn2-simp fn2-sim)) :hints (("Goal" :in-theory (enable fn2-simp))))
          ("-WFP" fn2-sim-wfp nil :frame fn2-sim :hints (("Goal" :in-theory (enable fn2-sim-wfp))))))
(fn2-sim-preserves update-fn2-sim-revision (v fn2-sim) :disable nil
  :specs (("-TYPE" fn2-simp nil :hyps ((fn2-simp fn2-sim)) :hints (("Goal" :in-theory (enable fn2-simp))))
          ("-WFP" fn2-sim-wfp nil :frame fn2-sim :hints (("Goal" :in-theory (enable fn2-sim-wfp))))))
(fn2-sim-preserves update-fn2-sim-initial-seed (v fn2-sim) :disable nil
  :specs (("-TYPE" fn2-simp nil :hyps ((fn2-simp fn2-sim)) :hints (("Goal" :in-theory (enable fn2-simp))))
          ("-WFP" fn2-sim-wfp nil :frame fn2-sim :hints (("Goal" :in-theory (enable fn2-sim-wfp))))))

(defthm fn2-sim-parent-consp
  (implies (fn2-simp fn2-sim) (consp fn2-sim))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn2-simp))))

(defun fn2-sim-ready (fn2-sim)
  (declare (xargs :stobjs fn2-sim))
  (let ((own (fn2-sim-wfp fn2-sim)))
    (stobj-let ((fn2-sim-network (fn2-sim-net fn2-sim))
                (fn2-sim-storage (fn2-sim-disk fn2-sim)))
      (ok)
      (and own (fn2-sim-network-wfp fn2-sim-network)
           (fn2-sim-storage-wfp fn2-sim-storage))
      ok)))

(assert-event (fn2-profile-exports-compliant-p
  '(fn2-sim-ready) (w state)))
