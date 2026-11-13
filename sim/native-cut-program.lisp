; Explicit storage microsteps for native death cuts.  The seeded simulator's
; atomic completion schedule is unchanged.  This driver exposes the interval
; after physical I/O and before its terminal post, retaining the raw result.
(in-package "ACL2")
(include-book "sim")

(include-book "native-cut-state")

(defun fn2-sim-native-stage (slot word fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil
                  :guard (and (fn2-core-wfp fn2-core) (fn2-sim-ready fn2-sim)
                              (fn2-own-wfp fn2-own) (unsigned-byte-p 32 word))))
  (if (not (fn2-sim-native-storagep slot fn2-sim))
      (mv :unsupported nil fn2-core fn2-sim fn2-own)
    (b* ((gen (fn2-sim-gen slot fn2-sim)) (kind (fn2-sim-kind slot fn2-sim))
         (event (fn2-terminal-event kind)) (len (fn2-sim-range-len slot fn2-sim))
         (now (fn2-sim-now fn2-sim))
         ((mv code count aux fn2-core fn2-sim fn2-own)
          (fn2-sim-physical slot *fn2-fault-none* word fn2-core fn2-sim fn2-own))
         ((when (and (eq code :would-block) (equal count 0)))
          (let ((fn2-sim (fn2-sim-set-due slot (min *fn2-u60-max* (+ 100 now)) fn2-sim)))
            (mv :waiting nil fn2-core fn2-sim fn2-own)))
         (packet (list slot gen kind event len code count aux word now))
         (fn2-sim (fn2-sim-set-active slot *fn2-sim-native-returned* fn2-sim)))
      (mv :returned packet fn2-core fn2-sim fn2-own))))

(defun fn2-sim-native-post (packet fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil
                  :guard (and (fn2-core-wfp fn2-core) (fn2-sim-ready fn2-sim)
                              (fn2-own-wfp fn2-own))))
  (if (not (and (fn2-sim-native-packetp packet fn2-sim)
                (= (fn2-sim-active (nth 0 packet) fn2-sim) *fn2-sim-native-returned*)))
      (mv nil fn2-core fn2-sim fn2-own)
    (let ((fn2-sim (fn2-sim-set-active (nth 0 packet) 1 fn2-sim)))
      (fn2-sim-complete-result (nth 0 packet) (nth 1 packet) (nth 2 packet)
        (nth 3 packet) (nth 4 packet) (nth 5 packet) (nth 6 packet) (nth 7 packet)
        *fn2-fault-none* (nth 8 packet) (nth 9 packet) nil fn2-core fn2-sim fn2-own))))

(defun fn2-sim-native-cut (cut slot word fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil
                  :guard (and (fn2-core-wfp fn2-core) (fn2-sim-ready fn2-sim)
                              (fn2-own-wfp fn2-own) (unsigned-byte-p 32 word))))
  (if (eq cut :before-physical)
      (mv-let (fn2-core fn2-sim fn2-own)
        (fn2-sim-crash (fn2-sim-profile fn2-sim) fn2-core fn2-sim fn2-own)
        (mv t fn2-core fn2-sim fn2-own))
    (b* (((mv status packet fn2-core fn2-sim fn2-own)
          (fn2-sim-native-stage slot word fn2-core fn2-sim fn2-own))
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

; The packet is the exact physical return, not a synthetic success.  On the
; supported storage path, exposing and then closing the interval must preserve
; every output of the ordinary atomic completion, including core and OWN.
(defthm fn2-sim-native-finish-is-atomic
  (implies (and (fn2-core-wfp fn2-core) (fn2-sim-ready fn2-sim)
                (fn2-own-wfp fn2-own) (unsigned-byte-p 32 word)
                (fn2-sim-native-storagep slot fn2-sim))
           (equal (fn2-sim-native-cut :finish slot word fn2-core fn2-sim fn2-own)
                  (fn2-sim-complete slot *fn2-fault-none* word fn2-core fn2-sim fn2-own)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-sim-native-cut fn2-sim-native-stage fn2-sim-native-post
                             fn2-sim-native-packetp fn2-sim-native-storagep
                             fn2-sim-complete fn2-sim-inject)
                            (fn2-sim-physical fn2-sim-complete-result fn2-sim-crash)))))
