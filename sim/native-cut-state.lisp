; Raw physical-return state shared by native cuts and scheduled Fence completion.
(in-package "ACL2")
(include-book "sim-state")

; Active 3 is the existing early borrow-release continuation.  Active 4 is
; physical I/O finished, terminal post not sent.
; FN2-SIM-FIND-WRITE selects only active 1, so a crash cannot replay this write.

(defun fn2-sim-native-flightp (slot fn2-sim)
  (declare (xargs :stobjs fn2-sim :guard (fn2-sim-ready fn2-sim)))
  (and (natp slot) (< slot (fn2-sim-rows fn2-sim))
       (= (fn2-sim-active slot fn2-sim) 1)
       (= (fn2-sim-cancelled slot fn2-sim) 0)
       (fn2-action-completionp (fn2-sim-kind slot fn2-sim))
       (not (equal (fn2-sim-kind slot fn2-sim) *fn2-action-cancel*))))

(defun fn2-sim-native-storagep (slot fn2-sim)
  (declare (xargs :stobjs fn2-sim :guard (fn2-sim-ready fn2-sim)))
  (and (fn2-sim-native-flightp slot fn2-sim)
       (member-equal (fn2-sim-kind slot fn2-sim)
                     (list *fn2-action-read* *fn2-action-write* *fn2-action-fence*))))

(defun fn2-sim-native-faultp (fault)
  (declare (xargs :guard t))
  (member-equal fault
    (list *fn2-fault-none* *fn2-fault-read-io* *fn2-fault-no-space* *fn2-fault-dead*
          *fn2-fault-flush-io* *fn2-fault-short-write* *fn2-fault-bitrot*
          *fn2-fault-misread* *fn2-fault-miswrite* *fn2-fault-lying-flush*
          *fn2-fault-tear* *fn2-fault-fail-slow* *fn2-fault-fragment*
          *fn2-fault-short-send* *fn2-fault-reset* *fn2-fault-half-open* *fn2-fault-nonreading*)))

(defthm fn2-sim-native-fault-not-injected
  (implies (fn2-sim-native-faultp fault)
           (not (member-equal fault
                  (list *fn2-fault-stale* *fn2-fault-forged*
                        *fn2-fault-overcount* *fn2-fault-malformed*)))))
(in-theory (disable fn2-sim-native-faultp))

; Packet fields: slot, generation, kind, event, length, raw code, raw count,
; raw auxiliary result, schedule word, the original completion time, and the physical fault.
(defun fn2-sim-native-packetp (packet fn2-sim)
  (declare (xargs :stobjs fn2-sim :guard (fn2-sim-ready fn2-sim)))
  (and (true-listp packet) (= (len packet) 11)
       (natp (nth 0 packet)) (< (nth 0 packet) (fn2-sim-rows fn2-sim))
       (unsigned-byte-p 60 (nth 1 packet)) (natp (nth 4 packet))
       (equal (nth 1 packet) (fn2-sim-gen (nth 0 packet) fn2-sim))
       (equal (nth 2 packet) (fn2-sim-kind (nth 0 packet) fn2-sim))
       (equal (nth 3 packet) (fn2-terminal-event (nth 2 packet)))
       (equal (nth 4 packet) (fn2-sim-range-len (nth 0 packet) fn2-sim))
       (unsigned-byte-p 32 (nth 8 packet)) (unsigned-byte-p 60 (nth 9 packet))
       (fn2-sim-native-faultp (nth 10 packet))))

(local (defthm fn2-native-update-same
  (equal (update-nth i a (update-nth i b xs)) (update-nth i a xs))
  :hints (("Goal" :induct (update-nth i a xs)))))
(local (defthm fn2-native-update-current
  (implies (and (natp i) (< i (len xs)))
           (equal (update-nth i (nth i xs) xs) xs))
  :hints (("Goal" :induct (update-nth i (nth i xs) xs)))))

(local (defthm fn2-native-nth-atom
  (implies (not (consp xs)) (equal (nth i xs) nil))
  :hints (("Goal" :induct (nth i xs)))))

(local (defthm fn2-native-update-head
  (implies (consp xs) (equal (update-nth 0 (nth 0 xs) xs) xs))))

(defthm fn2-sim-native-active-roundtrip
  (implies (and (fn2-sim-ready fn2-sim) (natp slot)
                (< slot (fn2-sim-rows fn2-sim))
                (equal (fn2-sim-active slot fn2-sim) 1))
           (equal (fn2-sim-set-active slot 1
                    (fn2-sim-set-active slot *fn2-sim-native-returned* fn2-sim))
                  fn2-sim))
  :hints (("Goal" :cases ((consp fn2-sim))
           :use ((:instance fn2-native-update-current (i slot) (xs (nth *fn2-sim-active$ai* fn2-sim))))
           :in-theory (e/d (fn2-sim-set-active fn2-sim-active
                                    update-fn2-sim-active$ai update-nth-array
                                    fn2-sim-ready fn2-sim-wfp)
                            (update-nth nth)))))


(defthm fn2-sim-native-returned-ready
  (implies (and (fn2-sim-ready fn2-sim) (natp slot)
                (< slot (fn2-sim-rows fn2-sim)))
           (fn2-sim-ready (fn2-sim-set-active slot *fn2-sim-native-returned* fn2-sim)))
  :hints (("Goal" :in-theory (enable fn2-sim-ready))))

(defthm fn2-sim-native-returned-active
  (implies (natp slot)
           (equal (fn2-sim-active slot (fn2-sim-set-active slot *fn2-sim-native-returned* fn2-sim))
                  *fn2-sim-native-returned*))
  :hints (("Goal" :in-theory (enable fn2-sim-active))))
