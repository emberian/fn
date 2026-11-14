; Constructor/API dependency control for the raw-return state used by the
; later real physical Fence fixture. This is not a physical-cut witness.
(in-package "ACL2")
(include-book "../sim/native-cut-state")

(defun fn2-native-cut-state-control ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-sim
    (mv-let (ok fn2-sim)
      (b* ((fn2-sim (fn2-sim-init 7 :friendly "raw-state-unit" *fn2-profile-tiny* fn2-sim))
           (fn2-sim (fn2-sim-put 0 (active 1) (gen 1) (kind *fn2-action-fence*) (range-len 0)
                      (return-code (fn2-sim-return-code-keyword->code :ok))
                      (return-count 3) (return-aux 5) (return-word 7) (return-time 9)
                      (return-fault *fn2-fault-none*)))
           ; unreachable-in-composition: count3/aux5 deliberately distinguish
           ; the typed columns. A real physical Fence has count0/aux0. These
           ; synthetic values are only an API/codec identity control.
           (packet (list 0 1 *fn2-action-fence* *fn2-event-fence-result* 0 :ok 3 5 7 9 *fn2-fault-none*))
           (before (and (fn2-simp fn2-sim) (fn2-sim-ready fn2-sim)
                        (fn2-sim-native-flightp 0 fn2-sim)
                        (fn2-sim-native-packetp packet fn2-sim)
                        (not (fn2-sim-native-packetp (update-nth 1 2 packet) fn2-sim))))
           (fn2-sim (fn2-sim-set-active 0 *fn2-sim-native-returned* fn2-sim))
           (returned (and (fn2-simp fn2-sim) (fn2-sim-ready fn2-sim)
                          (not (fn2-sim-native-flightp 0 fn2-sim))
                          (fn2-sim-native-packetp packet fn2-sim)
                          (equal (fn2-sim-return-code-code->keyword
                                   (fn2-sim-return-code 0 fn2-sim)) :ok)
                          (= (fn2-sim-return-count 0 fn2-sim) 3)
                          (= (fn2-sim-return-aux 0 fn2-sim) 5)
                          (= (fn2-sim-return-word 0 fn2-sim) 7)
                          (= (fn2-sim-return-time 0 fn2-sim) 9)
                          (= (fn2-sim-return-fault 0 fn2-sim) *fn2-fault-none*)))
           (fn2-sim (fn2-sim-set-active 0 1 fn2-sim)))
        (mv (and before returned (fn2-sim-native-flightp 0 fn2-sim)
                 (= (fn2-sim-return-count 0 fn2-sim) 3) (= (fn2-sim-return-aux 0 fn2-sim) 5))
            fn2-sim))
      ok)))
(assert-event (fn2-native-cut-state-control))
