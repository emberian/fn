; Raw acceptance controls: force the real pool-refusal branch, then let the
; listener Close, adapter and client oracle run. Restore all hooks on exit.
(in-package "ACL2")
(defun fn2-l1-controls ()
  (let* ((profile (put-assoc-equal :c 1 *fn2-profile-tiny*))
         (core (create-fn2-core)))
    (fn2-core-init profile core)
    (assert (= (nth-value 2 (fn2-machine-run 0 4 core)) 1))
    (assert (zerop (fn2-machine-admission-credits *fn2-echo-admission-ordinal* core)))
    (multiple-value-bind (bytes steps actions runnable) (fn2-machine-run 1 4 core)
      (declare (ignore bytes steps))
      (assert (and (zerop actions) (null runnable))))
    (assert (= (fn2-machine-admission-head *fn2-echo-admission-ordinal* core) 1))
    (assert (= (fn2-machine-wait-head core) *fn2-none*))
    ; An unsuccessful Accept returns the reservation and wakes the FIFO waiter.
    (fn2-machine-observe *fn2-listener-kind* 0 1 *fn2-event-accept-result*
                         *fn2-outcome-failed* 0 0 0 0 core)
    (assert (= (fn2-machine-admission-credits *fn2-echo-admission-ordinal* core) 1))
    (assert (= (fn2-machine-grant-one core) 1))
    (assert (= (nth-value 2 (fn2-machine-run 1 4 core)) 1))
    (assert (zerop (fn2-machine-admission-credits *fn2-echo-admission-ordinal* core))))
  (let ((reserve (symbol-function 'fn2-core-reserve))
        (abi (symbol-function 'fn2-abi-landings))
        (refuse (symbol-function 'fn2-network-refuse))
        (profile (put-assoc-equal :c 1 (put-assoc-equal :accept-credits 1 *fn2-profile-tiny*))))
    (unwind-protect
        (progn
          (setf (symbol-function 'fn2-core-reserve)
                (lambda (class kind owner generation core)
                  (if (= kind *fn2-echo-kind*) (values :exhausted 0 0 core)
                    (funcall reserve class kind owner generation core))))
          ; The refusal mutation targets the workload. Physical ABI evidence
          ; still executes every probe using the real reservation operation.
          (setf (symbol-function 'fn2-abi-landings)
                (lambda (core sim own)
                  (let ((injected-reserve (symbol-function 'fn2-core-reserve)))
                    (unwind-protect
                        (progn (setf (symbol-function 'fn2-core-reserve) reserve)
                               (funcall abi core sim own))
                      (setf (symbol-function 'fn2-core-reserve) injected-reserve)))))
          (let* ((result (fn2-sim-run-echo 20261028 0 profile)) (live (nth 9 result)))
            (assert (equal (first result) '(:fail :liveness-drops)))
            (assert (equal (first live) '(:fail :liveness-drops)))
            (assert (= (second live) (fourth live) 200))
            (assert (= (fn2-echo-stat :admission-refused (nth 6 live)) 200))
            (assert (zerop (fn2-echo-stat :unattributed (nth 6 live)))))
          ; Removing only attribution must fail safety, not bless a plain Close.
          (setf (symbol-function 'fn2-network-refuse) (symbol-function 'fn2-network-close))
          (let ((result (fn2-sim-run-echo 20261028 1 profile)))
            (assert (equal (first result) '(:fail :unattributed-drops)))
            (assert (= (fn2-echo-stat :unattributed (nth 7 result)) 1))))
      (setf (symbol-function 'fn2-core-reserve) reserve
            (symbol-function 'fn2-abi-landings) abi
            (symbol-function 'fn2-network-refuse) refuse))
    (assert (and (eq (symbol-function 'fn2-core-reserve) reserve)
                 (eq (symbol-function 'fn2-abi-landings) abi)
                 (eq (symbol-function 'fn2-network-refuse) refuse))))
  (format t "L1 CONTROLS reservation=PASS FIFO-wake=PASS admission-refused=200 live-drop=REJECTED unattributed-safety=REJECTED~%"))
