; Simulator fault codes are not served action IDs. Reuse only the existing
; enum/constant producers, with a separate declaration registry entry.
(in-package "ACL2")
(include-book "../books/operations")

(make-event
 (let ((families
        '(
          (fn2-fault (:fragment 0) (:short-send 1) (:delay 2) (:reset 3) (:half-open 4) (:nonreading 5)
            (:read-io 6) (:bitrot 7) (:misread 8) (:miswrite 9) (:lying-flush 10) (:tear 11)
            (:no-space 12) (:dead 13) (:fail-slow 14) (:crash 15) (:monotonic-jump 16)
            (:realtime-back 17) (:duplicate 18) (:stale 19) (:forged 20) (:overcount 21)
            (:malformed 22) (:flush-io 23) (:short-write 24) (:release-order 25) (:none 26) (:write-io 27) (:count 28)))))
   (value (fn2-declare '(:operation-set fn2-sim-faults)
                      (list :enums (fn2-code-enums families)) nil
                      (fn2-code-families families)))))

; Keep historical none=26; it is a sentinel inside the indexed domain,
; never a selectable or counted fault. New real classes may follow it.
(defun fn2-sim-real-faultp (fault)
 (declare (xargs :guard t))
 (and (natp fault) (< fault *fn2-fault-count*)
      (not (equal fault *fn2-fault-none*))))

(assert-event (and (equal *fn2-fault-none* 26)
                   (equal *fn2-fault-write-io* 27)
                   (equal *fn2-fault-count* (+ 1 *fn2-fault-write-io*))
                   (not (fn2-sim-real-faultp *fn2-fault-none*))
                   (fn2-sim-real-faultp *fn2-fault-write-io*)
                   (equal *fn2-fault-read-io* 6)
                   (equal *fn2-fault-no-space* 12)
                   (equal *fn2-fault-flush-io* 23)))
