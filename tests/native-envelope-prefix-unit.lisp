; A legal finite native prefix need not contain the canonical complete wire.
(in-package "ACL2")
(include-book "../books/owed-native")
(include-book "evidence/native-envelope-trace")

(defun fn2-native-envelope-prefix-counterexample (trace)
  (declare (xargs :verify-guards nil))
  (and (fn2-envelope-steps-ok-p trace)
       (fn2-envelope-date-free-p trace)
       (<= (len (fn2-env-trace-conns trace nil nil)) 4)
       (not (equal (fn2-envelope-replay-wires trace)
                   (fn2-envelope-canonical-wires trace)))))
(defthm fn2-native-envelope-counterexample-by-definition
  (equal (fn2-native-envelope-prefix-counterexample trace)
         (not (fn2-native-envelope-refines$owed trace)))
  :hints (("Goal" :in-theory '(fn2-native-envelope-prefix-counterexample
                              fn2-native-envelope-refines$owed))))

; The sixth event accepts a connection; its greeting has not been sent.
(assert-event
 (and (fn2-native-envelope-prefix-counterexample (take 6 *fn2-native-trace*))
      (equal (fn2-envelope-replay-wires (take 6 *fn2-native-trace*)) '(nil))
      (equal (len (car (fn2-envelope-canonical-wires (take 6 *fn2-native-trace*)))) 39)))

; Keep the existing complete recorded run as a positive correspondence control.
; This is evidence for this run, not a theorem about all completed schedules.
(assert-event
 (and (fn2-envelope-steps-ok-p *fn2-native-trace*)
      (fn2-envelope-date-free-p *fn2-native-trace*)
      (<= (len (fn2-env-trace-conns *fn2-native-trace* nil nil)) 4)
      (equal (fn2-envelope-replay-wires *fn2-native-trace*)
             (fn2-envelope-canonical-wires *fn2-native-trace*))))
