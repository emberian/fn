; A5r's refinement keystone's teeth (layer doc 4.1.6) over a recorded native
; trace (fn2/tests/evidence/native-envelope-trace.lisp, written by
; fn2/tests/native-loop.lsp on loopback TCP), and ENVELOPE on it.
(in-package "ACL2")
(include-book "../books/owed-native")
(include-book "evidence/native-envelope-trace")

; The recorded schedule is legal, DATE-free, and its replay sends what the
; canonical view sends; the clients' own bytes agree too.
(defun fn2-native-test-refines ()
  (declare (xargs :verify-guards nil))
  (and (fn2-envelope-steps-ok-p *fn2-native-trace*)
       (fn2-envelope-date-free-p *fn2-native-trace*)
       (consp (fn2-envelope-replay-wires *fn2-native-trace*))
       (equal (fn2-envelope-replay-wires *fn2-native-trace*)
              (fn2-envelope-canonical-wires *fn2-native-trace*))
       (eq (fn2-envelope-check *fn2-native-trace* *fn2-native-clients* *fn2-native-profile*) :pass)))

; Dropping the first Send result: the schedule is illegal (the replay's
; outbox no longer matches) and the replay's wires are not the canonical
; ones, so the legality hypothesis carries the statement.
(defun fn2-native-drop-first-send (trace kinds)
  (declare (xargs :verify-guards nil))
  (cond ((atom trace) nil)
        ((and (consp (car trace)) (eq (car (car trace)) :take))
         (cons (car trace) (fn2-native-drop-first-send (cdr trace) (put-assoc-equal (nth 1 (car trace)) (nth 3 (car trace)) kinds))))
        ((and (consp (car trace)) (eq (car (car trace)) :post)
              (equal (cdr (assoc-equal (nth 2 (car trace)) kinds)) *fn2-action-send*))
         (cdr trace))
        (t (cons (car trace) (fn2-native-drop-first-send (cdr trace) kinds)))))
(defun fn2-native-test-refines-negative ()
  (declare (xargs :verify-guards nil))
  (let ((m (fn2-native-drop-first-send *fn2-native-trace* nil)))
    (and (not (fn2-envelope-steps-ok-p m))
         (fn2-envelope-date-free-p m)
         (not (equal (fn2-envelope-replay-wires m) (fn2-envelope-canonical-wires m))))))
(assert-event (and (fn2-native-test-refines) (fn2-native-test-refines-negative)))
(value-triple (cw "NATIVE UNIT: recorded native schedule legal, replay wires = canonical wires, ENVELOPE pass; dropped Send refused PASS~%"))
