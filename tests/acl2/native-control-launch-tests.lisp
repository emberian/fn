; Teeth for books/native-control-launch.lisp (packet B).
(in-package "ACL2")
(include-book "../../books/native-control-launch")

(defconst *ncla-max* (fn-native-control-max-active-clients))
(assert-event (equal *ncla-max* 16))
; REACHABLE: an idle plane launches; one below the ceiling launches and the
; launch reaches the ceiling exactly.
(assert-event (equal (fn-ncla-launch-disposition nil 0) :launch))
(assert-event (equal (fn-ncla-launch-disposition nil (1- *ncla-max*)) :launch))
(assert-event (<= (+ 1 (1- *ncla-max*)) *ncla-max*))
; At the ceiling and one past it: :busy by name.
(assert-event (equal (fn-ncla-launch-disposition nil *ncla-max*) :busy))
(assert-event (equal (fn-ncla-launch-disposition nil (1+ *ncla-max*)) :busy))
; Stopping wins over everything.
(assert-event (equal (fn-ncla-launch-disposition t 0) :stopping))
(assert-event (equal (fn-ncla-launch-disposition t *ncla-max*) :stopping))
; A count that is no natural never launches.
(assert-event (equal (fn-ncla-launch-disposition nil -1) :busy))
(assert-event (equal (fn-ncla-launch-disposition nil :many) :busy))
; Hypothesis removal for fn-ncla-at-the-ceiling-is-busy: without
; (not stoppingp) the answer at the ceiling is :stopping; without the
; ceiling hypothesis (one below it) the answer is :launch.
(assert-event (not (equal (fn-ncla-launch-disposition t *ncla-max*) :busy)))
(assert-event (not (equal (fn-ncla-launch-disposition nil (1- *ncla-max*)) :busy)))
