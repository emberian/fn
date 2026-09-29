; Teeth for books/native-control-launch.lisp (packet B; PKT-700: the ceiling
; is the store profile's field 16).
(in-package "ACL2")
(include-book "../../books/native-control-launch")

(defconst *ncla-p* *fn-bs-profile-development*)
(defconst *ncla-max* (fn-bs-profile-max-control-clients *ncla-p*))
(assert-event (equal *ncla-max* 16))
; REACHABLE: an idle plane launches; one below the ceiling launches and the
; launch reaches the ceiling exactly.
(assert-event (equal (fn-ncla-launch-disposition nil 0 *ncla-p*) :launch))
(assert-event (equal (fn-ncla-launch-disposition nil (1- *ncla-max*) *ncla-p*) :launch))
(assert-event (<= (+ 1 (1- *ncla-max*)) *ncla-max*))
; At the ceiling and one past it: :busy by name.
(assert-event (equal (fn-ncla-launch-disposition nil *ncla-max* *ncla-p*) :busy))
(assert-event (equal (fn-ncla-launch-disposition nil (1+ *ncla-max*) *ncla-p*) :busy))
; Stopping wins over everything.
(assert-event (equal (fn-ncla-launch-disposition t 0 *ncla-p*) :stopping))
(assert-event (equal (fn-ncla-launch-disposition t *ncla-max* *ncla-p*) :stopping))
; A count that is no natural never launches.
(assert-event (equal (fn-ncla-launch-disposition nil -1 *ncla-p*) :busy))
(assert-event (equal (fn-ncla-launch-disposition nil :many *ncla-p*) :busy))
; Hypothesis removal for fn-ncla-at-the-ceiling-is-busy: without
; (not stoppingp) the answer at the ceiling is :stopping; without the
; ceiling hypothesis (one below it) the answer is :launch.
(assert-event (not (equal (fn-ncla-launch-disposition t *ncla-max* *ncla-p*) :busy)))
(assert-event (not (equal (fn-ncla-launch-disposition nil (1- *ncla-max*) *ncla-p*) :busy)))

; The ceiling is the profile's, not a constant: a profile of 200 launches the
; 17th through the 200th worker and refuses the 201st; a profile of 5 (the
; four reserved workers and one waiter) refuses the 6th.
(defconst *ncla-wide* (fn-bs-profile-resolve '(:development ((16 . 200))) nil))
(defconst *ncla-narrow* (fn-bs-profile-resolve '(:development ((16 . 5))) nil))
(assert-event (fn-bs-profile-admittedp *ncla-wide*))
(assert-event (fn-bs-profile-admittedp *ncla-narrow*))
(assert-event (equal (fn-ncla-launch-disposition nil 16 *ncla-wide*) :launch))
(assert-event (equal (fn-ncla-launch-disposition nil 199 *ncla-wide*) :launch))
(assert-event (equal (fn-ncla-launch-disposition nil 200 *ncla-wide*) :busy))
(assert-event (equal (fn-ncla-launch-disposition nil 4 *ncla-narrow*) :launch))
(assert-event (equal (fn-ncla-launch-disposition nil 5 *ncla-narrow*) :busy))
; The keystone's positive witness over the wide profile: a launch at 199
; leaves the workers within the ceiling.
(assert-event (<= (+ 1 199) (fn-bs-profile-max-control-clients *ncla-wide*)))
