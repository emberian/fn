; B5-1: defcolumns' generated init gives a fresh table (resize to 0, then n;
; extras emptied or reset), so a death leaves every core child at its init
; values; a planted survivor is reported by the same comparison.
(in-package "ACL2")
(include-book "../sim/check-death")
(fn2-book-layer :b)
(assert-event
 (let ((d (fn2-b-death-control (fn2-b-test-profile *fn2-profile-tiny* 0))))
  (and (car d) (cadr d))))
(assert-event
 (let ((d (fn2-b-death-control (fn2-b-test-profile *fn2-profile-tiny* 1))))
  (and (car d) (cadr d))))
