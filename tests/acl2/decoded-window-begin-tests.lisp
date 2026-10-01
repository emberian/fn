(in-package "ACL2")
(include-book "../../books/decoded-window-begin")
(defun pwzt-initializer (token)
 (declare (xargs :verify-guards nil))
 (with-local-stobj pgs-digest-state
 (mv-let (answer pgs-digest-state)
 (with-local-stobj fn-zin-st
 (mv-let (answer fn-zin-st pgs-digest-state)
 (with-local-stobj fn-zin-win
 (mv-let (answer fn-zin-win fn-zin-st pgs-digest-state)
 (with-local-stobj fn-zin-tab
 (mv-let (answer fn-zin-tab fn-zin-win fn-zin-st pgs-digest-state)
 (with-local-stobj fn-zin-out
 (mv-let (answer fn-zin-out fn-zin-tab fn-zin-win fn-zin-st pgs-digest-state)
 (mv-let (z pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
 (fn-pwz-begin token 301 pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
 (mv (list z (fn-zin-preset fn-zin-st)) fn-zin-out fn-zin-tab fn-zin-win fn-zin-st pgs-digest-state))
 (mv answer fn-zin-tab fn-zin-win fn-zin-st pgs-digest-state)))
 (mv answer fn-zin-win fn-zin-st pgs-digest-state)))
 (mv answer fn-zin-st pgs-digest-state)))
 (mv answer pgs-digest-state)))
 answer)))
; REACHABLE POSITIVE: actual typed initializer keeps all captured coordinates.
(assert-event (let* ((token '(:decoded-window 17 7 100 320 120 40 200 99 250 0))
 (r (pwzt-initializer token)) (z (car r)) (raw (nth 1 z)))
 (and (fn-pwz-tokenp token) (equal (car z) :scan)
 (equal (list (nth 1 raw) (nth 2 raw) (nth 3 raw) (nth 11 raw) (nth 12 raw)) '(7 100 320 120 40))
 (equal (nth 13 raw) 40) (equal (nth 5 raw) 0)
 (equal (nth 8 raw) 17) (equal (nth 9 raw) 301) (equal (nth 10 raw) token)
 (equal (list (nth 2 z) (nth 3 z) (nth 4 z)) '(250 200 50))
 (equal (nth 1 r) 0))))
