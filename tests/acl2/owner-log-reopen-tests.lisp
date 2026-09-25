; Teeth for books/owner-log-reopen.lisp (PKT-101).
(in-package "ACL2")
(include-book "../../books/owner-log-reopen")
(include-book "std/testing/must-fail" :dir :system)

; Witnesses: one SIGHUP with a log file reopens and handles it; two more
; arriving together reopen once; with no log file the request is handled
; and nothing is opened; no new request, nothing.
(assert-event (equal (fn-olr-decide t 0 1) '(:reopen 1)))
(assert-event (equal (fn-olr-decide t 1 3) '(:reopen 3)))
(assert-event (equal (fn-olr-decide nil 0 1) '(:ignore 1)))
(assert-event (equal (fn-olr-decide t 3 3) '(:none 3)))
(assert-event
 (equal (fn-olr-line 2 nil)
        (fn-record-string-octets "reopened log signal=hup requests=2 time=none")))

; Teeth for fn-olr-reopen-iff-requested, one per hypothesis: without
; (natp handled) a non-natural count is not echoed back; without
; (natp requested) a non-natural request is not handled.
(must-fail
 (assert-event (equal (cadr (fn-olr-decide t 5/2 3)) (max 5/2 3))))
(must-fail
 (assert-event (equal (cadr (fn-olr-decide t 0 1/2)) (max 0 1/2))))
; The conclusion's iff fails for a request that is not a natural.
(must-fail
 (assert-event (iff (equal (car (fn-olr-decide t 0 1/2)) :reopen) (< 0 1/2))))
