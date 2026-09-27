; Witnesses for books/owner-log-route.lisp (lane commit-onto-log, 2026-09-27).
; The owner's composites are the file route's success sequences by definition
; (the two -by-definition theorems; their phase facts over the store node are
; books/store-log-route-phases.lisp's, and the native module
; tests/test_native_commit_log.py observes the phases the host checks).  Here:
; the operator's batch bounds with no limit configured are the defaults.
(in-package "ACL2")
(include-book "../../books/owner-log-route")

(assert-event (equal (fn-olr-bmax nil) *fn-olr-batch-records-default*))
(assert-event (equal (fn-olr-bmax nil) 64))
(assert-event (equal (fn-olr-omax nil) 16777216))
(assert-event (posp (fn-olr-bmax '(1 2 3))))
