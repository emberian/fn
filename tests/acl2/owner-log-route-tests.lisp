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

; fn-olr-bounds (the host's call): a configuration record after `policy set
; log-batch-records 2' (the :set-limit delta native-admin plans) bounds a batch
; at 2.  Mutation witness (labelled): the call the host made before, the
; record itself given to fn-olr-bmax, reads the default 64.
(defconst *olrt-v2*
  (fn-cfg-apply-delta (fn-cfg-value-make-full nil nil nil nil nil nil nil nil nil nil nil)
                      2 0 (fn-cfg-set-limit "log-batch-records" 2)))
(defconst *olrt-cfg2* (fn-cfg-make 2 *olrt-v2*))
(assert-event (equal (fn-olr-bounds *olrt-cfg2*) (list 2 16777216)))
(assert-event (equal (fn-olr-bmax *olrt-cfg2*) 64))
(assert-event (equal (fn-olr-bounds (fn-cfg-make 1 (fn-cfg-value-make-full nil nil nil nil nil nil nil nil nil nil nil)))
                     (list 64 16777216)))
