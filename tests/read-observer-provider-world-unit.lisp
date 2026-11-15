; PREPARED UNEXECUTED: the actual assembly emits fn2-read-core-events.
; Inspect that world; do not hand-write a twin CORE wrapper or inferred child.
(in-package "ACL2")
(include-book "../books/assembly-attach")
(assert-event
 (and
  (equal (getpropc 'fn2-read-observer-enter 'formals nil (w state))
   '(x fresh fn2-reads fn2-c-source-control fn2-c-source-readers fn2-id-decides
     fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool))
  (equal (getpropc 'fn2-read-observer-enter 'stobjs-out nil (w state))
   '(nil fn2-reads fn2-c-source-control fn2-c-source-readers fn2-run-loads
     fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases))
  (equal (getpropc 'fn2-read-lookup 'formals nil (w state)) '(x sid budget fn2-core))
  (equal (getpropc 'fn2-read-release 'formals nil (w state)) '(x fn2-core))
  (equal (getpropc 'fn2-read-release 'stobjs-out nil (w state)) '(nil fn2-core))
  (equal (getpropc 'fn2-run-load-region-park 'stobjs-out nil (w state))
   '(nil fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases))))
