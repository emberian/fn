; Leaf attachment book (Astra A10 / Fable R6): attaches per-kind leaf
; implementations (fn2-conn, fn2-upload, fn2-txn, fn2-cursor, fn2-ctl, fn2-cns)
; to the constrained dispatch stubs in assembly-dispatch.lisp after executor.lisp.
(in-package "ACL2")
(include-book "executor")
(include-book "assembly-callbacks-d-conn")
(include-book "assembly-callbacks-d-upload")
(include-book "assembly-callbacks-d-txn")
(include-book "assembly-callbacks-d-cursor")
(include-book "assembly-callbacks-e-cns")
(fn2-machine-attach-all-events)
