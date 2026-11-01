; Layer D's operations after layer A's and layer C's sections (each section its
; own book keeps it under the one-minute rule): the operations the connection
; and the upload share, then the connection's helpers. The connection's
; continuations are assembly-callbacks-d-conn.lisp, the upload's
; assembly-callbacks-d-upload.lisp, the transaction's operations and
; continuations assembly-callbacks-d-txn.lisp.
(in-package "ACL2")
(include-book "assembly-callbacks-c")
(fn2-upload-op-events)
(fn2-conn-op-events)
