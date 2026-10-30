; A5r's loop acceptance (layer doc 4.1.5): the served core (the listener
; admitting fn2-conn) under the native adapter on loopback TCP, conn-unit's
; fixtures as clients in their every-split chunkings, WIRE per client and
; ENVELOPE over the boundary trace, then ENVELOPE's seven controls; the trace
; of the first client set is written to fn2/tests/evidence/native-envelope-trace.lisp
; for the refinement keystone's teeth. Run: tools/acl2 < fn2/tests/native-loop.lsp
(in-package "ACL2")
(include-book "fn2/tests/conn-unit")
(include-book "fn2/sim/check-envelope")
(set-inhibit-output-lst '(proof-tree prove event summary observation warning))
(defconst *fn2-nl-profile* (put-assoc-equal :trace nil *fn2-conn-wire-profile*))
:q
(handler-case
 (progn
  (load "fn2/host/ffi.lisp")
  (load "fn2/host/adapter.lisp")
  (load "fn2/host/native-clients.lisp")
  (load "fn2/host/native-loop-driver.lisp")
  (sb-ext:exit :code (if (fn2-nl-main) 0 1)))
 (cl:error (c) (format t "NATIVE LOOP ERROR: ~A~%" c) (finish-output) (sb-ext:exit :code 1)))
