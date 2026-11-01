; A5r's socket session for the surface harness (layer doc 4.1.4; the Python
; side is fn2/tests/surface/fn2_native_session.py, the hook
; FN2_SURFACE_SIM_NNTP=fn2.tests.surface.fn2_native_session:session for H's
; unchanged sim_target.py). This LD part includes the certified books; the
; session then leaves the ACL2 loop (:q), loads fn2/host/*.lisp and
; fn2/host/native-session-raw.lisp, and serves on 127.0.0.1 with the
; control lines on stdin, serving the surface sessions' profile and seeded
; store (seeded-store.lsp; reading over local.test with three articles and
; local.empty), as the simulator session does. Answers are marker lines, as the simulator
; session's: @@FN2SS <tag> ...@@.
(in-package "ACL2")
(include-book "../sim/check-wire")
(ld "seeded-store.lsp")
(set-inhibit-output-lst '(proof-tree prove event summary observation warning))
(value-triple (cw "@@FN2SS books - 0 0@@~%"))
