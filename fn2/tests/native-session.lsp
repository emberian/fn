; A5r's socket session for the surface harness (layer doc 4.1.4; the Python
; side is fn2/tests/surface/fn2_native_session.py, the hook
; FN2_SURFACE_SIM_NNTP=fn2.tests.surface.fn2_native_session:session for H's
; unchanged sim_target.py). This LD part includes the certified books; the
; session then leaves the ACL2 loop (:q), loads fn2/host/*.lisp and
; fn2/host/native-session-raw.lisp, and serves on 127.0.0.1 with the
; control lines on stdin. Answers are marker lines, as the simulator
; session's: @@FN2SS <tag> ...@@.
(in-package "ACL2")
(include-book "../books/owed-conn")
(include-book "../sim/check-wire")
(include-book "../sim/check-envelope")
(set-inhibit-output-lst '(proof-tree prove event summary observation warning))
(defconst *fn2-ns-profile* (put-assoc-equal :trace nil *fn2-conn-wire-profile*))
(value-triple (cw "@@FN2SS books - 0 0@@~%"))
