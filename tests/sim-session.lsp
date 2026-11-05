; Layer D's simulator session (sim/session.lisp) for the surface harness's
; long-lived ACL2 process (tests/surface/fn2_sim_session.py): the book, the
; output settings that keep each answer one marker line, then "ready".
(in-package "ACL2")
(include-book "../sim/session")
(set-inhibit-output-lst '(proof-tree prove event summary observation warning))
(set-fmt-hard-right-margin 1000000 state)
(set-fmt-soft-right-margin 1000000 state)
(value-triple (cw "@@FN2SS ready - 0 0@@~%"))
