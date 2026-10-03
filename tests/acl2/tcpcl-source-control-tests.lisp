(in-package "ACL2")
(include-book "../../books/tcpcl-source-control")
(include-book "tcpcl-received-source-refinement-tests")
; Complete unconditional no-ACK/reception boundary positive on a reachable
; negotiated session. The unchanged reception clock is not a peer observation.
(assert-event
 (let* ((s *tcsr-up*) (r (fn-tclsctl-turn s 10001 nil)))
  (and (equal (cadr r) (list (fn-tcl-make-keepalive)))
       (or (equal (cadr r) nil) (equal (cadr r) (list (fn-tcl-make-keepalive))))
       (equal (fn-tcl-session-inbound (car r)) (fn-tcl-session-inbound s))
       (equal (fn-tcl-session-last-rx (car r)) (fn-tcl-session-last-rx s))
       (fn-tcl-session-cheapp s) (fn-tcl-session-cheapp (car r))
       (equal (fn-tcl-session-last-tx (car r)) 10001)
       (equal (cadr (fn-tclsctl-turn (car r) 10002 nil)) nil)
       (equal (fn-tclsctl-turn s 10001 t) (list s nil)))))
; Sole cheap-state hypothesis removal, corrupted internal session. No actual
; malformed network frame bypasses the carried session invariant.
(assert-event
 (let* ((s (fn-tcl-make-session :passive :established nil nil nil
             (fn-tcl-make-negotiated 1 1000 1000 nil '(100)) nil nil -1 0 0 nil))
        (r (fn-tclsctl-turn s 1000 nil)))
  (and (not (fn-tcl-session-cheapp s))
       (not (fn-tcl-session-cheapp (car r))))))
(assert-event
 (equal (fn-tclsctl-turn *tcsr-up* (+ 1 *fn-clock-max*) nil) (list *tcsr-up* nil)))
