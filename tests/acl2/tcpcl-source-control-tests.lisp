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

(assert-event (equal (fn-tclsctl-source-action t :source nil nil nil) :source))
(assert-event (equal (fn-tclsctl-source-action t :source t nil nil) :read))
(assert-event (equal (fn-tclsctl-source-action t :source t t 4) :buffer))
(assert-event (equal (fn-tclsctl-source-action t :source t t 1) :source))
(assert-event (equal (fn-tclsctl-source-action t :source t t 7) :source))
(assert-event (equal (fn-tclsctl-source-action t :done t t 4) :source))
(assert-event (equal (fn-tclsctl-source-action t :write t t 4) :write))
(assert-event (equal (fn-tclsctl-source-action nil :done t t 4) :done))
(assert-event
 (let* ((s *tcsr-up*) (r (fn-tcl-step s (fn-tcl-make-keepalive) 100)))
  (and (fn-tcl-session-cheapp s) (fn-clock-timep 100)
       (equal (fn-tcl-session-phase s) :established)
       (equal (fn-tcl-session-inbound (fn-tcl-result-session r)) (fn-tcl-session-inbound s))
       (not (equal (fn-tcl-session-phase s) :closed))
       (equal (fn-tcl-session-last-rx (fn-tcl-result-session r)) 100))))
(assert-event
 (let* ((s (fn-tcl-next *tcsr-up* :closed nil nil nil 0))
        (r (fn-tcl-step s (fn-tcl-make-keepalive) 100)))
  (and (equal (fn-tcl-session-phase s) :closed)
       (not (equal (fn-tcl-session-last-rx (fn-tcl-result-session r)) 100)))))
