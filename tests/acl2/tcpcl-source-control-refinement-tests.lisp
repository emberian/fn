(in-package "ACL2")
(include-book "../../books/tcpcl-source-control-refinement")
(include-book "tcpcl-received-source-refinement-tests")
; Reach an actual partial inbound transfer through negotiated session/start.
(defconst *tcsc-live*
 (fn-tcl-result-session
  (fn-tcl-step-source *tcsr-up* (fn-tcl-make-xfer-segment 2 7 nil '(65)) 2)))
; Complete antecedent/conclusion of both parser composition keystones. The
; next transfer's prefix remains unconsumed; no parser loop runs it here.
(assert-event
 (let* ((s *tcsc-live*) (rest '(1 0)) (now 100)
        (r (fn-tcl-host-source-drive s (cons 4 rest) now))
        (model (fn-tcl-step s (fn-tcl-make-keepalive) now)))
  (and (fn-tcl-session-cheapp s) (fn-clock-timep now)
       (fn-cbor-octet-listp (cons 4 rest))
       (fn-tcl-transferringp (fn-tcl-session-phase s))
       (consp (fn-tcl-session-inbound s))
       (equal r (list (fn-tcl-result-session model)
                      (fn-tcl-result-events model) rest :stepped))
       (equal (fn-tcl-session-inbound (car r)) (fn-tcl-session-inbound s))
       (equal (fn-tcl-session-last-rx (car r)) now)
       (equal (caddr r) rest) (equal (cadddr r) :stepped)
       (equal (cadr r) nil))))
; Sole transferring-phase hypothesis removal. Closed is a legitimate terminal
; state, not corrupted network input; both full conclusions fail affirmatively.
(assert-event
 (let* ((s (fn-tcl-next *tcsr-up* :closed nil nil nil 0))
        (rest '(1 0)) (now 100)
        (r (fn-tcl-host-source-drive s (cons 4 rest) now))
        (model (fn-tcl-step s (fn-tcl-make-keepalive) now)))
  (and (fn-tcl-session-cheapp s) (fn-clock-timep now)
       (fn-cbor-octet-listp (cons 4 rest))
       (not (fn-tcl-transferringp (fn-tcl-session-phase s)))
       (not (equal r (list (fn-tcl-result-session model)
                           (fn-tcl-result-events model) rest :stepped)))
       (not (and (equal (fn-tcl-session-inbound (car r)) (fn-tcl-session-inbound s))
                 (equal (fn-tcl-session-last-rx (car r)) now)
                 (equal (caddr r) rest) (equal (cadddr r) :stepped))))))
