(in-package "ACL2")
(include-book "../../books/tcpcl-source-control-refinement")
(include-book "../../books/defkeystone")
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

; TEETH-21 BEGIN
(defconst *tcsc-closed* (fn-tcl-next *tcsr-up* :closed nil nil nil 0))
(defteeth fn-tclsctl-source-drive-keepalive-preserves-custody-and-reception
  :claim (((transferring (fn-tcl-transferringp (fn-tcl-session-phase s))))
          (let ((r (fn-tcl-host-source-drive s (cons 4 rest) now)))
            (and (equal (fn-tcl-session-inbound (car r)) (fn-tcl-session-inbound s))
                 (equal (fn-tcl-session-last-rx (car r)) now)
                 (equal (caddr r) rest)
                 (equal (cadddr r) :stepped))))
  :subject fn-tcl-host-source-drive
  :witness ((s *tcsc-live*) (rest '(1 0)) (now 100))
  :breaks ((transferring ((s *tcsc-closed*))))
  :mutations ((reception-not-stamped
               (:conclusion (let ((r (fn-tcl-host-source-drive s (cons 4 rest) now)))
                              (equal (fn-tcl-session-last-rx (car r)) (+ 1 now))))
               ((s *tcsc-live*) (rest '(1 0)) (now 100))
               :fault "a keepalive that stamps last-rx a tick after the clock")))
(defteeth fn-tclsctl-source-drive-keepalive-refines-session
  :claim (((transferring (fn-tcl-transferringp (fn-tcl-session-phase s))))
          (equal (fn-tcl-host-source-drive s (cons 4 rest) now)
                 (let ((r (fn-tcl-step s (fn-tcl-make-keepalive) now)))
                   (list (fn-tcl-result-session r) (fn-tcl-result-events r) rest :stepped))))
  :subject fn-tcl-host-source-drive
  :witness ((s *tcsc-live*) (rest '(1 0)) (now 100))
  :breaks ((transferring ((s *tcsc-closed*))))
  :mutations ((events-dropped
               (:conclusion (let ((r (fn-tcl-step s (fn-tcl-make-keepalive) now)))
                              (equal (fn-tcl-host-source-drive s (cons 4 rest) now)
                                     (list (fn-tcl-result-session r) :dropped rest :stepped))))
               ((s *tcsc-live*) (rest '(1 0)) (now 100))
               :fault "the drive reporting no events for the keepalive's step")))
; TEETH-21 END
