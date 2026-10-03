; Independent KEEPALIVE while local received-source work owns input/END ACK.
; This does not observe peer reception or forgive an idle timeout. The normal
; input/tick driver resumes after the local operation; its observations remain
; authoritative. Exactly one independent control message may be queued.
(in-package "ACL2")
(include-book "tcpcl-session")
(defun fn-tclsctl-turn (s now blocked)
 (declare (xargs :guard t))
 (let* ((n (fn-tcl-session-negotiated s))
        (interval (* 1000 (nfix (fn-tcl-negotiated-keepalive n)))))
  (if (and (fn-clock-timep now) (not blocked) n (fn-tcl-transferringp (fn-tcl-session-phase s))
           (< 0 interval) (<= interval (- (nfix now) (nfix (fn-tcl-session-last-tx s)))))
   (list (fn-tcl-next s (fn-tcl-session-phase s) (fn-tcl-session-inbound s)
                     (fn-tcl-session-outbound s) (fn-tcl-session-term s) (nfix now))
         (list (fn-tcl-make-keepalive)))
   (list s nil))))
(defthm fn-tclsctl-never-releases-ack
 (or (equal (cadr (fn-tclsctl-turn s now blocked)) nil)
     (equal (cadr (fn-tclsctl-turn s now blocked)) (list (fn-tcl-make-keepalive))))
 :hints (("Goal" :in-theory (enable fn-tclsctl-turn))))
(defthm fn-tclsctl-preserves-reception
 (and (equal (fn-tcl-session-inbound (car (fn-tclsctl-turn s now blocked)))
             (fn-tcl-session-inbound s))
      (equal (fn-tcl-session-last-rx (car (fn-tclsctl-turn s now blocked)))
             (fn-tcl-session-last-rx s)))
 :hints (("Goal" :in-theory (enable fn-tclsctl-turn fn-tcl-next fn-tcl-make-session
                                   fn-tcl-session-inbound fn-tcl-session-last-rx))))
(defthm fn-tclsctl-preserves-cheapp
 (implies (fn-tcl-session-cheapp s)
  (fn-tcl-session-cheapp (car (fn-tclsctl-turn s now blocked))))
 :hints (("Goal" :in-theory (enable fn-tclsctl-turn fn-tcl-session-cheapp fn-tcl-next fn-clock-timep))))
