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

; Only fixed-size control headers may bypass local received-source custody.
; XFER_SEGMENT/SESS_INIT stay in the one retained socket vector until the old
; source retires. TCP stream order supplies backpressure without another job.
(defun fn-tclsctl-control-header-p (octet)
 (declare (xargs :guard t)) (and (member-equal octet '(2 3 4 5 6)) t))
(defun fn-tclsctl-source-action (pending base input-turn buffered octet)
 (declare (xargs :guard t))
 (cond ((not pending) base)
       ((equal base :done) :source)
       ((not (equal base :source)) base)
       ((not input-turn) :source)
       (buffered (if (fn-tclsctl-control-header-p octet) :buffer :source))
       (t :read)))

; Incoming KEEPALIVE uses the original session transition. Unlike an outgoing
; timer tick, it is a peer reception observation. Preserve the live inbound
; record even if ending settles; custody-held host roots/ACK are independent.
(defthm fn-tclsctl-received-keepalive-preserves-inbound
 (equal (fn-tcl-session-inbound
          (fn-tcl-result-session (fn-tcl-step s (fn-tcl-make-keepalive) now)))
        (fn-tcl-session-inbound s))
 :hints (("Goal" :in-theory
          (enable fn-tcl-step fn-tcl-settle fn-tcl-touch-rx fn-tcl-next
                  fn-tcl-make-keepalive fn-tcl-msg-kind fn-tcl-make-result
                  fn-tcl-result-session fn-tcl-session-phase
                  fn-tcl-session-inbound fn-tcl-make-session))))
(defthm fn-tclsctl-received-keepalive-records-actual-reception
 (implies (not (equal (fn-tcl-session-phase s) :closed))
  (equal (fn-tcl-session-last-rx
           (fn-tcl-result-session (fn-tcl-step s (fn-tcl-make-keepalive) now))) now))
 :hints (("Goal" :in-theory
          (enable fn-tcl-step fn-tcl-settle fn-tcl-touch-rx fn-tcl-next
                  fn-tcl-make-keepalive fn-tcl-msg-kind fn-tcl-make-result
                  fn-tcl-result-session fn-tcl-session-phase
                  fn-tcl-session-inbound fn-tcl-session-last-rx fn-tcl-make-session))))
