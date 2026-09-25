; fn: the owner reopens its service log on SIGHUP (PKT-101).
;
; Log rotation by copy and truncate can lose a line written between the copy
; and the truncate (spike-operator record, deferral 10).  Rotation by rename
; loses none if the owner then reopens `[log] path': a line goes to the
; renamed file or to the new one.  The signal is I/O: the host's handler only
; counts SIGHUPs (a monotonic natural, no allocation, no lock, no core call).
; Whether a reopen is due, and the line that records it, are decided here;
; host/native/owner.lisp `fnn-owner-maybe-reopen-log' asks
; host/owner-host.lisp `fn-owner-log-reopen' once per accept poll (at most a
; second apart) and carries out exactly what it answers.

(in-package "ACL2")
(include-book "owner-log")

; HANDLED is the count the owner last acted on, REQUESTED the handler's
; count now, CONFIGURED whether the run opened a `[log] path' (with none the
; service log is stderr and there is nothing to reopen).
;   (:reopen N)   reopen, then write `fn-olr-line', and N is handled
;   (:ignore N)   a request with no log file: N is handled, nothing opened
;   (:none H)     no request since H
(defun fn-olr-decide (configured handled requested)
  (declare (xargs :guard t))
  (cond ((not (and (natp handled) (natp requested) (< handled requested)))
         (list :none (nfix handled)))
        (configured (list :reopen requested))
        (t (list :ignore requested))))

(defun fn-olr-line (requested obs)
  "The first line written to the reopened file."
  (declare (xargs :guard t))
  (fn-olog-join (list (fn-olog-text "reopened")
                      (fn-olog-text "log")
                      (fn-olog-field "signal" (fn-olog-text "hup"))
                      (append (fn-olog-text "requests=") (fn-olog-decimal requested))
                      (append (fn-olog-text "time=") (fn-olog-time obs)))))

; KEYSTONE.  A reopen happens exactly when a log file is configured and a
; SIGHUP has arrived since the last one acted on; whatever the answer, every
; request counted so far is then handled, so none waits for a later signal
; and none is acted on twice.
(defthm fn-olr-reopen-iff-requested
  (implies (and (natp handled) (natp requested))
           (and (iff (equal (car (fn-olr-decide configured handled requested))
                            :reopen)
                     (and configured (< handled requested)))
                (equal (cadr (fn-olr-decide configured handled requested))
                       (max handled requested)))))
