; One-shot client of a protected remote NNTP node. The owner activates a
; :taken row after recovery and transfers its booked account to this actor.
(in-package "ACL2")
(include-book "peer-pull-reply")
(include-book "xfnc-ops")
(include-book "peer-pull-import")
(include-book "peer-pull-plan")

(defcost fn2-pull-connect :child fn2-issue-connect :descriptors 1 :answers t
 :tables (fn2-core-ops) :effects ((:acquire (:operation)))
 :doc "Connect to the operator-authorized concrete remote IP and port.")
(defcost fn2-pull-read-line :child fn2-peer-pull-line :bytes 2048
 :doc "Classify one externally framed NNTP status line in the held RX workspace.")
(defcost fn2-pull-reply-count :child fn2-peer-pull-reply-count :bytes 2048
 :doc "Classify the protected counted status and determine the exact allowed FNCT reply span.")
(defcost fn2-pull-command :child fn2-peer-pull-format-command :answers t :bytes 1024
 :tables (fn2-core-pool) :doc "Write STARTTLS or one protected authentication command into exclusive TX.")
(defcost fn2-pull-wipe :child fn2-peer-pull-wipe :answers t :bytes 1280
 :tables (fn2-core-pool) :doc "Overwrite the caller's secret-bearing bytes, then truncate its exclusive range.")
(make-event
 (value (cons 'progn
  (append (fn2-arms-op-face-events 'fn2-pull-connect 'fn2-issue-connect (w state))
          (fn2-arms-op-face-events 'fn2-pull-read-line 'fn2-peer-pull-line (w state))
          (fn2-arms-op-face-events 'fn2-pull-reply-count 'fn2-peer-pull-reply-count (w state))
          (fn2-arms-op-face-events 'fn2-pull-command 'fn2-peer-pull-format-command (w state))
          (fn2-arms-op-face-events 'fn2-pull-wipe 'fn2-peer-pull-wipe (w state))))))

(defun fn2-pull-release-private (slot gen okind oslot ogen fn2-core)
 (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
 (fn2-core-release slot gen okind oslot ogen fn2-core))
(fn2-core-preserves fn2-pull-release-private (slot gen okind oslot ogen fn2-core) :position 1 :rows nil)
(in-theory (disable fn2-pull-release-private))
(defcost fn2-pull-release-private :answers t :tables (fn2-core-pool)
 :doc "Return the auxiliary range in the actor's TX bundle after clearing its private bytes.")
