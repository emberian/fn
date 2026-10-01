; Late BPA disposition of a completely received TCPCL transfer.  The native
; host holds fn-tcl-complete's END XFER_ACK until its durability callback
; returns, then executes this ACL2-selected outbound message list.
(in-package "ACL2")
(include-book "def-loop")
(include-book "tcpcl-session")

(defun fn-tcl-held-prior-messagep (message)
  (declare (xargs :guard t))
  (if (equal (fn-tcl-msg-kind message) :xfer-ack)
      (and (fn-tcl-xfer-ack-shapep message)
           (fn-cbor-octetp (fn-tcl-xfer-ack-flags message))
           (not (fn-tcl-flag-end (fn-tcl-xfer-ack-flags message))))
    t))

(defun fn-tcl-held-final-ackp (messages xfer-id)
  (declare (xargs :guard t))
  (and (consp messages)
       (if (consp (cdr messages))
           (and (fn-tcl-held-prior-messagep (car messages))
                (fn-tcl-held-final-ackp (cdr messages) xfer-id))
         (and (null (cdr messages))
              (fn-tcl-xfer-ack-shapep (car messages))
              (fn-cbor-octetp (fn-tcl-xfer-ack-flags (car messages)))
              (fn-tcl-flag-end
               (fn-tcl-xfer-ack-flags (car messages)))
              (equal (fn-tcl-xfer-ack-xfer-id (car messages)) xfer-id)))))

; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(def-loop fn-tcl-held-prior-messages (messages)
  :over messages :while (consp (cdr messages))
  :body (car messages))

(defun fn-tcl-output-has-final-ackp (messages xfer-id)
  (declare (xargs :guard t))
  (if (atom messages) nil
    (or (and (fn-tcl-xfer-ack-shapep (car messages))
             (fn-cbor-octetp (fn-tcl-xfer-ack-flags (car messages)))
             (fn-tcl-flag-end (fn-tcl-xfer-ack-flags (car messages)))
             (equal (fn-tcl-xfer-ack-xfer-id (car messages)) xfer-id))
        (fn-tcl-output-has-final-ackp (cdr messages) xfer-id))))

(defun fn-tcl-delivery-refuse-reason (reason)
  (declare (xargs :guard t))
  (if (member-equal reason '(:busy :capacity :persistence))
      *fn-tcl-refuse-no-resources*
    *fn-tcl-refuse-not-acceptable*))

(defun fn-tcl-delivery-plan (messages xfer-id result)
  (declare (xargs :guard t))
  (if (not (fn-tcl-held-final-ackp messages xfer-id))
      (list :delivery :fault nil :missing-final-ack)
    (if (not (and (true-listp result) (equal (len result) 2)))
        (list :delivery :fault nil :bad-callback-result)
      (cond ((and (equal (car result) :accepted)
                  (or (null (cadr result)) (stringp (cadr result))))
             (list :delivery :accepted messages (cadr result)))
            ((equal (car result) :refused)
             (list :delivery :refused
                   (append (fn-tcl-held-prior-messages messages)
                           (list (fn-tcl-make-xfer-refuse
                                  (fn-tcl-delivery-refuse-reason (cadr result))
                                  xfer-id)))
                   (cadr result)))
            ((equal (car result) :uncertain)
             (list :delivery :uncertain nil (cadr result)))
            (t (list :delivery :fault nil :bad-callback-result))))))

(defun fn-tcl-delivery-plan-status (plan)
  (declare (xargs :guard t))
  (if (true-listp plan) (nth 1 plan) nil))
(defun fn-tcl-delivery-plan-messages (plan)
  (declare (xargs :guard t))
  (if (true-listp plan) (nth 2 plan) nil))
(defun fn-tcl-delivery-plan-detail (plan)
  (declare (xargs :guard t))
  (if (true-listp plan) (nth 3 plan) nil))

; PKT-873 (lane durability-bugs, 2026-09-28): the session's progress point.
; A receiving node that acknowledged a transfer (its custody is durable)
; hands that custody to progress -- the local delivery, the receipt it
; queues -- while the session is still open, not only when it ends: a peer
; that keeps its session open with keepalives (dtn7-rs pools its sessions)
; would otherwise hold an acknowledged custody undelivered for as long as the
; node runs.  The host (host/native/tcpcl.lisp fnn-tcl-session) marks the
; custody when this answers T and runs the progress hook at the session's
; first quiet read timeout after it; a session the peer ends first is
; delivered by the node's between-sessions pass, as before.
(defun fn-tcl-delivery-plan-progress-p (plan)
  (declare (xargs :guard t))
  (equal (fn-tcl-delivery-plan-status plan) :accepted))

; KEYSTONE (PRF-1036).  The delivery plan (host/native/tcpcl.lisp acts on its status and
; writes its messages), two-sided per status: a plan is :accepted exactly
; when the final ACK of the transfer is held and the durability callback
; answered (:accepted nil-or-string), :refused exactly when it is held and
; the callback answered (:refused detail), :uncertain exactly when it is held
; and the callback answered (:uncertain detail); an accepted plan carries the
; held messages, a refused plan the prior messages followed by one XFER_REFUSE
; naming the transfer with the detail's reason code, an uncertain or faulted
; plan no message at all (nothing is sent on uncertainty); a fault names the
; missing final ACK or the malformed callback.  The status is one of the four.
(defthm fn-tcl-delivery-plan-decides-exactly-by-the-held-final-ack-and-the-callback
  (let* ((plan (fn-tcl-delivery-plan messages xfer-id result))
         (status (fn-tcl-delivery-plan-status plan))
         (held (fn-tcl-held-final-ackp messages xfer-id))
         (wf (and (true-listp result) (equal (len result) 2))))
    (and (member-equal status '(:accepted :refused :uncertain :fault))
         (iff (equal status :accepted)
              (and held wf (equal (car result) :accepted)
                   (or (null (cadr result)) (stringp (cadr result)))))
         (iff (equal status :refused)
              (and held wf (equal (car result) :refused)))
         (iff (equal status :uncertain)
              (and held wf (equal (car result) :uncertain)))
         (implies (equal status :accepted)
                  (and (equal (fn-tcl-delivery-plan-messages plan) messages)
                       (equal (fn-tcl-delivery-plan-detail plan) (cadr result))))
         (implies (equal status :refused)
                  (and (equal (fn-tcl-delivery-plan-messages plan)
                              (append (fn-tcl-held-prior-messages messages)
                                      (list (fn-tcl-make-xfer-refuse
                                             (fn-tcl-delivery-refuse-reason
                                              (cadr result))
                                             xfer-id))))
                       (equal (fn-tcl-delivery-plan-detail plan) (cadr result))))
         (implies (member-equal status '(:uncertain :fault))
                  (null (fn-tcl-delivery-plan-messages plan)))
         (implies (equal status :fault)
                  (member-equal (fn-tcl-delivery-plan-detail plan)
                                '(:missing-final-ack :bad-callback-result)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-tcl-delivery-plan
                                   fn-tcl-delivery-plan-status
                                   fn-tcl-delivery-plan-messages
                                   fn-tcl-delivery-plan-detail)
                                  (fn-tcl-held-final-ackp
                                   fn-tcl-held-prior-messages
                                   fn-tcl-make-xfer-refuse
                                   fn-tcl-delivery-refuse-reason)))))
