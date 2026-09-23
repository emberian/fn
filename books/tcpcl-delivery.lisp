; Late BPA disposition of a completely received TCPCL transfer.  The native
; host holds fn-tcl-complete's END XFER_ACK until its durability callback
; returns, then executes this ACL2-selected outbound message list.
(in-package "ACL2")
(include-book "tcpcl-session")

(defun fn-tcl-held-final-ackp (messages xfer-id)
  (declare (xargs :guard t))
  (and (consp messages)
       (fn-tcl-xfer-ack-shapep (car messages))
       (fn-cbor-octetp (fn-tcl-xfer-ack-flags (car messages)))
       (equal (fn-tcl-xfer-ack-xfer-id (car messages)) xfer-id)
       (if (consp (cdr messages))
           (and (not (fn-tcl-flag-end
                      (fn-tcl-xfer-ack-flags (car messages))))
                (fn-tcl-held-final-ackp (cdr messages) xfer-id))
         (and (null (cdr messages))
              (fn-tcl-flag-end
               (fn-tcl-xfer-ack-flags (car messages)))))))

(defun fn-tcl-held-partial-acks (messages)
  (declare (xargs :guard t))
  (if (and (consp messages) (consp (cdr messages)))
      (cons (car messages) (fn-tcl-held-partial-acks (cdr messages)))
    nil))

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
                   (append (fn-tcl-held-partial-acks messages)
                           (list (fn-tcl-make-xfer-refuse
                                  (fn-tcl-delivery-refuse-reason (cadr result))
                                  xfer-id)))
                   (cadr result)))
            ((equal (car result) :uncertain)
             (list :delivery :uncertain nil (cadr result)))
            (t (list :delivery :fault nil :bad-callback-result))))))

(defun fn-tcl-delivery-plan-status (plan)
  (declare (xargs :guard t)) (nth 1 plan))
(defun fn-tcl-delivery-plan-messages (plan)
  (declare (xargs :guard t)) (nth 2 plan))
(defun fn-tcl-delivery-plan-detail (plan)
  (declare (xargs :guard t)) (nth 3 plan))
