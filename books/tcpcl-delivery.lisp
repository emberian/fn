; Late BPA disposition of a completely received TCPCL transfer.  The native
; host holds fn-tcl-complete's END XFER_ACK until its durability callback
; returns, then executes this ACL2-selected outbound message list.
(in-package "ACL2")
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
(defun fn-tcl-held-prior-messages-loop (messages acc)
  (declare (xargs :guard (true-listp acc) :verify-guards nil))
  (if (and (consp messages) (consp (cdr messages)))
      (fn-tcl-held-prior-messages-loop (cdr messages) (cons (car messages) acc))
    (revappend acc nil)))

(defun fn-tcl-held-prior-messages (messages)
  (declare (xargs :verify-guards nil :guard t))
  (mbe :logic
       (if (and (consp messages) (consp (cdr messages)))
           (cons (car messages) (fn-tcl-held-prior-messages (cdr messages)))
         nil)
       :exec (fn-tcl-held-prior-messages-loop messages nil)))

(local
 (defthm fn-tcl-held-prior-messages-loop-is-revappend
   (equal (fn-tcl-held-prior-messages-loop messages acc)
          (revappend acc (fn-tcl-held-prior-messages messages)))
   :hints (("Goal" :induct (fn-tcl-held-prior-messages-loop messages acc)
                   :in-theory (union-theories '(fn-tcl-held-prior-messages-loop fn-tcl-held-prior-messages revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-tcl-held-prior-messages-loop)

(verify-guards fn-tcl-held-prior-messages
  :hints (("Goal"
           :in-theory
           (union-theories '(revappend fn-tcl-held-prior-messages)
                           (union-theories (theory 'minimal-theory)
                                           (executable-counterpart-theory :here)))
           :use
           ((:instance fn-tcl-held-prior-messages-loop-is-revappend (acc nil))))))


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
