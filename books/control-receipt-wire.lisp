; Receipt observations reuse FNCT's administrative argv and reasoned line
; grammar. No new frame family, status enumeration, or Lisp reader.
(in-package "ACL2")
(include-book "control-observation")
(include-book "native-control-reason")
(include-book "outcome-class")

(defun fn-nco-receipt-command (argv)
  (declare (xargs :guard t))
  (and (equal (len argv) 4)
       (equal (fn-nco-at 0 argv) '(99 111 110 116 114 111 108))
       (equal (fn-nco-at 1 argv) '(114 101 99 101 105 112 116))
       (cond ((equal (fn-nco-at 2 argv) '(115 116 97 116 117 115)) :status)
             ((equal (fn-nco-at 2 argv) '(114 101 108 101 97 115 101)) :release))))

(defun fn-nco-status-argv (token releasep)
  (declare (xargs :guard t))
  (list '(99 111 110 116 114 111 108) '(114 101 99 101 105 112 116)
        (if releasep '(114 101 108 101 97 115 101) '(115 116 97 116 117 115))
        token))

; Status does not consume the result. Release is an explicit, separate
; request sent only after the client received a terminal reply.
(defun fn-nco-wire-step (st argv)
  (declare (xargs :guard t))
  (let* ((op (fn-nco-receipt-command argv))
         (token (fn-nco-at 2 st))
         (text (fn-nco-token-text token)))
    (cond
     (op
      (if (not (and token (equal (fn-nco-at 3 argv) (fn-record-string-octets text))))
          (list st (list :reason :uncertain :receipt-unknown))
        (if (eq op :release)
            (let ((r (fn-nco-owner-step st (list :release token))))
              (list (cadr r) (list :reason
                                  (if (eq (car r) :released) :accepted :refused)
                                  (car r))))
          (list st (if (eq (fn-nco-at 3 st) :requested)
                       (list :reason :accepted :requested text)
                     (list :reason (fn-nco-at 4 st) (fn-nco-at 5 st)))))))
     (t
      (let* ((r (fn-nco-owner-step st (list :request argv)))
             (next (cadr r)))
        (list next
              (if (eq (car r) :requested)
                  (list :reason :accepted :requested
                        (fn-nco-token-text (fn-nco-at 2 next)))
                (list :reason :refused :receipt-in-flight text))
              (and (eq (car r) :requested) :run)))))))

(defun fn-nco-client-follow (argv status word line)
  (declare (xargs :guard t))
  (and (eq (fn-nco-work-class 17 argv) :store-sized)
       (eq status :accepted)
       (equal word (fn-nctrl-reason-word :requested))
       (consp line)
       (fn-nco-status-argv line nil)))

; Unknown receipt is an observation failure, not the job's terminal result.
; This decision is shared by automatic polling and manual status queries.
(defun fn-nco-client-status (status word)
  (declare (xargs :guard t))
  (if (equal word (fn-nctrl-reason-word :receipt-unknown)) :uncertain status))

; S3b also covers death before a new owner is listening: after ACK,
; no-owner is loss of observation, never proof that the job was refused.
(defun fn-nco-client-observed-status (status word)
  (declare (xargs :guard t))
  (if (equal word (fn-nctrl-reason-word :no-owner))
      :uncertain
    (fn-nco-client-status status word)))

(defun fn-nco-client-waitp (status word)
  (declare (xargs :guard t))
  (or (eq status :busy)
      (and (eq status :accepted)
           (equal word (fn-nctrl-reason-word :requested)))))


; The actual status entry exposes the one retained terminal outcome and
; preserves it, so repeated status observations cannot consume or replace it.
(defthm fn-nco-status-observes-the-completion
  (implies (and (fn-nco-at 2 st) (equal (fn-nco-at 3 st) :completed))
           (equal (fn-nco-wire-step
                   st (fn-nco-status-argv
                       (fn-record-string-octets (fn-nco-token-text (fn-nco-at 2 st))) nil))
                  (list st (list :reason (fn-nco-at 4 st) (fn-nco-at 5 st)))))
  :hints (("Goal" :in-theory (disable fn-nco-token-text fn-record-string-octets)))
  :rule-classes nil)


(defun fn-nco-client-releasep (status)
  (declare (xargs :guard t))
  (and (member-eq status '(:accepted :refused :fault)) t))

(defun fn-nco-client-heldp (status word line)
  (declare (xargs :guard t))
  (and (eq status :refused) (consp line)
       (equal word (fn-nctrl-reason-word :receipt-in-flight))))

; S3b: the actual status entry answers a distinct observation word for a
; receipt it does not hold. It cannot promise work or fabricate completion.
(defthm fn-nco-unknown-receipt-status
  (implies (not (and (fn-nco-at 2 st)
                    (equal text (fn-record-string-octets
                                 (fn-nco-token-text (fn-nco-at 2 st))))))
           (let ((r (fn-nco-wire-step st (fn-nco-status-argv text nil))))
             (and (equal r (list st (list :reason :uncertain :receipt-unknown)))
                  (not (equal (fn-nco-at 2 (fn-nco-at 1 r)) :requested))
                  (not (fn-nco-terminalp (fn-nco-at 2 (fn-nco-at 1 r)))))))
  :hints (("Goal" :in-theory (disable fn-nco-token-text fn-record-string-octets)))
  :rule-classes nil)

(defthm fn-nco-unknown-receipt-stops-with-exit-3
  (implies (equal word (fn-nctrl-reason-word :receipt-unknown))
           (and (equal (fn-nco-client-status status word) :uncertain)
                (not (fn-nco-client-waitp (fn-nco-client-status status word) word))
                (equal (fn-outcome-code
                        (fn-outcome-of-status (fn-nco-client-status status word))) 3)))
  :rule-classes nil)

(defthm fn-nco-lost-owner-after-receipt-is-uncertain
  (implies (equal word (fn-nctrl-reason-word :no-owner))
           (and (equal (fn-nco-client-observed-status status word) :uncertain)
                (not (fn-nco-client-waitp (fn-nco-client-observed-status status word) word))
                (not (fn-nco-client-releasep (fn-nco-client-observed-status status word)))
                (equal (fn-outcome-code
                        (fn-outcome-of-status (fn-nco-client-observed-status status word))) 3)))
  :rule-classes nil)
