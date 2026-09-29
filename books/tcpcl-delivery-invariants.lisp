; The host-called late-disposition planner cannot turn a definitive refusal
; or an ambiguous publication into a successful final END acknowledgement.
(in-package "ACL2")
(include-book "tcpcl-delivery")
(include-book "tcpcl-host-drive")

; Every final ACK in a machine event stream must be immediately followed by
; the delivery event for the same transfer.  This describes the event order
; seen by fnn-tcl-act, including coalesced decoded frames.
(defun fn-tcl-delivery-eventsp (events)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom events)
      t
    (let ((event (car events)))
      (cond ((and (consp event) (equal (car event) :send))
             (let ((message (cadr event)))
               (if (fn-tcl-held-prior-messagep message)
                   (fn-tcl-delivery-eventsp (cdr events))
                 (and (fn-tcl-xfer-ack-shapep message)
                      (fn-cbor-octetp (fn-tcl-xfer-ack-flags message))
                      (fn-tcl-flag-end (fn-tcl-xfer-ack-flags message))
                      (consp (cdr events))
                      (equal (car (cadr events)) :bundle-received)
                      (equal (cadr (cadr events))
                             (fn-tcl-xfer-ack-xfer-id message))
                      (fn-tcl-delivery-eventsp (cddr events))))))
            ((and (consp event) (equal (car event) :bundle-received)) nil)
            (t (fn-tcl-delivery-eventsp (cdr events)))))))

(defthm fn-tcl-delivery-eventsp-of-append
  (implies (and (fn-tcl-delivery-eventsp left)
                (fn-tcl-delivery-eventsp right))
           (fn-tcl-delivery-eventsp (append left right)))
  :hints (("Goal" :induct (fn-tcl-delivery-eventsp left)
                   :in-theory (enable fn-tcl-delivery-eventsp))))

(defthm fn-tcl-complete-delivery-events
  (implies (and (fn-cbor-octetp flags) (fn-tcl-flag-end flags))
           (fn-tcl-delivery-eventsp
            (fn-tcl-result-events (fn-tcl-complete s xfer-id flags len data now))))
  :hints (("Goal" :in-theory (enable fn-tcl-complete
                                     fn-tcl-send-event
                                     fn-tcl-delivery-eventsp))))

(defthm fn-tcl-recv-segment-delivery-events
  (implies (and (fn-tcl-session-cheapp s)
                (fn-tcl-messagep m (fn-tcl-segment-mru s))
                (equal (fn-tcl-msg-kind m) :xfer-segment)
                (fn-clock-timep now))
           (fn-tcl-delivery-eventsp
            (fn-tcl-result-events (fn-tcl-recv-segment s m now))))
  :hints (("Goal" :do-not-induct t
                   :in-theory
                   (e/d (fn-tcl-recv-segment fn-tcl-stage fn-tcl-refuse
                          fn-tcl-complete fn-tcl-broken-stream
                          fn-tcl-send-event fn-tcl-delivery-eventsp
                          fn-tcl-xfer-ack-shapep fn-tcl-msg-kind
                          fn-tcl-make-xfer-refuse fn-tcl-messagep)
                        (fn-tcl-session-cheapp fn-tcl-ext-decision)))))

(defthm fn-tcl-step-delivery-events
  (implies (and (fn-tcl-session-cheapp s)
                (fn-tcl-messagep m (fn-tcl-segment-mru s))
                (fn-clock-timep now))
           (fn-tcl-delivery-eventsp
            (fn-tcl-result-events (fn-tcl-step s m now))))
  :hints (("Goal" :do-not-induct t
                   :use ((:instance fn-tcl-recv-segment-delivery-events
                                    (s (fn-tcl-touch-rx s now)))
                         (:instance fn-tcl-touch-rx-fields))
                   :in-theory
                   (e/d (fn-tcl-step fn-tcl-settle fn-tcl-recv-contact
                          fn-tcl-recv-init fn-tcl-recv-ack fn-tcl-recv-refuse
                          fn-tcl-recv-term fn-tcl-unexpected
                          fn-tcl-broken-stream fn-tcl-send-event
                          fn-tcl-delivery-eventsp fn-tcl-msg-kind
                          fn-tcl-own-contact fn-tcl-own-init)
                        (fn-tcl-session-cheapp fn-tcl-messagep fn-tcl-recv-segment
                         fn-tcl-ext-decision)))))

(defthm fn-tcl-input-error-delivery-events
  (fn-tcl-delivery-eventsp
   (fn-tcl-result-events (fn-tcl-input-error s header reason now)))
  :hints (("Goal" :in-theory (enable fn-tcl-input-error fn-tcl-fail-live
                                     fn-tcl-delivery-eventsp
                                     fn-tcl-send-event fn-tcl-msg-kind))))

; This is the recursive driver used by fn-tcl-host-drive on each socket read.
; The result covers arbitrary coalescing of decoded frames in that read.
(defthm fn-tcl-drive-delivery-events
  (fn-tcl-delivery-eventsp
   (fn-tcl-result-events (fn-tcl-drive s buf now)))
  :hints (("Goal" :induct (fn-tcl-drive s buf now)
                   :in-theory
                   (e/d (fn-tcl-drive)
                        (fn-tcl-sessionp fn-tcl-session-cheapp
                         fn-tcl-messagep fn-tcl-step fn-tcl-decode-for
                         fn-tcl-input-error fn-tcl-segment-mru)))))

; These two projections mirror fnn-tcl-act's ordered :send collection up to
; the first :bundle-received, and its reset after handling that bundle.
(defun fn-tcl-first-bundle-event (events)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom events) nil
    (if (and (consp (car events)) (equal (caar events) :bundle-received))
        (car events)
      (fn-tcl-first-bundle-event (cdr events)))))

(defun fn-tcl-held-before-first-bundle (events)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom events) nil
    (if (and (consp (car events)) (equal (caar events) :bundle-received))
        nil
      (if (and (consp (car events)) (equal (caar events) :send))
          (cons (cadar events) (fn-tcl-held-before-first-bundle (cdr events)))
        (fn-tcl-held-before-first-bundle (cdr events))))))

(defun fn-tcl-events-after-first-bundle (events)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom events) nil
    (if (and (consp (car events)) (equal (caar events) :bundle-received))
        (cdr events)
      (fn-tcl-events-after-first-bundle (cdr events)))))

(defthm fn-tcl-delivery-events-imply-held-final
  (implies (and (fn-tcl-delivery-eventsp events)
                (fn-tcl-first-bundle-event events))
           (fn-tcl-held-final-ackp
            (fn-tcl-held-before-first-bundle events)
            (cadr (fn-tcl-first-bundle-event events))))
  :hints (("Goal" :induct (fn-tcl-delivery-eventsp events)
                   :in-theory (enable fn-tcl-delivery-eventsp
                                      fn-tcl-first-bundle-event
                                      fn-tcl-held-before-first-bundle
                                      fn-tcl-held-final-ackp))))

(defthm fn-tcl-delivery-eventsp-after-first-bundle
  (implies (fn-tcl-delivery-eventsp events)
           (fn-tcl-delivery-eventsp
            (fn-tcl-events-after-first-bundle events)))
  :hints (("Goal" :induct (fn-tcl-delivery-eventsp events)
                   :in-theory (enable fn-tcl-delivery-eventsp
                                      fn-tcl-events-after-first-bundle))))

; Exact host-called wrapper.  Its event list is the driver list, and at the
; first delivery boundary the messages accumulated by fnn-tcl-act satisfy
; the planner's gate.  Apply the same theorem to the post-bundle suffix for
; each later completed bundle in a coalesced read.
(defthm fn-tcl-host-drive-bundle-has-held-final
  (implies (fn-tcl-first-bundle-event (cadr (fn-tcl-host-drive s buf now)))
           (fn-tcl-held-final-ackp
            (fn-tcl-held-before-first-bundle
             (cadr (fn-tcl-host-drive s buf now)))
            (cadr (fn-tcl-first-bundle-event
                   (cadr (fn-tcl-host-drive s buf now))))))
  :hints (("Goal" :in-theory (enable fn-tcl-host-drive
                                     fn-tcl-host-triple))))

(defthm fn-tcl-complete-produces-held-final-ack
  (implies (and (fn-cbor-octetp flags)
                (fn-tcl-flag-end flags))
           (let ((events (fn-tcl-result-events
                          (fn-tcl-complete s xfer-id flags len data now))))
             (and (fn-tcl-held-final-ackp (list (cadr (car events))) xfer-id)
                  (equal (cadr events) (list :bundle-received xfer-id data)))))
  :hints (("Goal" :in-theory (enable fn-tcl-complete
                                     fn-tcl-send-event
                                     fn-tcl-held-final-ackp))))

(defthm fn-tcl-held-prior-messages-have-no-final
  (implies (fn-tcl-held-final-ackp messages xfer-id)
           (not (fn-tcl-output-has-final-ackp
                 (fn-tcl-held-prior-messages messages) xfer-id)))
  :hints (("Goal" :induct (fn-tcl-held-final-ackp messages xfer-id)
                   :in-theory (enable fn-tcl-held-final-ackp
                                      fn-tcl-held-prior-messagep
                                      fn-tcl-held-prior-messages
                                      fn-tcl-output-has-final-ackp))))

(defthm fn-tcl-output-has-final-ackp-append
  (equal (fn-tcl-output-has-final-ackp (append left right) xfer-id)
         (or (fn-tcl-output-has-final-ackp left xfer-id)
             (fn-tcl-output-has-final-ackp right xfer-id)))
  :hints (("Goal" :induct (append left right)
                   :in-theory (enable fn-tcl-output-has-final-ackp))))

(defthm fn-tcl-late-refusal-gets-no-final-ack
  (implies (fn-tcl-held-final-ackp messages xfer-id)
           (let ((plan (fn-tcl-delivery-plan
                        messages xfer-id (list :refused reason))))
             (and (equal (fn-tcl-delivery-plan-status plan) :refused)
                  (equal (fn-tcl-delivery-plan-messages plan)
                         (append
                          (fn-tcl-held-prior-messages messages)
                          (list (fn-tcl-make-xfer-refuse
                                 (fn-tcl-delivery-refuse-reason reason)
                                 xfer-id))))
                  (not (fn-tcl-output-has-final-ackp
                        (fn-tcl-delivery-plan-messages plan) xfer-id)))))
  :hints (("Goal" :in-theory (enable fn-tcl-delivery-plan
                                     fn-tcl-delivery-plan-status
                                     fn-tcl-delivery-plan-messages
                                     fn-tcl-output-has-final-ackp
                                     fn-tcl-make-xfer-refuse
                                     fn-tcl-xfer-ack-shapep))))

(defthm fn-tcl-uncertain-delivery-withholds-final-ack
  (implies (fn-tcl-held-final-ackp messages xfer-id)
           (let ((plan (fn-tcl-delivery-plan
                        messages xfer-id (list :uncertain reason))))
             (and (equal (fn-tcl-delivery-plan-status plan) :uncertain)
                  (null (fn-tcl-delivery-plan-messages plan)))))
  :hints (("Goal" :in-theory (enable fn-tcl-delivery-plan
                                     fn-tcl-delivery-plan-status
                                     fn-tcl-delivery-plan-messages))))

(defthm fn-tcl-accepted-delivery-releases-only-held-final
  (implies (and (fn-tcl-held-final-ackp messages xfer-id)
                (or (null path) (stringp path)))
           (equal (fn-tcl-delivery-plan-messages
                   (fn-tcl-delivery-plan messages xfer-id
                                         (list :accepted path)))
                  messages))
  :hints (("Goal" :in-theory (enable fn-tcl-delivery-plan
                                     fn-tcl-delivery-plan-messages))))

; The ACK and the progress point.  A plan's messages carry the transfer's
; final END acknowledgement only for an :accepted callback result (the
; custody the callback made durable), and exactly then the plan names the
; in-session progress point (PKT-873).
(local
 (defthm fn-tcl-held-prior-messages-have-no-final-ack
   (implies (fn-tcl-held-final-ackp messages xfer-id)
            (not (fn-tcl-output-has-final-ackp
                  (fn-tcl-held-prior-messages messages) xfer-id)))
   :hints (("Goal" :induct (fn-tcl-held-final-ackp messages xfer-id)
            :in-theory (enable fn-tcl-held-final-ackp fn-tcl-held-prior-messages
                               fn-tcl-held-prior-messagep fn-tcl-output-has-final-ackp)))))

(local
 (defthm fn-tcl-final-ack-not-in-a-refuse-tail
   (not (fn-tcl-output-has-final-ackp
         (list (fn-tcl-make-xfer-refuse reason xfer-id)) x))
   :hints (("Goal" :in-theory (enable fn-tcl-output-has-final-ackp
                                      fn-tcl-make-xfer-refuse fn-tcl-xfer-ack-shapep
                                      fn-tcl-msg-kind)))))

(local
 (defthm fn-tcl-output-has-final-ackp-of-append
   (equal (fn-tcl-output-has-final-ackp (append a b) x)
          (or (fn-tcl-output-has-final-ackp a x) (fn-tcl-output-has-final-ackp b x)))
   :hints (("Goal" :in-theory (enable fn-tcl-output-has-final-ackp)))))

; KEYSTONE (PKT-873).  The subject is fn-tcl-delivery-plan with
; fn-tcl-delivery-plan-progress-p, both called by host/native/tcpcl.lisp
; fnn-tcl-act on every completed inbound transfer.  If the messages the plan
; releases carry the transfer's final END ACK, the callback's result was
; (:accepted PATH) -- durable custody -- and the plan names the progress
; point, so the node runs that custody's delivery at the session's first
; quiet read timeout (or, if the peer ends the session first, in the
; between-sessions pass).  No acknowledged custody waits for its session to
; close.
(defthm fn-tcl-acknowledged-custody-is-progressed-in-its-turn
  (let ((plan (fn-tcl-delivery-plan messages xfer-id result)))
    (implies (fn-tcl-output-has-final-ackp (fn-tcl-delivery-plan-messages plan) xfer-id)
             (and (equal (car result) :accepted)
                  (equal (fn-tcl-delivery-plan-status plan) :accepted)
                  (fn-tcl-delivery-plan-progress-p plan))))
  :hints (("Goal" :in-theory (enable fn-tcl-delivery-plan fn-tcl-delivery-plan-messages
                                     fn-tcl-delivery-plan-status
                                     fn-tcl-delivery-plan-progress-p))))

; And the converse: a refusal, an uncertain publication and a fault name no
; progress point (nothing was taken into custody).
(defthm fn-tcl-unaccepted-delivery-names-no-progress
  (implies (not (equal (car result) :accepted))
           (not (fn-tcl-delivery-plan-progress-p
                 (fn-tcl-delivery-plan messages xfer-id result))))
  :hints (("Goal" :in-theory (enable fn-tcl-delivery-plan fn-tcl-delivery-plan-status
                                     fn-tcl-delivery-plan-progress-p))))
