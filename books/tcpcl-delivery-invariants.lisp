; The host-called late-disposition planner cannot turn a definitive refusal
; or an ambiguous publication into a successful final END acknowledgement.
(in-package "ACL2")
(include-book "tcpcl-delivery")

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

(defthm fn-tcl-held-partial-acks-have-no-final
  (implies (fn-tcl-held-final-ackp messages xfer-id)
           (not (fn-tcl-output-has-final-ackp
                 (fn-tcl-held-partial-acks messages) xfer-id)))
  :hints (("Goal" :induct (fn-tcl-held-final-ackp messages xfer-id)
                   :in-theory (enable fn-tcl-held-final-ackp
                                      fn-tcl-held-partial-acks
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
                          (fn-tcl-held-partial-acks messages)
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
