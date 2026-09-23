;;; Bounded native contact runner over the single FNBS foundation service.
;;; ACL2 decides the window, ready peer and contact event.  This host observes
;;; one clock reading, drives durable effects, and reports three outcomes.
(in-package "ACL2")

(defun fnn-bpc-u64-argument (text label)
  ; A syntactic input bound before PARSE-INTEGER.  ACL2 below decides whether
  ; the resulting integer is a valid clock time and window endpoint.
  (unless (and (stringp text) (<= 1 (length text) 20)
               (every #'digit-char-p text))
    (error 'fnn-usage-error
           :message (format nil "bp-contact: invalid ~a" label)))
  (parse-integer text))

(defun fnn-bpc-advance-clock (service obs)
  ; Every iteration consumes one ACL2 effect batch.  No host success is
  ; inferred from a pending journal write or from a TCPCL acknowledgement.
  (loop repeat (fnn-core 'fn-bpn-host-machine-max-jobs)
        for effects = (fnn-bps-step service (list :clock obs))
        while effects do (fnn-bps-drive-effects service effects)))

(defun fnn-bpc-drive-contact (service event)
  (if (third event)
      (progn
        (loop repeat (fnn-core 'fn-bpn-host-machine-max-jobs)
              for effects = (fnn-bps-step service event)
              while effects
              do (fnn-bps-drive-effects service effects)
              when (not (eq (fnn-bps-outcome service) :accepted))
                do (loop-finish))
        (fnn-bps-drive-effects
         service (fnn-bps-step service (list :contact (second event) nil))))
    (fnn-bps-drive-effects service (fnn-bps-step service event))))

(defun fnn-command-bp-contact-tick (journal node-id peer-id start end
                                    lifetime crc-type hop-limit transfer-mru
                                    wall wall-error)
  (let* ((config (fnn-bp-config node-id lifetime crc-type hop-limit transfer-mru))
         (peer (fnn-bp-eid peer-id))
         (window (fnn-core 'fn-bpsc-window peer start end)))
    (unless window (fnn-refuse "bp-contact: ACL2 refused contact window"))
    (let ((service (fnn-bps-open journal config wall wall-error)))
      (unwind-protect
           (let* ((obs (fnn-bp-observation wall wall-error)))
             (fnn-bpc-advance-clock service obs)
             (let* ((ready (fnn-core 'fn-bpn-host-ready-peers
                                     (fnn-bps-base service)))
                    (decision (fnn-core 'fn-bpsc-contact-decision
                                        window peer obs ready))
                    (event (fnn-core 'fn-bpsc-contact-event
                                     window peer obs ready)))
               (unless event (fnn-fault "bp-contact: ACL2 rejected contact event"))
               (format t "BP contact ~(~a~) peer=~a~%" decision peer-id)
               (fnn-bpc-drive-contact service event)
               (fnn-bps-exit-code service)))
        (fnn-bps-release service)))))

(defun fnn-dispatch-bp-contact (command args)
  (unless (string= command "tick")
    (error 'fnn-usage-error
           :message (format nil "unknown bp-contact command ~a" command)))
  (when (< (length args) 5)
    (error 'fnn-usage-error
           :message "bp-contact: tick needs journal node peer start end"))
  (when (> (length args) 11)
    (error 'fnn-usage-error :message "bp-contact: too many arguments"))
  (flet ((number (index default label)
           (let ((value (fnn-tcl-arg args index)))
             (if value (fnn-bpc-u64-argument value label) default))))
    (fnn-command-bp-contact-tick
     (first args) (second args) (third args)
     (fnn-bpc-u64-argument (fourth args) "start")
     (fnn-bpc-u64-argument (fifth args) "end")
     (number 5 +fnn-bp-lifetime+ "lifetime")
     (number 6 +fnn-bp-crc-type+ "CRC type")
     (number 7 +fnn-bp-hop-limit+ "hop limit")
     (number 8 +fnn-tcl-transfer-mru+ "transfer MRU")
     (let ((value (fnn-tcl-arg args 9)))
       (and value (fnn-bpc-u64-argument value "wall clock")))
     (number 10 0 "wall error"))))

(fnn-register-verb "bp-contact" #'fnn-dispatch-bp-contact)
