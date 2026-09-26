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

;; fnn-bpc-drive-contact is in bp-service.lisp: `bp-service run/resume',
;; `bp-obligation request', this verb and `bp-node serve' drive every base
;; contact through it, and ACL2 (fn-bpnj-contact-next) decides each offer.

(defun fnn-command-bp-contact-tick (journal node-id peer-id start-delay end-delay
                                    lifetime crc-type hop-limit transfer-mru
                                    wall wall-error &optional store-root)
  (let* ((config (fnn-bp-config node-id lifetime crc-type hop-limit transfer-mru))
         (peer (fnn-bp-eid peer-id))
         (obs (fnn-bp-observation wall wall-error))
         (window (fnn-core 'fn-bpsc-relative-window
                           peer obs start-delay end-delay)))
    (unless window (fnn-refuse "bp-contact: ACL2 refused contact window"))
    (let ((service (fnn-bps-open journal config wall wall-error)))
      (unwind-protect
           (progn
             ;; [STORE]: route the queued jobs by that Store's bp-route table.
             (fnn-bps-use-store-routes service store-root)
             (fnn-bpc-advance-clock service obs)
             (let* ((ready (fnn-core 'fn-bpn-host-ready-peers
                                     (fnn-bps-base service)))
                    (decision (fnn-core 'fn-bpsc-contact-decision
                                        window peer obs ready))
                    (event (fnn-core 'fn-bpsc-contact-event
                                     window peer obs ready)))
               (unless event (fnn-fault "bp-contact: ACL2 rejected contact event"))
               (format t "BP contact ~(~a~) peer=~a~%" decision peer-id)
               ;; The service keeps :process transfer scope: the caller of this
               ;; one-shot verb asked for the transfer, so an uncertain one is
               ;; its answer (exit 3) and a refused one exit 2, although ACL2
               ;; has requeued the job exactly as it does under bp-node serve
               ;; (spec bp-node-machine 4.3.2).
               (fnn-bpc-drive-contact service event)
               (fnn-bps-exit-code service)))
        (fnn-bps-release service)))))

(defun fnn-dispatch-bp-contact (command args)
  (unless (string= command "tick")
    (error 'fnn-usage-error
           :message (format nil "unknown bp-contact command ~a" command)))
  (when (< (length args) 5)
    (error 'fnn-usage-error
           :message "bp-contact: tick needs journal node peer start-delay end-delay"))
  (when (> (length args) 12)
    (error 'fnn-usage-error :message "bp-contact: too many arguments"))
  (flet ((number (index default label)
           (let ((value (fnn-tcl-arg args index)))
             (if value (fnn-bpc-u64-argument value label) default))))
    (fnn-command-bp-contact-tick
     (first args) (second args) (third args)
     (fnn-bpc-u64-argument (fourth args) "start delay")
     (fnn-bpc-u64-argument (fifth args) "end delay")
     (number 5 +fnn-bp-lifetime+ "lifetime")
     (number 6 +fnn-bp-crc-type+ "CRC type")
     (number 7 +fnn-bp-hop-limit+ "hop limit")
     (number 8 +fnn-tcl-transfer-mru+ "transfer MRU")
     (let ((value (fnn-tcl-arg args 9)))
       (and value (fnn-bpc-u64-argument value "wall clock")))
     (number 10 0 "wall error")
     ;; [STORE]: route the queued jobs by STORE's bp-route table.
     (fnn-tcl-arg args 11))))

(fnn-register-verb "bp-contact" (fnn-bp-verb #'fnn-dispatch-bp-contact))
