; Logical remote response reference shares the existing typed FNCT contract.
; No independent FNCR response kind, host framing, native grant or installed
; bounded report writer is established by these logical octet-list adapters.
(in-package "ACL2")
(include-book "consumer-reason")
(include-book "consumer-remote-codec")

; Required report dimension comes from the actual installed report producer,
; independently of Store R and query cardinality. Codec compatibility alone
; is not physical allocation authority or a source-lifetime certificate.
(defun fn-cr-response-profilep (report-ceiling)
 (declare (xargs :guard t))
 (and (posp report-ceiling) (<= report-ceiling *fn-stxa-max-octets*)
      (<= (+ 9 346 report-ceiling) *fn-ncl-poll-max-payload*)
      (<= (+ 9 346 report-ceiling) *fn-frame-max-payload*)))

(defun fn-cr-response-installed-profile (state)
 (declare (xargs :stobjs state :guard t))
 (mv '(:unavailable :remote-report-profile-issuer) nil state))

(defun fn-cr-response-encode (operation status reason cursor ack frontier gap report)
 (declare (xargs :guard t))
 (cond ((not (member-eq operation *fn-cr-operations*)) :bad)
       ((eq status :unavailable)
        (fn-native-control-reasoned-reply-encode :busy :remote-source-unavailable))
       ((not (eq status :accepted))
        (if (member-eq status '(:refused :uncertain :fault :busy))
            (fn-native-control-reasoned-reply-encode status reason) :bad))
       ((member-eq operation '(:poll :wait))
        (fn-ncl-poll-reply-encode :accepted cursor report))
       ((eq operation :status)
        (fn-ncl-status-reply-encode :accepted ack frontier gap))
       (t (fn-ncl-reply-encode :accepted cursor))))

; A remote client never downgrades an authenticated request to the private
; local request grammar. Only the exact shared busy/reason pair denotes an
; unavailable source; ordinary busy, uncertain, refusal and fault stay typed.
(defun fn-cr-response-client-read (operation octets)
 (declare (xargs :guard t))
 (if (not (member-eq operation *fn-cr-operations*)) '(:transport)
  (let ((reply (fn-ncr-client-read operation octets)))
   (cond ((eq (fn-cp-nth 0 reply) :resend) '(:transport :remote-no-downgrade))
         ((and (eq (fn-cp-nth 0 reply) :status)
               (eq (fn-cp-nth 1 reply) :busy)
               (equal (fn-cp-nth 2 reply) (fn-nctrl-reason-word :remote-source-unavailable)))
          (list :status :unavailable (fn-cp-nth 2 reply)))
         (t reply)))))

(in-theory (disable fn-cr-response-profilep fn-cr-response-installed-profile
 fn-cr-response-encode fn-cr-response-client-read))
