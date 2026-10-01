; Registered received-provider producer route. Completion retains the exact
; reversed segment references + maintained cumulative count; never flattens
; a transfer. The legacy logical/spool driver stays separately scoped.
(in-package "ACL2")
(include-book "tcpcl-session")
(set-verify-guards-eagerness 0)

(defun fn-tcl-complete-source (s xfer-id flags count reverse-segments now)
 (declare (xargs :guard t))
 (fn-tcl-make-result
  (fn-tcl-next s (fn-tcl-session-phase s) nil (fn-tcl-session-outbound s)
               (fn-tcl-session-term s) now)
  (list (fn-tcl-send-event (fn-tcl-make-xfer-ack flags xfer-id count))
        (list :bundle-segments-received xfer-id reverse-segments count)) nil))

(defun fn-tcl-recv-segment-source (s m now)
  (declare (xargs :guard (and (fn-tcl-session-cheapp s)
                              (fn-tcl-transferringp (fn-tcl-session-phase s))
                              (fn-tcl-session-negotiated s)
                              (fn-tcl-messagep m (fn-tcl-segment-mru s))
                              (equal (fn-tcl-msg-kind m) :xfer-segment))
                  :verify-guards nil))
  (let* ((flags (fn-tcl-xfer-segment-flags m))
         (xfer-id (fn-tcl-xfer-segment-xfer-id m))
         (ext (fn-tcl-xfer-segment-ext m))
         (data (fn-tcl-xfer-segment-data m))
         (dlen (len data))
         (inb (fn-tcl-session-inbound s))
         (mru (fn-tcl-transfer-mru s)))
    (cond
     ((and inb (or (not (equal xfer-id (fn-tcl-inbound-xfer-id inb)))
                   (fn-tcl-flag-start flags)))
      (fn-tcl-broken-stream s (fn-tcl-inbound-xfer-id inb) now))
     ((and (not inb) (not (fn-tcl-flag-start flags)))
      (fn-tcl-broken-stream s nil now))
     ((not inb)
      ; START of a new transfer
      (if (equal (fn-tcl-session-phase s) :ending)
          (fn-tcl-refuse s xfer-id *fn-tcl-refuse-session-terminating* now)
        (let ((d (fn-tcl-ext-decision ext mru)))
          (cond ((equal (car d) :refuse) (fn-tcl-refuse s xfer-id (car (cdr d)) now))
                ((< mru dlen) (fn-tcl-refuse s xfer-id *fn-tcl-refuse-no-resources* now))
                ((and (car (cdr d)) (< (car (cdr d)) dlen))
                 (fn-tcl-refuse s xfer-id *fn-tcl-refuse-not-acceptable* now))
                ((fn-tcl-flag-end flags)
                 (if (and (car (cdr d)) (not (equal (car (cdr d)) dlen)))
                     (fn-tcl-refuse s xfer-id *fn-tcl-refuse-not-acceptable* now)
                   (fn-tcl-complete-source s xfer-id flags dlen (list data) now)))
                (t (fn-tcl-stage s (fn-tcl-make-inbound xfer-id (list data) dlen (car (cdr d)))
                                 flags xfer-id dlen now))))))
     (t
      ; continuation of the live transfer
      (let ((new-len (+ (fn-tcl-inbound-received-len inb) dlen))
            (total (fn-tcl-inbound-total inb)))
        (cond ((< mru new-len)
               (fn-tcl-refuse s xfer-id *fn-tcl-refuse-no-resources* now))
              ((and total (< total new-len))
               (fn-tcl-refuse s xfer-id *fn-tcl-refuse-not-acceptable* now))
              ((fn-tcl-flag-end flags)
               (if (and total (not (equal total new-len)))
                   (fn-tcl-refuse s xfer-id *fn-tcl-refuse-not-acceptable* now)
                 (fn-tcl-complete-source s xfer-id flags new-len
                                         (cons data (fn-tcl-inbound-staged inb)) now)))
              (t (fn-tcl-stage s (fn-tcl-make-inbound xfer-id
                                                      (cons data (fn-tcl-inbound-staged inb))
                                                      new-len total)
                               flags xfer-id new-len now))))))))

; Every valid transferring segment goes through the source producer. Falling
; back to ordinary STEP is only for other message kinds/invalid phase, whose
; branch cannot invoke completion. No host selector changes protocol bounds.
(defun fn-tcl-step-source (s m now)
 (declare (xargs :guard (and (fn-tcl-session-cheapp s)
   (fn-tcl-messagep m (fn-tcl-segment-mru s)) (fn-clock-timep now))
   :verify-guards nil))
 (if (and (not (equal (fn-tcl-session-phase s) :closed))
          (equal (fn-tcl-msg-kind m) :xfer-segment)
          (fn-tcl-transferringp (fn-tcl-session-phase s))
          (fn-tcl-session-negotiated s))
  (let ((s1 (fn-tcl-touch-rx s now)))
   (fn-tcl-settle (fn-tcl-recv-segment-source s1 m now)))
  (fn-tcl-step s m now)))

; One parsed message per scheduler invocation. A remainder returns to the
; caller; there is no drive-to-completion loop in this received source path.
(defun fn-tcl-host-source-drive (s buf now)
 (declare (xargs :guard (and (fn-tcl-session-cheapp s)
   (fn-cbor-octet-listp buf) (fn-clock-timep now)) :verify-guards nil))
 (if (or (eq (fn-tcl-session-phase s) :closed) (not (consp buf)))
  (list s nil buf :need)
  (let ((d (fn-tcl-decode-for s buf)))
   (cond
    ((fn-tcl-parse-okp d)
     (let ((r (fn-tcl-step-source s (fn-tcl-parse-msg d) now)))
      (list (fn-tcl-result-session r) (fn-tcl-result-events r)
            (fn-tcl-parse-rest d) :stepped)))
    ((fn-tcl-parse-needp d) (list s nil buf :need))
    (t (let ((r (fn-tcl-input-error s (car buf) (fn-tcl-parse-reason d) now)))
        (list (fn-tcl-result-session r) (fn-tcl-result-events r) buf :refused)))))))

(defun fn-tcl-host-source-more-p (result)
 (declare (xargs :guard t))
 (and (eq (fn-cbor-ag-car (fn-cbor-ag-cdr (fn-cbor-ag-cdr (fn-cbor-ag-cdr result)))) :stepped)
      (consp (fn-cbor-ag-car (fn-cbor-ag-cdr (fn-cbor-ag-cdr result))))))
