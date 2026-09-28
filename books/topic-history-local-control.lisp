; Experimental local topic administration over the existing FNCT frame.  The
; peer UID is an OS observation supplied separately, never a request field.
(in-package "ACL2")
(include-book "native-control")

(defconst *fn-thlc-request-kind* 7)
(defconst *fn-thlc-reply-kind* 8)

(defun fn-thlc-request-encode (operation source-sequence quota)
  (declare (xargs :guard t))
  (let ((payload
         (case operation
           (:install (and (null source-sequence) (null quota) '(0)))
           (:anchor (and (fn-record-uint32p source-sequence)
                         (posp quota) (<= quota 64)
                         (append '(1) (fn-cbor-u32-bytes source-sequence)
                                 (list quota))))
           (:report (and (fn-record-uint32p source-sequence) (null quota)
                         (cons 2 (fn-cbor-u32-bytes source-sequence))))
           (otherwise nil))))
    (if payload (fn-nctrl-seal *fn-thlc-request-kind* payload) :bad)))

(defun fn-thlc-request-decode (octets)
  (declare (xargs :guard t))
  (let ((opened (fn-nctrl-open octets *fn-thlc-request-kind*)))
    (if (not (fn-frame-result-okp opened)) (list :refused :frame)
      (let ((payload (fn-frame-result-payload opened)))
        (cond
         ((equal payload '(0)) (list :topic :install nil nil))
         ((and (fn-cbor-octet-listp payload)
               (equal (len payload) 6) (equal (car payload) 1)
               (posp (nth 5 payload)) (<= (nth 5 payload) 64))
          (list :topic :anchor (fn-cbor-u32-from (cdr payload))
                (nth 5 payload)))
         ((and (fn-cbor-octet-listp payload)
               (equal (len payload) 5) (equal (car payload) 2))
          (list :topic :report (fn-cbor-u32-from (cdr payload)) nil))
         (t (list :refused :request)))))))

(defun fn-thlc-status-code (status)
  (case status (:accepted 0) (:refused 1) (:uncertain 2)
        (:fault 3) (:replayed-historical 4) (otherwise nil)))
(defun fn-thlc-code-status (code)
  (case code (0 :accepted) (1 :refused) (2 :uncertain)
        (3 :fault) (4 :replayed-historical) (otherwise nil)))
(verify-guards fn-thlc-status-code)
(verify-guards fn-thlc-code-status)

; A retry names a durable prior admission, so its control command succeeds
; without publishing a second event. Keep this outcome distinct on the wire.
; Its outcome class (HST-009, PRF-143): a replay of a durable admission is
; already satisfied, every other status is the control family's.
(defun fn-thlc-outcome-class (status)
  (declare (xargs :guard t))
  (if (equal status :replayed-historical) :accepted
    (fn-native-control-outcome-class status)))

(defun fn-thlc-status-exit-code (status)
  (declare (xargs :guard t))
  (fn-outcome-code (fn-thlc-outcome-class status)))

(defun fn-thlc-reply-encode (status)
  (declare (xargs :guard t))
  (let ((code (fn-thlc-status-code status)))
    (if code (fn-nctrl-seal *fn-thlc-reply-kind* (list code)) :bad)))

(defun fn-thlc-reply-decode (octets)
  (declare (xargs :guard t))
  (let ((opened (fn-nctrl-open octets *fn-thlc-reply-kind*)))
    (if (not (fn-frame-result-okp opened)) (list :refused :frame)
      (let ((payload (fn-frame-result-payload opened)))
        (if (and (consp payload) (null (cdr payload))
                 (fn-thlc-code-status (car payload)))
            (list :topic-reply (fn-thlc-code-status (car payload)))
          (list :refused :reply))))))

(defun fn-thlc-absolute-pathp (path)
  (declare (xargs :guard t))
  (and (consp path) (equal (car path) 47)
       (fn-cbor-octet-listp path)
       (<= (len path) *fn-ncfg-max-path*)
       (not (member-equal 0 path))))

(defun fn-thlc-decimal-octetsp (octets)
  (declare (xargs :guard t))
  (and (fn-cbor-octet-listp octets)
       (fn-native-admin-decimalp (fn-record-octets-string octets))))

(defun fn-thlc-decimal-value (octets)
  (declare (xargs :guard t))
  (fn-native-admin-decimal-value
   (coerce (fn-record-octets-string octets) 'list)))

(defun fn-thlc-cli-plan (command argv)
  (declare (xargs :guard t))
  (let ((control (fn-th-at 0 argv))
        (sequence (fn-th-at 1 argv))
        (quota (fn-th-at 2 argv)))
    (cond
     ((not (fn-thlc-absolute-pathp control)) (list :usage :control-path))
     ((equal command '(105 110 115 116 97 108 108)) ; install
      (if (equal (len argv) 1)
          (list :run :install control nil nil)
        (list :usage :install)))
     ((equal command '(97 110 99 104 111 114)) ; anchor
      (if (and (equal (len argv) 3)
               (fn-thlc-decimal-octetsp sequence)
               (fn-thlc-decimal-octetsp quota)
               (posp (fn-thlc-decimal-value quota))
               (<= (fn-thlc-decimal-value quota) 64))
          (list :run :anchor control (fn-thlc-decimal-value sequence)
                (fn-thlc-decimal-value quota))
        (list :usage :anchor)))
     ((equal command '(114 101 112 111 114 116)) ; report
      (if (and (equal (len argv) 2)
               (fn-thlc-decimal-octetsp sequence))
          (list :run :report control (fn-thlc-decimal-value sequence) nil)
        (list :usage :report)))
     (t (list :usage :operation)))))
