(in-package "ACL2")
(include-book "../../books/consumer-remote-reply")

(defconst *crrt-cursor*
 (fn-cp-cursor-encode (fn-cp-cursor '(104) '(105) '(99) '(112) '(113) 1 2 3 4)))
(defun fn-crrt-roundtrip (reply)
 (let ((bytes (fn-crr-encode-reference reply 1024)))
  (and (fn-crr-profilep 1024) (fn-crr-replyp reply 1024)
       (fn-cbor-octet-listp bytes)
       (equal (fn-crr-decode-reference bytes 1024) reply))))

; Distinct accepted answer shapes cover every selected operation's wire kind.
(assert-event (fn-crrt-roundtrip '(:remote-reply :accepted :progress nil 0 0 0 nil)))
(assert-event (fn-crrt-roundtrip (list :remote-reply :accepted :progress *crrt-cursor* 0 0 0 nil)))
(assert-event (fn-crrt-roundtrip (list :remote-reply :accepted :position *crrt-cursor* 0 0 0 nil)))
(assert-event (fn-crrt-roundtrip '(:remote-reply :accepted :status nil 7 10 3 nil)))
(assert-event (fn-crrt-roundtrip (list :remote-reply :accepted :poll *crrt-cursor* 0 0 0 '(65 66))))
; Refused, ambiguous durable outcome and unavailable source stay distinct.
(assert-event
 (and (fn-crrt-roundtrip '(:remote-reply :refused :progress nil 0 0 0 nil))
      (fn-crrt-roundtrip '(:remote-reply :uncertain :progress nil 0 0 0 nil))
      (fn-crrt-roundtrip '(:remote-reply :unavailable :position nil 0 0 0 nil))))
; An unavailable poll carries the exact gap cursor, never an article/report.
(assert-event (fn-crrt-roundtrip (list :remote-reply :unavailable :poll *crrt-cursor* 0 0 0 nil)))
; Corrupted answers cannot disclose an invented position or incompatible count.
(assert-event
 (and (equal (fn-crr-encode-reference (list :remote-reply :uncertain :progress *crrt-cursor* 0 0 0 nil) 1024) :bad)
      (equal (fn-crr-encode-reference '(:remote-reply :accepted :status nil 11 10 -1 nil) 1024) :bad)
      (equal (fn-crr-encode-reference (list :remote-reply :unavailable :poll *crrt-cursor* 0 0 0 '(65)) 1024) :bad)
      (equal (fn-crr-encode-reference '(:remote-reply :accepted :position nil 0 0 0 nil) 1024) :bad)))
; Profile bounds are codec representability checks, never allocation grants.
(assert-event
 (and (fn-crr-profilep 1) (fn-crr-profilep 1024)
      (not (fn-crr-profilep 0)) (not (fn-crr-profilep 4294967295))
      (equal (fn-crr-encode-reference (list :remote-reply :accepted :poll *crrt-cursor* 0 0 0 '(65 66)) 1) :bad)))
; Recomputed integrity does not bless a request kind as a reply.
(assert-event
 (let* ((reply '(:remote-reply :accepted :status nil 7 10 3 nil))
        (payload (fn-frame-fields-octets (fn-crr-spec 1024) (fn-crr-wire-values reply)))
        (prefix (fn-frame-protected *fn-crr-magic* 1 1 payload)))
  (equal (fn-crr-decode-reference (append prefix (fn-frame-trailer prefix)) 1024)
         '(:refused :reply-frame))))
; Wire mutation is refused, including a truncated trailer.
(assert-event
 (let ((bytes (fn-crr-encode-reference '(:remote-reply :accepted :status nil 7 10 3 nil) 1024)))
  (and (equal (fn-crr-decode-reference (cons 0 (cdr bytes)) 1024) '(:refused :reply-frame))
       (equal (fn-crr-decode-reference (take 20 bytes) 1024) '(:refused :reply-frame)))))

(assert-event (fn-crrt-roundtrip (list :remote-reply :accepted :poll *crrt-cursor* 0 0 0 '(0))))
; Strict optional tags reject empty-data aliases, even under valid integrity.
(assert-event
 (let* ((values '(:accepted :progress (0) 0 0 0 (1)))
        (payload (fn-frame-fields-octets (fn-crr-spec 1024) values))
        (prefix (fn-frame-protected *fn-crr-magic* 1 2 payload)))
  (equal (fn-crr-decode-reference (append prefix (fn-frame-trailer prefix)) 1024)
         '(:refused :reply-fields))))
