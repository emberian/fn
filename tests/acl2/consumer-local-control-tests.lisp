(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)
(include-book "../../books/consumer-local-control")

(defconst *ncl-id* '(7))
(defconst *ncl-cli-id* '(99)) ; c, printable CLI ID
(defconst *ncl-group* '(102 110 46 116 101 115 116))
(defconst *ncl-cursor*
  (fn-cp-cursor '(1) '(2) *ncl-id* '(108 111 99 97 108)
                *ncl-group* 1 0 1 2))
(defconst *ncl-token* (fn-cp-cursor-encode *ncl-cursor*))
(assert-event (<= *fn-ncl-poll-max-payload* *fn-frame-max-payload*))
(assert-event
 (equal (fn-ncl-request-decode (fn-ncl-request-encode :bootstrap nil nil))
        '(:consumer :bootstrap nil nil)))
(assert-event
 (equal (fn-ncl-request-decode
         (fn-ncl-request-encode :poll *ncl-id* nil))
        (list :consumer :poll *ncl-id* nil)))
(assert-event
 (equal (fn-ncl-cli-plan '(98 111 111 116 115 116 114 97 112)
                         (list '(47 116 109 112 47 99)))
        '(:run :bootstrap (47 116 109 112 47 99) nil nil nil)))
(assert-event
 (equal (fn-ncl-request-decode
         (fn-ncl-request-encode :register *ncl-id* *ncl-group*))
        (list :consumer :register *ncl-id* *ncl-group*)))
(assert-event
 (equal (fn-ncl-request-decode
         (fn-ncl-request-encode :ack *ncl-token* nil))
        (list :consumer :ack *ncl-token* nil)))
(assert-event
 (equal (fn-ncl-request-decode
         (fn-ncl-request-encode :position *ncl-id* nil))
        (list :consumer :position *ncl-id* nil)))
(assert-event
 (equal (fn-ncl-request-decode
         (fn-ncl-request-encode :status *ncl-id* nil))
        (list :consumer :status *ncl-id* nil)))
(assert-event
 (equal (fn-ncl-cli-plan '(115 116 97 116 117 115)
                         (list '(47 116 109 112 47 99) *ncl-cli-id*))
        '(:run :status (47 116 109 112 47 99) (99) nil nil)))
(assert-event
 (equal (fn-ncl-cli-plan '(115 116 97 116 117 115)
                         (list '(47 116 109 112 47 99) '(10)))
        '(:usage :status)))
(assert-event
 (equal (fn-ncl-reply-decode
         (fn-ncl-reply-encode :accepted *ncl-token*))
        (list :consumer-reply :accepted *ncl-token*)))
(assert-event
 (equal (fn-ncl-status-reply-decode
         (fn-ncl-status-reply-encode :accepted 7 7 0))
        '(:consumer-status-reply :accepted 7 7 0)))
(assert-event
 (equal (fn-ncl-status-reply-decode
         (fn-ncl-status-reply-encode :accepted 3 11 8))
        '(:consumer-status-reply :accepted 3 11 8)))
; PRF-068 keystone witness also reaches the uint32 ceiling with a nonzero gap.
(assert-event
 (equal (fn-ncl-status-reply-decode
         (fn-ncl-status-reply-encode
          :accepted 1 *fn-cbor-max-uint* (1- *fn-cbor-max-uint*)))
        (list :consumer-status-reply :accepted
              1 *fn-cbor-max-uint* (1- *fn-cbor-max-uint*))))
(assert-event
 (equal (fn-ncl-status-reply-decode
         (fn-ncl-status-reply-encode :refused nil nil nil))
        '(:consumer-status-reply :refused nil nil nil)))
(assert-event
 (equal (fn-ncl-status-reply-decode
         (fn-ncl-status-reply-encode :uncertain nil nil nil))
        '(:consumer-status-reply :uncertain nil nil nil)))
(assert-event
 (equal (fn-ncl-status-reply-decode
         (fn-ncl-status-reply-encode :fault nil nil nil))
        '(:consumer-status-reply :fault nil nil nil)))
(must-fail
 (assert-event
  (equal (fn-ncl-status-reply-decode
          (fn-ncl-status-reply-encode :other nil nil nil))
         '(:consumer-status-reply :other nil nil nil))))
(assert-event
 (equal (fn-ncl-status-reply-decode
         (fn-ncl-status-reply-encode :accepted 3 11 8))
        '(:consumer-status-reply :accepted 3 11 8)))
; The next four must-fail cases isolate, in theorem order, the ACK uint32,
; frontier uint32, ACK<=frontier and exact-distance hypotheses.  Each keeps
; every other premise true and falsifies the claimed decoded value.
(must-fail
 (assert-event
  (equal (fn-ncl-status-reply-decode
          (fn-ncl-status-reply-encode :accepted -1 11 12))
         '(:consumer-status-reply :accepted -1 11 12))))
(must-fail
 (assert-event
  (equal (fn-ncl-status-reply-decode
          (fn-ncl-status-reply-encode
           :accepted 3 (1+ *fn-cbor-max-uint*)
           (- (1+ *fn-cbor-max-uint*) 3)))
         (list :consumer-status-reply :accepted
               3 (1+ *fn-cbor-max-uint*)
               (- (1+ *fn-cbor-max-uint*) 3)))))
(must-fail
 (assert-event
  (equal (fn-ncl-status-reply-decode
          (fn-ncl-status-reply-encode
           :accepted 11 3 (- 3 11)))
         (list :consumer-status-reply :accepted
               11 3 (- 3 11)))))
(must-fail
 (assert-event
  (equal (fn-ncl-status-reply-decode
          (fn-ncl-status-reply-encode :accepted 3 11 7))
         '(:consumer-status-reply :accepted 3 11 7))))
(assert-event (eq (fn-ncl-status-reply-encode :accepted 3 11 7) :bad))
(defconst *ncl-status-overbound-payload* (make-list 14 :initial-element 0))
(defconst *ncl-status-overbound-protected*
  (fn-frame-protected *fn-nctrl-magic* *fn-nctrl-version*
                      *fn-ncl-status-reply-kind*
                      *ncl-status-overbound-payload*))
(assert-event
 (equal (fn-ncl-status-reply-decode
         (append *ncl-status-overbound-protected*
                 (fn-frame-trailer *ncl-status-overbound-protected*)))
        '(:refused :frame)))
(defconst *ncl-status-malformed-gap-payload*
  (append '(0) (fn-cbor-u32-bytes 3) (fn-cbor-u32-bytes 11)
          (fn-cbor-u32-bytes 7)))
(defconst *ncl-status-malformed-gap-protected*
  (fn-frame-protected *fn-nctrl-magic* *fn-nctrl-version*
                      *fn-ncl-status-reply-kind*
                      *ncl-status-malformed-gap-payload*))
(assert-event
 (equal (fn-ncl-status-reply-decode
         (append *ncl-status-malformed-gap-protected*
                 (fn-frame-trailer *ncl-status-malformed-gap-protected*)))
        '(:refused :reply)))
(defconst *ncl-report*
  (fn-record-encode-impl
   (fn-record-make 0 0 0 "<poll@fn.test>" '(65) '("fn.test")
                   "poll-pin" "poll-content" "poll-release" 1 841000000)))
(assert-event
 (equal (fn-ncl-poll-reply-decode
         (fn-ncl-poll-reply-encode :accepted *ncl-token* *ncl-report*))
        (list :consumer-poll-reply :accepted *ncl-token* *ncl-report*)))
(assert-event
 (equal (fn-ncl-poll-reply-decode
         (fn-ncl-poll-reply-encode :accepted *ncl-token* nil))
        (list :consumer-poll-reply :accepted *ncl-token* nil)))

;; D27: the carried event's fields are codec ceilings (u32), so no witness
;; sits at them.  A value past every old cap (a 300,000-octet record and a
;; 220,000-octet source) still fits the consumer report envelope, and a
;; report past the composite's ceiling is refused before frame creation
;; (fn-ncl-poll-reply-past-the-composite-is-bad, below).
(defconst *ncl-max-shape-event*
  (fn-stxa-make-carried
   *fn-cbor-max-uint* *fn-cbor-max-uint*
   *fn-cbor-max-uint* *fn-cbor-max-uint*
   (make-list *fn-stxk-max-profile* :initial-element 1)
   (make-list *fn-record-max-metadata* :initial-element 2)
   (make-list 300000 :initial-element 3)
   (make-list *fn-stxe-max-octets* :initial-element 4)
   (make-list 220000 :initial-element 5)
   (make-list *fn-record-max-metadata* :initial-element 6)))
(assert-event (fn-stxa-p *ncl-max-shape-event*))
(defconst *ncl-max-shape-bytes* (fn-stxa-encode *ncl-max-shape-event*))
(assert-event
 (and (consp *ncl-max-shape-bytes*)
      (< 196608 (len *ncl-max-shape-bytes*))
      (<= (len *ncl-max-shape-bytes*) *fn-stxa-max-octets*)
      (not (eq (fn-ncl-poll-reply-encode
                :accepted *ncl-token* *ncl-max-shape-bytes*) :bad))))
(defthm fn-ncl-poll-reply-past-the-composite-is-bad
  (implies (< *fn-stxa-max-octets* (len report))
           (equal (fn-ncl-poll-reply-encode status cursor report) :bad))
  :hints (("Goal" :in-theory (enable fn-ncl-poll-reply-encode
                                     fn-ncl-poll-event-bytesp)))
  :rule-classes nil)
(assert-event
 (equal (fn-ncl-reply-decode (fn-ncl-reply-encode :uncertain nil))
        '(:consumer-reply :uncertain nil)))
(assert-event (equal (fn-ncl-request-encode :ack '(1 2 3) nil) :bad))
(assert-event
 (equal (fn-ncl-request-decode
         (fn-nctrl-seal *fn-ncl-request-kind* '(255)))
        '(:refused :kind)))
(assert-event (equal (fn-ncl-reply-encode :refused *ncl-token*) :bad))
(assert-event
 (equal (fn-ncl-cli-plan '(114 101 103 105 115 116 101 114)
                        (list '(47 116 109 112 47 99)
                              *ncl-cli-id* *ncl-group* '(47 116 109 112 47 116)))
        (list :run :register '(47 116 109 112 47 99)
              *ncl-cli-id* *ncl-group* '(47 116 109 112 47 116))))
(assert-event
 (equal (fn-ncl-cli-plan '(97 99 107)
                        (list '(47 116 109 112 47 99) '(47 116 109 112 47 116)))
        '(:run :ack (47 116 109 112 47 99) (47 116 109 112 47 116) nil nil)))
(assert-event
 (equal (fn-ncl-cli-plan '(97 99 107)
                        (list '(116 109 112 47 99) '(47 116 109 112 47 116)))
        '(:usage :control-path)))
(assert-event
 (equal (fn-ncl-cli-plan '(112 111 108 108)
                         (list '(47 116 109 112 47 99) *ncl-cli-id*
                               '(47 116 109 112 47 99 117)
                               '(47 116 109 112 47 114)))
        '(:run :poll (47 116 109 112 47 99) (99)
               (47 116 109 112 47 99 117)
               (47 116 109 112 47 114))))

; --- PRF-234: the bound consumer's two requests ------------------------------
; bound-poll (code 7) carries the consumer id and the account's password;
; bound-ack (code 8) the password, then the cursor.  Both round-trip.
(defconst *ncl-secret* '(99 111 114 114 101 99 116)) ; correct
(assert-event
 (equal (fn-ncl-request-decode
         (fn-ncl-request-encode :bound-poll *ncl-id* *ncl-secret*))
        (list :consumer :bound-poll *ncl-id* *ncl-secret*)))
(assert-event
 (equal (fn-ncl-request-decode
         (fn-ncl-request-encode :bound-ack *ncl-token* *ncl-secret*))
        (list :consumer :bound-ack *ncl-token* *ncl-secret*)))
; The longest password (496 octets) round-trips; one more is not encoded.
(defconst *ncl-long-secret* (make-list 496 :initial-element 120))
(assert-event
 (equal (fn-ncl-request-decode
         (fn-ncl-request-encode :bound-ack *ncl-token* *ncl-long-secret*))
        (list :consumer :bound-ack *ncl-token* *ncl-long-secret*)))
(assert-event
 (equal (fn-ncl-request-encode :bound-poll *ncl-id*
                               (make-list 497 :initial-element 120))
        :bad))
; No password, no request.
(assert-event (equal (fn-ncl-request-encode :bound-poll *ncl-id* nil) :bad))
; A password field longer than its payload is refused by name.
(assert-event
 (equal (fn-ncl-request-decode
         (fn-nctrl-seal *fn-ncl-request-kind* '(7 1 7 0 9 99)))
        '(:refused :secret)))
; The plain kinds keep their 513-octet payload bound: a 514-octet poll
; payload is refused :size, exactly as before this change.
(assert-event
 (equal (fn-ncl-request-decode
         (fn-nctrl-seal *fn-ncl-request-kind*
                        (cons 5 (make-list 513 :initial-element 1))))
        '(:refused :size)))
; The CLI: bound-poll CONTROL NAME SECRET-FILE CURSOR REPORT and
; bound-ack CONTROL CURSOR-FILE SECRET-FILE.
(assert-event
 (equal (fn-ncl-cli-plan '(98 111 117 110 100 45 112 111 108 108)
                         (list '(47 99) *ncl-cli-id* '(47 115) '(47 107) '(47 114)))
        (list :run :bound-poll '(47 99) *ncl-cli-id* '(47 107) '(47 114) '(47 115))))
(assert-event
 (equal (fn-ncl-cli-plan '(98 111 117 110 100 45 97 99 107)
                         (list '(47 99) '(47 107) '(47 115)))
        (list :run :bound-ack '(47 99) '(47 107) nil nil '(47 115))))
(assert-event
 (equal (fn-ncl-cli-plan '(98 111 117 110 100 45 112 111 108 108)
                         (list '(47 99) *ncl-cli-id* '(47 115) '(47 115) '(47 114)))
        '(:usage :bound-poll)))
; A secret file's one final line end is not part of the password.
(assert-event (equal (fn-ncl-secret-of-file '(112 119 10)) '(112 119)))
(assert-event (equal (fn-ncl-secret-of-file '(112 119 13 10)) '(112 119)))
(assert-event (equal (fn-ncl-secret-of-file '(112 119)) '(112 119)))

; PKT-709: help and the register steps.
(assert-event (equal (fn-ncl-cli-plan '(104 101 108 112) nil) (list :help)))
(assert-event (stringp (fn-ncl-usage-text)))
; The register retry is books/consumer-reason.lisp fn-ncr-cli-after (its
; tests: tests/acl2/consumer-reason-tests.lisp).
