; Teeth for books/consumer-wait-codec.lisp (PRF-252, CNS-007): the wait
; requests (codes 9 and 10) and their command lines.  The subjects are the
; functions host/native-control-host.lisp calls:
; fn-cwait-request-encode / -decode (fn-native-control-host-consumer-
; request-encode / -decode) and fn-cwait-cli-plan (-consumer-cli-plan).
(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)
(include-book "../../books/consumer-wait-codec")

(defconst *cwc-id* '(97 103 101 110 116 45 49))            ; agent-1
(defconst *cwc-secret* '(99 111 114 114 101 99 116))       ; correct
(defconst *cwc-long-id* (make-list 65 :initial-element 97)) ; past fn-cp-idp

; --- the wire: positive witnesses of both round trips ------------------------
(assert-event (not (equal (fn-cwait-request-encode :wait *cwc-id* 30) :bad)))
(assert-event
 (equal (fn-cwait-request-decode (fn-cwait-request-encode :wait *cwc-id* 30))
        (list :consumer :wait *cwc-id* 30)))
(assert-event
 (equal (fn-cwait-request-decode (fn-cwait-request-encode :wait *cwc-id* 0))
        (list :consumer :wait *cwc-id* 0)))
(assert-event
 (equal (fn-cwait-request-decode
         (fn-cwait-request-encode :wait *cwc-id* *fn-cwait-max-seconds*))
        (list :consumer :wait *cwc-id* 3600)))
(assert-event
 (not (equal (fn-cwait-request-encode :bound-wait *cwc-id*
                                      (list 30 *cwc-secret*))
             :bad)))
(assert-event
 (equal (fn-cwait-request-decode
         (fn-cwait-request-encode :bound-wait *cwc-id* (list 30 *cwc-secret*)))
        (list :consumer :bound-wait *cwc-id* (list 30 *cwc-secret*))))
; The longest password (496 octets) round-trips; 497 is not encoded.
(assert-event
 (equal (fn-cwait-request-decode
         (fn-cwait-request-encode :bound-wait *cwc-id*
                                  (list 30 (make-list 496 :initial-element 120))))
        (list :consumer :bound-wait *cwc-id*
              (list 30 (make-list 496 :initial-element 120)))))
(assert-event
 (equal (fn-cwait-request-encode :bound-wait *cwc-id*
                                 (list 30 (make-list 497 :initial-element 120)))
        :bad))

; --- the wire: the round trips' one hypothesis ------------------------------
; The encoder refuses a timeout past 3 600 s, an id past 64 octets and a
; missing password; the round trip fails for what it refuses.
(assert-event (equal (fn-cwait-request-encode :wait *cwc-id* 3601) :bad))
(assert-event (equal (fn-cwait-request-encode :wait *cwc-long-id* 30) :bad))
(assert-event (equal (fn-cwait-request-encode :bound-wait *cwc-id* (list 30 nil))
                     :bad))
(must-fail
 (assert-event
  (equal (fn-cwait-request-decode (fn-cwait-request-encode :wait *cwc-id* 3601))
         (list :consumer :wait *cwc-id* 3601))))
(must-fail
 (assert-event
  (equal (fn-cwait-request-decode
          (fn-cwait-request-encode :bound-wait *cwc-long-id* (list 30 *cwc-secret*)))
         (list :consumer :bound-wait *cwc-long-id* (list 30 *cwc-secret*)))))

; --- the decoder's refusals ---------------------------------------------------
; A wait frame whose timeout exceeds 3 600 s, is short, or carries trailing
; octets; a bound wait with no password.
(defun cwc-frame (payload) (fn-nctrl-seal *fn-ncl-request-kind* payload))
(assert-event
 (equal (fn-cwait-request-decode
         (cwc-frame (append '(9) (fn-cp-id-bytes *cwc-id*) (fn-cbor-u32-bytes 3601))))
        '(:refused :timeout)))
(assert-event
 (equal (fn-cwait-request-decode
         (cwc-frame (append '(9) (fn-cp-id-bytes *cwc-id*) '(0 0 30))))
        '(:refused :timeout)))
(assert-event
 (equal (fn-cwait-request-decode
         (cwc-frame (append '(9) (fn-cp-id-bytes *cwc-id*) (fn-cbor-u32-bytes 30)
                            '(0))))
        '(:refused :timeout)))
(assert-event
 (equal (fn-cwait-request-decode
         (cwc-frame (append '(10) (fn-cp-id-bytes *cwc-id*) (fn-cbor-u32-bytes 30))))
        '(:refused :secret)))
(assert-event
 (equal (fn-cwait-request-decode (cwc-frame '(9 0)))
        '(:refused :consumer)))
; A 514-octet wait payload is :size (the plain kinds' bound).
(assert-event
 (equal (fn-cwait-request-decode (cwc-frame (cons 9 (make-list 513 :initial-element 1))))
        '(:refused :size)))

; --- every other kind is the consumer codec's --------------------------------
(assert-event
 (equal (fn-cwait-request-encode :poll *cwc-id* nil)
        (fn-ncl-request-encode :poll *cwc-id* nil)))
(assert-event
 (equal (fn-cwait-request-decode (fn-ncl-request-encode :poll *cwc-id* nil))
        (list :consumer :poll *cwc-id* nil)))
(assert-event
 (equal (fn-cwait-request-decode
         (fn-ncl-request-encode :bound-poll *cwc-id* *cwc-secret*))
        (list :consumer :bound-poll *cwc-id* *cwc-secret*)))
; Hypothesis of fn-cwait-request-decode-of-another-code-is-the-consumer-decode:
; a wait frame is not the consumer codec's (which knows no code 9).
(assert-event (equal (fn-ncl-request-decode
                      (fn-cwait-request-encode :wait *cwc-id* 30))
                     '(:refused :kind)))
(must-fail
 (assert-event
  (equal (fn-cwait-request-decode (fn-cwait-request-encode :wait *cwc-id* 30))
         (fn-ncl-request-decode (fn-cwait-request-encode :wait *cwc-id* 30)))))
(must-fail
 (assert-event
  (equal (fn-cwait-request-encode :wait *cwc-id* 30)
         (fn-ncl-request-encode :wait *cwc-id* 30))))

; --- the command lines ---------------------------------------------------------
(defconst *cwc-w* '(119 97 105 116))                       ; wait
(defconst *cwc-bw* '(98 111 117 110 100 45 119 97 105 116)) ; bound-wait
(defconst *cwc-30* '(51 48))
(assert-event
 (equal (fn-cwait-cli-plan *cwc-w* (list '(47 99) *cwc-id* '(47 107) '(47 114)
                                         *fn-cwait-timeout-flag* *cwc-30*))
        (list :run :wait '(47 99) *cwc-id* '(47 107) '(47 114) nil 30)))
(assert-event
 (equal (fn-cwait-cli-plan *cwc-bw* (list '(47 99) *cwc-id* '(47 115) '(47 107)
                                          '(47 114) *fn-cwait-timeout-flag*
                                          *cwc-30*))
        (list :run :bound-wait '(47 99) *cwc-id* '(47 107) '(47 114) '(47 115) 30)))
; Refused: a timeout past 3 600, not decimal, no flag, the same file twice.
(assert-event
 (equal (fn-cwait-cli-plan *cwc-w* (list '(47 99) *cwc-id* '(47 107) '(47 114)
                                         *fn-cwait-timeout-flag* '(51 54 48 49)))
        '(:usage :wait)))
(assert-event
 (equal (fn-cwait-cli-plan *cwc-w* (list '(47 99) *cwc-id* '(47 107) '(47 114)
                                         *fn-cwait-timeout-flag* '(45 49)))
        '(:usage :wait)))
(assert-event
 (equal (fn-cwait-cli-plan *cwc-w* (list '(47 99) *cwc-id* '(47 107) '(47 114)
                                         '(45 45 116) *cwc-30*))
        '(:usage :wait)))
(assert-event
 (equal (fn-cwait-cli-plan *cwc-bw* (list '(47 99) *cwc-id* '(47 107) '(47 107)
                                          '(47 114) *fn-cwait-timeout-flag*
                                          *cwc-30*))
        '(:usage :bound-wait)))
; Every other command is the consumer plan's.
(assert-event
 (equal (fn-cwait-cli-plan '(112 111 108 108) (list '(47 99) *cwc-id* '(47 107) '(47 114)))
        (fn-ncl-cli-plan '(112 111 108 108) (list '(47 99) *cwc-id* '(47 107) '(47 114)))))
(must-fail
 (assert-event
  (equal (fn-cwait-cli-plan *cwc-w* (list '(47 99) *cwc-id* '(47 107) '(47 114)
                                          *fn-cwait-timeout-flag* *cwc-30*))
         (fn-ncl-cli-plan *cwc-w* (list '(47 99) *cwc-id* '(47 107) '(47 114)
                                        *fn-cwait-timeout-flag* *cwc-30*)))))
