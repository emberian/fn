; Teeth for outbound feed reply framing.  One host call yields at most one
; line, so FNFD records can become durable before another reply is applied.
(in-package "ACL2")
(include-book "../../books/feed-wire-input")

(defconst *fwi-zero* (fn-fwi-initial-state))

; A CR at one network boundary and LF at the next still produces one line.
(defconst *fwi-cr* (fn-fwi-step *fwi-zero* '(50 48 48 32 111 107 13)))
(assert-event (equal (fn-fwi-kind *fwi-cr*) :need-input))
(assert-event (fn-fwi-statep (fn-fwi-next-state *fwi-cr*)))
(defconst *fwi-line* (fn-fwi-step (fn-fwi-next-state *fwi-cr*) '(10)))
(assert-event (equal (fn-fwi-kind *fwi-line*) :line))
(assert-event (equal (fn-fwi-line *fwi-line*) '(50 48 48 32 111 107)))

; The second line stays retained until the host has persisted the first.
(defconst *fwi-two* (fn-fwi-step *fwi-zero*
                                  '(50 48 48 13 10 50 48 51 13 10)))
(assert-event (equal (fn-fwi-kind *fwi-two*) :line))
(assert-event (equal (fn-fwi-line *fwi-two*) '(50 48 48)))
(defconst *fwi-two-drain* (fn-fwi-step (fn-fwi-next-state *fwi-two*) nil))
(assert-event (equal (fn-fwi-kind *fwi-two-drain*) :line))
(assert-event (equal (fn-fwi-line *fwi-two-drain*) '(50 48 51)))

; RFC 3977's 510 content octets fit before CRLF; the 511th closes input.
(defconst *fwi-510* (fn-fwi-step *fwi-zero*
                                 (append (make-list 510 :initial-element 65)
                                         '(13 10))))
(assert-event (and (equal (fn-fwi-kind *fwi-510*) :line)
                   (equal (len (fn-fwi-line *fwi-510*)) 510)))
(defconst *fwi-510-partial*
  (fn-fwi-step *fwi-zero* (make-list 510 :initial-element 65)))
(assert-event (equal (fn-fwi-kind *fwi-510-partial*) :need-input))
(defconst *fwi-511* (fn-fwi-step (fn-fwi-next-state *fwi-510-partial*) '(65)))
(assert-event (equal (fn-fwi-kind *fwi-511*) :closed))

; The bounded retained suffix must be drained before another socket chunk.
(assert-event (equal (fn-fwi-kind
                      (fn-fwi-step (fn-fwi-next-state *fwi-two*) '(50)))
                     :invalid))
