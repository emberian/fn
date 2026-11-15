; Real protocol actor control: one oversized APPEND spans CTL loans, then
; malformed authenticated EOF is refused and the same connection retries.
; This requires the paired CTL transport and CNS continuation implementation.
(in-package "ACL2")
(include-book "cns-raw-eof-unit")

; Same exact producer/reply/STATUS/no-publication oracle as the established
; small-frame controls; the article crosses both RX and feed quanta.
(assert-event (fn2-cre-ok 6144 0))
(assert-event (fn2-cre-ok 6144 4096))
(assert-event (fn2-cre-ok 6144 :bad-final-byte))
(assert-event (fn2-cre-ok 6144 :good-crlf))
