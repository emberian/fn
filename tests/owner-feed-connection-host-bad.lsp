(in-package "ACL2")

; This fixture is deliberately false.  The shell test requires the composed
; host-check runner to reject it, proving an `ld` failure cannot print success.
(assert-event (equal 1 2))
