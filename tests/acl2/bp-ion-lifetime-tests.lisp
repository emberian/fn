(in-package "ACL2")
(include-book "../../books/bp-ion-lifetime")

; Positive witnesses assert the whole keystone conclusion, including both
; helper bounds and equality to the original milliseconds.
(assert-event
 (let* ((lifetime 3600000) (seconds (fn-bpit-helper-seconds lifetime)))
   (and seconds (integerp seconds) (<= 1 seconds) (<= seconds 2147483)
        (equal (* 1000 seconds) lifetime) (equal seconds 3600))))
(assert-event (equal (fn-bpit-helper-seconds 1000) 1))
(assert-event (equal (fn-bpit-helper-seconds 2147483000) 2147483))
; Refutations of rounding and passing milliseconds directly to the helper.
(assert-event (not (fn-bpit-helper-seconds 60001)))
(assert-event (not (fn-bpit-helper-seconds 999)))
(assert-event (not (fn-bpit-helper-seconds 2147484000)))
(assert-event (not (fn-bpit-helper-seconds 0)))
(assert-event (not (fn-bpit-helper-seconds -1000)))
(assert-event (not (fn-bpit-helper-seconds 'bad)))
