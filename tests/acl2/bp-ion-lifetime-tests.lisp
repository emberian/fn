(in-package "ACL2")
(include-book "../../books/bp-ion-lifetime")
(include-book "../../books/defkeystone")

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

; TEETH-62 BEGIN
; fn-bpit-helper-seconds-preserves-lifetime with its teeth (TEETH CONTRACT v1).
(defteeth fn-bpit-helper-seconds-preserves-lifetime
  :claim (((whole-seconds (fn-bpit-helper-seconds lifetime)))
          (let ((seconds (fn-bpit-helper-seconds lifetime)))
             (and (integerp seconds) (<= 1 seconds) (<= seconds 2147483)
                  (equal (* 1000 seconds) lifetime))))
  :subject fn-bpit-helper-seconds
  :witness ((lifetime 3600000))
  :breaks ((whole-seconds ((lifetime 999))))
  :mutations ((milliseconds-as-seconds
               (:conclusion (let ((seconds (fn-bpit-helper-seconds lifetime))) (equal seconds lifetime)))
               ((lifetime 3600000))
               :fault "the helper handed the milliseconds themselves, not their seconds")))
