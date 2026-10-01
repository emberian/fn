(in-package "ACL2")
(include-book "../../books/recovery-profile-envelope")

; Current grammar coordinate: changes to the underlying codec deliberately
; require updating the image workspace and its matching source evidence.
(assert-event
 (equal (fn-recovery-profile-envelope)
        '(:profile-envelope :fnsm-v1 10 600 32 642 1 643)))
(assert-event
 (equal (nth 5 (fn-recovery-profile-envelope))
        (+ *fn-frame-header-octets* *fn-bs-meta-max-config-payload*
           *fn-frame-trailer-octets*)))
(assert-event
 (equal (nth 7 (fn-recovery-profile-envelope))
        (+ (nth 5 (fn-recovery-profile-envelope))
           (nth 6 (fn-recovery-profile-envelope)))))
