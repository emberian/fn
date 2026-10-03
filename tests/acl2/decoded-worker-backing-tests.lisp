(in-package "ACL2")
(include-book "../../books/decoded-worker-backing")

(assert-event
 (and (equal (fn-dwb-parent-octets) 80)
      (equal (fn-dwb-carry-octets) 112)
      (equal (fn-dwb-digest-octets) 672)
      (equal (fn-dwb-decoder-register-octets) 208)
      (equal (fn-dwb-requested-window-octets) 16432)
      (equal (fn-dwb-octet-buffers-octets) 69424)
      (equal (fn-dwb-fixed-storage-octets) 86928)))

; Component charge cannot be reported as complete job allocation coverage.
(assert-event
 (and (equal (fn-dwb-fixed-storage-vector) '(86928 0 0 1 1))
      (equal (fn-dwb-coverage) :partial-fixed-storage)
      (not (eq (fn-dwb-coverage) :complete))))
