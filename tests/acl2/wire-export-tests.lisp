; Full-size execution regression: these conversions formerly consumed a
; control-stack frame per octet, including when proving FILE-HEX's guard.
(in-package "ACL2")
(include-book "../../books/wire-export")

; Preserve the total old arithmetic, including nfix/mod on non-octets.
(assert-event
 (equal (fn-wgx-hex-string '(0 1 15 16 255 256 -1)) "00010f10ff0000"))

; Exercise the actual complete file, not a shortened surrogate.
(assert-event
 (equal (length (fn-wgx-file-hex)) (* 2 (len *fn-wgx-file-octets*))))
