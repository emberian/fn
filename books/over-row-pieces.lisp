; Fixed source references for the actual OVER row machine. PRF-1066.
(in-package "ACL2")
(include-book "nntp-syntax")
(include-book "legacy-parser-cursor")
(include-book "nov-piece-window")

; A span contains (handle at length origin-pin). Absent fields denote the
; empty string. Capturing references never reads or flattens field bytes.
(defun fn-obc-span-piece (span)
  (declare (xargs :guard t))
  (if span
      (list :span (fn-lpc-at 0 span) (fn-lpc-at 1 span)
            (fn-lpc-at 2 span) nil (fn-lpc-at 3 span))
    ""))

(defun fn-obc-parser-pieces (number parser)
  (declare (xargs :guard t))
  (list (fn-nntp-decimal-field number) '(9)
        (fn-obc-span-piece (fn-lpc-field parser 0)) '(9)
        (fn-obc-span-piece (fn-lpc-field parser 1)) '(9)
        (fn-obc-span-piece (fn-lpc-field parser 2)) '(9)
        (fn-obc-span-piece (fn-lpc-field parser 3)) '(9)
        (fn-obc-span-piece (fn-lpc-field parser 4)) '(9)
        (list :decimal (nfix (fn-lpc-at 1 parser)) nil) '(9)
        (list :decimal (fn-lpc-body-lines parser) nil) '(13 10)))

