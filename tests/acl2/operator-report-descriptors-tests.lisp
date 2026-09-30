(in-package "ACL2")
(include-book "../../books/operator-report-descriptors")

; Reachable descriptor antecedents and complete reference output, including
; retained unrelated custody evidence and both final disposition words.
(assert-event
 (let ((fields (fn-ord-peer "peer" 12 1)))
   (and (stringp "peer") (natp 12) (natp 1) (fn-orf-fieldsp fields)
        (equal (fn-orf-run (fn-orf-start fields))
               (fn-nls-text "retire peer=peer undelivered=12 dropped=1
")))))
(assert-event
 (let ((fields (fn-ord-header 1 456)))
   (and (natp 1) (natp 456) (fn-orf-fieldsp fields)
        (equal (fn-orf-run (fn-orf-start fields))
               (fn-nls-text "obligations=1 reserved=456
")))))
(assert-event
 (let ((fields (fn-ord-obligation "forward-unrelated" t 123 "message")))
   (and (stringp "forward-unrelated") (natp 123) (stringp "message")
        (fn-orf-fieldsp fields)
        (equal (fn-orf-run (fn-orf-start fields))
               (fn-nls-text "obligation id=forward-unrelated kind=forward charge=123 subject=message
")))))
(assert-event
 (let ((fields (fn-ord-obligation "archive" nil 0 "")))
   (and (stringp "archive") (natp 0) (stringp "") (fn-orf-fieldsp fields)
        (equal (fn-orf-run (fn-orf-start fields))
               (fn-nls-text "obligation id=archive kind=archive charge=0 subject=
")))))
(assert-event
 (let ((fields (fn-ord-end t 0 0)))
   (and (natp 0) (fn-orf-fieldsp fields)
        (equal (fn-orf-run (fn-orf-start fields))
               (fn-nls-text "retired state=drained undelivered=0 obligations=0
")))))
(assert-event
 (let ((fields (fn-ord-end nil 5 1)))
   (and (natp 5) (natp 1) (fn-orf-fieldsp fields)
        (equal (fn-orf-run (fn-orf-start fields))
               (fn-nls-text "retired state=deadline undelivered=5 obligations=1
")))))
(assert-event
 (and (fn-orf-fieldsp (fn-ord-release))
      (equal (fn-orf-run (fn-orf-start (fn-ord-release)))
             (fn-nls-text "retire release: what stays is released only by `carry drop WORK --abandon REASON' on the stopped store
"))))
