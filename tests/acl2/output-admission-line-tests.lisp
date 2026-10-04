; Witnesses for books/output-admission-line.lisp: which admission words are
; answered on the wire, with which line, and whether the connection closes.
(in-package "ACL2")
(include-book "../../books/output-admission-line")
(include-book "std/testing/assert-bang" :dir :system)

(defconst *oadl-unpriced* '(:refused :unpriced-output-family :newnews))
(defconst *oadl-over* '(:refused :output-tariff-unaffordable :article))

(assert! (fn-oadl-wordp *oadl-unpriced*))
(assert! (fn-oadl-wordp *oadl-over*))
(assert! (not (fn-oadl-wordp '(:refused :invalid-output-preview))))
(assert! (not (fn-oadl-wordp '(:hold 9 :article))))

; 403, the connection kept.
(assert! (equal (fn-oadl-line *oadl-unpriced*)
                (append (fn-osch-text "403 command unavailable; its output is not priced on this server")
                        '(13 10))))
(assert! (not (fn-served-closingp (fn-oadl-effects *oadl-unpriced*))))
; 400 and close.
(assert! (equal (take 3 (fn-oadl-line *oadl-over*)) '(52 48 48)))
(assert! (fn-served-closingp (fn-oadl-effects *oadl-over*)))
; The log line names the family and the connection.
(assert! (equal (fn-oadl-log-line *oadl-unpriced* 7)
                (fn-osch-text "output admission: family unpriced, refused 403, connection 7 family NEWNEWS")))

; The status/health line: off without a policy, on with the pair.
(assert! (equal (fn-oadl-accounting-line nil) "output accounting: off (no [resources])"))
(assert! (equal (fn-oadl-accounting-line '(16777216 1048576))
                "output accounting: on output_heap_octets=16777216 output_quantum_heap_octets=1048576"))
(assert! (equal (fn-oadl-accounting-line '(1024 1024)) "output accounting: off (no [resources])"))
