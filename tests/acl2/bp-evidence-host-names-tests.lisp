(in-package "ACL2")
(include-book "../../books/bp-evidence-host-names")
(include-book "bp-receive-evidence-tests")
(include-book "must-fail-checked")

; KEYSTONE teeth (PRF-1032,
; fn-bpn-host-evidence-next-result-name-names-exactly-the-next-record): the
; recovered empty state (record 0 next) and each of the three outcomes by
; name: a string, the callee's name of the next sequence under the outcome's
; result kind; then a state that is not an evidence state and an outcome
; outside the three name nothing.
(assert-event
 (and (fn-bpn-evidence-statep *fn-t-bpe-empty*)
      (fn-bpn-evidence-outcomep :accepted)
      (fn-bpn-evidence-outcomep :refused)
      (fn-bpn-evidence-outcomep :uncertain)
      (stringp (fn-bpn-host-evidence-next-result-name *fn-t-bpe-empty* :accepted))
      (equal (fn-bpn-host-evidence-next-result-name *fn-t-bpe-empty* :accepted)
             (fn-bpn-evidence-name (fn-bpn-evidence-next *fn-t-bpe-empty*)
                                   (fn-bpn-evidence-result-kind :accepted)))
      (equal (fn-bpn-host-evidence-next-result-name *fn-t-bpe-empty* :accepted)
             "00000000000000000000.adu")
      (equal (fn-bpn-host-evidence-next-result-name *fn-t-bpe-empty* :refused)
             (fn-bpn-evidence-name (fn-bpn-evidence-next *fn-t-bpe-empty*)
                                   (fn-bpn-evidence-result-kind :refused)))
      (equal (fn-bpn-host-evidence-next-result-name *fn-t-bpe-empty* :uncertain)
             (fn-bpn-evidence-name (fn-bpn-evidence-next *fn-t-bpe-empty*)
                                   (fn-bpn-evidence-result-kind :uncertain)))))
(assert-event
 (and (not (fn-bpn-evidence-statep '(:corrupt)))
      (null (fn-bpn-host-evidence-next-result-name '(:corrupt) :accepted))
      (not (fn-bpn-evidence-outcomep :unknown))
      (null (fn-bpn-host-evidence-next-result-name *fn-t-bpe-empty* :unknown))))
(must-fail-checked
 (assert-event
  (stringp (fn-bpn-host-evidence-next-result-name '(:corrupt) :accepted))))
