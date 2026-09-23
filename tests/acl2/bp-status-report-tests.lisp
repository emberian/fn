; RFC 9171 section 6.1.1 wire facts.  Literal vectors are independent of the
; encoder, and include both subject shapes and timed and untimed assertions.
(in-package "ACL2")
(include-book "../../books/bp-status-report")

(defconst *fn-bpn-report-whole*
  '(:report ((nil) (nil) (nil) (nil)) 0 (:dtn-none) (0 0) nil))
(defconst *fn-bpn-report-whole-wire*
  '(130 1 132 132 129 244 129 244 129 244 129 244 0 130 1 0 130 0 0))

(defconst *fn-bpn-report-fragment*
  '(:report ((t 1000) (nil) (t) (nil)) 1 (:ipn 10 1) (100 7) (24 . 5)))
(defconst *fn-bpn-report-fragment-wire*
  '(130 1 134 132 130 245 25 3 232 129 244 129 245 129 244
    1 130 2 130 10 1 130 24 100 7 24 24 5))

(assert-event (equal (fn-bpn-report-encode *fn-bpn-report-whole*)
                     *fn-bpn-report-whole-wire*))
(assert-event (equal (fn-bpn-report-decode *fn-bpn-report-whole-wire*)
                     (fn-cbor-ok *fn-bpn-report-whole* nil)))
(assert-event (equal (fn-bpn-report-encode *fn-bpn-report-fragment*)
                     *fn-bpn-report-fragment-wire*))
(assert-event (equal (fn-bpn-report-encode-for-subject
                      *fn-bpn-report-fragment* t)
                     :bad)) ; a true assertion lacks its required time
(assert-event (equal (fn-bpn-report-encode-for-subject
                      *fn-bpn-report-fragment* nil)
                     :bad)) ; a timed assertion was not requested
(assert-event (equal (fn-bpn-report-encode-for-subject
                      *fn-bpn-report-whole* t)
                     *fn-bpn-report-whole-wire*))
(assert-event (equal (fn-bpn-report-encode-for-subject
                      '(:report ((t 1000) (nil) (t 1001) (nil))
                        1 (:ipn 10 1) (100 7) (24 . 5))
                      t)
                     '(130 1 134 132 130 245 25 3 232 129 244
                       130 245 25 3 233 129 244 1 130 2 130 10 1
                       130 24 100 7 24 24 5)))
(assert-event (equal (fn-bpn-report-decode *fn-bpn-report-fragment-wire*)
                     (fn-cbor-ok *fn-bpn-report-fragment* nil)))

; The subject's time-request flag permits a time only on true assertions.
; The parser has no subject bundle in hand, so it accepts both wire variants;
; generation must consult the subject flag before constructing a report.
(assert-event (equal (fn-bpn-report-encode
                      '(:report ((t) (nil) (nil) (nil)) 11
                        (:dtn-none) (1 2) nil))
                     '(130 1 132 132 129 245 129 244 129 244 129 244
                       11 130 1 0 130 1 2)))

(assert-event (not (fn-cbor-result-okp
                    (fn-bpn-report-decode
                     '(130 1 132 132 130 244 0 129 244 129 244 129 244
                       0 130 1 0 130 0 0))))) ; false with time
(assert-event (not (fn-cbor-result-okp
                    (fn-bpn-report-decode
                     '(130 1 132 132 129 244 129 244 129 244 129 244
                       0 130 1 0 130 0 0 0))))) ; trailing octet
(assert-event (not (fn-cbor-result-okp
                    (fn-bpn-report-decode
                     '(130 1 132 132 129 244 129 244 129 244 129 244
                       24 0 130 1 0 130 0 0))))) ; nonminimal zero
(assert-event (not (fn-cbor-result-okp
                    (fn-bpn-report-decode
                     '(130 1 132 132 129 244 129 244 129 244 129 244
                       12 130 1 0 130 0 0))))) ; out-of-profile reason
(assert-event (not (fn-cbor-result-okp
                    (fn-bpn-report-decode
                     '(130 1 134 132 129 244 129 244 129 244 129 244
                       0 130 1 0 130 0 0 130 0 5))))) ; nested fragment pair
(assert-event (not (fn-cbor-result-okp
                    (fn-bpn-report-decode
                     '(130 1 134 132 129 244 129 244 129 244 129 244
                       0 130 1 0 130 0 0 0))))) ; missing payload length
(assert-event (not (fn-cbor-result-okp
                    (fn-bpn-report-decode
                     (make-list (+ 1 *fn-bpn-report-max-input*)
                                :initial-element 0)))))
