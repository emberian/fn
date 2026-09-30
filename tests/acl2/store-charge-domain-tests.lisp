; PRF-1111: literal producer domain, including the complete codec range.
(in-package "ACL2")
(include-book "../../books/store-charge-domain")

; Reachable length inputs to the actual native charge producer. No payload
; allocation is needed to test a function whose input is the length.
(assert-event
 (and (fn-pfld-payload-sizep 0)
      (posp (fn-store-charge 0))
      (fn-record-uint32p (fn-store-charge 0))
      (equal (fn-store-charge 0) 1)))
(assert-event
 (and (fn-pfld-payload-sizep 32769)
      (posp (fn-store-charge 32769))
      (fn-record-uint32p (fn-store-charge 32769))
      (equal (fn-store-charge 32769) 10)))
(assert-event
 (and (fn-pfld-payload-sizep *fn-record-max-payload*)
      (posp (fn-store-charge *fn-record-max-payload*))
      (fn-record-uint32p (fn-store-charge *fn-record-max-payload*))
      (equal (fn-store-charge *fn-record-max-payload*) 1040385)))

; Hypothesis removal: a numeric producer-domain counterexample. This is
; NOT a reachable supported-profile request and allocates no giant payload.
; There are no retained theorem hypotheses. The omitted domain and the
; conjunction in the theorem's conclusion both fail affirmatively.
(defconst *scd-outside-codec* (* 4096 *fn-cbor-max-uint*))
(assert-event
 (and (natp *scd-outside-codec*)
      (not (fn-pfld-payload-sizep *scd-outside-codec*))
      (posp (fn-store-charge *scd-outside-codec*))
      (not (fn-record-uint32p (fn-store-charge *scd-outside-codec*)))
      (not (and (posp (fn-store-charge *scd-outside-codec*))
                (fn-record-uint32p (fn-store-charge *scd-outside-codec*))))))
