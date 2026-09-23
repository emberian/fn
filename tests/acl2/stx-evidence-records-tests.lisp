; Witnesses and teeth for the durable statement-verdict Store event.
(in-package "ACL2")
(include-book "../../books/stx-evidence-records")
(include-book "../../books/codec-attach")

(defconst *stxe-profile-unknown* '(117 110 107 110 111 119 110 45 118 49))
(defconst *stxe-evidence*
  (fn-stxe-make 3 7 11 "<evidence@example.invalid>" :unverified
                *fn-stx-token-signature* 5 *stxe-profile-unknown*))

(assert-event (fn-stxe-p *stxe-evidence*))
(assert-event (consp (fn-stxe-encode *stxe-evidence*)))
(assert-event
 (equal (fn-stmt-value
         (fn-stxe-decode-exact (fn-stxe-encode *stxe-evidence*)))
        *stxe-evidence*))

; An unknown algorithm profile is retained byte-exact but never interpreted
; as authority.
(assert-event
 (equal (fn-stxe-profile
         (fn-stmt-value
          (fn-stxe-decode-exact (fn-stxe-encode *stxe-evidence*))))
        *stxe-profile-unknown*))
(assert-event (equal (fn-stxe-authority-verdict *stxe-evidence*)
                     :unsupported-profile))
(defconst *stxe-hybrid-evidence*
  (fn-stxe-make 4 8 12 "<hybrid@example.invalid>" :verified
                '(1) 6 *fn-hsig-profile-tag*))
(assert-event (fn-stxe-profile-supportedp *fn-hsig-profile-tag*))
(assert-event (equal (fn-stxe-authority-verdict *stxe-hybrid-evidence*)
                     :requires-binding))
(assert-event
 (equal (fn-stxe-authority-verdict
         (fn-stmt-value
          (fn-stxe-decode-exact (fn-stxe-encode *stxe-hybrid-evidence*))))
        :requires-binding))

; Envelope kind and bounds have teeth.
(assert-event
 (not (fn-stmt-okp
       (fn-stxe-decode-exact
        (cons 0 (cdr (fn-stxe-encode *stxe-evidence*)))))))
(assert-event
 (equal (fn-stmt-value
         (fn-stxe-decode-exact
          (make-list (1+ *fn-stxe-max-octets*) :initial-element 0)))
        :limit))

; The common Store ordering coordinates are accessible without decoding the
; verdict detail or profile.
(assert-event (equal (fn-stxe-sequence *stxe-evidence*) 3))
(assert-event (equal (fn-stxe-txid *stxe-evidence*) 7))
(assert-event (equal (fn-stxe-generation *stxe-evidence*) 11))
