; Teeth for books/bp-fnbs-codec-equivalence: the served recognizer and
; codec against their -before-guards twins on the codec tests' actual
; kind-5 witnesses, on records the recognizer refuses, and on inputs that
; are not lists at all (the theorems hold on every input).
(in-package "ACL2")
(include-book "../../books/bp-fnbs-codec-equivalence")
(include-book "../../books/bp-fnbs-inspect")
(include-book "bp-fnbs-codec-tests")

; Reachable positive witnesses: the codec tests' anchored and anonymous
; records (built by fn-bpnf-step's persist effect), on both twins.
(assert-event (and (fn-bpnf-stored-recordp *bpnfc-anchored-record*)
                   (fn-bpnf-stored-recordp-before-guards
                    *bpnfc-anchored-record*)))
(assert-event (and (fn-bpnf-stored-recordp *bpnfc-anon-record*)
                   (fn-bpnf-stored-recordp-before-guards *bpnfc-anon-record*)))

(defconst *bpnfce-values*
  (fn-bpnf-stored-record-values *bpnfc-anchored-record*))
(assert-event (equal (fn-bpnf-stored-from-values *bpnfce-values*)
                     *bpnfc-anchored-record*))
(assert-event (equal (fn-bpnf-stored-from-values-before-guards *bpnfce-values*)
                     *bpnfc-anchored-record*))

; A record whose held bundle is not a bundle: both refuse it (the earlier
; recognizer read its id through fn-bpb-bundle-id outside that function's
; guard; the served one asks fn-bpnf-heldp first).
(defconst *bpnfce-non-bundle-record*
  (let ((held (nth 3 *bpnfc-anchored-record*)))
    (fn-bpnf-stored-record
     (nth 1 *bpnfc-anchored-record*) (nth 2 *bpnfc-anchored-record*)
     (update-nth 7 '(:not-a-bundle) held))))
(assert-event (not (fn-bpb-bundlep
                    (fn-bpnf-held-bundle (nth 3 *bpnfce-non-bundle-record*)))))
(assert-event (and (not (fn-bpnf-stored-recordp *bpnfce-non-bundle-record*))
                   (not (fn-bpnf-stored-recordp-before-guards
                         *bpnfce-non-bundle-record*))))

; Values whose wire does not decode to a bundle: the served codec refuses
; before building a held record, the earlier one built and refused.  The
; earlier one builds through fn-bpnf-frame-held-with-anchor, whose guard
; (fn-bpb-bundlep bundle) a non-bundle now violates, so its logical value
; (nil, as the equality theorem says) is evaluated with guard checking off.
(defconst *bpnfce-bad-wire-values* (update-nth 10 '(255 255 255) *bpnfce-values*))
(with-guard-checking-event
 :none
 (assert-event (and (null (fn-bpnf-stored-from-values *bpnfce-bad-wire-values*))
                    (null (fn-bpnf-stored-from-values-before-guards
                           *bpnfce-bad-wire-values*)))))

; Inputs that are not lists: equal (nil) on both sides, as the theorems say
; of every input.  The earlier definitions read slots through nth before any
; recognizer (their guards were never verified), which a dotted list
; violates, so they are evaluated with guard checking off.
(with-guard-checking-event
 :none
 (assert-event (and (equal (fn-bpnf-stored-recordp 7)
                           (fn-bpnf-stored-recordp-before-guards 7))
                    (equal (fn-bpnf-stored-recordp '(:bpnf-stored 1 2 . 3))
                           (fn-bpnf-stored-recordp-before-guards
                            '(:bpnf-stored 1 2 . 3)))
                    (equal (fn-bpnf-stored-from-values '(1 2 . 3))
                           (fn-bpnf-stored-from-values-before-guards '(1 2 . 3)))
                    (equal (fn-bpnf-stored-from-values :atom)
                           (fn-bpnf-stored-from-values-before-guards :atom)))))

; The host-called projection under the served recognizer on the actual
; frame: the ADU is the bundle's payload.
(assert-event
 (equal (fn-bpnf-inspect-adu (fn-bpnf-stored-record-frame *bpnfc-anchored-record*))
        (list :ready (fn-bpb-payload *bpnfc-bundle*))))
(assert-event (equal (fn-bpnf-inspect-adu '(1 2 3)) '(:fault :invalid-fnbs)))
