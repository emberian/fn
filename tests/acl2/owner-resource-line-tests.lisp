(in-package "ACL2")
(include-book "../../books/owner-resource-line")
(include-book "owner-cold-line-tests")

(defun orlnt-span (oc id octs word)
  (declare (xargs :mode :program))
  (with-local-stobj fn-octets
    (mv-let (result fn-octets)
      (let ((fn-octets (fn-octets-from-list octs fn-octets)))
        (mv (fn-orln-unavailable-span oc id 0 word fn-octets) fn-octets))
      result)))

(defconst *orlnt-octs* (append *oclnt-l2* *oclnt-l3*))
(defconst *orlnt-r* (orlnt-span *oclnt-oc1* 0 *orlnt-octs* :read-resources-unavailable))
; Full literal positive witness: natural in-range offset, named refusal,
; command mode, exact line consumption/progress, exact one403, owner unchanged.
(assert-event
 (and (natp 0) (<= 0 (len *orlnt-octs*))
      (fn-orln-refusalp :read-resources-unavailable)
      (fn-ocln-commandp *oclnt-oc1* 0)
      (equal (fn-own-tls-result-consumed *orlnt-r*) (len *oclnt-l2*))
      (< 0 (fn-own-tls-result-consumed *orlnt-r*))
      (equal (fn-own-tls-result-effects *orlnt-r*)
             (list (list :reply (fn-orln-unavailable-line :read-resources-unavailable))))
      (equal (take 3 (fn-orln-unavailable-line :read-resources-unavailable)) '(52 48 51))
      (equal (fn-own-tls-result-owner *orlnt-r*) (fn-ocln-owner-at-line *oclnt-oc1* 0))
      (equal (fn-own-tls-result-owner *orlnt-r*) *oclnt-oc1*)))
(assert-event (equal (t2r-host-read (fn-own-tls-result-owner *orlnt-r*) *orrt-views* 0 *oclnt-l3* *t2-s1*)
                     *oclnt-r3-direct*))
(assert-event (not (equal (fn-orln-unavailable-line :read-resources-unavailable)
                          (fn-otb-unavailable-line 0 0 nil))))
(assert-event (not (equal (fn-orln-unavailable-line :read-resources-unavailable)
                          (fn-orln-unavailable-line :read-identities-exhausted))))
; Remove the named-refusal hypothesis: every retained premise holds, the
; omitted predicate fails and the consumption conclusion fails (resultnil).
(assert-event
 (let ((r (orlnt-span *oclnt-oc1* 0 *orlnt-octs* :admitted)))
   (and (natp 0) (<= 0 (len *orlnt-octs*))
        (fn-ocln-commandp *oclnt-oc1* 0)
        (not (fn-orln-refusalp :admitted))
        (equal r nil)
        (not (equal (fn-own-tls-result-consumed r) (len *oclnt-l2*))))))
; Remove command mode: all retained premises hold, but an article-body line
; cannot be answered as a resource-refused command.
(assert-event
 (let ((r (orlnt-span *oclnt-oa* 0 *orlnt-octs* :read-resources-unavailable)))
   (and (natp 0) (<= 0 (len *orlnt-octs*))
        (fn-orln-refusalp :read-resources-unavailable)
        (not (fn-ocln-commandp *oclnt-oa* 0))
        (equal r nil)
        (not (equal (fn-own-tls-result-consumed r) (len *oclnt-l2*))))))
; Mutation that consumes the rest of a pipeline is refuted affirmatively.
(assert-event (not (equal (fn-own-tls-result-consumed *orlnt-r*) (len *orlnt-octs*))))
