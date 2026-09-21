(in-package "ACL2")
(include-book "../../books/bp-receive-evidence")
(include-book "std/testing/must-fail" :dir :system)

(defconst *fn-t-bpe-empty* (fn-bpn-evidence-recover nil))
(assert-event (equal *fn-t-bpe-empty* (fn-bpn-evidence-state 0)))

(defconst *fn-t-bpe-accepted*
  (fn-bpn-evidence-authorize *fn-t-bpe-empty* :accepted t t t))
(assert-event (fn-bpn-evidence-operationp *fn-t-bpe-accepted*))
(assert-event
 (equal (fn-bpn-evidence-operation-wire-name *fn-t-bpe-accepted*)
        "00000000000000000000.wire"))
(assert-event
 (equal (fn-bpn-evidence-operation-result-name *fn-t-bpe-accepted*)
        "00000000000000000000.adu"))

; Reachable restart witnesses: both a completed verdict and a wire-only cut
; consume identity zero, so a later session gets identity one.
(assert-event
 (equal
  (fn-bpn-evidence-recover
   (list (cons "00000000000000000000.adu" :regular)
         (cons "00000000000000000000.wire" :regular)))
  (fn-bpn-evidence-state 1)))
(assert-event
 (equal
  (fn-bpn-evidence-recover
   (list (cons "00000000000000000000.wire" :regular)))
  (fn-bpn-evidence-state 1)))

; Conflicting sidecars, a sidecar without its exact wire, a gap, and a
; non-regular exact name all fail closed.
(assert-event
 (equal
  (car (fn-bpn-evidence-recover
        (list (cons "00000000000000000000.adu" :regular)
              (cons "00000000000000000000.refused" :regular)
              (cons "00000000000000000000.wire" :regular))))
  :fault))
(assert-event
 (equal
  (car (fn-bpn-evidence-recover
        (list (cons "00000000000000000000.refused" :regular))))
  :fault))
(assert-event
 (equal
  (car (fn-bpn-evidence-recover
        (list (cons "00000000000000000001.wire" :regular))))
  :fault))
(assert-event
 (equal
  (car (fn-bpn-evidence-recover
        (list (cons "00000000000000000000.wire" :other))))
  :fault))

; Teeth: allocation authority needs the held lock and both exact absence
; observations.  Dropping any one does not produce a publication operation.
(must-fail
 (assert-event
  (fn-bpn-evidence-operationp
   (fn-bpn-evidence-authorize *fn-t-bpe-empty* :accepted nil t t))))
(must-fail
 (assert-event
  (fn-bpn-evidence-operationp
   (fn-bpn-evidence-authorize *fn-t-bpe-empty* :accepted t nil t))))
(must-fail
 (assert-event
  (fn-bpn-evidence-operationp
   (fn-bpn-evidence-authorize *fn-t-bpe-empty* :accepted t t nil))))

(value-triple :bp-receive-evidence-tests-passed)
