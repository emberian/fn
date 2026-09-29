(in-package "ACL2")
(include-book "../../books/bp-receive-evidence")
(include-book "must-fail-checked")
(include-book "../../books/codec-attach")

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
(must-fail-checked
 (assert-event
  (fn-bpn-evidence-operationp
   (fn-bpn-evidence-authorize *fn-t-bpe-empty* :accepted nil t t))))
(must-fail-checked
 (assert-event
  (fn-bpn-evidence-operationp
   (fn-bpn-evidence-authorize *fn-t-bpe-empty* :accepted t nil t))))
(must-fail-checked
 (assert-event
  (fn-bpn-evidence-operationp
   (fn-bpn-evidence-authorize *fn-t-bpe-empty* :accepted t t nil))))

; KEYSTONE teeth (PRF-1007,
; fn-bpn-evidence-authorize-admits-exactly-the-locked-next-identity).
; Reachable positive witness: the complete antecedent by name, then every
; conjunct of the conclusion, for a refused outcome (the :accepted one is
; *fn-t-bpe-accepted* above).
(assert-event
 (and (fn-bpn-evidence-statep *fn-t-bpe-empty*)
      (< (fn-bpn-evidence-next *fn-t-bpe-empty*) *fn-bpn-evidence-max-records*)
      (fn-bpn-evidence-outcomep :refused)
      (let ((answer (fn-bpn-evidence-authorize *fn-t-bpe-empty* :refused t t t)))
        (and (fn-bpn-evidence-operationp answer)
             (equal (fn-bpn-evidence-operation-identity answer) 0)
             (equal (fn-bpn-evidence-operation-wire-name answer)
                    "00000000000000000000.wire")
             (equal (fn-bpn-evidence-operation-result-name answer)
                    "00000000000000000000.refused")
             (equal (fn-bpn-evidence-operation-wire-publication answer)
                    (fn-jpub-initial t))
             (equal (fn-bpn-evidence-operation-result-publication answer)
                    (fn-jpub-initial t))
             (equal (fn-bpn-evidence-operation-successor answer)
                    (fn-bpn-evidence-state 1))))))
; Hypothesis-removal witnesses, each affirming the retained antecedent and
; that the answer is the one refusal, never an operation: an unclassified
; outcome; the record ceiling; a lock report that is truthy but not t (the
; host passes booleans, and only t is authority).  The held lock and the two
; absence observations are the must-fail-checked teeth above.
(assert-event
 (and (fn-bpn-evidence-statep *fn-t-bpe-empty*)
      (not (fn-bpn-evidence-outcomep :bogus))
      (equal (fn-bpn-evidence-authorize *fn-t-bpe-empty* :bogus t t t)
             '(:refused :evidence-admission))))
(defconst *fn-t-bpe-full*
  (fn-bpn-evidence-state *fn-bpn-evidence-max-records*))
(assert-event
 (and (fn-bpn-evidence-statep *fn-t-bpe-full*)
      (not (< (fn-bpn-evidence-next *fn-t-bpe-full*)
              *fn-bpn-evidence-max-records*))
      (equal (fn-bpn-evidence-authorize *fn-t-bpe-full* :accepted t t t)
             '(:refused :evidence-admission))))
(assert-event
 (and (fn-bpn-evidence-outcomep :accepted)
      (not (equal 1 t))
      (equal (fn-bpn-evidence-authorize *fn-t-bpe-empty* :accepted 1 t t)
             '(:refused :evidence-admission))))
; Corrupted-state witness (labelled so): a state that is not ready is refused
; whatever the evidence says.
(assert-event
 (and (not (fn-bpn-evidence-statep '(:ready -1)))
      (equal (fn-bpn-evidence-authorize '(:ready -1) :accepted t t t)
             '(:refused :evidence-admission))))

(value-triple :bp-receive-evidence-tests-passed)
