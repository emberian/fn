; SCN-1068. Supplied observations test matching only, never real crypto.
(in-package "ACL2")
(include-book "../../books/bpsec-operation")

(assert-event
 (and (eq (symbol-class 'fn-bps-op-complete (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-bps-op-cancel (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-bps-operationp (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-bps-completionp (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-bps-currentp (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-bps-opp (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-bps-refp (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-bps-op-byte-spanp (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-bps-fixed-recordp (w state)) :common-lisp-compliant)))

(defconst *fn-bpsot-bib*
  (fn-bps-op-make :verify-bib '(:bps-ref 1 2) '(:bps-ref 10 3)
                 '(:bps-ref 20 4) '(:bps-ref 30 5) 7 1 1
                 '(:bps-bib-params 6 7 (:bytes-span 40 100 24))
                 '(:bps-ref 50 6) '(:bytes-span 40 200 48)))
(defconst *fn-bpsot-bcb*
  (fn-bps-op-make :decrypt-bcb '(:bps-ref 2 2) '(:bps-ref 10 3)
                 '(:bps-ref 20 4) '(:bps-ref 31 5) 8 1 2
                 '(:bps-bcb-params 3 7 (:bytes-span 40 300 12) nil :separate-tag)
                 '(:bps-ref 51 6) '(:bytes-span 40 400 16)))

(defun fn-bpsot-issued (descriptor)
  (declare (xargs :guard t)) (list :bps-operation :issued descriptor))
(defun fn-bpsot-verified (descriptor)
  (declare (xargs :guard t))
  (list :bps-completion descriptor :verified
        (if (eq (fn-bps-field 1 descriptor) :decrypt-bcb) '(:bps-ref 60 7) nil) :ok))
(defun fn-bpsot-current (descriptor)
  (declare (xargs :guard t)) (fn-bps-op-current descriptor))

; Complete antecedent and conclusion of the evidence keystone, nonempty
; descriptor refs and expected spans; both BIB and BCB output shapes.
(defun fn-bpsot-positive (descriptor)
  (declare (xargs :guard t))
  (let* ((opstate (fn-bpsot-issued descriptor)) (current (fn-bpsot-current descriptor))
         (completion (fn-bpsot-verified descriptor))
         (result (fn-bps-op-complete opstate current completion)))
    (and (fn-bps-field 4 result)
         (fn-bps-operationp opstate) (eq (fn-bps-field 1 opstate) :issued)
         (fn-bps-currentp current) (equal current (fn-bps-op-current (fn-bps-field 2 opstate)))
         (fn-bps-completionp completion) (equal (fn-bps-field 1 completion) (fn-bps-field 2 opstate))
         (eq (fn-bps-field 2 completion) :verified)
         (equal (fn-bps-field 4 result) (list :bps-evidence (fn-bps-field 2 opstate) (fn-bps-field 3 completion)))
         (equal result (list :bps-completed :verified :ok (list :bps-operation :settled descriptor)
                             (list :bps-evidence descriptor (fn-bps-field 3 completion))))
         (fn-bps-operationp (fn-bps-field 3 result)))))
(assert-event (fn-bpsot-positive *fn-bpsot-bib*))
(assert-event (fn-bpsot-positive *fn-bpsot-bcb*))
(assert-event
 (and (fn-bps-completionp (fn-bpsot-verified *fn-bpsot-bib*))
      (fn-bps-completionp (fn-bpsot-verified *fn-bpsot-bcb*))
      (fn-bps-fixed-recordp 12 *fn-bpsot-bib*)
      (fn-bps-op-byte-spanp '(:bytes-span 40 200 48))
      (fn-bps-refp '(:bps-ref 50 6))))

; No invented field for the RFC ciphertext-carried tag form.
(assert-event
 (let* ((descriptor (fn-bps-op-make :decrypt-bcb '(:bps-ref 3 2) '(:bps-ref 10 3)
                 '(:bps-ref 20 4) '(:bps-ref 31 5) 8 1 2
                 '(:bps-bcb-params 1 0 (:bytes-span 40 300 16) (:bytes-span 40 500 40) :tag-in-ciphertext)
                 '(:bps-ref 52 6) nil)))
   (and (fn-bps-opp descriptor) (fn-bpsot-positive descriptor))))

; Foreign valid descriptors: alter only actual target, expected span or input
; incarnation. Complete foreign keystone antecedent/conclusion, rightful issued
; operation unconsumed, no evidence, and operation preservation conclusion.
(defun fn-bpsot-foreign (foreign)
  (declare (xargs :guard t))
  (let* ((opstate (fn-bpsot-issued *fn-bpsot-bib*)) (completion (fn-bpsot-verified foreign))
         (result (fn-bps-op-complete opstate (fn-bpsot-current *fn-bpsot-bib*) completion)))
    (and (fn-bps-operationp opstate) (fn-bps-completionp completion)
         (not (equal (fn-bps-field 1 completion) (fn-bps-field 2 opstate)))
         (equal result (list :bps-completed :ignored :foreign-completion opstate nil))
         (fn-bps-operationp (fn-bps-field 3 result)))))
(assert-event
 (fn-bpsot-foreign (fn-bps-op-make :verify-bib '(:bps-ref 1 2) '(:bps-ref 10 3)
   '(:bps-ref 20 4) '(:bps-ref 30 5) 7 2 1 (fn-bps-field 9 *fn-bpsot-bib*)
   '(:bps-ref 50 6) '(:bytes-span 40 200 48))))
(assert-event
 (fn-bpsot-foreign (fn-bps-op-make :verify-bib '(:bps-ref 1 2) '(:bps-ref 10 3)
   '(:bps-ref 20 4) '(:bps-ref 30 5) 7 1 1 (fn-bps-field 9 *fn-bpsot-bib*)
   '(:bps-ref 50 6) '(:bytes-span 40 201 48))))
(assert-event
 (fn-bpsot-foreign (fn-bps-op-make :verify-bib '(:bps-ref 1 2) '(:bps-ref 10 3)
   '(:bps-ref 20 4) '(:bps-ref 30 5) 7 1 1 (fn-bps-field 9 *fn-bpsot-bib*)
   '(:bps-ref 50 7) '(:bytes-span 40 200 48))))

(defun fn-bpsot-stale (current)
  (declare (xargs :guard t))
  (let* ((opstate (fn-bpsot-issued *fn-bpsot-bib*))
         (completion (fn-bpsot-verified *fn-bpsot-bib*))
         (result (fn-bps-op-complete opstate current completion)))
    (and (fn-bps-operationp opstate) (fn-bps-completionp completion)
         (not (equal current (fn-bps-op-current *fn-bpsot-bib*)))
         (equal result (list :bps-completed :ignored :stale-current
                             (list :bps-operation :settled *fn-bpsot-bib*) nil))
         (fn-bps-operationp (fn-bps-field 3 result)))))
(assert-event (fn-bpsot-stale nil))
(assert-event (fn-bpsot-stale '(:bps-current (:bps-ref 10 3) (:bps-ref 20 5) (:bps-ref 30 5) (:bps-ref 50 6))))
(assert-event (fn-bpsot-stale '(:bps-current (:bps-ref 10 3) (:bps-ref 20 4) (:bps-ref 30 6) (:bps-ref 50 6))))
(assert-event (fn-bpsot-stale '(:bps-current (:bps-ref 10 3) (:bps-ref 20 4) (:bps-ref 30 5) (:bps-ref 50 7))))
(assert-event (fn-bpsot-stale '(:bps-current (:bps-ref 10 3) (:bps-ref 20 4) (:bps-ref 30 5))))

; Complete retired-operation keystone antecedent/conclusion for cancelled
; and settled operations, including late verified after an uncertain result.
(defun fn-bpsot-retired (opstate)
  (declare (xargs :guard t))
  (let* ((descriptor (fn-bps-field 2 opstate))
         (result (fn-bps-op-complete opstate (fn-bpsot-current descriptor) (fn-bpsot-verified descriptor))))
    (and (fn-bps-operationp opstate) (not (eq (fn-bps-field 1 opstate) :issued))
         (not (eq (fn-bps-field 1 (fn-bps-op-cancel opstate)) :issued))
         (not (eq (fn-bps-field 1 (fn-bps-field 3 result)) :issued))
         (not (fn-bps-field 4 result)) (fn-bps-operationp (fn-bps-field 3 result)))))
(assert-event
 (let* ((issued (fn-bpsot-issued *fn-bpsot-bib*)) (cancelled (fn-bps-op-cancel issued)))
   (and (fn-bps-operationp issued) (fn-bps-operationp cancelled)
        (equal cancelled (list :bps-operation :cancelled *fn-bpsot-bib*))
        (fn-bpsot-retired cancelled)
        (equal (fn-bps-op-complete cancelled (fn-bpsot-current *fn-bpsot-bib*) (fn-bpsot-verified *fn-bpsot-bib*))
               (list :bps-completed :ignored :cancelled (list :bps-operation :settled *fn-bpsot-bib*) nil)))))
(assert-event
 (let* ((issued (fn-bpsot-issued *fn-bpsot-bcb*)) (current (fn-bpsot-current *fn-bpsot-bcb*))
        (first (fn-bps-op-complete issued current (fn-bpsot-verified *fn-bpsot-bcb*)))
        (settled (fn-bps-field 3 first)))
   (and (fn-bps-field 4 first) (fn-bpsot-retired settled)
        (equal (fn-bps-op-complete settled current (fn-bpsot-verified *fn-bpsot-bcb*))
               (list :bps-completed :ignored :duplicate settled nil)))))
(assert-event
 (let* ((issued (fn-bpsot-issued *fn-bpsot-bib*)) (current (fn-bpsot-current *fn-bpsot-bib*))
        (completion (list :bps-completion *fn-bpsot-bib* :uncertain nil :primitive-fault))
        (result (fn-bps-op-complete issued current completion)) (settled (fn-bps-field 3 result)))
   (and (fn-bps-operationp issued) (fn-bps-completionp completion)
        (equal result (list :bps-completed :uncertain :primitive-fault (list :bps-operation :settled *fn-bpsot-bib*) nil))
        (fn-bpsot-retired settled))))

; Closed status/detail/output combinations; faults stay uncertain.
(assert-event
 (let* ((issued (fn-bpsot-issued *fn-bpsot-bib*)) (current (fn-bpsot-current *fn-bpsot-bib*)))
   (and (equal (fn-bps-op-complete issued current (list :bps-completion *fn-bpsot-bib* :failed nil :authentication-failed))
               (list :bps-completed :failed :authentication-failed (list :bps-operation :settled *fn-bpsot-bib*) nil))
        (equal (fn-bps-op-complete issued current (list :bps-completion *fn-bpsot-bib* :unsupported nil :unsupported-profile))
               (list :bps-completed :unsupported :unsupported-profile (list :bps-operation :settled *fn-bpsot-bib*) nil))
        (equal (fn-bps-op-complete issued current (list :bps-completion *fn-bpsot-bib* :uncertain nil :primitive-unavailable))
               (list :bps-completed :uncertain :primitive-unavailable (list :bps-operation :settled *fn-bpsot-bib*) nil)))))
(assert-event
 (let* ((issued (fn-bpsot-issued *fn-bpsot-bib*)) (current (fn-bpsot-current *fn-bpsot-bib*))
        (completion (list :bps-completion *fn-bpsot-bib* :failed nil :primitive-fault)))
   (and (fn-bps-operationp issued) (not (fn-bps-completionp completion))
        (equal (fn-bps-op-complete issued current completion)
               (list :bps-completed :ignored :malformed-completion issued nil)))))
(assert-event
 (and (not (fn-bps-completionp (list :bps-completion *fn-bpsot-bcb* :verified nil :ok)))
      (not (fn-bps-completionp (list :bps-completion *fn-bpsot-bib* :verified '(:bps-ref 60 7) :ok)))
      (not (fn-bps-completionp (list :bps-completion *fn-bpsot-bcb* :uncertain '(:bps-ref 60 7) :primitive-fault)))
      (not (fn-bps-fixed-recordp 3 '(1 2 3 . 4)))
      (not (fn-bps-refp '(:bps-ref 1 2 3)))
      (not (fn-bps-op-byte-spanp '(:bytes-span 40 18446744073709551615 1)))))

; Hypothesis-removal teeth for preservation: corrupted state is affirmatively
; invalid and stays invalid; this is not a reachable issued-state witness.
(assert-event
 (let* ((corrupted '(:bps-operation :issued malformed))
        (result (fn-bps-op-complete corrupted nil (fn-bpsot-verified *fn-bpsot-bib*))))
   (and (not (fn-bps-operationp corrupted))
        (not (fn-bps-operationp (fn-bps-field 3 result)))
        (not (fn-bps-operationp (fn-bps-op-cancel corrupted))))))
; Remove only nonissued premise: all retained state validity holds, while
; positive verification disproves the no-evidence conclusion.
(assert-event
 (let* ((issued (fn-bpsot-issued *fn-bpsot-bib*))
        (result (fn-bps-op-complete issued (fn-bpsot-current *fn-bpsot-bib*) (fn-bpsot-verified *fn-bpsot-bib*))))
   (and (fn-bps-operationp issued) (eq (fn-bps-field 1 issued) :issued)
        (fn-bps-field 4 result))))
