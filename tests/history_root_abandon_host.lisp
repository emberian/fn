; Normal ACL2 PROGRAM host eligibility checks. Load the actual
; fn-owner-hroot-get and fn-owner-hroot-abandon-word definitions first.
; This is executable host admission/behavior evidence, not a theorem.
(in-package "ACL2")

(make-event
 (let* ((old (and (boundp-global 'fn-owner-history-roots state) (f-get-global 'fn-owner-history-roots state)))
        (state (f-put-global 'fn-owner-history-roots nil state)))
  (mv-let (erp word state) (fn-owner-hroot-abandon-word 7 state)
   (let ((state (f-put-global 'fn-owner-history-roots old state)))
    (if (and (null erp) (eq word :history-root-held))
        (value '(value-triple :passed))
      (er soft 'history-root-cleanup "unexpected eligibility ~x0" word))))))

(make-event
 (let* ((old (and (boundp-global 'fn-owner-history-roots state) (f-get-global 'fn-owner-history-roots state)))
        (state (f-put-global 'fn-owner-history-roots '((7 :building nil nil)) state)))
  (mv-let (erp word state) (fn-owner-hroot-abandon-word 7 state)
   (let ((state (f-put-global 'fn-owner-history-roots old state)))
    (if (and (null erp) (eq word :ready))
        (value '(value-triple :passed))
      (er soft 'history-root-cleanup "unexpected eligibility ~x0" word))))))

(make-event
 (let* ((old (and (boundp-global 'fn-owner-history-roots state) (f-get-global 'fn-owner-history-roots state)))
        (state (f-put-global 'fn-owner-history-roots '((7 :live nil nil)) state)))
  (mv-let (erp word state) (fn-owner-hroot-abandon-word 7 state)
   (let ((state (f-put-global 'fn-owner-history-roots old state)))
    (if (and (null erp) (eq word :history-root-held))
        (value '(value-triple :passed))
      (er soft 'history-root-cleanup "unexpected eligibility ~x0" word))))))

(make-event
 (let* ((old (and (boundp-global 'fn-owner-history-roots state) (f-get-global 'fn-owner-history-roots state)))
        (state (f-put-global 'fn-owner-history-roots '((7 :retired nil nil)) state)))
  (mv-let (erp word state) (fn-owner-hroot-abandon-word 7 state)
   (let ((state (f-put-global 'fn-owner-history-roots old state)))
    (if (and (null erp) (eq word :history-root-held))
        (value '(value-triple :passed))
      (er soft 'history-root-cleanup "unexpected eligibility ~x0" word))))))

(make-event
 (let* ((old (and (boundp-global 'fn-owner-history-roots state) (f-get-global 'fn-owner-history-roots state)))
        (state (f-put-global 'fn-owner-history-roots '((7 :building nil ((8 . lease)))) state)))
  (mv-let (erp word state) (fn-owner-hroot-abandon-word 7 state)
   (let ((state (f-put-global 'fn-owner-history-roots old state)))
    (if (and (null erp) (eq word :history-root-held))
        (value '(value-triple :passed))
      (er soft 'history-root-cleanup "unexpected eligibility ~x0" word))))))
