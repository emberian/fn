(in-package "ACL2")
(include-book "../books/log-model")

(defconst *fn2-lm-test-b1* '(1 0 ((:put article-a)) (body-a manifest-a)))
(defconst *fn2-lm-test-b2* '(2 1 ((:put article-b)) (body-b)))
(defconst *fn2-lm-test-history* (list *fn2-lm-test-b1* *fn2-lm-test-b2*))
(defconst *fn2-lm-test-honest* (fn2-cm-profile :crash-only t t nil 0 0))
(defconst *fn2-lm-test-broad* (fn2-cm-profile :broad t t nil 0 2))
(defconst *fn2-lm-test-witness* (fn2-cm-profile :broad t t t 0 2))
(defconst *fn2-lm-test-lying* (fn2-cm-profile :lying nil t nil 0 2))
(defconst *fn2-lm-test-no-integrity* (fn2-cm-profile :broad t nil nil 0 2))

(defconst *fn2-lm-test-ack-prefix*
  (list (list :submit-batch *fn2-lm-test-b1*)
        '(:batch-writes-complete 1 (body-a manifest-a))
        '(:fence-ok 1) '(:acknowledge 1)
        (list :submit-batch *fn2-lm-test-b2*)
        '(:batch-writes-complete 2 (body-b)) '(:fence-ok 2) '(:acknowledge 2)))
(defconst *fn2-lm-test-ack-trace* (append *fn2-lm-test-ack-prefix* '((:crash))))

; Positive tooth evaluates the whole keystone antecedent and conclusion, on
; a nonempty history with two actual acknowledgements.
(assert-event
 (and (fn2-lm-durable-ack-hyps *fn2-lm-test-ack-trace* *fn2-lm-test-honest*
                               :intact *fn2-lm-test-history*)
      (fn2-lm-acknowledged-in-historyp
       (fn2-lm-at 3 (fn2-lm-trace-state *fn2-lm-test-ack-trace*)) *fn2-lm-test-history*)))

; Hypothesis-removal tooth 1: every other premise holds, but lying barriers
; permit the shorter consistent image without an independent witness.
(assert-event
 (let ((recovered (list *fn2-lm-test-b1*)))
   (and (not (fn2-cm-persistence-fence *fn2-lm-test-lying*))
        (fn2-lm-no-destructionp (fn2-lm-trace-state *fn2-lm-test-ack-trace*))
        (fn2-lm-recovery-allowedp *fn2-lm-test-ack-trace* *fn2-lm-test-lying* :intact recovered)
        (not (fn2-lm-acknowledged-in-historyp '(2 1) recovered)))))

; Hypothesis-removal tooth 2: honest barriers do not prevent later destruction.
(defconst *fn2-lm-test-corrupt*
  (append *fn2-lm-test-ack-trace* '((:corrupt-required 2))))
(assert-event
 (let ((recovered (list *fn2-lm-test-b1*)))
   (and (fn2-cm-persistence-fence *fn2-lm-test-broad*)
        (not (fn2-lm-no-destructionp (fn2-lm-trace-state *fn2-lm-test-corrupt*)))
        (fn2-lm-recovery-allowedp *fn2-lm-test-corrupt* *fn2-lm-test-broad* :damaged recovered)
        (not (fn2-lm-acknowledged-in-historyp '(2 1) recovered)))))

; Hypothesis-removal tooth 3: the forbidden shorter result is an actual value.
(assert-event
 (let ((recovered (list *fn2-lm-test-b1*)))
   (and (fn2-cm-persistence-fence *fn2-lm-test-honest*)
        (fn2-lm-no-destructionp (fn2-lm-trace-state *fn2-lm-test-ack-trace*))
        (not (fn2-lm-recovery-allowedp *fn2-lm-test-ack-trace* *fn2-lm-test-honest* :intact recovered))
        (not (fn2-lm-acknowledged-in-historyp '(2 1) recovered)))))

; ROUND2 E.5 row 1: honest fence/no later destruction, including repeated death.
(assert-event
 (and (fn2-lm-recovery-allowedp
       (append *fn2-lm-test-ack-trace* '((:crash) (:crash)))
       *fn2-lm-test-honest* :intact *fn2-lm-test-history*)
      ; A budget is permission to inject faults, not evidence faults occurred.
      (fn2-lm-durable-ack-hyps *fn2-lm-test-ack-trace* *fn2-lm-test-broad*
                               :intact *fn2-lm-test-history*)
      (not (fn2-lm-recovery-allowedp *fn2-lm-test-ack-trace* *fn2-lm-test-broad* :intact nil))))

; ROUND2 E.5 row 2: surviving integrity evidence forces a named stop.
(assert-event
 (let ((recovered (list *fn2-lm-test-b1*)))
   (and (fn2-lm-recovery-allowedp *fn2-lm-test-corrupt* *fn2-lm-test-broad* :damaged recovered)
        (fn2-lm-recovery-allowedp *fn2-lm-test-corrupt* *fn2-lm-test-broad* :unknown recovered)
        (not (fn2-lm-recovery-allowedp *fn2-lm-test-corrupt* *fn2-lm-test-broad* :intact recovered))
        (not (fn2-lm-recovery-allowedp *fn2-lm-test-corrupt* *fn2-lm-test-broad* :torn-tail recovered))
        (fn2-lm-recovery-allowedp *fn2-lm-test-corrupt* *fn2-lm-test-no-integrity* :intact recovered))))

(defconst *fn2-lm-test-rollback* (append *fn2-lm-test-ack-trace* '((:rollback 1))))
(defconst *fn2-lm-test-receipt*
  (append *fn2-lm-test-rollback* '((:present-frontier client-receipt-batch-2 2))))
; ROUND2 E.5 row 3: both the independent assumption and presented witness.
(assert-event
 (let ((recovered (list *fn2-lm-test-b1*)))
   (and (equal (fn2-lm-conflicting-witness
                (fn2-lm-at 8 (fn2-lm-trace-state *fn2-lm-test-receipt*)) recovered)
               'client-receipt-batch-2)
        (fn2-lm-recovery-allowedp *fn2-lm-test-receipt* *fn2-lm-test-witness* :damaged recovered)
        (fn2-lm-recovery-allowedp *fn2-lm-test-receipt* *fn2-lm-test-witness* :unknown recovered)
        (not (fn2-lm-recovery-allowedp *fn2-lm-test-receipt* *fn2-lm-test-witness* :intact recovered)))))

; ROUND2 E.5 row 4: older consistent image, every independent witness absent.
(assert-event
 (let ((recovered (list *fn2-lm-test-b1*)))
   (and (fn2-lm-recovery-allowedp *fn2-lm-test-rollback* *fn2-lm-test-witness* :intact recovered)
        (fn2-lm-recovery-allowedp *fn2-lm-test-receipt* *fn2-lm-test-broad* :intact recovered)
        (fn2-lm-recovery-allowedp
         (append *fn2-lm-test-receipt* '((:crash))) *fn2-lm-test-witness* :intact recovered))))

; E.4: a complete batch without any client acknowledgement may be adopted.
(defconst *fn2-lm-test-unacked*
  (list (list :submit-batch *fn2-lm-test-b1*)
        '(:batch-writes-complete 1 (body-a manifest-a)) '(:crash)))
(assert-event
 (and (fn2-lm-recovery-allowedp *fn2-lm-test-unacked* *fn2-lm-test-honest* :intact nil)
      (fn2-lm-recovery-allowedp *fn2-lm-test-unacked* *fn2-lm-test-honest*
                                :intact (list *fn2-lm-test-b1*))))

; A write whose completion was lost can also have landed completely.
(assert-event
 (fn2-lm-recovery-allowedp
  (list (list :submit-batch *fn2-lm-test-b1*) '(:crash) '(:survives 1))
  *fn2-lm-test-honest* :intact (list *fn2-lm-test-b1*)))

; E.4: checksum position alone is not evidence of a harmless torn tail.
(defconst *fn2-lm-test-tail* (append *fn2-lm-test-unacked* '((:bad-tail 1))))
(assert-event
 (and (fn2-lm-recovery-allowedp *fn2-lm-test-tail* *fn2-lm-test-honest* :torn-tail nil)
      (not (fn2-lm-recovery-allowedp *fn2-lm-test-tail* *fn2-lm-test-honest* :intact nil))
      (fn2-lm-recovery-allowedp *fn2-lm-test-tail* *fn2-lm-test-broad* :unknown nil)
      (not (fn2-lm-recovery-allowedp *fn2-lm-test-tail* *fn2-lm-test-broad* :torn-tail nil))
      (not (fn2-lm-recovery-allowedp *fn2-lm-test-tail* *fn2-lm-test-broad* :damaged nil))))

; A malformed acknowledged tail is later destruction, not a permitted crash
; tear. Broad recovery reports uncertainty instead of hiding the lost batch.
(assert-event
 (let ((trace (append *fn2-lm-test-ack-trace* '((:bad-tail 2)))))
   (and (not (fn2-lm-no-destructionp (fn2-lm-trace-state trace)))
        (fn2-lm-recovery-allowedp trace *fn2-lm-test-broad*
                                  :unknown (list *fn2-lm-test-b1*))
        (not (fn2-lm-recovery-allowedp trace *fn2-lm-test-honest*
                                       :torn-tail (list *fn2-lm-test-b1*)))
        (fn2-lm-recovery-allowedp (append trace '((:crash))) *fn2-lm-test-broad*
                                  :unknown (list *fn2-lm-test-b1*)))))

; Every transition checks its ordering, predecessor and dependency premises.
(assert-event
 (let* ((s (fn2-lm-step (list :submit-batch *fn2-lm-test-b1*) (fn2-lm-initial)))
        (s2 (fn2-lm-step (list :submit-batch *fn2-lm-test-b2*) s)))
   (and (fn2-lm-event-allowedp '(:batch-writes-complete 1 (body-a manifest-a)) s)
        (fn2-lm-event-allowedp '(:batch-writes-complete 1 (manifest-a body-a)) s)
        (not (fn2-lm-event-allowedp '(:batch-writes-complete 1 (body-a)) s))
        (not (fn2-lm-event-allowedp '(:fence-ok 1) s))
        (not (fn2-lm-event-allowedp '(:acknowledge 1) s))
        (not (fn2-lm-event-allowedp '(:bad-tail 1) s))
        (not (fn2-lm-event-allowedp '(:rollback 0) s))
        (not (fn2-lm-event-allowedp '(:present-frontier receipt 1) s))
        (not (fn2-lm-event-allowedp '(:survives 1) s))
        (not (fn2-lm-event-allowedp '(:corrupt-required 1) s))
        (not (fn2-lm-event-allowedp '(:bogus 1) s))
        (not (fn2-lm-event-allowedp '(:submit-batch (2 0 nil nil)) s))
        (not (fn2-lm-event-allowedp '(:submit-batch (2 1 nil (x x))) s))
        ; Completing/fencing batch 2 first cannot acknowledge past batch 1.
        (not (fn2-lm-event-allowedp '(:acknowledge 2)
              (fn2-lm-step '(:fence-ok 2)
               (fn2-lm-step '(:batch-writes-complete 2 (body-b)) s2)))))))

(assert-event
 (and (not (fn2-lm-recovery-allowedp '((:bogus)) *fn2-lm-test-honest* :intact nil))
      (not (fn2-lm-recovery-allowedp '((:crash) . bad) *fn2-lm-test-honest* :intact nil))
      (not (fn2-lm-recovery-allowedp nil *fn2-lm-test-honest* :intact nil))
      (not (fn2-lm-recovery-allowedp *fn2-lm-test-ack-trace* *fn2-lm-test-honest*
                                    :intact (list *fn2-lm-test-b2*)))))

; Seat repair: without A-INTEGRITY-EVIDENCE corruption carries no detection
; claim, but a recovery that reports it is not refused for doing so.
(assert-event
 (let ((recovered (list *fn2-lm-test-b1*)))
   (and (fn2-lm-recovery-allowedp *fn2-lm-test-corrupt* *fn2-lm-test-no-integrity* :damaged recovered)
        (fn2-lm-recovery-allowedp *fn2-lm-test-corrupt* *fn2-lm-test-no-integrity* :unknown recovered)
        (not (fn2-lm-recovery-allowedp *fn2-lm-test-corrupt* *fn2-lm-test-no-integrity* :torn-tail recovered)))))
