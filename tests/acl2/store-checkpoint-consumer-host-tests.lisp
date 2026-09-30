(in-package "ACL2")
(include-book "../../host/store-checkpoint-consumer-host")

; Seeded loader-metadata mutation fixture. This executes the actual PROGRAM
; readout; it does not assert an authenticated parse or account publication.
(make-event
 (let* ((cp '(:consumer-state (1) (2) 7 1 nil
              (:authority 1 2 (:ns) (:rows) nil)))
        (publication (list :ok cp '(:account-root 7 (:index) (:credentials)) 7))
        (checkpoint (list :fn-store-checkpoint nil nil nil publication nil nil))
        (state (f-put-global 'fn-store-sco-checkpoint checkpoint state))
        (state (f-put-global 'fn-store-sco-recovery-source '(:verified-checkpoint) state))
        (state (f-put-global 'fn-store-sco-recovery-source-generation 4 state))
        (observed (fn-store-sco-consumer-publication-value state))
        (state (f-put-global 'fn-store-sco-recovery-source nil state))
        (unavailable (fn-store-sco-consumer-publication-value state)))
  (if (and (equal observed (list :checkpoint-consumer 4 publication))
           (equal unavailable '(:unavailable :checkpoint-consumer)))
      (value '(value-triple :passed))
    (er soft 'consumer-publication-test "Wrong same-source readout"))))
