; B5 keystones over the actual recovery machine: the B3 commit fixture runs on
; the real core, adapter and router; the device dies; post-death faults act on
; the durable image; B5's recovery row runs on the fresh core. Statements are
; owed (not proofs); their teeth are evaluated in tests/recovery-proof-unit.
(in-package "ACL2")
(include-book "commit-proof")
(include-book "owed")
(fn2-book-layer :b)

(defun fn2-recovery-proof-run (commands profile mode members seed faults)
 (declare (xargs :verify-guards nil))
 (fn2-commit-proof-run-faults commands profile mode members seed faults))
; The B1 state of the run's projected trace; an untranslatable trace is invalid.
(defun fn2-recovery-proof-state (result)
 (declare (xargs :verify-guards nil))
 (mv-let (code trace) (fn2-history-translate (fn2-commit-proof-events result))
  (if (eq code :ok) (fn2-lm-trace-state trace)
   (update-fn2-lm-state-valid nil (fn2-lm-initial)))))

; Under honest fences and no later destruction of durable data, every
; acknowledged batch is in the recovered history, whatever the class.
(defthm-owed fn2-recovery-never-shortens-intact (commands profile mode members seed faults)
 (let* ((r (fn2-recovery-proof-run commands profile mode members seed faults))
        (s (fn2-recovery-proof-state r)))
  (implies (and (fn2-commit-proof-admitted r) (fn2-cm-profilep profile)
                (fn2-cm-persistence-fence profile)
                (fn2-lm-state-valid s) (fn2-lm-no-destructionp s))
           (fn2-lm-acknowledged-in-historyp (fn2-lm-state-acknowledged s)
                                           (fn2-commit-proof-recovered r))))
 :teeth (fn2-recovery-proof-intact-baseline fn2-recovery-proof-intact-fua
         fn2-recovery-proof-fence-removal fn2-recovery-proof-destruction-removal)
 :schema :crash :doc "Actual B5 recovery after the B3 fixture's death on the tiny profile, genesis arena; post-death faults are the harness's. Not a theorem for arbitrary adapters or checkpointed arenas (B6).")

; Under a profile that is not crash-only, a dirty tail (the harness's ground
; truth names its first defective batch) is never called torn or intact.
(defthm-owed fn2-recovery-broad-bad-tail-unknown (commands profile mode members seed faults)
 (let* ((r (fn2-recovery-proof-run commands profile mode members seed faults))
        (s (fn2-recovery-proof-state r)))
  (implies (and (fn2-commit-proof-admitted r) (fn2-cm-profilep profile)
                (not (eq (fn2-cm-profile-kind profile) :crash-only))
                (fn2-lm-state-valid s) (fn2-lm-state-bad-tail s))
           (member-eq (fn2-commit-proof-classification r) '(:unknown :damaged))))
 :teeth (fn2-recovery-proof-broad-tail fn2-recovery-proof-crash-only-tail)
 :schema :crash :doc "Classification by the machine's own evidence (dirty arena) and the profile bits it is given; the harness's bad-tail observation is independent ground truth from the manifests.")

; A rollback is reported detected only with A-INDEPENDENT-FRONTIER and a
; presented witness beyond the recovered history.
(defthm-owed fn2-recovery-rollback-needs-witness (commands profile mode members seed faults)
 (let* ((r (fn2-recovery-proof-run commands profile mode members seed faults))
        (s (fn2-recovery-proof-state r)))
  (implies (and (fn2-commit-proof-admitted r)
                (eq (fn2-commit-proof-outcome r) :rollback-detected))
           (and (fn2-cm-independent-frontier profile)
                (fn2-lm-conflicting-witness (fn2-lm-state-witnesses s)
                                            (fn2-commit-proof-recovered r)))))
 :teeth (fn2-recovery-proof-witnessed-rollback fn2-recovery-proof-unwitnessed-rollback
         fn2-recovery-proof-uncredited-witness fn2-recovery-proof-consistent-witness)
 :schema :crash :doc "The witness is a presented receipt (commit, seal) compared with the reconstructed chain (scholar ch. 4 item 10); local state alone never detects rollback.")
