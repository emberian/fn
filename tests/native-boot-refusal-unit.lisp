; Actual-world discrimination controls for the native recovery diagnostic.
(in-package "ACL2")
(include-book "../books/host-boundary")

(assert-event
 (equal *fn2-host-boot-recovery-detail*
        (position-eq :recovery (fn2-machine-declared 'fn2-boot :stops (w state)))))

(assert-event
 (equal (fn2-host-boot-refusal-class
         t *fn2-stop-reason-kind* *fn2-boot-kind* *fn2-host-boot-recovery-detail* :ok *fn2-recovery-machine-state-done* *fn2-rec-class-unknown* 1 0 *fn2-rec-assume-fence* 0)
        :broad-dirty-tail-unknown))

; Removing identifying input 1 must not retain the diagnosis.
(assert-event
 (equal (fn2-host-boot-refusal-class
         :different *fn2-stop-reason-kind* *fn2-boot-kind* *fn2-host-boot-recovery-detail* :ok *fn2-recovery-machine-state-done* *fn2-rec-class-unknown* 1 0 *fn2-rec-assume-fence* 0)
        :other-stop))

; Removing identifying input 2 must not retain the diagnosis.
(assert-event
 (equal (fn2-host-boot-refusal-class
         t :different *fn2-boot-kind* *fn2-host-boot-recovery-detail* :ok *fn2-recovery-machine-state-done* *fn2-rec-class-unknown* 1 0 *fn2-rec-assume-fence* 0)
        :other-stop))

; Removing identifying input 3 must not retain the diagnosis.
(assert-event
 (equal (fn2-host-boot-refusal-class
         t *fn2-stop-reason-kind* :different *fn2-host-boot-recovery-detail* :ok *fn2-recovery-machine-state-done* *fn2-rec-class-unknown* 1 0 *fn2-rec-assume-fence* 0)
        :other-stop))

; Removing identifying input 4 must not retain the diagnosis.
(assert-event
 (equal (fn2-host-boot-refusal-class
         t *fn2-stop-reason-kind* *fn2-boot-kind* :different :ok *fn2-recovery-machine-state-done* *fn2-rec-class-unknown* 1 0 *fn2-rec-assume-fence* 0)
        :other-stop))

; Removing identifying input 5 must not retain the diagnosis.
(assert-event
 (equal (fn2-host-boot-refusal-class
         t *fn2-stop-reason-kind* *fn2-boot-kind* *fn2-host-boot-recovery-detail* :different *fn2-recovery-machine-state-done* *fn2-rec-class-unknown* 1 0 *fn2-rec-assume-fence* 0)
        :other-stop))

; Removing identifying input 6 must not retain the diagnosis.
(assert-event
 (equal (fn2-host-boot-refusal-class
         t *fn2-stop-reason-kind* *fn2-boot-kind* *fn2-host-boot-recovery-detail* :ok :different *fn2-rec-class-unknown* 1 0 *fn2-rec-assume-fence* 0)
        :other-stop))

; Removing identifying input 7 must not retain the diagnosis.
(assert-event
 (equal (fn2-host-boot-refusal-class
         t *fn2-stop-reason-kind* *fn2-boot-kind* *fn2-host-boot-recovery-detail* :ok *fn2-recovery-machine-state-done* :different 1 0 *fn2-rec-assume-fence* 0)
        :other-stop))

; Removing identifying input 8 must not retain the diagnosis.
(assert-event
 (equal (fn2-host-boot-refusal-class
         t *fn2-stop-reason-kind* *fn2-boot-kind* *fn2-host-boot-recovery-detail* :ok *fn2-recovery-machine-state-done* *fn2-rec-class-unknown* :different 0 *fn2-rec-assume-fence* 0)
        :other-stop))

; Removing identifying input 9 must not retain the diagnosis.
(assert-event
 (equal (fn2-host-boot-refusal-class
         t *fn2-stop-reason-kind* *fn2-boot-kind* *fn2-host-boot-recovery-detail* :ok *fn2-recovery-machine-state-done* *fn2-rec-class-unknown* 1 :different *fn2-rec-assume-fence* 0)
        :other-stop))

; Removing identifying input 10 must not retain the diagnosis.
(assert-event
 (equal (fn2-host-boot-refusal-class
         t *fn2-stop-reason-kind* *fn2-boot-kind* *fn2-host-boot-recovery-detail* :ok *fn2-recovery-machine-state-done* *fn2-rec-class-unknown* 1 0 :different 0)
        :other-stop))

; Removing identifying input 11 must not retain the diagnosis.
(assert-event
 (equal (fn2-host-boot-refusal-class
         t *fn2-stop-reason-kind* *fn2-boot-kind* *fn2-host-boot-recovery-detail* :ok *fn2-recovery-machine-state-done* *fn2-rec-class-unknown* 1 0 *fn2-rec-assume-fence* :different)
        :other-stop))
