; Actual scanner-to-ownership initialization boundary. Source obligations;
; admission and the full candidate/projection preservation bridge remain open.
(in-package "ACL2")
(include-book "../books/recovery-frontier")
(defthm fn2-recovery-frontier-done-initializes-ownership-cursor
 (implies
  (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
       (eq (mv-nth 0 (fn2-recovery-frontier-step id fn2-core)) :done))
  (let ((fn2-core (mv-nth 1 (fn2-recovery-frontier-step id fn2-core))))
   (and (equal (fn2-machine-rc-stage id fn2-core) 5)
        (equal (fn2-machine-rc-own-token id fn2-core) 0)
        (equal (fn2-machine-rc-own-left id fn2-core) 0))))
 :hints (("Goal" :in-theory (enable fn2-recovery-frontier-step)))
 :rule-classes nil)

; Source-only stronger postcondition: :done preserves the authenticated
; current unit and its actual source while initializing ownership. This is
; valid for both full-base and selected callers; it asserts no new identity
; admission premise and does not claim that authentication proves uniqueness.
(include-book "recovery-frontier-done-frame")
(defthm fn2-recovery-frontier-done-enters-authenticated-ownership
 (implies
  (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
       (equal (mv-nth 0 (fn2-recovery-frontier-step id fn2-core)) :done))
  (let ((after (mv-nth 1 (fn2-recovery-frontier-step id fn2-core))))
   (and
    (equal (fn2-machine-rc-stage id after) 5)
    (equal (fn2-machine-rc-own-token id after) 0)
    (equal (fn2-machine-rc-own-left id after) 0)
    (fn2-rp-current-unit-auth-p id (fn2-machine-generation id fn2-core) after)
    (fn2-rp-current-source-p id after)
    (equal (fn2-recovery-selected-current-p id after)
           (fn2-recovery-selected-current-p id fn2-core))
    (equal (fn2-recovery-frontier-source-binding id after)
           (fn2-recovery-frontier-source-binding id fn2-core))
    (stobj-let ((fn2-mk (fn2-core-mk after))
                (fn2-journal-members (fn2-core-journal-members after))) (complete)
     (and (equal (fn2-mk-size 0 fn2-mk) (fn2-machine-rc-frontier-last id fn2-core))
          (equal (fn2-journal-members-next-event 0 fn2-journal-members)
                 (+ 1 (fn2-machine-rc-frontier-last id fn2-core)))) complete))))
 :rule-classes nil
 :hints (("Goal" :in-theory
  (enable fn2-recovery-frontier-step fn2-rp-current-unit-auth-p
          fn2-rp-current-unit-row-p fn2-rp-auth-hash-current-p
          fn2-rp-current-source-p fn2-recovery-selected-current-p))))
