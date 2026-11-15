; Actual scanner-to-ownership initialization boundary. Source obligations;
; admission and the full candidate/projection preservation bridge remain open.
(in-package "ACL2")
(include-book "../books/recovery-frontier")
(defthm fn2-recovery-frontier-done-initializes-ownership-cursor
 (implies
  (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
       (eq (mv-nth 0 (fn2-recovery-frontier-step id fn2-core)) :done))
  (let ((next (mv-nth 1 (fn2-recovery-frontier-step id fn2-core))))
   (and (equal (fn2-machine-rc-stage id next) 5)
        (equal (fn2-machine-rc-own-token id next) 0)
        (equal (fn2-machine-rc-own-left id next) 0))))
 :hints (("Goal" :in-theory (enable fn2-recovery-frontier-step)))
 :rule-classes nil)
