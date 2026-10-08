; MEM-013 phase 2 blocker. Load the five unchanged draft definitions as
; described in phase2-blocker.md before sending this event to proof_repl.
; This is a counterexample to the unconditional signed statement, not a
; proposed replacement theorem or a claim about a guarded served call.
(in-package "ACL2")

(defthm m13-keeps-w-length-counterexample
  (let* ((mem '(nil nil nil nil nil nil))
         (pw '(0 (0 0 0 0 0)
                 ((0 2047 nil) (0 0 nil) (0 0 nil) (0 0 nil) (0 0 nil))))
         (res (fn-his-place-run 1 '((:other 1 nil)) 0 pw '(1 2 3 4 5) 6 mem)))
    (and (equal (mv-nth 0 res) :done)
         (equal (pgs-w-length mem) 0)
         (equal (pgs-w-length (mv-nth 3 res)) 2049)))
  :hints (("Goal" :in-theory
           (enable fn-his-place-run fn-his-place-row fn-his-rcs-put
                   fn-his-rc-put fn-hp-x-put update-pgs-wi update-pgs-di
                   pgs-w-length)))
  :rule-classes nil)
