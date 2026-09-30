(in-package "ACL2")
(include-book "../../books/decoded-window-read")
(include-book "decoded-window-begin-tests")
; KEYSTONE fn-pwz-begin-captures-typed-request. REACHABLE POSITIVE.
; The helper executes the actual constructor on local concrete stobjs.
(assert-event
 (let* ((token '(:decoded-window 17 7 100 320 120 40 200 99 250 0))
        (z (car (pwzt-initializer token))))
   (and (fn-pwz-tokenp token) (fn-pwz-plan-matches-token z token))))
; KEYSTONE fn-pwz-begin-captures-typed-request. HYPOTHESIS-REMOVAL.
; Logical corrupted request: the only antecedent is the omitted typed-token
; predicate. This violates the constructor's served guard, not a native job.
(local
 (defthm pwzt-begin-kind-removal
   (let ((token '(:window 17 7 100 320 120 40 200 99 250 0)))
     (and (not (fn-pwz-tokenp token))
          (not (fn-pwz-plan-matches-token
                 (mv-nth 0 (fn-pwz-begin token 301 pgs-digest-state
                             fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)) token))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-pwz-plan-matches-token fn-pwz-tokenp)))))
; Full decoded publication/read positives await shared typed physical
; lifecycle and the real decoder/dictionary byte trajectory.
