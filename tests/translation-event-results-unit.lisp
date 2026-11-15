; Actual live-world macro invocation controls, independent of application load.
(in-package "ACL2")
(include-book "../books/translation-validation")
(include-book "std/testing/must-fail" :dir :system)

; Use a real checked function, not a fabricated export or replacement body.
(fn2-tv-check-function (fn2-tv-function 'fn2-tv-codes (w state)) 'fn2-tv-codes)
(fn2-tv-check-manifest (fn2-tv-manifest (w state)))
(fn2-tv-check-arm-inventory (fn2-tv-arm-inventory (w state)))
(fn2-tv-check-functions
 (list (cons 'fn2-tv-codes (fn2-tv-function 'fn2-tv-codes (w state)))))
(fn2-tv-check-packed-functions
 (list (cons 'fn2-tv-codes (fn2-tv-function 'fn2-tv-codes (w state)))))

; Preserve name/formals/guard/ABI; change only this actual function's body.
(must-fail
 (fn2-tv-check-function
  (update-nth 5 (fn2-tv-object '(quote nil))
              (fn2-tv-function 'fn2-tv-codes (w state)))
  'fn2-tv-codes))
(must-fail (fn2-tv-check-manifest nil))
(must-fail (fn2-tv-check-arm-inventory '(:invented-arm)))
(must-fail (fn2-tv-check-functions '((fn2-tv-codes))))
(must-fail (fn2-tv-check-packed-functions '((fn2-tv-codes))))
; This small tooling world has no served root: refusal must stay a refusal.
(must-fail (fn2-tv-check-served-closure nil nil))
