; runs-served certifies with identity before ordered. Its callers can already
; have loaded the overview and addressing schemas when they include that book.
(in-package "ACL2")
(include-book "../books/ordered")
(include-book "std/testing/must-fail" :dir :system)

; A schema outside the certified assembly must still invalidate its replay.
(must-fail
 (encapsulate ()
   (local (table fn2-schemas 'fn2-extra-schema '(:id 999)))
   (include-book "../books/runs-served")))

(include-book "../books/runs-served")
(make-event
 (let ((assembled (fn2-rs-assembled (w state)))
       (declared (strip-cars (fn2-decl-rows :schema (w state)))))
   (if (and (member-eq 'fn2-overview assembled)
            (member-eq 'fn2-identity-evidence assembled)
            (set-equalp-eq declared assembled))
       (value '(value-triple :assembled))
     (er soft 'runs-assembly-import-order "Assembled ~x0, declared ~x1."
         assembled declared))))
