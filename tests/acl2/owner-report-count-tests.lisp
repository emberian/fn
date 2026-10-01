(in-package "ACL2")
(include-book "../../books/owner-report-count")

; Reachable complete antecedent and complete conclusion of the count boundary.
(assert-event
 (let* ((source '(a b c)) (cursor (fn-orc-count-begin source)))
   (mv-let (word result) (fn-orc-count-run 4 cursor)
     (and (natp 4) (fn-orc-countp cursor)
          (equal word :counted) (equal (nth 2 result) (len source))))))

; Completion removal: every remaining entry/domain premise is true,
; omitted status is affirmatively false, and the final-count conclusion fails.
(assert-event
 (let* ((source '(a b c)) (cursor (fn-orc-count-begin source)))
   (mv-let (word result) (fn-orc-count-run 1 cursor)
     (and (natp 1) (fn-orc-countp cursor)
          (equal word :yield) (not (equal word :counted))
          (not (equal (nth 2 result) (len source)))))))

(assert-event
 (let ((cursor (fn-orc-count-begin '(a b c))))
   (mv-let (word result) (fn-orc-count-run 0 cursor)
     (and (equal word :yield) (equal result cursor)))))
