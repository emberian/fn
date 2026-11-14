; Actual ACL2 completion/effect controls for the canonical list primitive pilot.
(in-package "ACL2")

(assert-event
 (and (natp 3) (true-listp '(11 22))
      (equal (update-nth 3 99 '(11 22)) '(11 22 nil 99))
      (equal (nth 0 (update-nth 3 99 '(11 22))) 11)
      (equal (nth 2 (update-nth 3 99 '(11 22))) nil)
      (equal (nth 3 (update-nth 3 99 '(11 22))) 99)))

; This bridge's canonical call interface is partial on indices. ACL2 itself
; completes a negative index to zero; omitting the domain premise changes meaning.
(defthm fn2-list-negative-index-completion
 (and (not (natp -1))
      (equal (nth -1 '(11 22)) 11)
      (equal (update-nth -1 99 '(11 22)) '(99 22)))
 :rule-classes nil)

; List completion is not restricted to proper input lists.
(defthm fn2-list-dotted-tail-completion
 (and (equal (nth 1 '(11 . 22)) nil)
      (equal (update-nth 2 99 '(11 . 22)) '(11 nil 99)))
 :rule-classes nil)

; Same target value, corrupted unrelated sibling: scalar-only equality is weak.
(assert-event
 (let* ((correct (update-nth 1 99 '(11 22)))
        (mutant (update-nth 0 999 correct)))
   (and (equal (nth 1 correct) 99) (equal (nth 1 mutant) 99)
        (not (equal correct mutant)) (not (equal (nth 0 correct) (nth 0 mutant))))))

; ACL2 permits this rational insertion; the integer-only Val representation
; must explicitly refuse its representation instead of silently choosing zero.
(assert-event
 (and (equal (update-nth 1 1/2 '(11 22)) '(11 1/2))
      (not (integerp (nth 1 (update-nth 1 1/2 '(11 22)))))))
