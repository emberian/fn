(in-package "ACL2")
(include-book "../../books/msgid-query-state")

; A later physical candidate may carry the earliest catalog ordinal, even
; after another exact match was confirmed. Ordinal zero remains a real hit.
(assert-event
 (let* ((q (fn-miq-make '(:index-query 7) 3 '(9) 4 10 1 "<same>" 1
                        '(0 1 5) 3 nil :candidate))
        (a (mv-list 2 (fn-miq-confirm q 3 8 "<same>")))
        (q1 (fn-miq-with-progress (mv-nth 1 a) '(0 1 9) 0
                                  (fn-miq-best (mv-nth 1 a)) :candidate))
        (b (mv-list 2 (fn-miq-confirm q1 0 2 "<same>"))))
   (and (equal (mv-nth 0 a) :continue)
        (equal (fn-miq-best (mv-nth 1 a)) 3)
        (equal (fn-miq-answer (mv-nth 1 a)) nil)
        (equal (mv-nth 0 b) :continue)
        (equal (fn-miq-best (mv-nth 1 b)) 0)
        (equal (fn-miq-answer (mv-nth 1 b)) nil)
        (equal (fn-miq-answer
                (fn-miq-with-progress (mv-nth 1 b) '(0 0 0) nil 0 :done)) 0))))

; The same keyed tag can name a different exact Message-ID. A rejected tag
; collision clears pending but cannot change the retained best candidate.
(assert-event
 (let* ((q (fn-miq-make '(:index-query 7) 3 '(9) 4 10 1 "<same>" 1
                        '(0 1 5) 1 3 :candidate))
        (a (mv-list 2 (fn-miq-confirm q 1 4 "<collision>"))))
   (and (equal (mv-nth 0 a) :continue)
        (equal (fn-miq-best (mv-nth 1 a)) 3)
        (equal (fn-miq-pending (mv-nth 1 a)) nil)
        (equal (fn-miq-answer (mv-nth 1 a)) nil))))

; Corrupted captured-row/frontier evidence cannot be reported as absence.
(assert-event
 (let* ((q (fn-miq-make '(:index-query 7) 3 '(9) 4 10 1 "<same>" 1
                        '(0 1 5) 1 nil :candidate))
        (a (mv-list 2 (fn-miq-confirm q 1 10 "<same>"))))
   (and (equal (mv-nth 0 a) :recovery-required)
        (equal (mv-nth 1 a) q)
        (equal (fn-miq-phase (mv-nth 1 a)) :candidate))))
