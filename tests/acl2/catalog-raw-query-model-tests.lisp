(in-package "ACL2")
(include-book "../../books/catalog-raw-query-model")

; These are the reference semantics the retained operational query must meet.
; They do not assert the current host lookup has been replaced or refined.
(assert-event
 (let* ((a (fn-record-make 2 2 0 "<same>" '(65) '("g") "o" "s" "e" 1 0))
        (b (fn-record-make 4 4 0 "<other>" '(66) '("g") "o" "s" "e" 1 0))
        (c (fn-record-make 8 8 0 "<same>" '(67) '("g") "o" "s" "e" 1 0))
        (rows (list a b c)))
   (and (fn-record-p a) (fn-record-p b) (fn-record-p c)
        ; Row zero remains an answer, rather than a false/absence value.
        (equal (fn-craw-first-accepted-row "<same>" rows 10) 0)
        ; The answer is a catalog ordinal, not the Store sequence four.
        (equal (fn-craw-first-accepted-row "<other>" rows 10) 1)
        (equal (fn-craw-first-accepted-row "<absent>" rows 10) nil))))

; Append beyond the captured Store frontier must not enter the query result.
; At the later frontier the exact same row becomes eligible; this does not
; transfer the later query's result to the earlier capture.
(assert-event
 (let* ((old (fn-record-make 4 4 0 "<old>" '(65) '("g") "o" "s" "e" 1 0))
        (new (fn-record-make 10 10 0 "<new>" '(66) '("g") "o" "s" "e" 1 0))
        (rows (list old new)))
   (and (fn-record-p old) (fn-record-p new)
        (equal (fn-craw-first-accepted-row "<new>" rows 10) nil)
        (equal (fn-craw-first-accepted-row "<new>" rows 11) 1))))
