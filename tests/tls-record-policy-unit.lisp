(in-package "ACL2")
(include-book "../books/tls-record-policy")

; Send spans advance across quanta and partial successes; no prefix is replayed.
(assert-event (equal (mv-list 4 (fn2-tls-record-plan t 10 0 0 0 0 0 0 0 0 0 0 0 8 0 4)) '(:act 13 0 4)))
(assert-event (equal (mv-list 3 (fn2-tls-record-result t 0 4 4 0 10)) '(:ok 0 4)))
(assert-event (equal (mv-list 4 (fn2-tls-record-plan t 10 4 0 0 0 0 0 0 0 0 0 0 8 0 4)) '(:act 13 4 4)))
(assert-event (equal (mv-list 3 (fn2-tls-record-result t 0 2 4 4 10)) '(:ok 0 6)))
(assert-event (equal (mv-list 4 (fn2-tls-record-plan t 10 6 0 0 0 0 0 0 0 0 0 0 8 0 4)) '(:act 13 6 4)))
(assert-event (equal (mv-list 3 (fn2-tls-record-result t 0 4 4 6 10)) '(:ok 3 10)))
; Success cannot post while a staged output suffix or BIO output remains.
(assert-event (equal (mv-list 4 (fn2-tls-record-plan t 10 10 0 3 0 0 0 0 0 0 4 2 8 0 4)) '(:act 5 2 2)))
(assert-event (equal (mv-list 4 (fn2-tls-record-plan t 10 10 0 3 0 0 0 0 0 0 4 4 8 3 4)) '(:act 4 0 3)))
(assert-event (equal (mv-list 4 (fn2-tls-record-plan t 10 10 0 3 0 0 0 0 0 0 4 4 8 0 4)) '(:done 0 0 10)))
; WANT with no bytes preserves the retry prefix. Peer progress permits SSL
; retry before fd receive; without progress, receive one bounded ciphertext span.
(assert-event (equal (mv-list 3 (fn2-tls-record-result t 1 0 4 4 10)) '(:ok 1 4)))
(assert-event (equal (mv-list 4 (fn2-tls-record-plan t 10 4 0 1 8 9 0 0 0 0 0 0 8 0 4)) '(:act 13 4 4)))
(assert-event (equal (mv-list 4 (fn2-tls-record-plan t 10 4 0 1 9 9 0 0 0 0 0 0 8 0 4)) '(:act 6 0 4)))
; A contradictory raw WANT/count is retained as a physical prefix, then fails.
(assert-event (equal (mv-list 3 (fn2-tls-record-result t 1 2 4 4 10)) '(:contract 5 6)))
(assert-event (equal (mv-list 4 (fn2-tls-record-plan t 10 6 0 5 9 9 0 0 0 0 0 0 8 0 4)) '(:failed 0 0 6)))
(assert-event (equal (mv-list 3 (fn2-tls-record-result t 0 5 4 4 10)) '(:bounds 5 0)))
; Receive completes its authenticated prefix; it need not fill the whole loan.
(assert-event (equal (mv-list 3 (fn2-tls-record-result nil 0 2 4 0 10)) '(:ok 3 2)))
(assert-event (equal (mv-list 4 (fn2-tls-record-plan nil 10 0 2 3 0 0 0 0 0 0 0 0 8 0 4)) '(:done 0 0 2)))
