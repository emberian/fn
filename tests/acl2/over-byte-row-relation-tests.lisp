(in-package "ACL2")
(include-book "../../books/over-byte-row-relation")

(defconst *obcrt-source*
 (append (fn-record-string-octets "Subject: a") '(13 10 32 98 13 10)
 (fn-record-string-octets "From: c") '(13 10)
 (fn-record-string-octets "Date: d") '(13 10)
 (fn-record-string-octets "Message-ID: <e@x>") '(13 10)
 (fn-record-string-octets "References: <r@x>") '(13 10 13 10 122 13 10)))

(defthm obcrt-actual-feed-row-positive
 (let* ((fn-arena (list *obcrt-source*)) (number 7)
 (parser (fn-lpc-feed *obcrt-source* (fn-lpc-begin 0 (len *obcrt-source*) '(:origin 7)))))
 (and (equal (fn-lpc-verdict parser) :valid)
 (or (not (fn-lpc-field parser 0)) (natp (fn-lpc-at 1 (fn-lpc-field parser 0))))
 (or (not (fn-lpc-field parser 1)) (natp (fn-lpc-at 1 (fn-lpc-field parser 1))))
 (or (not (fn-lpc-field parser 2)) (natp (fn-lpc-at 1 (fn-lpc-field parser 2))))
 (or (not (fn-lpc-field parser 3)) (natp (fn-lpc-at 1 (fn-lpc-field parser 3))))
 (or (not (fn-lpc-field parser 4)) (natp (fn-lpc-at 1 (fn-lpc-field parser 4))))
 (equal (fn-npw-remaining (fn-obc-parser-pieces number parser) 0 fn-arena)
   (append
    (fn-nov-line number
      (list :ok (fn-record-string-octets (fn-hnov-subject (fn-lpc-nov-value parser fn-arena)))
                (fn-record-string-octets (fn-hnov-from (fn-lpc-nov-value parser fn-arena)))
                (fn-record-string-octets (fn-hnov-date (fn-lpc-nov-value parser fn-arena)))
                (fn-record-string-octets (fn-hnov-msgid (fn-lpc-nov-value parser fn-arena)))
                (fn-record-string-octets (fn-hnov-references (fn-lpc-nov-value parser fn-arena)))
                (nfix (fn-lpc-at 1 parser)) (fn-lpc-body-lines parser)))
    '(13 10)))))
 :rule-classes nil)

; Corrupted-state removal of literal field 0 start premise.
(defthm obcrt-row-without-field-0-start-corrupted-state
 (let* ((fn-arena '((65 66))) (number 7)
 (parser (list 0 2 '(:origin 7) 2
 (list :body nil nil nil nil nil nil nil (list '(0 -1 2 (:origin 7)) nil nil nil nil))
 4 '(:line 1) nil)))
 (and (not (or (not (fn-lpc-field parser 0)) (natp (fn-lpc-at 1 (fn-lpc-field parser 0)))))
 (or (not (fn-lpc-field parser 1)) (natp (fn-lpc-at 1 (fn-lpc-field parser 1))))
 (or (not (fn-lpc-field parser 2)) (natp (fn-lpc-at 1 (fn-lpc-field parser 2))))
 (or (not (fn-lpc-field parser 3)) (natp (fn-lpc-at 1 (fn-lpc-field parser 3))))
 (or (not (fn-lpc-field parser 4)) (natp (fn-lpc-at 1 (fn-lpc-field parser 4))))
 (not (equal (fn-npw-remaining (fn-obc-parser-pieces number parser) 0 fn-arena)
   (append
    (fn-nov-line number
      (list :ok (fn-record-string-octets (fn-hnov-subject (fn-lpc-nov-value parser fn-arena)))
                (fn-record-string-octets (fn-hnov-from (fn-lpc-nov-value parser fn-arena)))
                (fn-record-string-octets (fn-hnov-date (fn-lpc-nov-value parser fn-arena)))
                (fn-record-string-octets (fn-hnov-msgid (fn-lpc-nov-value parser fn-arena)))
                (fn-record-string-octets (fn-hnov-references (fn-lpc-nov-value parser fn-arena)))
                (nfix (fn-lpc-at 1 parser)) (fn-lpc-body-lines parser)))
    '(13 10))))))
 :rule-classes nil)

; Corrupted-state removal of literal field 1 start premise.
(defthm obcrt-row-without-field-1-start-corrupted-state
 (let* ((fn-arena '((65 66))) (number 7)
 (parser (list 0 2 '(:origin 7) 2
 (list :body nil nil nil nil nil nil nil (list nil '(0 -1 2 (:origin 7)) nil nil nil))
 4 '(:line 1) nil)))
 (and (or (not (fn-lpc-field parser 0)) (natp (fn-lpc-at 1 (fn-lpc-field parser 0))))
 (not (or (not (fn-lpc-field parser 1)) (natp (fn-lpc-at 1 (fn-lpc-field parser 1)))))
 (or (not (fn-lpc-field parser 2)) (natp (fn-lpc-at 1 (fn-lpc-field parser 2))))
 (or (not (fn-lpc-field parser 3)) (natp (fn-lpc-at 1 (fn-lpc-field parser 3))))
 (or (not (fn-lpc-field parser 4)) (natp (fn-lpc-at 1 (fn-lpc-field parser 4))))
 (not (equal (fn-npw-remaining (fn-obc-parser-pieces number parser) 0 fn-arena)
   (append
    (fn-nov-line number
      (list :ok (fn-record-string-octets (fn-hnov-subject (fn-lpc-nov-value parser fn-arena)))
                (fn-record-string-octets (fn-hnov-from (fn-lpc-nov-value parser fn-arena)))
                (fn-record-string-octets (fn-hnov-date (fn-lpc-nov-value parser fn-arena)))
                (fn-record-string-octets (fn-hnov-msgid (fn-lpc-nov-value parser fn-arena)))
                (fn-record-string-octets (fn-hnov-references (fn-lpc-nov-value parser fn-arena)))
                (nfix (fn-lpc-at 1 parser)) (fn-lpc-body-lines parser)))
    '(13 10))))))
 :rule-classes nil)

; Corrupted-state removal of literal field 2 start premise.
(defthm obcrt-row-without-field-2-start-corrupted-state
 (let* ((fn-arena '((65 66))) (number 7)
 (parser (list 0 2 '(:origin 7) 2
 (list :body nil nil nil nil nil nil nil (list nil nil '(0 -1 2 (:origin 7)) nil nil))
 4 '(:line 1) nil)))
 (and (or (not (fn-lpc-field parser 0)) (natp (fn-lpc-at 1 (fn-lpc-field parser 0))))
 (or (not (fn-lpc-field parser 1)) (natp (fn-lpc-at 1 (fn-lpc-field parser 1))))
 (not (or (not (fn-lpc-field parser 2)) (natp (fn-lpc-at 1 (fn-lpc-field parser 2)))))
 (or (not (fn-lpc-field parser 3)) (natp (fn-lpc-at 1 (fn-lpc-field parser 3))))
 (or (not (fn-lpc-field parser 4)) (natp (fn-lpc-at 1 (fn-lpc-field parser 4))))
 (not (equal (fn-npw-remaining (fn-obc-parser-pieces number parser) 0 fn-arena)
   (append
    (fn-nov-line number
      (list :ok (fn-record-string-octets (fn-hnov-subject (fn-lpc-nov-value parser fn-arena)))
                (fn-record-string-octets (fn-hnov-from (fn-lpc-nov-value parser fn-arena)))
                (fn-record-string-octets (fn-hnov-date (fn-lpc-nov-value parser fn-arena)))
                (fn-record-string-octets (fn-hnov-msgid (fn-lpc-nov-value parser fn-arena)))
                (fn-record-string-octets (fn-hnov-references (fn-lpc-nov-value parser fn-arena)))
                (nfix (fn-lpc-at 1 parser)) (fn-lpc-body-lines parser)))
    '(13 10))))))
 :rule-classes nil)

; Corrupted-state removal of literal field 3 start premise.
(defthm obcrt-row-without-field-3-start-corrupted-state
 (let* ((fn-arena '((65 66))) (number 7)
 (parser (list 0 2 '(:origin 7) 2
 (list :body nil nil nil nil nil nil nil (list nil nil nil '(0 -1 2 (:origin 7)) nil))
 4 '(:line 1) nil)))
 (and (or (not (fn-lpc-field parser 0)) (natp (fn-lpc-at 1 (fn-lpc-field parser 0))))
 (or (not (fn-lpc-field parser 1)) (natp (fn-lpc-at 1 (fn-lpc-field parser 1))))
 (or (not (fn-lpc-field parser 2)) (natp (fn-lpc-at 1 (fn-lpc-field parser 2))))
 (not (or (not (fn-lpc-field parser 3)) (natp (fn-lpc-at 1 (fn-lpc-field parser 3)))))
 (or (not (fn-lpc-field parser 4)) (natp (fn-lpc-at 1 (fn-lpc-field parser 4))))
 (not (equal (fn-npw-remaining (fn-obc-parser-pieces number parser) 0 fn-arena)
   (append
    (fn-nov-line number
      (list :ok (fn-record-string-octets (fn-hnov-subject (fn-lpc-nov-value parser fn-arena)))
                (fn-record-string-octets (fn-hnov-from (fn-lpc-nov-value parser fn-arena)))
                (fn-record-string-octets (fn-hnov-date (fn-lpc-nov-value parser fn-arena)))
                (fn-record-string-octets (fn-hnov-msgid (fn-lpc-nov-value parser fn-arena)))
                (fn-record-string-octets (fn-hnov-references (fn-lpc-nov-value parser fn-arena)))
                (nfix (fn-lpc-at 1 parser)) (fn-lpc-body-lines parser)))
    '(13 10))))))
 :rule-classes nil)

; Corrupted-state removal of literal field 4 start premise.
(defthm obcrt-row-without-field-4-start-corrupted-state
 (let* ((fn-arena '((65 66))) (number 7)
 (parser (list 0 2 '(:origin 7) 2
 (list :body nil nil nil nil nil nil nil (list nil nil nil nil '(0 -1 2 (:origin 7))))
 4 '(:line 1) nil)))
 (and (or (not (fn-lpc-field parser 0)) (natp (fn-lpc-at 1 (fn-lpc-field parser 0))))
 (or (not (fn-lpc-field parser 1)) (natp (fn-lpc-at 1 (fn-lpc-field parser 1))))
 (or (not (fn-lpc-field parser 2)) (natp (fn-lpc-at 1 (fn-lpc-field parser 2))))
 (or (not (fn-lpc-field parser 3)) (natp (fn-lpc-at 1 (fn-lpc-field parser 3))))
 (not (or (not (fn-lpc-field parser 4)) (natp (fn-lpc-at 1 (fn-lpc-field parser 4)))))
 (not (equal (fn-npw-remaining (fn-obc-parser-pieces number parser) 0 fn-arena)
   (append
    (fn-nov-line number
      (list :ok (fn-record-string-octets (fn-hnov-subject (fn-lpc-nov-value parser fn-arena)))
                (fn-record-string-octets (fn-hnov-from (fn-lpc-nov-value parser fn-arena)))
                (fn-record-string-octets (fn-hnov-date (fn-lpc-nov-value parser fn-arena)))
                (fn-record-string-octets (fn-hnov-msgid (fn-lpc-nov-value parser fn-arena)))
                (fn-record-string-octets (fn-hnov-references (fn-lpc-nov-value parser fn-arena)))
                (nfix (fn-lpc-at 1 parser)) (fn-lpc-body-lines parser)))
    '(13 10))))))
 :rule-classes nil)

(defthm obcrt-span-positive
 (let ((span '(0 0 5 (:origin 7))) (fn-arena '((65 13 10 9 66))))
 (and (or (not span) (natp (fn-lpc-at 1 span)))
 (equal (fn-npw-part-bytes (fn-obc-span-piece span) 0 fn-arena) (fn-lpc-span-value span fn-arena))
 (equal (fn-npw-part-bytes (fn-obc-span-piece span) 0 fn-arena) '(65 32 66))))
 :rule-classes nil)

(defthm obcrt-span-without-start-corrupted-state
 (let ((span '(0 -1 2 (:origin 7))) (fn-arena '((65 66))))
 (and (not (or (not span) (natp (fn-lpc-at 1 span))))
 (not (equal (fn-npw-part-bytes (fn-obc-span-piece span) 0 fn-arena) (fn-lpc-span-value span fn-arena)))))
 :rule-classes nil)
