; Exact-line boundary teeth; no production dependency on this book.
(in-package "ACL2")
(include-book "../../books/post-header-line")

; The positive witness asserts the complete text premise and conclusion.
(assert-event
 (let ((text '(68 97 116 101 58 32 120)))
   (and (fn-pb-line-textp text)
        (fn-pb-fixed-linep (+ 2 (len text))
                           (append text '(13 10 13 10 65 13 10))))))

; Removing line-textp is false: a prior blank line is not part of one line.
(assert-event
 (let ((text '(68 97 116 101 58 32 120 13 10 13 10 65)))
   (and (not (fn-pb-line-textp text))
        (not (fn-pb-fixed-linep (+ 2 (len text))
                                (append text '(13 10)))))))

; Final-pair-only checking would accept this adversarial span.
(assert-event
 (let ((x '(65 13 10 13 10 66 13 10)))
   (and (equal (nth 6 x) 13) (equal (nth 7 x) 10)
        (not (fn-pb-fixed-linep 8 x)))))

(assert-event
 (and (not (fn-pb-fixed-linep 4 '(65 66 13)))
      (not (fn-pb-fixed-linep 4 '(65 66 13 65)))
      (not (fn-pb-fixed-linep 4 '(65 10 13 10)))
      (fn-pb-fixed-linep 4 '(65 66 13 10 13 10))))
