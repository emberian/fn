;;; Exact scalar NOV metadata fixture in the runner's real saved image.
;;; No core definitions or host dispatches are replaced.
(in-package "ACL2")
(let* ((over '(:ok (83) (70) (68) (60 109 62) nil
                   123456789012345678901234567890 10000000000))
       (expected '(55 9 83 9 70 9 68 9 60 109 62 9 9
                   49 50 51 52 53 54 55 56 57 48 49 50 51 52 53 54 55 56 57 48
                   49 50 51 52 53 54 55 56 57 48 9 49 48 48 48 48 48 48 48 48 48 48))
       (row (fnn-core 'fn-nov-line 7 over))
       (framed (fnn-core 'fn-nntp-multi nil "224 overview" (list row))))
  (unless (equal row expected) (error "Wide NOV metadata changed: ~s" row))
  (unless (equal framed
                 (fnn-core 'fn-nntp-make-result nil
                           (list (fnn-core 'fn-nntp-reply-effect
                                 (append '(50 50 52 32 111 118 101 114 118 105 101 119 13 10)
                                         expected '(13 10 46 13 10))))))
    (error "Wide NOV semantic framing changed: ~s" framed))
  (unless (equal (fnn-core 'fn-nov-line 7 '(:ok nil nil nil nil nil 0 2))
                 '(55 9 9 9 9 9 9 48 9 50))
    (error "Ordinary NOV metadata changed"))
  (unless (equal (fnn-core 'fn-nntp-decimal-field 10000000000) '(48))
    (error "Status number renderer changed"))
  (format t "NATIVE-NOV-METADATA exact wide and ordinary rows; semantic framing passed~%"))
(sb-ext:exit :code 0)
