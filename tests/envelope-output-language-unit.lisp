(in-package "ACL2")
(include-book "../sim/envelope-output-language")
(assert-event
 (and (fn2-eo-language-p '((:exact 1) (:prefix 2 3) (:exact 4)) '(1 2 4))
      (not (fn2-eo-language-p '((:exact 1) (:prefix 2 3) (:exact 4)) '(1 3 4)))
      (not (fn2-eo-language-p '((:prefix . bad)) nil))
      (not (fn2-eo-language-p '((:exact 300)) '(300)))
      (not (fn2-eo-language-p '((:exact 1)) '(1 . bad)))))
; A prefix may skip its current byte and use the following row. Omitting
; that disjunct rejects this valid empty prefix.
(assert-event
 (let* ((following '((:exact 2))) (rest '(3)) (peer '(2)))
  (and (equal (fn2-eo-language-row following peer) '(t nil))
       (equal (fn2-eo-language-row (cons (cons :prefix rest) following) peer) '(t nil))
       (fn2-eo-language-p (cons '(:prefix 1 3) following) peer)
       (not (and (consp peer) (equal 1 (car peer))
                 (cadr (fn2-eo-language-row (cons (cons :prefix rest) following) peer)))))))
; Exact and prefix differ at the zero-length choice; both consume matching bytes.
(assert-event
 (and (equal (fn2-eo-language-row '((:exact 1) (:exact 2)) '(1 2)) '(t nil nil))
      (equal (fn2-eo-language-row '((:prefix 1) (:exact 2)) '(1 2)) '(t t nil))))
