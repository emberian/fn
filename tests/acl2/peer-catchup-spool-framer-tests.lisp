(in-package "ACL2")
(include-book "../../books/peer-catchup-spool-framer")

(assert-event
 (equal (fn-csp-framer-window (fn-csp-framer 1 t) '(46 46 120 13 10))
        '(:record-end (t nil nil 0 t) (46 120 13 10) nil 5)))
(assert-event
 (equal (fn-csp-framer-window (fn-csp-framer 1 nil) '(46 120 13 10))
        '(:record-end (t nil nil 0 nil) (46 46 120 13 10) nil 4)))
(assert-event
 (let* ((first (fn-csp-framer-window (fn-csp-framer 1 t) '(120 13)))
        (second (fn-csp-framer-window (cadr first) '(10))))
   (and (equal first '(:need (nil t nil 1 t) (120) nil 2))
        (equal second '(:record-end (t nil nil 0 t) (13 10) nil 1)))))
(assert-event
 (equal (car (fn-csp-framer-window (fn-csp-framer 1 t) '(46 13 10))) :refused))
(assert-event
 (equal (fn-csp-framer-window (fn-csp-framer 2 t) '(13 10 120 13 10))
        '(:record-end (t nil nil 0 t) (13 10 120 13 10) nil 5)))
(assert-event
 (equal (fn-csp-framer-window (fn-csp-framer 1 t) '(120 13 13 10))
        '(:record-end (t nil nil 0 t) (120 13 13 10) nil 4)))
(assert-event
 (let* ((input (cons 46 (make-list 511 :initial-element 120)))
        (first (fn-csp-framer-window (fn-csp-framer 1 nil) input))
        (second (fn-csp-framer-window (cadr first) (cadddr first))))
   (and (eq (car first) :yield) (equal (len (caddr first)) 512)
        (equal (cadddr first) '(120)) (equal (nth 4 first) 511)
        (eq (car second) :need) (equal (caddr second) '(120))
        (equal (nth 4 second) 1))))
(assert-event (equal (fn-csp-append-admit 511 512 '(13 10)) '(:refused 511 511)))
(assert-event (equal (fn-csp-append-admit 510 512 '(13 10)) '(:write 510 512)))
(assert-event
 (equal (fn-csp-append-admit 0 (expt 2 63) nil) '(:refused 0 0)))
