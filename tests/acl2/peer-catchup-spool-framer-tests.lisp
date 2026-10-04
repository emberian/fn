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

; Teeth: fn-csp-framer-window-accounts-for-every-octet. A window that yields
; mid-record returns exactly the unconsumed tail, and its emission is the
; per-octet reference over the consumed prefix (the transmit dot doubled).
(assert-event
 (let* ((input (cons 46 (make-list 511 :initial-element 120)))
        (f (fn-csp-framer 1 nil))
        (w (fn-csp-framer-window f input)))
   (and (equal (nth 4 w) 511)
        (equal (nth 3 w) (nthcdr 511 input))
        (equal (nth 2 w) (fn-csp-framer-emit f (take 511 input)))
        (equal (nth 1 w) (fn-csp-framer-after f (take 511 input)))
        (equal (take 2 (nth 2 w)) '(46 46)))))
; Receive across a CR split: two windows emit what one pass over the whole emits.
(assert-event
 (let* ((f (fn-csp-framer 1 t))
        (a (fn-csp-framer-window f '(46 46 120 13)))
        (b (fn-csp-framer-window (nth 1 a) '(10))))
   (equal (append (nth 2 a) (nth 2 b))
          (fn-csp-framer-emit f '(46 46 120 13 10)))))
