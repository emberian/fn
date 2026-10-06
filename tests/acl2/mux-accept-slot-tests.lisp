; Tests of books/mux-accept-slot.lisp (r71 F13): the pending-accept slot.
(in-package "ACL2")
(include-book "../../books/mux-accept-slot")

; SATISFIABLE: two open loops, both free: the cursor's loop is reserved, and
; round robin moves on with the cursor.
(assert-event (equal (fn-mxa-reserve 0 '((nil 0 nil) (nil 0 nil)) nil) '(:reserved 0)))
(assert-event (equal (fn-mxa-reserve 1 '((nil 0 nil) (nil 0 nil)) nil) '(:reserved 1)))
(assert-event (equal (fn-mxa-reserve 3 '((nil 0 nil) (nil 0 nil)) nil) '(:reserved 1)))
; The first loop holds a pending socket: the free one is taken.
(assert-event (equal (fn-mxa-reserve 0 '((nil 1 nil) (nil 0 nil)) nil) '(:reserved 1)))

; TEETH: every loop holds a pending socket, a reservation or is closed: the
; named deferral, never a reservation (the r2 red: 29 sockets accepted).
(assert-event (equal (fn-mxa-reserve 0 '((nil 1 nil) (t 0 nil)) nil)
                     '(:deferred :pending-accept-bound)))
(assert-event (equal (fn-mxa-reserve 5 '((nil 1 nil) (nil 0 t)) nil)
                     '(:deferred :pending-accept-bound)))
; A stopping service, or none: refused by name.
(assert-event (equal (fn-mxa-reserve 0 '((nil 0 nil)) t) '(:refused :stopping)))
(assert-event (equal (fn-mxa-reserve 0 nil nil) '(:refused :stopping)))

; The bound, concretely: after the grant every loop holds at most one and
; the total is at most the loop count.
(assert-event
 (let* ((loops '((nil 1 nil) (nil 0 nil)))
        (r (fn-mxa-reserve 0 loops nil))
        (after (fn-mxa-grant (cadr r) loops)))
   (and (fn-mxa-at-most-one-each after)
        (equal (fn-mxa-pending-total after) 2))))

; The line.
(assert-event (equal (fn-mxa-deferral-line '((nil 1 nil) (t 0 nil)))
                     "accept deferred reason=pending-accept-bound pending=2 loops=2"))
