(in-package "ACL2")
(include-book "../../books/bp-session-profile")
(assert-event (equal (fn-bpsp-read nil) '(2 1 nil 30000)))
(assert-event (equal (fn-bpsp-read (fn-bpsp-write 2 3 nil 40000)) '(2 3 nil 40000)))
(assert-event (equal (fn-bpsp-read (fn-bpsp-write 0 1 20000000 10)) '(0 1 20000000 10)))
(assert-event (not (fn-bpsp-read '(105 110 98 111 117 110 100 32 48 10 105 110 98 111 117 110 100 32 49))))
(assert-event (not (fn-bpsp-read '(105 110 98 111 117 110 100 32 49 13 10))))
(assert-event
 (let* ((p '(2 1 nil 30000)) (dynamic 100000000) (store 1000) (held 1000)
        (g (fn-bpsp-startup p 1000 1000 dynamic store held)))
  (and (equal (car g) :hold)
       (<= (+ store held (second g)) dynamic)
       (<= (+ (third g) (* (+ (fifth g) (sixth g)) (fourth g))) (second g)))))
; Literal hypothesis removal: refusal is not a capacity certificate. ACL2's
; logic totalizes the arithmetic on the refused answer; expose it with NFIX.
(assert-event
 (let* ((p '(2 1 nil 30000)) (dynamic 1) (store 1000) (held 1000)
        (g (fn-bpsp-startup p 1000 1000 dynamic store held)))
  (and (not (equal (car g) :hold))
       (not (<= (+ store held (nfix (second g))) dynamic)))))
(assert-event
 (let ((row '(:bp-session-grant 2 1 :incoming nil nil)) (observation :socket-closed))
  (and (not (fifth row)) (member-equal observation '(:no-socket :socket-closed))
       (not (equal (car (fn-bpsg-step row observation)) :settle)))))
(assert-event
 (let ((row '(:bp-session-grant 2 1 :incoming t nil)) (observation :socket-closed))
  (and (not (not (fifth row))) (member-equal observation '(:no-socket :socket-closed))
       (equal (car (fn-bpsg-step row observation)) :settle))))
(assert-event
 (let ((row '(:bp-session-grant 2 1 :incoming nil t)) (observation :no-context))
  (and (not (fifth row)) (not (member-equal observation '(:no-socket :socket-closed)))
       (equal (car (fn-bpsg-step row observation)) :settle))))
(assert-event
 (equal (fn-bpsg-step '(:bp-session-grant 2 7 :outgoing nil t) :rearm-socket)
        '(:retain (:bp-session-grant 2 7 :outgoing nil nil))))
(assert-event
 (equal (car (fn-bpsg-step '(:bp-session-grant 2 7 :outgoing nil nil) :rearm-socket)) :fault))
(assert-event (not (fn-bpsg-release-ready t t nil nil nil nil nil)))

(assert-event (equal (fn-bpsg-context-abort-plan nil nil nil nil nil) :retire-context))
(assert-event (equal (fn-bpsg-context-abort-plan t nil nil nil nil) :retain-context))
(assert-event (equal (fn-bpsg-context-abort-plan nil '(:root) nil nil nil) :retain-context))
(assert-event (equal (fn-bpsg-context-abort-plan nil nil '(:token) nil nil) :retain-context))
(assert-event (equal (fn-bpsg-context-abort-plan nil nil nil '(:source) nil) :retain-context))
(assert-event (equal (fn-bpsg-context-abort-plan nil nil nil nil t) :retain-context))
; Logical terminal alone cannot invent a physical return receipt.
(assert-event (equal (car (fn-bpsg-step '(:bp-session-grant 2 1 :incoming nil nil)
                                        :released-context)) :retain))
