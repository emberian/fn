(in-package "ACL2")
(include-book "../../books/bp-session-profile")
(assert-event (equal (fn-bpsp-read nil) '(2 1 nil 30000 120000 600000)))
(assert-event (equal (fn-bpsp-read (fn-bpsp-write 2 3 nil 40000 7000 90000)) '(2 3 nil 40000 7000 90000)))
(assert-event (equal (fn-bpsp-read (fn-bpsp-write 0 1 20000000 10 1 1)) '(0 1 20000000 10 1 1)))
(assert-event (not (fn-bpsp-read '(105 110 98 111 117 110 100 32 48 10 105 110 98 111 117 110 100 32 49))))
(assert-event (not (fn-bpsp-read '(105 110 98 111 117 110 100 32 49 13 10))))
(assert-event
 (let* ((p '(2 1 nil 30000 120000 600000)) (dynamic 100000000) (store 1000) (held 1000)
        (g (fn-bpsp-startup p 1000 1000 dynamic store held)))
  (and (equal (car g) :hold)
       (<= (+ store held (second g)) dynamic)
       (<= (+ (third g) (* (+ (fifth g) (sixth g)) (fourth g))) (second g)))))
; Literal hypothesis removal: refusal is not a capacity certificate. ACL2's
; logic totalizes the arithmetic on the refused answer; expose it with NFIX.
(assert-event
 (let* ((p '(2 1 nil 30000 120000 600000)) (dynamic 1) (store 1000) (held 1000)
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

; S025: the no-progress bounds are profile rows, positive and bounded; the
; accessors read what the host captures at startup.
(assert-event (equal (fn-bpsp-passive-ms (fn-bpsp-read (fn-bpsp-write 2 1 nil 30000 4000 5000))) 4000))
(assert-event (equal (fn-bpsp-stall-ms (fn-bpsp-read (fn-bpsp-write 2 1 nil 30000 4000 5000))) 5000))
(assert-event (equal (fn-bpsp-passive-ms (fn-bpsp-read nil)) 120000))
(assert-event (equal (fn-bpsp-stall-ms (fn-bpsp-read nil)) 600000))
; Teeth: a zero bound is the unbounded hole, and a bound past 2^32 is unrepresentable.
(assert-event (not (fn-bpsp-write 2 1 nil 30000 0 5000)))
(assert-event (not (fn-bpsp-write 2 1 nil 30000 4000 0)))
(assert-event (not (fn-bpsp-write 2 1 nil 30000 (expt 2 32) 5000)))
(assert-event (not (fn-bpsp-write 2 1 nil 30000 4000 (expt 2 32))))
(assert-event (not (fn-bpsp-profilep '(2 1 nil 30000 4000))))
(assert-event (not (fn-bpsp-read (append (fn-bpsp-write 2 1 nil 30000 4000 5000)
                                         '(112 97 115 115 105 118 101 45 109 115 32 49 10)))))
; the legacy four-row file still reads, with the default bounds
(assert-event (equal (fn-bpsp-read '(105 110 98 111 117 110 100 32 50 10 111 117 116 98 111 117 110 100 32 49 10))
                     '(2 1 nil 30000 120000 600000)))

; S025: contention is a waiting peer AND a full incoming class.
(assert-event (fn-bpsp-incoming-contended t 2 2))
(assert-event (fn-bpsp-incoming-contended t 3 2))
; Teeth: remove each hypothesis in turn.
(assert-event (not (fn-bpsp-incoming-contended nil 2 2)))
(assert-event (not (fn-bpsp-incoming-contended t 1 2)))
(assert-event (not (fn-bpsp-incoming-contended t 0 2)))
(assert-event (not (fn-bpsp-incoming-contended t nil 2)))
(assert-event (not (fn-bpsp-incoming-contended t 2 nil)))
