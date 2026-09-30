(in-package "ACL2")
(include-book "../../books/consumer-remote-ingress")
(include-book "consumer-account-auth-tests")

(defun fn-crit-request (op login consumer groups cursor seconds)
 (declare (xargs :guard t))
 (list :remote-consumer op login *crat-secret* consumer groups cursor seconds))

;@positive fn-cre-ingress-authenticates-exact-named-current-account
(assert-event
 (let* ((r (fn-crit-request :poll '(97) '(99) nil nil 0))
        (answer (fn-cre-ingress r t 3 (fn-crat-cp) 3
                   (fn-cp-nth 3 (fn-crat-cp)) (fn-crat-pub))))
  (and (eq (car answer) :authenticated) (fn-cre-envelopep r) (equal t t)
       (equal (fn-cra-authenticate (fn-crat-cp) 3 (fn-cp-nth 3 (fn-crat-cp))
                (fn-crat-pub) (fn-cp-nth 2 r) (fn-cp-nth 3 r) t)
              (list :ok (fn-cp-nth 2 answer) (fn-cp-nth 3 answer)
                        (fn-cp-nth 4 answer) (fn-cp-nth 5 answer)))
       (equal (fn-cp-nth 1 answer) r))))

;@hypothesis-removal fn-cre-ingress-authenticates-exact-named-current-account authenticated-result
(assert-event
 (let* ((r (fn-crit-request :poll '(97) '(99) nil nil 0))
        (answer (fn-cre-ingress r nil 3 (fn-crat-cp) 3
                   (fn-cp-nth 3 (fn-crat-cp)) (fn-crat-pub))))
  (and (not (eq (car answer) :authenticated)) (not (equal nil t)))))

; Missing real installation is unavailable, not durability uncertainty.
(assert-event
 (equal (fn-cre-ingress (fn-crit-request :poll '(97) '(99) nil nil 0)
           t 3 (fn-crat-cp) 3 (fn-cp-nth 3 (fn-crat-cp)) nil)
        '(:unavailable :account-authority)))

; The allowlist admits all eight tags; private commands never reach auth.
(assert-event
 (and (fn-cre-envelopep (fn-crit-request :register '(97) '(99) '((97)) nil 0))
      (fn-cre-envelopep (fn-crit-request :rebase '(97) '(99) '((97)) nil 0))
      (fn-cre-envelopep (fn-crit-request :poll '(97) '(99) nil nil 0))
      (fn-cre-envelopep (fn-crit-request :wait '(97) '(99) nil nil 1))
      (fn-cre-envelopep (fn-crit-request :position '(97) '(99) nil nil 0))
      (fn-cre-envelopep (fn-crit-request :status '(97) '(99) nil nil 0))
      (fn-cre-envelopep (fn-crit-request :ack '(97) '(99) nil '(1) 0))
      (fn-cre-envelopep (fn-crit-request :unregister '(97) '(99) nil nil 0))
      (equal (fn-cre-ingress (fn-crit-request :bootstrap '(97) '(99) nil nil 0)
               t 3 (fn-crat-cp) 3 (fn-cp-nth 3 (fn-crat-cp)) (fn-crat-pub))
             '(:refused :request))))

(assert-event
 (let* ((r (fn-crit-request :poll '(97) '(99) nil nil 0))
        (wire (fn-cr-request-encode r 3)))
  (and (equal (fn-cr-request-decode wire t 3) r)
       (equal (fn-cre-header-plan (take 10 wire) t 3)
              (list :receive (- (len wire) 10)))
       (equal (fn-cre-header-plan (take 10 wire) nil 3) '(:refused :protected-channel))
       (equal (fn-cre-header-plan '(70 78 67 84 1 1 0 0 0 0) t 3) '(:refused :frame))
       (equal (fn-cre-header-plan '(70 78 67 82 2 1 0 0 0 0) t 3) '(:refused :frame))
       (equal (fn-cre-header-plan '(70 78 67 82 1 1 255 255 255 255) t 3) '(:refused :frame)))))

; Equal passwords name two distinct current account incarnations. Every WAIT
; invocation sees the supplied current committed projection again.
(assert-event
 (let ((a (fn-cre-ingress (fn-crit-request :wait '(97) '(99) nil nil 1)
            t 3 (fn-crat-cp) 3 (fn-cp-nth 3 (fn-crat-cp)) (fn-crat-pub)))
       (b (fn-cre-ingress (fn-crit-request :wait '(98) '(99) nil nil 1)
            t 3 (fn-crat-cp) 3 (fn-cp-nth 3 (fn-crat-cp)) (fn-crat-pub))))
  (and (eq (car a) :authenticated) (eq (car b) :authenticated)
       (not (equal (fn-cp-nth 3 a) (fn-cp-nth 3 b)))
       (equal (fn-cre-ingress (fn-crit-request :wait '(97) '(99) nil nil 1)
                t 3 (fn-carv-revision-state (fn-crat-cp) 2) 3
                (fn-cp-nth 3 (fn-crat-cp)) (fn-crat-pub))
              '(:unavailable :account-authority)))))

;@positive fn-cre-selected-existing-route-is-exact-account-and-consumer
(assert-event
 (let* ((r (fn-crit-request :poll '(97) '(99) nil nil 0))
        (i (fn-cre-ingress r t 3 (fn-crat-cp) 3 (fn-cp-nth 3 (fn-crat-cp)) (fn-crat-pub)))
        (old (append (fn-cp-entry '(99) (fn-cp-nth 2 i) '(99) 1 (fn-cp-nth 5 i) 1 0)
                      (list '((97)) (fn-cp-nth 3 i))))
        (route (fn-cre-selected-route i old)))
  (and old (eq (car route) :definition-request) (eq (car i) :authenticated)
       (equal (fn-cp-nth 1 old) (fn-cp-nth 4 (fn-cp-nth 1 i)))
       (equal (fn-cp-nth 2 old) (fn-cp-nth 2 i))
       (equal (fn-cp-nth 9 old) (fn-cp-nth 3 i))
       (equal (fn-cp-nth 1 route) '((97))))))

;@hypothesis-removal fn-cre-selected-existing-route-is-exact-account-and-consumer existing-entry
(assert-event
 (let* ((r (fn-crit-request :register '(97) '(99) '((97)) nil 0))
        (i (fn-cre-ingress r t 3 (fn-crat-cp) 3 (fn-cp-nth 3 (fn-crat-cp)) (fn-crat-pub))))
  (and (not nil) (eq (car (fn-cre-selected-route i nil)) :definition-request)
       (not (and (eq (car i) :authenticated)
                  (equal (fn-cp-nth 1 nil) (fn-cp-nth 4 (fn-cp-nth 1 i)))
                  (equal (fn-cp-nth 2 nil) (fn-cp-nth 2 i))
                  (equal (fn-cp-nth 9 nil) (fn-cp-nth 3 i)))))))

;@hypothesis-removal fn-cre-selected-existing-route-is-exact-account-and-consumer accepted-route
(assert-event
 (let* ((r (fn-crit-request :poll '(97) '(99) nil nil 0))
        (i (fn-cre-ingress r t 3 (fn-crat-cp) 3 (fn-cp-nth 3 (fn-crat-cp)) (fn-crat-pub)))
        (old (append (fn-cp-entry '(100) (fn-cp-nth 2 i) '(99) 1 (fn-cp-nth 5 i) 1 0)
                      (list '((97)) (fn-cp-nth 3 i)))))
  (and old (not (eq (car (fn-cre-selected-route i old)) :definition-request))
       (not (and (eq (car i) :authenticated)
                  (equal (fn-cp-nth 1 old) (fn-cp-nth 4 (fn-cp-nth 1 i)))
                  (equal (fn-cp-nth 2 old) (fn-cp-nth 2 i))
                  (equal (fn-cp-nth 9 old) (fn-cp-nth 3 i)))))))

; Refused admission, missing installed authority and I/O absence stay distinct.
(assert-event
 (and (equal (fn-cre-receive-failure '(:refused :operation-budget)) '(:refused :operation-budget))
      (equal (fn-cre-receive-failure '(:unavailable :runtime-operation-source)) '(:unavailable :runtime-operation-source))
      (equal (fn-cre-receive-failure '(:uncertain :persistence)) '(:uncertain :persistence))
      (equal (fn-cre-receive-failure :timeout) '(:unavailable :timeout))))
