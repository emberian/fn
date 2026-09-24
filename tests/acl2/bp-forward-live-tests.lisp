; Direct outer-step smoke for the durable attempt/result callback sequence.
; The separate N04 teeth book supplies two actual received kind-5 rows.
(in-package "ACL2")
(include-book "../../books/bp-node-progress")
(include-book "../../books/codec-attach")
(include-book "bp-forward-attempt-tests")

(defconst *bpnfl-base*
  (fn-bpn-initial-machine-state *bpnfa-config* 8 1048576))
(defconst *bpnfl-s0*
  (fn-bpnp-with-credit
   (fn-bpnf-state-with-arrival
    *bpnfl-base* (list *bpnfa-h1*) nil nil nil nil nil 9 3 1)
   2 2))
(defconst *bpnfl-session* (cons 1 1))
(defun bpnfl-open ()
  (fn-bpnp-step
   *bpnfl-s0*
   (list :session *bpnfa-peer* *bpnfl-session* t 32768 *bpnfa-obs*)))
(defun bpnfl-proposal () (car (fn-bpnf-answer-effects (bpnfl-open))))
(defun bpnfl-attempt-durable ()
  (fn-bpnp-step
   (fn-bpnf-answer-state (bpnfl-open))
   (list :persist-result 9 3 :durable)))
(defun bpnfl-send () (car (fn-bpnf-answer-effects (bpnfl-attempt-durable))))
(defun bpnfl-result-proposal ()
  (fn-bpnp-step
   (fn-bpnf-answer-state (bpnfl-attempt-durable))
   (list :forward-result 9 3 *bpnfl-session* :sent *bpnfa-obs*)))
(defun bpnfl-result-effect ()
  (car (fn-bpnf-answer-effects (bpnfl-result-proposal))))
(defun bpnfl-done ()
  (fn-bpnp-step
   (fn-bpnf-answer-state (bpnfl-result-proposal))
   (list :persist-result 9 4 :durable)))

(assert-event
 (equal (fn-bpnp-host-eventp
         (list :session *bpnfa-peer* *bpnfl-session* t 32768 *bpnfa-obs*))
        t))
(assert-event (equal (car (bpnfl-proposal)) :persist-attempt))
(assert-event (equal (fn-bpnp-used (fn-bpnf-answer-state (bpnfl-open))) 2))
(assert-event (equal (fn-bpnp-debt (fn-bpnf-answer-state (bpnfl-open))) 2))
(assert-event (equal (car (bpnfl-send)) :cl-send))
(assert-event
 (equal (fn-bpn-nth 6 (bpnfl-send))
        (fn-bpn-nth 1 (fn-bpnp-forward-image
                      *bpnfa-h1* *bpnfa-local* *bpnfa-obs*))))
(assert-event (equal (fn-bpnp-used (fn-bpnf-answer-state (bpnfl-attempt-durable))) 3))
(assert-event (equal (fn-bpnp-debt (fn-bpnf-answer-state (bpnfl-attempt-durable))) 3))
(assert-event (equal (car (bpnfl-result-effect)) :persist-forward-result))
(assert-event (equal (car (car (fn-bpnf-answer-effects (bpnfl-done)))) :forward-ready))
(assert-event (equal (fn-bpnp-used (fn-bpnf-answer-state (bpnfl-done))) 4))
(assert-event (equal (fn-bpnp-debt (fn-bpnf-answer-state (bpnfl-done))) 1))
(assert-event
 (equal (fn-bpn-nth 12 (car (fn-bpnf-held-list
                            (fn-bpnf-answer-state (bpnfl-done)))))
        '(:dispatch-done)))
