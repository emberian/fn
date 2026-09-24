; One ordered physical namespace: kind 5, dispatch 6/v2, attempt 8/v1,
; and result 9/v1.  A changed session must not silently settle the attempt.
(in-package "ACL2")
(include-book "../../books/bp-fnbs-family-replay")
(include-book "../../books/bp-node-debt")
(include-book "../../books/codec-attach")
(include-book "bp-fnbs-codec-tests")

(defconst *bpnfrw-held* (fn-bpn-nth 3 *bpnfc-anchored-record*))
(defconst *bpnfrw-identity*
  (fn-bpah-held-primary-identity *bpnfrw-held*))
(defconst *bpnfrw-dispatch*
  (fn-bpnp-dispatch-record 9 1 0 *bpnfrw-identity* *bpnfc-peer*))
(defconst *bpnfrw-attempt*
  (fn-bpnp-forward-attempt-record
   9 2 0 *bpnfrw-identity* *bpnfc-peer* (cons 1 1) 0))
(defconst *bpnfrw-result*
  (fn-bpnp-forward-result-record
   9 3 0 *bpnfrw-identity* 9 2 (cons 1 1) :sent))
(defun bpnfrw-rows ()
  (list (list (fn-bpnf-stored-record-name 9 0)
              (fn-bpnf-stored-record-frame *bpnfc-anchored-record*))
        (list (fn-bpnf-stored-record-name 9 1)
              (fn-bpnp-dispatch-frame *bpnfrw-dispatch*))
        (list (fn-bpnf-stored-record-name 9 2)
              (fn-bpnp-attempt-frame *bpnfrw-attempt*))
        (list (fn-bpnf-stored-record-name 9 3)
              (fn-bpnp-result-frame *bpnfrw-result*))))
(defun bpnfrw-replay ()
  (fn-bpnf-family-replay-rows (bpnfrw-rows) *bpnfc-base*))

(assert-event (equal (car (bpnfrw-replay)) :ready))
(assert-event (equal (fn-bpn-nth 3 (bpnfrw-replay)) (cons 9 3)))
(assert-event (equal (fn-bpn-nth 4 (bpnfrw-replay)) 1))
(assert-event
 (equal (fn-bpn-nth 12 (car (fn-bpn-nth 1 (bpnfrw-replay))))
        '(:dispatch-done)))
(assert-event
 (null (fn-bpn-nth 13 (car (fn-bpn-nth 1 (bpnfrw-replay))))))
(assert-event
 (equal (fn-bpnd-held-debt
         (car (fn-bpn-nth 1 (bpnfrw-replay))) *bpnfc-local*)
        1))
(assert-event
 (equal (car (fn-bpnf-family-replay-rows
              (append (take 3 (bpnfrw-rows))
                      (list (list (fn-bpnf-stored-record-name 9 3)
                                  (fn-bpnp-result-frame
                                   (fn-bpnp-forward-result-record
                                    9 3 0 *bpnfrw-identity* 9 2
                                    (cons 1 2) :sent)))))
              *bpnfc-base*))
        :fault))
