; INTERNAL retained-claim transforms. The owner entry proves actual C source,
; current BODY and same-slot history before calling; these list arguments
; cannot issue, refund, promote or establish a receipt.
(in-package "ACL2")
(include-book "account-adoption-turn")

(defun fn-act-suspend (token output current)
 (declare (xargs :guard t))
 (if (and (fn-act-livep token current)
          (eq (fn-cp-nth 2 current) :reserved)
          (eq (fn-cp-nth 4 current) :operation-select)
          (fn-cado-widthp 6 output)
          (eq (fn-cp-nth 0 output) :account-config-suspension)
          (fn-cado-widthp 6 (fn-cp-nth 9 current))
          (eq (fn-cp-nth 0 (fn-cp-nth 9 current)) :account-turn-reservation))
     (mv :account-turn-retained
         (update-nth 8 output (update-nth 2 :suspended current)))
   (mv :account-return-pending current)))

(defun fn-act-rebind (token slot nonce current)
 (declare (xargs :guard t))
 (let ((intent (fn-cp-nth 9 current)))
  (if (and (fn-act-livep token current)
           (eq (fn-cp-nth 2 current) :suspended)
           (eq (fn-cp-nth 4 current) :operation-select)
           (fn-cado-widthp 6 (fn-cp-nth 8 current))
           (eq (fn-cp-nth 0 (fn-cp-nth 8 current)) :account-config-suspension)
           (fn-cado-widthp 6 intent)
           (eq (fn-cp-nth 0 intent) :account-turn-reservation)
           (natp slot) (natp nonce) (natp (fn-cp-nth 5 intent))
           (equal slot (fn-cp-nth 4 intent))
           (< (fn-cp-nth 5 intent) nonce))
      (mv :account-turn-rebound
          (update-nth 9 (update-nth 5 nonce (update-nth 4 slot intent))
                      (update-nth 2 :reserved current)))
    (mv :account-continuation-changed current))))
