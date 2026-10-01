(defun fnn-owner-serialized-with-control-turn
 (service cid callback &optional (class :control) epilogue)
 "Pass actual slot/nonce/slots/pool through one scheduler quantum.
CALLBACK is preconstructed by its funded caller and returns five CL values:
word, answer, actual slots, pool and STATE. Retain effects before classification.
No numeric BODY or supplied receipt is accepted."
 (let ((binding (fnn-owner-service-control-binding service)))
  (if (not binding) (values :owner-control-unavailable :refused)
   (fnn-with-owner-control-issued-turn (binding slot nonce slots pool)
    (multiple-value-prog1
     (fnn-owner-gated (service class)
      (when (fnn-owner-service-stopping service)
       (fnn-refuse "owner service is stopping"))
      (fnn-owner-shared-action-locked service cid
       (lambda ()
        (multiple-value-bind (word answer next-slots next-pool next-state)
            (funcall callback slot nonce slots pool)
         (when next-slots (setf slots next-slots))
         (when next-pool (setf pool next-pool))
         (when next-state (setf *the-live-state* next-state))
         (unless (and next-slots next-pool next-state)
          (fnn-fixed-callback-fail 'fn-ats-prepay-body-internal
                                   :control-body-missing-state nil))
         (values word answer)))))
     ; The actual scheduler cleanup has returned. The caller must already
     ; have relinquished its registered private aliases; NIL here alone is
     ; not a retirement receipt. The static epilogue leaves ATS slots readonly.
     (setf callback nil)
     (when epilogue
      (multiple-value-bind (word next-pool next-state)
          (funcall epilogue slot nonce slots pool)
       (when next-pool (setf pool next-pool))
       (when next-state (setf *the-live-state* next-state))
       (unless (and next-pool next-state (member word '(:account-turn-returned :account-turn-not-owned)))
        (fnn-fixed-callback-fail 'fn-owner-account-turn-return
                                 :control-epilogue-incomplete word)))))))))
