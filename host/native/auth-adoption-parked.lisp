;;; PARKED at stage 0 (2026-10-01; planning/design-store-representation-2026-10-01.md
;;; section 4, D46, MODE 2026-10-01 section 2b): fnn-native-auth-adopt-config of
;;; host/native/auth.lisp (Codex, fd2d31660 and after), moved here unchanged
;;; from e9a2a0ba9^ so the code stays in the tree; host/native/auth.lisp is
;;; the 7aad444ce direct path again.  No build loads this file: the account
;;; adoption host chain (host/account-adoption*-host.lisp,
;;; host/native/account-adoption.lisp) is out of the image build (D46).  It
;;; returns with the adoption producer (stage-0 unwired item 5): the owner
;;; control binding, compiled rows and operation source, the typed C joins;
;;; then fnn-native-auth-install routes through this function again.

(in-package "ACL2")

;;; NOTREADY source join: owner adoption begin/tick and typed account prepare/
;;; finish must be installed together with the operation census and restart
;;; producer. This caller deliberately has no direct-set-config fallback.
(defun fnn-native-auth-adopt-config (service config bindings)
  ;; The core uses actual CP incarnation/transaction coordinate for this
  ;; nonauthorizing candidate. No entropy observation is requested before the
  ;; genuine issuer; NIL records absence and confers no uniqueness authority.
  (let ((entropy nil))
    (multiple-value-bind (word answer)
        (fnn-owner-serialized-with-control-turn
          service nil
          (lambda (slot nonce slots pool)
            (let ((result (fnn-account-adoption-begin
                            config bindings entropy slot nonce slots pool)))
              (fnn-account-retain-control-effects service result)
              (setf config nil bindings nil entropy nil)
              (multiple-value-prog1 (values-list result) (setf result nil))))
          :control #'fnn-account-adoption-epilogue)
      (declare (ignore answer))
      ;; The outer issuer exposes only core word/answer after scheduler
      ;; cleanup. Missing installed binding invokes no allocating callback.
      (unless (eq word :yield)
        (return-from fnn-native-auth-adopt-config
          (case word
            (:accepted :accepted)
            (:recovery-required (fnn-indeterminate "account begin requires recovery"))
            ((:refused :unavailable :owner-control-unavailable) :refused)
            (otherwise (fnn-fault "malformed account begin result"))))))
    (loop
      (multiple-value-bind (word answer)
          (fnn-owner-serialized-with-control-turn
            service nil
            (lambda (slot nonce slots pool)
              (let* ((result (fnn-account-adoption-tick slot nonce slots pool))
                     (retained (fnn-account-retain-control-effects service result))
                     (slots (third retained)) (pool (fourth retained))
                     (step (fnn-core 'fn-cado-result-action retained))
                     (kind (fnn-core 'fn-cad-action-kind step)))
                (when (member kind '(:publish :configure))
                  (let* ((publication
                         (if (eq kind :configure)
                             (fnn-owner-account-configuration-publication-locked
                               service slot nonce slots pool)
                           (fnn-owner-account-publication-locked service slot nonce slots pool)))
                         (retained-publication (fnn-account-retain-control-effects service publication))
                         (next-slots (third retained-publication))
                         (next-pool (fourth retained-publication))
                         (published (fnn-core 'fn-cado-result-action retained-publication)))
                    (setf result publication)
                    (when (eq (fnn-core 'fn-cad-action-kind published) :durable)
                      ; The pooled collector still reads the registered
                      ; genuine outcome internally, never this transport word.
                      (setf result (fnn-account-adoption-collect slot nonce next-slots next-pool))
                      (fnn-account-retain-control-effects service result))
                    (setf publication nil retained-publication nil published nil)))
                (setf step nil retained nil)
                (multiple-value-prog1 (values-list result) (setf result nil))))
            :control #'fnn-account-adoption-epilogue)
        (declare (ignore answer))
        (case word
          (:yield nil)
          (:accepted (return :accepted))
          ((:refused :unavailable :owner-control-unavailable) (return :refused))
          (:recovery-required
           (fnn-indeterminate "account authority adoption requires recovery"))
          (otherwise (fnn-fault "owner returned malformed account adoption action")))))))

