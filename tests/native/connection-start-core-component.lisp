;;; Disposable ACL2/SBCL component: real PREPARE/START/ABORT/FINISH and
;;; world-selected callbacks. Installation/costs are synthetic fixtures.
;;; This tests the native boundary, not the complete served owner operation.
(in-package "ACL2")

(defvar *fnn-start-test-owner-lock*
  (sb-thread:make-mutex :name "connection component owner"))

(defun fnn-start-test-fixture (kind)
  (let ((pool (create-fn-page-read-pool))
        (slots (create-fn-allocation-turn-slots))
        (mio (create-fn-mio$c)))
    ;; Unverified ACL2 test setup is deliberately outside the operation.
    (multiple-value-bind (word slots1 mio1 pool1)
        (fn-cost-setup (not (eq kind :absent)) slots mio pool)
      (assert (and (eq word :constructed) (eq slots slots1)
                   (eq mio mio1) (eq pool pool1))))
    (f-put-global 'fn-owner '((nil nil nil 42)) *the-live-state*)
    (f-put-global 'fn-owner-connection-operation-ticket nil *the-live-state*)
    (f-put-global 'fn-owner-connection-operation-installation
      (unless (eq kind :unavailable)
        (list :connection-operation-installation 9
              '(:allocation-epoch-association :runtime :profile :pool 10 1000)
              :synthetic-source 1000 '(40 0 0 0 1)
              (if (eq kind :body-yield) 700 40) 0 0 20))
      *the-live-state*)
    (assert (fn-aec-pool-statep pool))
    (values (fnn-connection-turn-binding-make pool slots 0) mio)))

(defun fnn-start-test-call (callback mio pool)
  (fnn-core-mv 'fn-owner-index-connection-start
    (funcall callback :reader nil nil nil mio pool *the-live-state*)))

(defun fnn-start-test-retained (binding ticket next)
  (let ((pool (fnn-connection-turn-binding-pool binding))
        (slots (fnn-connection-turn-binding-slots binding)))
    (assert (eq (fn-prp-alloc-mode pool) :recovery))
    (assert (= (fn-prp-alloc-active-turns pool) 1))
    (assert (= (fn-prp-alloc-allocated pool) 70))
    (assert (= (fn-ats-noncesi 0 slots) 0))
    (assert (= (fn-ats-phasesi 0 slots) 3))
    (assert (= (fn-prl-nth 2 (fn-owner-page-read-ledger pool)) next))
    (assert (equal ticket (fn-owner-connection-operation-ticket *the-live-state*)))))

(defun fnn-start-test-prepare-then-escape
    (kind family address peer slot slots mio pool state)
  ;; Execute the actual core and then inject loss of its native acknowledgment.
  (multiple-value-prog1
      (fn-owner-index-connection-prepare
        kind family address peer slot slots mio pool state)
    (error "injected escape after actual PREPARE")))

(fnn-install-raw-dispatch)
(dolist (entry '(fn-owner-index-connection-prepare fn-owner-index-connection-start
                 fn-owner-index-connection-finish fn-owner-index-connection-fault))
  (assert (eq (fnn-fixed-raw-callback entry) (symbol-function entry))))

(let ((start (fnn-fixed-raw-callback 'fn-owner-index-connection-start)))
  ;; Same owner -> extent span covers PREPARE, actual provider effects and the
  ;; allocating epilogue. The production caller must establish this span too.
  (dolist (kind '(:success :absent))
    (multiple-value-bind (binding mio) (fnn-start-test-fixture kind)
      (let ((pool (fnn-connection-turn-binding-pool binding))
            (slots (fnn-connection-turn-binding-slots binding))
            (cleanup nil))
        (sb-thread:with-mutex (*fnn-start-test-owner-lock*)
          (sb-thread:with-recursive-lock (*fnn-extent-lock*)
            (multiple-value-bind (word nonce same-mio)
                (fnn-connection-turn-prepare binding :reader nil nil nil mio)
              (assert (and (eq word :prepared) (= nonce 0) (eq mio same-mio)))
              (assert (= (fn-prp-alloc-active-turns pool) 1))
              (assert (= (fn-prp-alloc-allocated pool) 70))
              (assert (= (fn-ats-phasesi 0 slots) 3))
              (assert
                (equal
                  (multiple-value-list
                    (fnn-with-prepaid-connection-turn (binding nonce)
                      (multiple-value-bind (erp result token fuel mio1 pool1 state1)
                          (fnn-start-test-call start mio pool)
                        (assert (and (not erp) (eq mio mio1) (eq pool pool1)
                                     (eq state1 *the-live-state*)))
                        (assert (if (eq kind :success)
                                    (and (eq result :reserved)
                                         (equal token '(:connection-holder 2 1 0)))
                                  (and (eq result :refused) (not token))))
                        (unwind-protect
                            (values result token :third)
                          (when token
                            (multiple-value-bind (released left backing pool2)
                                (fn-icr-abort token fuel (fn-mio$c-provider mio) pool)
                              (declare (ignore left))
                              (assert (and (eq released :released) (eq pool pool2)
                                           (eq backing (fn-mio$c-provider mio))))))
                          (assert (= (fn-prp-alloc-active-turns pool) 1))
                          (assert (= (fn-prp-alloc-allocated pool) 70))
                          (setf cleanup (list :allocating :epilogue))))))
                  (if (eq kind :success)
                      '(:reserved (:connection-holder 2 1 0) :third)
                    '(:refused nil :third)))))))
        (assert (equal cleanup '(:allocating :epilogue)))
        (assert (= (fn-prp-alloc-active-turns pool) 0))
        (assert (= (fn-prp-alloc-allocated pool) 70))
        (assert (= (fn-prl-nth 2 (fn-owner-page-read-ledger pool)) 2))
        (assert (equal (fn-prl-nth 1 (fn-owner-page-read-ledger pool)) '(0 0 0 0 2)))
        (assert (eq (fn-omk-at 1 (fn-owner-connection-operation-ticket *the-live-state*))
                    :finished)))))

  ;; PREPARE settles definite pre-ticket refusals itself. No token/receipt is
  ;; handed to the outer macro, and spent gate allocation is never refunded.
  (dolist (kind '(:unavailable :body-yield :bad-input))
    (multiple-value-bind (binding mio) (fnn-start-test-fixture kind)
      (let ((pool (fnn-connection-turn-binding-pool binding)))
        (multiple-value-bind (word nonce same-mio)
            (fnn-connection-turn-prepare binding
              (if (eq kind :bad-input) :invalid :reader) nil nil nil mio)
          (assert (and (not nonce) (eq mio same-mio)
                       (eq word (case kind (:unavailable :unsupported-runtime)
                                          (:body-yield :yield) (otherwise :refused))))))
        (assert (null (fn-owner-connection-operation-ticket *the-live-state*)))
        (assert (= (fn-prp-alloc-active-turns pool) 0))
        (assert (= (fn-prp-alloc-allocated pool) 30))
        (assert (= (fn-prl-nth 2 (fn-owner-page-read-ledger pool)) 1)))))

  ;; A lost PREPARE acknowledgment retains the real prepaid ticket and receipt.
  (multiple-value-bind (binding mio) (fnn-start-test-fixture :prepare-escape)
    (setf (fnn-connection-turn-binding-prepare binding)
          #'fnn-start-test-prepare-then-escape)
    (assert (handler-case
                (progn (fnn-connection-turn-prepare binding :reader nil nil nil mio) nil)
              (fnn-fixed-callback-fault () t)))
    (let ((ticket (fn-owner-connection-operation-ticket *the-live-state*)))
      (assert (eq (fn-omk-at 1 ticket) :prepaid))
      (fnn-start-test-retained binding ticket 1)
      (multiple-value-bind (erp word token fuel mio1 pool1 state1)
          (fnn-start-test-call start mio (fnn-connection-turn-binding-pool binding))
        (declare (ignore fuel mio1 pool1 state1))
        (assert (and (not erp) (eq word :recovery-required) (not token))))
      (fnn-start-test-retained binding ticket 1)))

  ;; An escape after real registration retains both holder and scheduling
  ;; receipts. No synthetic replacement ticket or direct count decrement.
  (multiple-value-bind (binding mio) (fnn-start-test-fixture :body-escape)
    (let ((pool (fnn-connection-turn-binding-pool binding)) (ticket nil))
      (multiple-value-bind (word nonce same-mio)
          (fnn-connection-turn-prepare binding :reader nil nil nil mio)
        (assert (and (eq word :prepared) (= nonce 0) (eq mio same-mio)))
        (assert
          (eq (catch 'fnn-start-test-abandon
                (fnn-with-prepaid-connection-turn (binding nonce)
                  (multiple-value-bind (erp result token fuel mio1 pool1 state1)
                      (fnn-start-test-call start mio pool)
                    (declare (ignore fuel mio1 pool1 state1))
                    (assert (and (not erp) (eq result :reserved)
                                 (equal token '(:connection-holder 2 1 0))))
                    (setf ticket (fn-owner-connection-operation-ticket *the-live-state*))
                    (throw 'fnn-start-test-abandon :abandoned))))
              :abandoned)))
      (assert (eq (fn-omk-at 1 ticket) :started))
      (assert (eq (fn-omk-at 6 (fn-ibp-connection-pending (fn-mio$c-provider mio)))
                  :registered))
      (assert (equal (fn-prl-nth 1 (fn-owner-page-read-ledger pool)) '(40 0 0 0 2)))
      (fnn-start-test-retained binding ticket 2)
      (fnn-connection-turn-fault binding)
      (fnn-start-test-retained binding ticket 2))))

(let ((waiter (sb-thread:make-thread
                (lambda ()
                  (sb-thread:with-mutex (*fnn-start-test-owner-lock*)
                    (sb-thread:with-mutex (*fnn-extent-lock*) :acquired))))))
  (assert (eq (sb-thread:join-thread waiter :timeout 2 :default :timed-out) :acquired)))
(format t "~&CONNECTION-START-ACTUAL-CORE PASS success/absent/unavailable/yield/input/prepare-escape/body-escape~%")
