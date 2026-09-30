;;; Dedicated disposable ACL2/SBCL test only. Actual STATE finish/fault and
;;; native outer macro; installation, operation ticket and allowance are fixtures.
;;; PREPARE/START and the genuine constructor factory are not selected here.
(in-package "ACL2")

(defun fnn-ticket-test-pool (turns next)
  (let* ((pool (create-fn-page-read-pool))
         (reservation (sb-ext:dynamic-space-size))
         (association (list :allocation-epoch-association
                            :test-runtime :test-profile :test-pool
                            sb-vm:gencgc-page-bytes reservation))
         (installation (list :allocation-epoch-installation association
                             most-positive-fixnum reservation 1 0 0 0 0
                             64 128 256)))
    (assert (fn-aec-installationp installation))
    (update-fn-prp-alloc-installation installation pool)
    (update-fn-prp-alloc-mode :draining pool)
    (update-fn-prp-alloc-epoch 17 pool)
    (update-fn-prp-alloc-occupied 65536 pool)
    (update-fn-prp-alloc-allocated 512 pool)
    (update-fn-prp-alloc-active-turns turns pool)
    (update-fn-prp-alloc-gc-nonce nil pool)
    (fn-owner-page-read-keep-ledger
     (fn-prl-build '(1000000 1000 1000 1000 100)
                   '(0 0 0 0 0) next nil '(0 0 0 0 0)) pool)
    (assert (fn-aec-pool-statep pool))
    pool))


(defun fnn-ticket-test-fixture (kind)
  (let* ((pool (fnn-ticket-test-pool 0 0))
         (slots (create-fn-allocation-turn-slots)))
    (update-fn-prp-alloc-mode :active pool)
    (assert (eq (fn-ats-construct-internal '(:connection-start) slots pool)
                :constructed))
    (multiple-value-bind (word nonce actual-slots actual-pool)
        (fn-ats-enter-internal 0 :connection-start slots pool)
      (assert (and (eq word :gate-owned) (= nonce 0)
                   (eq actual-slots slots) (eq actual-pool pool)))
      (assert (eq (fn-ats-prepay-body-internal 0 nonce 32 slots pool) :prepaid))
      (let* ((ticket (unless (eq kind :no-ticket)
                       (list :connection-operation-ticket
                             (if (eq kind :intent) :start-intent :started)
                             :reader nil nil nil 23 0 nonce 17 9
                             :fixture-descriptor '(40 0 0 0 1) 8 32 :fixture-token)))
             ;; Test binding uses the real world-selected finish/fault entries.
             ;; It does NOT pretend the still-unjoined PREPARE factory exists.
             (binding (%make-fnn-connection-turn-binding
                       :pool pool :slots slots :slot 0 :prepare nil
                       :finish (fnn-fixed-raw-callback 'fn-owner-index-connection-finish)
                       :fault (fnn-fixed-raw-callback 'fn-owner-index-connection-fault))))
        (f-put-global 'fn-owner-connection-operation-ticket ticket *the-live-state*)
        (f-put-global 'fn-owner-connection-operation-installation
                      :fixture-installation *the-live-state*)
        (assert (fn-ats-matchingp 0 nonce slots pool))
        (values binding nonce ticket)))))

(defun fnn-ticket-test-finish-then-escape (slot nonce slots pool state)
  ;; Fault injection after the REAL core return, not a mocked finish result.
  (multiple-value-prog1
      (fn-owner-index-connection-finish slot nonce slots pool state)
    (error "injected escape after actual core finish")))

(defun fnn-ticket-test-retained (binding nonce ticket active allocated phase)
  (let ((pool (fnn-connection-turn-binding-pool binding))
        (slots (fnn-connection-turn-binding-slots binding)))
    (assert (eq (fn-prp-alloc-mode pool) :recovery))
    (assert (= (fn-prp-alloc-active-turns pool) active))
    (assert (= (fn-prp-alloc-allocated pool) allocated))
    (assert (= (fn-ats-noncesi 0 slots) nonce))
    (assert (= (fn-ats-phasesi 0 slots) phase))
    (assert (equal ticket (fn-owner-connection-operation-ticket *the-live-state*)))
    (assert (eq (fn-owner-connection-operation-installation *the-live-state*)
                :fixture-installation))))

(fnn-install-raw-dispatch)
(dolist (entry '(fn-owner-index-connection-finish fn-owner-index-connection-fault))
  (assert (eq (fnn-fixed-raw-callback entry) (symbol-function entry))))

;; The full returned MVs survive the actual outer cleanup and actual ticket
;; completion. Duplicate native completion fences without a second decrement.
(multiple-value-bind (binding nonce ticket) (fnn-ticket-test-fixture :success)
  (let* ((pool (fnn-connection-turn-binding-pool binding))
         (allocated (fn-prp-alloc-allocated pool))
         (cleanup nil))
    (assert (equal
             (multiple-value-list
              (fnn-with-prepaid-connection-turn (binding nonce)
                (unwind-protect (values :cid :custody :third)
                  (assert (= (fn-prp-alloc-active-turns pool) 1))
                  (assert (equal ticket (fn-owner-connection-operation-ticket *the-live-state*)))
                  (setf cleanup (list :allocating :epilogue)))))
             '(:cid :custody :third)))
    (assert (equal cleanup '(:allocating :epilogue)))
    (assert (= (fn-prp-alloc-active-turns pool) 0))
    (assert (= (fn-prp-alloc-allocated pool) allocated))
    (let ((finished (update-nth 1 :finished ticket)))
      (assert (equal finished (fn-owner-connection-operation-ticket *the-live-state*)))
      (assert (handler-case (progn (fnn-connection-turn-finish binding nonce) nil)
                (fnn-fixed-callback-fault () t)))
      (fnn-ticket-test-retained binding nonce finished 0 allocated 0))))

;; Every one of these has an ACTUAL matching owned ATS receipt. The missing,
;; retained-intent or wrong-nonce STATE ticket cannot be bypassed to consume it.
(dolist (kind '(:no-ticket :intent :wrong-nonce))
  (multiple-value-bind (binding nonce ticket) (fnn-ticket-test-fixture kind)
    (let ((allocated (fn-prp-alloc-allocated (fnn-connection-turn-binding-pool binding))))
      (assert (handler-case
                  (progn (fnn-connection-turn-finish binding
                           (if (eq kind :wrong-nonce) (+ 1 nonce) nonce)) nil)
                (fnn-fixed-callback-fault () t)))
      (fnn-ticket-test-retained binding nonce ticket 1 allocated 3))))

;; Body nonlocal exit: actual fault retains the live ticket and receipt, never
;; ordinary completion. A second fault is the exact idempotent core transition.
(multiple-value-bind (binding nonce ticket) (fnn-ticket-test-fixture :body-escape)
  (let ((allocated (fn-prp-alloc-allocated (fnn-connection-turn-binding-pool binding))))
    (assert (eq (catch 'fnn-ticket-abandon
                  (fnn-with-prepaid-connection-turn (binding nonce)
                    (throw 'fnn-ticket-abandon :abandoned))) :abandoned))
    (fnn-ticket-test-retained binding nonce ticket 1 allocated 3)
    (fnn-connection-turn-fault binding)
    (fnn-ticket-test-retained binding nonce ticket 1 allocated 3)))

;; Actual finish changed both STATE and slots before raw escape. Both native
;; fences preserve the finished roots, zero count and spent allocation.
(multiple-value-bind (binding nonce ticket) (fnn-ticket-test-fixture :finish-escape)
  (let ((allocated (fn-prp-alloc-allocated (fnn-connection-turn-binding-pool binding))))
    (setf (fnn-connection-turn-binding-finish binding) #'fnn-ticket-test-finish-then-escape)
    (assert (handler-case
                (fnn-with-prepaid-connection-turn (binding nonce) :body)
              (fnn-fixed-callback-fault () t)))
    (fnn-ticket-test-retained binding nonce (update-nth 1 :finished ticket)
                              0 allocated 0)))
(let ((waiter (sb-thread:make-thread
               (lambda () (sb-thread:with-mutex (*fnn-extent-lock*) :acquired)))))
  (assert (eq (sb-thread:join-thread waiter :timeout 2 :default :timed-out) :acquired)))
(format t "~&CONNECTION-TICKET-ACTUAL-CORE PASS finish/replay/missing/intent/nonce/body-escape/finish-escape~%")
