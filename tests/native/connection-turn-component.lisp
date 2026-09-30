;;; Actual native transport/macros with explicitly recording core callbacks.
;;; Run in an independent selected SBCL, never a product or another proof world.
(in-package "ACL2")
(defvar *the-live-state* :test-state)
(defvar *fnn-turn-test-pool* (vector :pool))
(defvar *fnn-turn-test-slots* (vector :slots))
(defvar *fnn-turn-test-mio* (vector :mio))
(defvar *fnn-turn-test-epilogue* nil)
(defvar *fnn-turn-test-finishes* 0)
(defvar *fnn-turn-test-faults* 0)
(defvar *fnn-turn-test-failure* nil)
(defvar *fnn-turn-test-word* :test-prepared)
(defun fnn-turn-test-common (slots pool state)
  (assert (eq slots *fnn-turn-test-slots*))
  (assert (eq pool *fnn-turn-test-pool*))
  (assert (eq state *the-live-state*))
  (assert (sb-thread:holding-mutex-p *fnn-extent-lock*)))
(defun fnn-turn-test-prepare (kind family address peer slot slots mio pool state)
  (fnn-turn-test-common slots pool state)
  (assert (and (eq kind :exposure) (eq family :ipv4)
               (equal address '(127 0 0 1)) (equal peer '(65)) (= slot 3)))
  (assert (eq mio *fnn-turn-test-mio*))
  (when (eq *fnn-turn-test-failure* :prepare)
    (throw 'raw-ev-fncall :injected))
  ;; Zero is a valid shared OLD NEXT nonce, not absence of an issued receipt.
  (values nil *fnn-turn-test-word* 0 slots mio pool state))
(defun fnn-turn-test-finish (slot nonce slots pool state)
  (fnn-turn-test-common slots pool state)
  (assert (and (= slot 3) (= nonce 0) *fnn-turn-test-epilogue*))
  (incf *fnn-turn-test-finishes*)
  (case *fnn-turn-test-failure*
    (:finish (error "injected finish escape"))
    (:stale (values nil :stale slots pool state))
    (otherwise (values nil :left slots pool state))))
(defun fnn-turn-test-fault (slots pool state)
  (fnn-turn-test-common slots pool state)
  (incf *fnn-turn-test-faults*)
  (values nil :recovery-required slots pool state))
(setf (gethash 'fn-owner-index-connection-prepare *fnn-raw-dispatch*)
      'fnn-turn-test-prepare
      (gethash 'fn-owner-index-connection-finish *fnn-raw-dispatch*)
      'fnn-turn-test-finish
      (gethash 'fn-owner-index-connection-fault *fnn-raw-dispatch*)
      'fnn-turn-test-fault)
(let ((binding (fnn-connection-turn-binding-make
                *fnn-turn-test-pool* *fnn-turn-test-slots* 3)))
  (multiple-value-bind (word nonce mio)
      (fnn-connection-turn-prepare binding :exposure :ipv4 '(127 0 0 1)
                                   '(65) *fnn-turn-test-mio*)
    (assert (and (eq word :test-prepared) (= nonce 0)
                 (eq mio *fnn-turn-test-mio*))))
  (assert (equal
           (multiple-value-list
            (fnn-with-prepaid-connection-turn (binding 0)
              (unwind-protect (values :cid :node :third)
                (setf *fnn-turn-test-epilogue* t))))
           '(:cid :node :third)))
  (assert (= *fnn-turn-test-finishes* 1))
  (assert (= *fnn-turn-test-faults* 0))
  ;; Body cleanup errors keep the receipt, rather than ordinary completion.
  (setf *fnn-turn-test-epilogue* nil)
  (assert (handler-case
              (fnn-with-prepaid-connection-turn (binding 0)
                (unwind-protect :body (error "injected allocating cleanup")))
            (error () t)))
  (assert (= *fnn-turn-test-finishes* 1))
  (assert (= *fnn-turn-test-faults* 1))
  ;; A nonlocal return also retains/fences instead of decrementing.
  (assert (eq (catch 'fnn-test-abandon
                (fnn-with-prepaid-connection-turn (binding 0)
                  (throw 'fnn-test-abandon :abandoned))) :abandoned))
  (assert (= *fnn-turn-test-finishes* 1))
  (assert (= *fnn-turn-test-faults* 2))
  (setf *fnn-turn-test-failure* :prepare)
  (assert (handler-case
              (progn (fnn-connection-turn-prepare binding :exposure :ipv4
                        '(127 0 0 1) '(65) *fnn-turn-test-mio*) nil)
            (fnn-fixed-callback-fault () t)))
  (assert (= *fnn-turn-test-faults* 3))
  (setf *fnn-turn-test-epilogue* t *fnn-turn-test-failure* :finish)
  (assert (handler-case
              (fnn-with-prepaid-connection-turn (binding 0) :body)
            (fnn-fixed-callback-fault () t)))
  (assert (= *fnn-turn-test-finishes* 2))
  (assert (= *fnn-turn-test-faults* 5))
  (setf *fnn-turn-test-failure* :stale)
  (assert (handler-case
              (fnn-with-prepaid-connection-turn (binding 0) :body)
            (fnn-fixed-callback-fault () t)))
  (assert (= *fnn-turn-test-finishes* 3))
  (assert (= *fnn-turn-test-faults* 7))
  ;; Interruption can precede entry into the finish function's own protection.
  ;; An outer 'finishing' flag would wrongly suppress this required fence.
  (flet ((fnn-connection-turn-finish (binding nonce)
           (declare (ignore binding nonce)) (error "before finish entry")))
    (assert (handler-case
                (fnn-with-prepaid-connection-turn (binding 0) :body)
              (error () t))))
  (assert (= *fnn-turn-test-finishes* 3))
  (assert (= *fnn-turn-test-faults* 8))
  (let ((waiter (sb-thread:make-thread
                 (lambda () (sb-thread:with-mutex (*fnn-extent-lock*) :acquired)))))
    (assert (eq (sb-thread:join-thread waiter :timeout 2 :default :timed-out)
                :acquired))))
(format t "~&CONNECTION-TURN PASS finishes=~D faults=~D~%"
        *fnn-turn-test-finishes* *fnn-turn-test-faults*)
