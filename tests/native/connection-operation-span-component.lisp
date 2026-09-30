;;; Run after connection-start-core-component in the same disposable world.
;;; Actual compiled callbacks; installation/allowances remain synthetic.
(in-package "ACL2")
(defvar *fnn-span-finishes* 0)
(defvar *fnn-span-faults* 0)
(defvar *fnn-span-finish-escape* nil)
(defun fnn-span-assert-exclusion ()
  (assert (sb-thread:holding-mutex-p *fnn-start-test-owner-lock*))
  (assert (sb-thread:holding-mutex-p *fnn-extent-lock*)))
(defun fnn-span-finish (slot nonce slots pool state)
  (fnn-span-assert-exclusion)
  (incf *fnn-span-finishes*)
  (multiple-value-prog1
      (fn-owner-index-connection-finish slot nonce slots pool state)
    (when *fnn-span-finish-escape* (error "lost actual FINISH acknowledgment"))))
(defun fnn-span-fault (slots pool state)
  (fnn-span-assert-exclusion)
  (incf *fnn-span-faults*)
  (fn-owner-index-connection-fault slots pool state))
(defun fnn-span-excludes-waiter ()
  (fnn-span-assert-exclusion)
  (let ((thread
          (sb-thread:make-thread
           (lambda ()
             (let ((acquired (sb-thread:grab-mutex *fnn-extent-lock* :waitp nil)))
               (when acquired (sb-thread:release-mutex *fnn-extent-lock*))
               acquired)))))
    (assert (null (sb-thread:join-thread thread :timeout 2 :default :timed-out)))))

(dolist (kind '(:success :absent :unavailable :body-yield :bad-input
               :prepare-escape :body-escape :finish-escape))
  (multiple-value-bind (binding mio) (fnn-start-test-fixture kind)
    (let ((pool (fnn-connection-turn-binding-pool binding))
          (body-entered nil) (cleanup nil) (outcome nil))
      (setf *fnn-span-finishes* 0 *fnn-span-faults* 0
            *fnn-span-finish-escape* (eq kind :finish-escape)
            (fnn-connection-turn-binding-finish binding) #'fnn-span-finish
            (fnn-connection-turn-binding-fault binding) #'fnn-span-fault)
      (when (eq kind :prepare-escape)
        (setf (fnn-connection-turn-binding-prepare binding)
              #'fnn-start-test-prepare-then-escape))
      (sb-thread:with-mutex (*fnn-start-test-owner-lock*)
        (setf outcome
          (handler-case
              (catch 'fnn-span-abandon
                (multiple-value-list
                  (fnn-with-connection-operation
                      ((nonce current-mio) binding
                       (if (eq kind :bad-input) :invalid :reader)
                       nil nil nil mio)
                    (setf body-entered t)
                    (assert (= nonce 0))
                    (assert (eq current-mio mio))
                    (fnn-span-excludes-waiter)
                    (multiple-value-bind (erp word token fuel mio1 pool1 state1)
                        (fnn-start-test-call
                         (fnn-fixed-raw-callback 'fn-owner-index-connection-start)
                         current-mio pool)
                      (assert (and (not erp) (eq mio1 mio) (eq pool1 pool)
                                   (eq state1 *the-live-state*)))
                      (unwind-protect
                          (if (eq kind :body-escape)
                              (throw 'fnn-span-abandon :abandoned)
                            (values word token :third :fourth))
                        (fnn-span-excludes-waiter)
                        (assert (= (fn-prp-alloc-active-turns pool) 1))
                        (when (and token (not (eq kind :body-escape)))
                          (multiple-value-bind (released left backing pool2)
                              (fn-icr-abort token fuel (fn-mio$c-provider mio) pool)
                            (declare (ignore left))
                            (assert (and (eq released :released) (eq pool2 pool)
                                         (eq backing (fn-mio$c-provider mio))))))
                        (setf cleanup (list :allocating :cleanup)))))))
            (fnn-fixed-callback-fault () :fault))))
      (case kind
        ((:success :absent)
         (assert body-entered)
         (assert (equal outcome
                  (if (eq kind :success)
                      '(:reserved (:connection-holder 2 1 0) :third :fourth)
                    '(:refused nil :third :fourth))))
         (assert (equal cleanup '(:allocating :cleanup)))
         (assert (= *fnn-span-finishes* 1)) (assert (= *fnn-span-faults* 0))
         (assert (= (fn-prp-alloc-active-turns pool) 0))
         (assert (= (fn-prp-alloc-allocated pool) 70))
         (assert (eq :finished
                     (fn-omk-at 1 (fn-owner-connection-operation-ticket *the-live-state*)))))
        ((:unavailable :body-yield :bad-input)
         (assert (not body-entered)) (assert (null cleanup))
         (assert (equal outcome
                  (list (case kind (:unavailable :unsupported-runtime)
                                   (:body-yield :yield) (otherwise :refused)) nil mio)))
         (assert (= *fnn-span-finishes* 0)) (assert (= *fnn-span-faults* 0))
         (assert (= (fn-prp-alloc-active-turns pool) 0))
         (assert (= (fn-prp-alloc-allocated pool) 30)))
        (:prepare-escape
         (assert (eq outcome :fault)) (assert (not body-entered))
         (assert (= *fnn-span-finishes* 0)) (assert (= *fnn-span-faults* 2))
         (fnn-start-test-retained binding
           (fn-owner-connection-operation-ticket *the-live-state*) 1))
        (:body-escape
         (assert (eq outcome :abandoned)) (assert body-entered)
         (assert (equal cleanup '(:allocating :cleanup)))
         (fnn-start-test-retained binding
           (fn-owner-connection-operation-ticket *the-live-state*) 2)
         (assert (= *fnn-span-finishes* 0)) (assert (= *fnn-span-faults* 1)))
        (:finish-escape
         (assert (eq outcome :fault)) (assert body-entered)
         (assert (equal cleanup '(:allocating :cleanup)))
         (assert (= *fnn-span-finishes* 1)) (assert (= *fnn-span-faults* 2))
         (assert (= (fn-prp-alloc-active-turns pool) 0))
         (assert (= (fn-prp-alloc-allocated pool) 70))
         (assert (eq (fn-prp-alloc-mode pool) :recovery))
         (assert (eq :finished
                     (fn-omk-at 1 (fn-owner-connection-operation-ticket *the-live-state*))))))
      (let ((waiter (sb-thread:make-thread
                      (lambda ()
                        (sb-thread:with-mutex (*fnn-start-test-owner-lock*)
                          (sb-thread:with-mutex (*fnn-extent-lock*) :acquired))))))
        (assert (eq :acquired (sb-thread:join-thread waiter :timeout 2 :default :timed-out)))))))
(format t "~&CONNECTION-OPERATION-SPAN PASS 8 actual-core cases~%")
