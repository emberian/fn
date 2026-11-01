; Read-only diagnosis of unmodified echo admission and client accounting.
(in-package "ACL2")
(defvar *pass2-live* nil)
(defvar *pass2-origin* nil)
(defvar *pass2-turn* 0)
(defvar *pass2-core-transitions* 0)
(defvar *pass2-ref-transitions* 0)
(defvar *pass2-randoms* 0)
(defvar *pass2-last-turn-verdict* nil)
(defun pass2-record (x)
  (e1q-record (list* :event :turn *pass2-turn* :live *pass2-live* x)))
(defun pass2-client (record)
  (list :nonce (first record) :todo (length (second record))
        :expected (length (third record)) :sent (fourth record)
        :received (fifth record) :terminal (seventh record)
        :age (eighth record) :death-epoch (nth 9 record)))
(defun pass2-allocator (core)
  (list :free-head (fn2-machine-free-head core)
        :active (fn2-machine-active-count core)
        :capacity (fn2-machine-connection-count core)
        :stop (fn2-core-stop-reason core)))
(defun pass2-install ()
  (e1q-wrap 'fn2-echo-rounds
    (lambda (old args)
      (let ((*pass2-live* (third args))) (apply old args))))
  (e1q-wrap 'fn2-transition
    (lambda (old args) (incf *pass2-core-transitions*) (apply old args)))
  (e1q-wrap 'fn2-ref-transition
    (lambda (old args) (incf *pass2-ref-transitions*) (apply old args)))
  (e1q-wrap 'fn2-check-trace-turn
    (lambda (old args) (incf *pass2-turn*) (apply old args)))
  (e1q-wrap 'fn2-sim-random
    (lambda (old args)
      (let ((result (multiple-value-list (apply old args))))
        (incf *pass2-randoms*)
        (e1q-record (list :random *pass2-randoms* (first result)))
        (values-list result))))
  (e1q-wrap 'fn2-echo-check-turn
    (lambda (old args)
      (let ((result (multiple-value-list (apply old args))))
        (setf *pass2-last-turn-verdict* (first result))
        (values-list result))))
  (e1q-wrap 'fn2-listener-admit
    (lambda (old args)
      (let* ((id (first args)) (core (car (last args)))
             (cap (list (fn2-machine-cap-index id core) (fn2-machine-cap-nonce id core)))
             (before (pass2-allocator core))
             (result (multiple-value-list (apply old args)))
             (phase (fn2-machine-phase id core)))
        (pass2-record
          (list :admission :cap cap :before before :after (pass2-allocator core)
                :listener-phase phase
                :decision (if (= phase *fn2-listener-state-closing*) :refused :admitted)))
        (values-list result))))
  (e1q-wrap 'fn2-connection-release
    (lambda (old args)
      (let* ((id (first args)) (core (car (last args)))
             (cap (list (fn2-machine-cap-index id core) (fn2-machine-cap-nonce id core)))
             (before (pass2-allocator core))
             (result (multiple-value-list (apply old args))))
        (pass2-record (list :reclamation :cap cap :before before :after (pass2-allocator core)))
        (values-list result))))
  (e1q-wrap 'fn2-sim-echo-accept
    (lambda (old args)
      (let* ((sim (sixth args)) (word (third args))
             (cap (mod word 1))
             (before (fn2-sim-cap cap sim))
             (result (multiple-value-list (apply old args)))
             (after (fn2-sim-cap cap sim)))
        (when (/= before after)
          (pass2-record (list :network-accept :cap (list cap after) :previous-nonce before)))
        (values-list result))))
  (e1q-wrap 'fn2-sim-physical
    (lambda (old args)
      (let ((*pass2-origin* :server-adapter)) (apply old args))))
  (e1q-wrap 'fn2-echo-client-step
    (lambda (old args)
      (let* ((*pass2-origin* :client-oracle)
             (before (pass2-client (second args)))
             (result (multiple-value-list (apply old args))))
        (when (or (> (third result) 0) (> (fourth result) 0))
          (pass2-record (list :client-step :cap (first args) :before before
                              :after (pass2-client (second result))
                              :echoed (third result) :dropped (fourth result)
                              :cause (sixth result))))
        (values-list result))))
  (e1q-wrap 'fn2-network-close
    (lambda (old args)
      (let* ((cap (first args)) (nonce (second args)) (net (third args))
             (before (fn2-network-cap-code cap nonce net))
             (result (multiple-value-list (apply old args))))
        (pass2-record (list :network-close :origin *pass2-origin*
                           :cap (list cap nonce) :before before
                           :return (first result) :after (fn2-network-cap-code cap nonce net)))
        (values-list result))))
  (e1q-wrap 'fn2-echo-client-round
    (lambda (old args)
      (let* ((before (mapcar #'pass2-client (first args)))
             (result (multiple-value-list (apply old args))))
        (when (or (> (third result) 0) (> (fourth result) 0) (> (fifth result) 0))
          (pass2-record (list :client-round :before before
                              :after (mapcar #'pass2-client (second result))
                              :accepted (third result) :echoed (fourth result)
                              :dropped (fifth result) :stats (seventh result))))
        (when (and *pass2-live* (> (fifth result) 0))
          (throw 'pass2-done
            (list :first-live-drop :turn *pass2-turn* :core *pass2-core-transitions*
                  :reference *pass2-ref-transitions* :randoms *pass2-randoms*
                  :turn-monitor *pass2-last-turn-verdict* :client-verdict (first result)
                  :before before :after (mapcar #'pass2-client (second result)))))
        (values-list result)))))
