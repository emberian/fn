(in-package "ACL2")
(include-book "machines-a-run")
(defmacro fn2-machine-dispatch-events ()
 '(progn
(fn2-resolve :callbacks)
(make-event
 (value (cons 'progn (fn2-machine-observe-events 'fn2-machine-observe (fn2-machine-names (w state)) (w state)))))
(make-event
 (value (cons 'progn (fn2-machine-all-observe-rows (fn2-machine-names (w state)) (w state)))))

; The kinds' arm certificates under one dispatch, for the cost-composition
; obligation over a word of runs (executor.lisp).
(make-event
 (value `(progn
           (defun fn2-machine-arm-charge-ok-p (kind phase bytes steps descriptors)
             (declare (xargs :guard t))
             (case kind ,@(fn2-machine-arm-certificate-arms (fn2-machine-names (w state)) 0 nil)
               (otherwise nil)))
           (defun fn2-machine-arm-bound (kind phase)
             (declare (xargs :guard t))
             (case kind ,@(fn2-machine-arm-certificate-arms (fn2-machine-names (w state)) 0 t)
               (otherwise 0))))))

(make-event
 (value `(defun fn2-machine-run (id budget fn2-core)
           (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
           (if (not (eq (fn2-machine-stopped-read-code id fn2-core) :ok))
               (fn2-machine-refuse-phase id fn2-core)
             (if (equal (fn2-machine-stopped id fn2-core) 1)
               (fn2-machine-idle id fn2-core)
             (case (fn2-machine-kind id fn2-core)
               ,@(fn2-machine-run-arms (fn2-machine-names (w state)) 0)
               (otherwise (fn2-machine-refuse-phase id fn2-core))))))))
(fn2-core-preserves fn2-machine-run (id budget fn2-core) :position 4 :rows nil)

(assert-event
 (fn2-assert-compliant-p
  '(fn2-machine-observe fn2-machine-run fn2-machine-take-wake
    fn2-listener-accept fn2-listener-admitting fn2-listener-close fn2-machine-admit-connection
    fn2-connection-submit fn2-connection-reply fn2-connection-drain fn2-machine-grant-one fn2-machine-park)
  (w state)))


(fn2-resolve :dispatch)
))
