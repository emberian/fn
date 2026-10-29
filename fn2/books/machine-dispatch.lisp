(in-package "ACL2")
(include-book "machines-a-run")
(defmacro fn2-machine-dispatch-events ()
 '(progn
(make-event
 (value (cons 'progn (fn2-machine-observe-events 'fn2-machine-observe (fn2-machine-names (w state)) (w state)))))

(make-event
 (value `(defun fn2-machine-run (id budget fn2-core)
           (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
           (if (or (not (fn2-machine-idp id fn2-core))
                   (equal (fn2-machine-stopped id fn2-core) 1))
               (fn2-machine-idle id fn2-core)
             (case (fn2-machine-kind id fn2-core)
               ,@(fn2-machine-run-arms (fn2-machine-names (w state)) 0)
               (otherwise (fn2-machine-refuse-phase id fn2-core)))))))
(fn2-core-shape-lemmas fn2-machine-run (id budget) 4)

(assert-event
 (fn2-profile-exports-compliant-p
  '(fn2-machine-observe fn2-machine-run fn2-machine-take-wake
    fn2-listener-step fn2-connection-submit fn2-connection-reply fn2-connection-drain fn2-machine-grant-one fn2-machine-park)
  (w state)))

))
