; Materialize dispatch after all registered continuations.
(in-package "ACL2")
(include-book "assembly-callbacks")
(include-book "dispatch-held")

;; The footprint contracts (-DC-KIDS, fn2-dc-*) and the directory relation
;; FN2-CTF-DIR with its chained contracts (fn2-ctf-dir-*) are machines.lisp's:
;; the wait sources' attachments use them first (defwait). Here the relation
;; (once), and the wait grants' derived contracts from their constraints.
(make-event (value (fn2-ctf-dir-basis-form (w state))))
(make-event (value (cons 'progn (fn2-machine-wait-frame-events (fn2-machine-waits (w state)) (w state)))))

;; THE ATTACHMENTS (assembly-attach.lisp, after the kinds' implementations):
;; each kind's run and observe functions get footprint contracts (callees
;; first, under the kind), the footprint is checked within the stub's frame
;; (an attachment changing a child outside it is refused, naming the child
;; and the functions whose contracts change it), the directory contracts
;; follow, and the stub's frame claims are proved of the attachment before
;; its defattach. An observe attachment also keeps the operation table and
;; the pool (FN2-DISPATCH-OPS-POOL): its footprint off both, else refused
;; naming the contracts that write them.
(defun fn2-dispatch-attach-events (names world)
  (declare (xargs :mode :program))
  (if (atom names) nil
    (let* ((name (car names))
           (run (fn2-columns-sym name "-RUN"))
           (run-stub (fn2-columns-sym name "-RUN-STUB"))
           (obs (fn2-columns-col-name 'fn2-machine-observe name))
           (obs-stub (fn2-columns-col-name 'fn2-machine-observe (fn2-columns-sym name "-STUB")))
           (e (fn2-dispatch-frame-children name world)))
      (if (and (function-symbolp run world) (function-symbolp run-stub world))
          (append
           `((make-event (value (cons 'progn (fn2-dc-forms (fn2-dc-todo '(,run ,obs) ',name (w state) nil 64) ',name))))
             (make-event (value (fn2-dc-frame-check ',run-stub ',run ',name ',e (w state))))
             (make-event (value (fn2-dc-frame-check ',obs-stub ',obs ',name ',e (w state))))
             ;; the observe stub keeps the operation table and the pool
             (make-event (value (fn2-dispatch-ops-pool-form ',obs-stub ',obs ',name ',e (w state))))
             (make-event (value (cons 'progn (fn2-ctf-dir-forms (fn2-ctf-postorder-new '(,run ,obs) (w state)) ',name))))
             (make-event (value (fn2-dc-frame-kids ',run 4 '(id budget fn2-core) ',e ',name "-DISPATCH-KIDS" (w state))))
             (make-event (value (fn2-dc-frame-kids ',obs 1 '(id event outcome reason count aux0 aux1 fn2-core) ',e ',name "-DISPATCH-KIDS" (w state))))
             (defattach (,run-stub ,run)
                        (,obs-stub ,obs)
                        (,(fn2-columns-sym name "-ARM-CHARGE-OK-P-STUB") ,(fn2-columns-sym name "-ARM-CHARGE-OK-P"))
                        (,(fn2-columns-sym name "-ARM-BOUND-STUB") ,(fn2-columns-sym name "-ARM-BOUND")))
             (in-theory (disable ,(fn2-columns-sym run "-DISPATCH-KIDS") ,(fn2-columns-sym obs "-DISPATCH-KIDS")
                                 ,(fn2-columns-sym obs "-DISPATCH-OPS-POOL")))
             (make-event (fn2-dc-disable-form (fn2-ctf-postorder-new '(,run ,obs) (w state)) ',name (w state))))
           (fn2-dispatch-attach-events (cdr names) world))
        (fn2-dispatch-attach-events (cdr names) world)))))
(defmacro fn2-dispatch-attach-all-events ()
  '(make-event (value (cons 'progn (fn2-dispatch-attach-events (fn2-machine-names (w state)) (w state))))))

(fn2-resolve :callbacks)
;; the stubs' default bodies' contracts, then the stubs (machines.lisp)
(fn2-machine-stub-all-events)
(make-event
 (value (cons 'progn (fn2-machine-observe-events 'fn2-machine-observe (fn2-machine-names (w state)) (w state)))))
(make-event
 (value (cons 'progn (fn2-machine-all-observe-rows (fn2-machine-names (w state)) (w state)))))
(make-event
 (value `(progn
           (defun fn2-machine-arm-charge-ok-p (kind phase bytes steps descriptors)
             (declare (xargs :guard t))
             (case kind ,@(fn2-machine-arm-certificate-arms (fn2-machine-names (w state)) 0 nil (w state))
               (otherwise nil)))
           (defun fn2-machine-arm-bound (kind phase)
             (declare (xargs :guard t))
             (case kind ,@(fn2-machine-arm-certificate-arms (fn2-machine-names (w state)) 0 t (w state))
               (otherwise 0))))))
(make-event
 (value `(defun fn2-machine-run (id budget fn2-core)
           (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
           (if (not (eq (fn2-machine-stopped-read-code id fn2-core) :ok))
               (fn2-machine-refuse-phase id fn2-core)
             (if (equal (fn2-machine-stopped id fn2-core) 1)
               (fn2-machine-idle id fn2-core)
             (case (fn2-machine-kind id fn2-core)
               ,@(fn2-machine-run-arms (fn2-machine-names (w state)) 0 (w state))
               (otherwise (fn2-machine-refuse-phase id fn2-core))))))))
(fn2-core-preserves fn2-machine-run (id budget fn2-core) :position 4 :rows nil)
(assert-event
 (fn2-assert-compliant-p
  '(fn2-machine-observe fn2-machine-run fn2-machine-take-wake
    fn2-listener-run-accepting fn2-listener-run-admitting fn2-listener-run-closing fn2-machine-admit
    fn2-echo-run-command fn2-echo-run-reply fn2-echo-run-draining fn2-machine-grant-one fn2-machine-park)
  (w state)))
(fn2-resolve :dispatch)
