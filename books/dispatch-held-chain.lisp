; The held-frame chain (dispatch-held.lisp) of each dispatched kind with a
; held claim (machines.lisp fn2-dispatch-held-kind-p: conn, upload, ctl): every function its run reaches that returns the
; operation table, the pool or the core keeps the observation of every owner
; kind but the ones it writes as. Its own book, beside the executor's, so
; the attachments (assembly-attach) only read the run's lemmas.
(in-package "ACL2")
(include-book "dispatch-held")
(include-book "assembly-callbacks")
;; the kinds attached in assembly-attach: those whose run its leaf books define
(deflabel fn2-dh-chain-kinds)
(include-book "assembly-callbacks-d-conn")
(include-book "assembly-callbacks-d-upload")
(include-book "assembly-callbacks-d-txn")
(include-book "assembly-callbacks-d-cursor")
(include-book "assembly-callbacks-e-cns")
(include-book "assembly-callbacks-e-auth")
(defun fn2-dh-kind-chain-events (names world)
  (declare (xargs :mode :program))
  (if (atom names) nil
    (let* ((name (car names)) (run (fn2-columns-sym name "-RUN")))
      (if (and (function-symbolp run world) (fn2-dispatch-held-kind-p name world)
               (< (getpropc 'fn2-dh-chain-kinds 'absolute-event-number 0 world)
                  (getpropc run 'absolute-event-number 0 world)))
          (cons `(make-event (value (cons 'progn (fn2-dh-chain-forms (fn2-dh-postorder-new '(,run) (w state)) ',name))))
                (fn2-dh-kind-chain-events (cdr names) world))
        (fn2-dh-kind-chain-events (cdr names) world)))))
(make-event (value (cons 'progn (fn2-dh-kind-chain-events (fn2-machine-names (w state)) (w state)))))
