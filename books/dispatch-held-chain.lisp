; The held-frame chain (dispatch-held.lisp) of each dispatched kind with a
; held claim (machines.lisp fn2-dispatch-held-kind-p: conn, upload, cursor,
; ctl): every function its run reaches that returns the operation table, the
; pool, an owner table or the core keeps the observation of every owner kind
; but the ones it writes as, and the stored owners avoiding it. The owner
; chain (the stored owners alone) of every other run and observe function
; whose closure writes an owner table (txn, cns, auth; the cursor's observe).
; Its own book, beside the executor's, so the attachments (assembly-attach)
; only read the lemmas.
(in-package "ACL2")
(include-book "dispatch-owners")
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
    (let* ((name (car names)) (run (fn2-columns-sym name "-RUN"))
           (obs (fn2-columns-col-name 'fn2-machine-observe name))
           (held (fn2-dispatch-held-kind-p name world)))
      (if (and (function-symbolp run world)
               (< (getpropc 'fn2-dh-chain-kinds 'absolute-event-number 0 world)
                  (getpropc run 'absolute-event-number 0 world)))
          (append
           ;; the held chain of a held kind's run (with its owner conclusions)
           (and held
                (list `(make-event (value (cons 'progn (fn2-dh-chain-forms (fn2-dh-postorder-new '(,run) (w state)) ',name))))))
           ;; the owner chain of every other run and observe function writing an owner table
           (and (not held) (fn2-dh-owner-writes-p run world)
                (list `(make-event (value (cons 'progn (fn2-dh-chain-forms-m (fn2-dh-postorder-m '(,run) :owners (w state)) ',name :owners))))))
           (and (fn2-dh-owner-writes-p obs world)
                (list `(make-event (value (cons 'progn (fn2-dh-chain-forms-m (fn2-dh-postorder-m '(,obs) :owners (w state)) ',name :owners))))))
           (fn2-dh-kind-chain-events (cdr names) world))
        (fn2-dh-kind-chain-events (cdr names) world)))))
(make-event (value (cons 'progn (fn2-dh-kind-chain-events (fn2-machine-names (w state)) (w state)))))
