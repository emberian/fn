; Program-mode bridge: decoded bounded local records enter the executable model.
(in-package "ACL2")
(include-book "../books/bp-workflow-records")

(defun fn-workflow-install-replay (records state)
 (declare (xargs :stobjs state :mode :program))
 (let* ((sn (f-get-global 'fn-store-sn state))
        (node (and sn (fn-sn-node sn)))
        (answer (fn-bp-replay-journal node records)))
  (if (car answer)
      (let ((state (f-put-global 'fn-workflow-state (fn-bp-journal-nth 1 answer) state)))
       ; Effects reconstructed from old durable records are audit history, not
       ; permission to repeat external actions after open.
       (let ((state (f-put-global 'fn-workflow-effects nil state)))
        (value :ready)))
    (value :fault))))

(defun fn-workflow-state (state)
 (declare (xargs :stobjs state :mode :program))
 (value (f-get-global 'fn-workflow-state state)))
(defun fn-workflow-effects (state)
 (declare (xargs :stobjs state :mode :program))
 (value (f-get-global 'fn-workflow-effects state)))

(defun fn-workflow-preflight-record (record state)
 (declare (xargs :stobjs state :mode :program))
 (let ((answer (fn-bp-apply-journal-record
                (f-get-global 'fn-workflow-state state) record)))
  (value (if (car answer) :ready :fault))))

(defun fn-workflow-preflight-history (records state)
 (declare (xargs :stobjs state :mode :program))
 (let* ((sn (f-get-global 'fn-store-sn state))
        (node (and sn (fn-sn-node sn)))
        (answer (fn-bp-replay-journal node records)))
  (value (if (car answer) :ready :fault))))

(defun fn-workflow-apply-record (record state)
 (declare (xargs :stobjs state :mode :program))
 (let ((answer (fn-bp-apply-journal-record
                (f-get-global 'fn-workflow-state state) record)))
  (if (not (car answer)) (value :fault)
   (let ((state (f-put-global 'fn-workflow-state
                              (fn-bp-journal-nth 1 answer) state)))
    ; These effects belong only to this just-durable operation.  Disk replay
    ; effects remain historical and are never returned through this gate.
    (let ((state (f-put-global 'fn-workflow-effects
                               (fn-bp-journal-nth 2 answer) state)))
     (value :ready))))))
(defun fn-workflow-fencedp (state)
 (declare (xargs :stobjs state :mode :program))
 (value (if (fn-bp-state-fenced (f-get-global 'fn-workflow-state state)) t nil)))
(defun fn-workflow-work-status (work-id state)
 (declare (xargs :stobjs state :mode :program))
 ; ACL2 owns the projection; this reports it.  :absent means no such work in
 ; the installed image, never "enqueued but not yet attempted".
 (value (fn-bp-work-status work-id
         (fn-bp-state-works (f-get-global 'fn-workflow-state state)))))

(defun fn-workflow-take-submit (work-id attempt-id generation state)
 (declare (xargs :stobjs state :mode :program))
 (let* ((effects (f-get-global 'fn-workflow-effects state))
        (effect (and (consp effects) (car effects))))
  (if (and (equal (len effects) 1) (equal (fn-bp-journal-nth 0 effect) :submit)
           (equal (fn-bp-journal-nth 1 effect) work-id)
           (equal (fn-bp-journal-nth 2 effect) attempt-id)
           (equal (fn-bp-journal-nth 3 effect) generation))
      (let ((state (f-put-global 'fn-workflow-effects nil state))) (value t))
    (value nil))))
