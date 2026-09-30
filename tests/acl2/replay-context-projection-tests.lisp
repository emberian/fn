(in-package "ACL2")
(include-book "../../books/replay-context-projection")
(include-book "replay-produced-size-tests")
; Public replay fixture only, not configured Store/native qualification.
(defun rict-boundary (ctx row)
 (mv-let (checked effect child sizes) (fn-replay-identity-produced-effects ctx row)
  (declare (ignore sizes))
  (equal (fn-replay-identity-step (fn-ripc-without-prior-verdicts ctx) row)
         (fn-ripc-core-checked-context checked effect child))))
(defun rict-live (fn-arena)
 (declare (xargs :mode :program :stobjs fn-arena))
 (mv-let (row fn-arena) (fn-intern-event *ript-carried-event* nil 0 fn-arena)
  (mv-let (checked effect child sizes)
   (fn-replay-identity-produced-effects *ript-ctx* row)
   (declare (ignore sizes))
   (let* ((snapshot (fn-stxk-make 1 2 1 3 '(1) '(2)))
          (after (fn-replay-identity-step checked snapshot)))
    (mv
     (and (fn-hstxa-p row) (eq effect :verdict)
          (equal child *ript-carried-child*)
          (eq (fn-stxk-context-kind checked) :ok)
          (equal (fn-stxk-context-verdicts checked) (list child))
          (rict-boundary *ript-ctx* row)
          ; Mutation: removing the NEW verdict would break full core output.
          (not (equal (fn-replay-identity-step (fn-ripc-without-prior-verdicts *ript-ctx*) row)
                      (fn-ripc-without-prior-verdicts checked)))
          ; Reachable next public decision retains OLD original evidence;
          ; legacy core has no accumulated prior verdicts.
          (equal (fn-store-event-sequence snapshot) (fn-stxk-context-next checked))
          (fn-stxk-p snapshot) (eq (fn-stxk-context-kind after) :ok)
          (equal (fn-stxk-context-verdicts after) (list child))
          (rict-boundary checked snapshot)) fn-arena)))))
(defun rict-local ()
 (declare (xargs :mode :program))
 (with-local-stobj fn-arena
  (mv-let (ok fn-arena) (rict-live fn-arena) ok)))
(make-event (value (list 'assert-event (rict-local))))
; Fault also projects exact public result while preserving original evidence.
(assert-event
 (let* ((ctx (fn-stxk-context :ok 7 nil (list *ript-carried-child*) nil nil))
        (event *ript-snapshot*))
  (and (not (equal (fn-store-event-sequence event) (fn-stxk-context-next ctx)))
       (eq (fn-stxk-context-kind (fn-replay-identity-step ctx event)) :fault)
       (rict-boundary ctx event))))
