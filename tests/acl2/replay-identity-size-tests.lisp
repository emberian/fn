; Literal actual-replay carry antecedents, effects and independent removals.
(in-package "ACL2")
(include-book "../../books/replay-identity-size")

(defun rist-carries (xs)
  (if (consp xs) (cons (fn-scs-summary (car xs)) (rist-carries (cdr xs))) nil))
(defconst *rist-ctx* (fn-stxk-initial-context 0))
(defconst *rist-event* (fn-stxk-make 0 1 1 0 '(1) '(7 8)))
(defconst *rist-installed* (fn-replay-identity-step *rist-ctx* *rist-event*))
(defconst *rist-verdict* (fn-stxe-make 1 2 2 "<a@x>" :unverified '(9) 0 '(1)))

(defun rist-effects (ctx event)
  (mv-list 3 (fn-replay-identity-effects ctx event)))
(defun rist-child-exactp (ctx event ec)
  (implies (member-eq (nth 1 (rist-effects ctx event))
                      '(:snapshot :verdict))
           (equal ec (fn-scs-summary
                      (nth 2 (rist-effects ctx event))))))
(defun rist-resultp (ctx cs event ec)
  (mv-let (next carries) (fn-ris-step ctx cs event ec)
    (fn-scs-correspondsp carries next)))

; Reachable nonempty snapshot: complete literal antecedent and conclusion.
(assert-event
 (let ((ctx *rist-ctx*) (event *rist-event*)
       (cs (rist-carries *rist-ctx*)) (ec (fn-scs-summary *rist-event*)))
   (and (fn-ics-contextp ctx) (fn-scs-correspondsp cs ctx)
        (rist-child-exactp ctx event ec) (rist-resultp ctx cs event ec)
        (equal (nth 1 (rist-effects ctx event)) :snapshot)
        (equal (nth 2 (rist-effects ctx event)) event)
        (fn-ics-contextp (fn-replay-identity-step ctx event))
        (equal (fn-stxk-context-snapshots (fn-replay-identity-step ctx event))
               (cons event (fn-stxk-context-snapshots ctx)))
        (equal (fn-stxk-context-verdicts (fn-replay-identity-step ctx event))
               (fn-stxk-context-verdicts ctx)))))

; Actual standalone verdict checks successfully, but deliberately appends none.
(assert-event
 (let ((ctx *rist-installed*) (event *rist-verdict*) (ec '(999 nil nil)))
   (and (fn-ics-contextp ctx)
        (equal (fn-stxk-context-kind (fn-replay-identity-step ctx event)) :ok)
        (equal (nth 1 (rist-effects ctx event)) :none)
        (null (nth 2 (rist-effects ctx event)))
        (rist-child-exactp ctx event ec)
        (rist-resultp ctx (rist-carries ctx) event ec)
        (equal (fn-stxk-context-snapshots (fn-replay-identity-step ctx event))
               (fn-stxk-context-snapshots ctx))
        (equal (fn-stxk-context-verdicts (fn-replay-identity-step ctx event))
               (fn-stxk-context-verdicts ctx)))))

; Independent removal: old carries corrupted, other premises affirmed.
(assert-event
 (let* ((ctx *rist-ctx*) (event *rist-event*)
        (cs (update-nth 2 '(999 nil nil) (rist-carries ctx)))
        (ec (fn-scs-summary event)))
   (and (fn-ics-contextp ctx) (not (fn-scs-correspondsp cs ctx))
        (rist-child-exactp ctx event ec) (not (rist-resultp ctx cs event ec)))))
; Independent removal: actual changed-child size corrupted.
(assert-event
 (let* ((ctx *rist-ctx*) (event *rist-event*)
        (cs (rist-carries ctx)) (ec '(999 nil nil)))
   (and (fn-ics-contextp ctx) (fn-scs-correspondsp cs ctx)
        (not (rist-child-exactp ctx event ec))
        (not (rist-resultp ctx cs event ec)))))
; Corrupted-state removal: seventh field is outside the executable six-carry guard.
(assert-event (with-guard-checking :none
 (let* ((ctx '(:fault 0 nil nil nil :damaged :extra)) (event *rist-event*)
        (cs (rist-carries ctx)) (ec '(999 nil nil)))
   (and (not (fn-ics-contextp ctx)) (fn-scs-correspondsp cs ctx)
        (rist-child-exactp ctx event ec)
        (not (rist-resultp ctx cs event ec))
        (not (fn-ics-contextp (fn-replay-identity-step ctx event)))))))
