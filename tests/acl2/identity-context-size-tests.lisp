; PRF-1120. Literal transition hypotheses, reachable positives and removals.
(in-package "ACL2")
(include-book "../../books/identity-context-size")
(include-book "store-tree-size-tests")
(include-book "held-record-size-tests")

(defun icst-carries (xs)
  (if (consp xs) (cons (fn-scs-summary (car xs)) (icst-carries (cdr xs))) nil))
(defconst *icst-initial* (fn-stxk-initial-context 0))
(defconst *icst-snapshot* (fn-stxk-make 0 1 1 0 '(1) '(7 8)))
(defconst *icst-installed* (fn-stxk-apply-snapshot *icst-initial* *icst-snapshot*))
(defconst *icst-verdict* (fn-stxe-make 1 2 2 "<a@x>" :unverified '(9) 0 '(1)))

(defun icst-snapshot (ctx carries event event-carry)
  (mv-list 2 (fn-ics-snapshot ctx carries event event-carry)))
(defun icst-verdict (ctx carries event event-carry)
  (mv-list 2 (fn-ics-verdict ctx carries event event-carry)))
(defun icst-resultp (result)
  (fn-scs-correspondsp (nth 1 result) (nth 0 result)))

; Both positive witnesses assert every literal antecedent plus conclusion;
; both install nonempty data via their actual decision constructor.
(assert-event
 (let ((ctx *icst-initial*) (event *icst-snapshot*)
       (cs (icst-carries *icst-initial*)) (ec (fn-scs-summary *icst-snapshot*)))
   (and (fn-ics-contextp ctx) (fn-scs-correspondsp cs ctx)
        (equal ec (fn-scs-summary event))
        (icst-resultp (icst-snapshot ctx cs event ec))
        (consp (fn-stxk-context-snapshots (car (icst-snapshot ctx cs event ec)))))))
(assert-event
 (let ((ctx *icst-installed*) (event *icst-verdict*)
       (cs (icst-carries *icst-installed*)) (ec (fn-scs-summary *icst-verdict*)))
   (and (fn-ics-contextp ctx) (fn-scs-correspondsp cs ctx)
        (equal ec (fn-scs-summary event))
        (icst-resultp (icst-verdict ctx cs event ec))
        (consp (fn-stxk-context-verdicts (car (icst-verdict ctx cs event ec)))))))

; Snapshot duplicate, conflict, cursor-width crossing and initial fault.
(assert-event
 (let* ((ctx *icst-installed*) (cs (icst-carries ctx))
        (same (fn-stxk-make 1 2 2 0 '(1) '(7 8)))
        (bad (fn-stxk-make 1 2 2 0 '(1) '(7 9)))
        (r1 (icst-snapshot ctx cs same (fn-scs-summary same)))
        (r2 (icst-snapshot ctx cs bad (fn-scs-summary bad))))
   (and (icst-resultp r1) (icst-resultp r2)
        (equal (fn-stxk-context-snapshots (car r1)) (fn-stxk-context-snapshots ctx))
        (equal (fn-stxk-context-kind (car r2)) :fault))))
(assert-event
 (let* ((ctx (fn-stxk-context :ok 255 nil nil nil nil))
        (event (fn-stxk-make 255 256 256 0 '(1) '(7 8)))
        (result (icst-snapshot ctx (icst-carries ctx) event (fn-scs-summary event))))
   (and (icst-resultp result) (equal (fn-stxk-context-next (car result)) 256))))

; Each theorem: remove correspondence, affirm context and event hypotheses.
(assert-event
 (let* ((ctx *icst-initial*) (event *icst-snapshot*)
        (cs (update-nth 2 '(999 nil nil) (icst-carries ctx)))
        (ec (fn-scs-summary event)))
   (and (fn-ics-contextp ctx) (not (fn-scs-correspondsp cs ctx))
        (equal ec (fn-scs-summary event))
        (not (icst-resultp (icst-snapshot ctx cs event ec))))))
(assert-event
 (let* ((ctx *icst-installed*) (event *icst-verdict*)
        (cs (update-nth 3 '(999 nil nil) (icst-carries ctx)))
        (ec (fn-scs-summary event)))
   (and (fn-ics-contextp ctx) (not (fn-scs-correspondsp cs ctx))
        (equal ec (fn-scs-summary event))
        (not (icst-resultp (icst-verdict ctx cs event ec))))))

; Each theorem: remove event-size equality, affirm both retained hypotheses.
(assert-event
 (let* ((ctx *icst-initial*) (event *icst-snapshot*)
        (cs (icst-carries ctx)) (ec '(999 nil nil)))
   (and (fn-ics-contextp ctx) (fn-scs-correspondsp cs ctx)
        (not (equal ec (fn-scs-summary event)))
        (not (icst-resultp (icst-snapshot ctx cs event ec))))))
(assert-event
 (let* ((ctx *icst-installed*) (event *icst-verdict*)
        (cs (icst-carries ctx)) (ec '(999 nil nil)))
   (and (fn-ics-contextp ctx) (fn-scs-correspondsp cs ctx)
        (not (equal ec (fn-scs-summary event)))
        (not (icst-resultp (icst-verdict ctx cs event ec))))))

; Context hypothesis removal, explicitly corrupted-state (extra seventh slot).
; This logical case is outside the six-field sidecar's executable guard.

(assert-event (with-guard-checking :none
 (let* ((ctx '(:fault 0 nil nil nil :damaged :extra))
        (cs (icst-carries ctx)) (event *icst-snapshot*) (ec (fn-scs-summary event)))
   (and (not (fn-ics-contextp ctx)) (fn-scs-correspondsp cs ctx)
        (equal ec (fn-scs-summary event))
        (not (icst-resultp (icst-snapshot ctx cs event ec)))))))
(assert-event (with-guard-checking :none
 (let* ((ctx '(:fault 0 nil nil nil :damaged :extra))
        (cs (icst-carries ctx)) (event *icst-verdict*) (ec (fn-scs-summary event)))
   (and (not (fn-ics-contextp ctx)) (fn-scs-correspondsp cs ctx)
        (equal ec (fn-scs-summary event))
        (not (icst-resultp (icst-verdict ctx cs event ec)))))))


; Initial cursor can start across the same scalar-width boundary.
(assert-event
 (let ((result (mv-list 2 (fn-ics-begin 256))))
   (and (natp 256) (fn-ics-contextp (nth 0 result))
        (fn-scs-correspondsp (nth 1 result) (nth 0 result)))))
(assert-event
 (and (eq (symbol-class 'fn-ics-snapshot (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-ics-verdict (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-ics-begin (w state)) :common-lisp-compliant)))
