; Literal teeth for the actual planner boundary. Mutation/refusal witnesses
; below are explicitly corrupted-state cases, not reachable lifecycle claims.
(in-package "ACL2")
(include-book "../../books/consumer-account-row-relation")
(defconst *caarrt-32* (make-list 32 :initial-element 9))
(defconst *caarrt-16* (make-list 16 :initial-element 8))
(defun fn-caarrt-event (s txid op)
  (list :consumer-authority (fn-cp-nth 3 s) txid 0 op))
(defun fn-caarrt-next (s txid op)
  (fn-cp-nth 1 (fn-caa-step s (fn-caarrt-event s txid op))))
(defun fn-caarrt-row-op (candidate base birth flag)
  (list :authority-row candidate base '(97) birth
        *caarrt-32* *caarrt-16* *caarrt-32* *caarrt-32* *caarrt-32* flag))
(defun fn-caarrt-seal (s txid candidate base)
  (let ((p (fn-cp-nth 5 (fn-cp-nth 6 s))))
    (fn-caarrt-next s txid
     (list :authority-seal candidate base (fn-cp-nth 3 p) (fn-cp-nth 7 p)))))
(defun fn-caarrt-fence (s txid candidate base)
  (let ((p (fn-cp-nth 5 (fn-cp-nth 6 s))))
    (fn-caarrt-next s txid
     (list :authority-fence candidate base (fn-cp-nth 3 p) (fn-cp-nth 7 p)))))
(defconst *caarrt-initial* (fn-cp-state *caarrt-32* *caarrt-32* 0 1 nil))
(defconst *caarrt-begun*
 (fn-caarrt-next *caarrt-initial* 1 '(:authority-begin (65) 0 1 7)))
(defconst *caarrt-new-op* (fn-caarrt-row-op '(65) 0 2 1))
(defconst *caarrt-new-event* (fn-caarrt-event *caarrt-begun* 2 *caarrt-new-op*))
(defconst *caarrt-new-a* (fn-cp-nth 6 *caarrt-begun*))
(defconst *caarrt-rowed* (fn-caarrt-next *caarrt-begun* 2 *caarrt-new-op*))
(defconst *caarrt-sealed* (fn-caarrt-seal *caarrt-rowed* 3 '(65) 0))
(defconst *caarrt-prepared*
 (fn-caarrt-next *caarrt-sealed* 4 '(:authority-prepare (65) 0)))
(defconst *caarrt-published* (fn-caarrt-fence *caarrt-prepared* 5 '(65) 0))
(defconst *caarrt-retain-begun*
 (fn-caarrt-next *caarrt-published* 6 '(:authority-begin (66) 1 3 7)))
(defconst *caarrt-retain-a* (fn-cp-nth 6 *caarrt-retain-begun*))
(defconst *caarrt-retain-op* (fn-caarrt-row-op '(66) 1 2 0))
(defconst *caarrt-retain-event*
 (fn-caarrt-event *caarrt-retain-begun* 7 *caarrt-retain-op*))
(defconst *caarrt-tomb-op* '(:authority-tombstone (66) 1 (97) 2))
(defconst *caarrt-tomb-event*
 (fn-caarrt-event *caarrt-retain-begun* 7 *caarrt-tomb-op*))
(defconst *caarrt-tombed*
 (fn-caarrt-next *caarrt-retain-begun* 7 *caarrt-tomb-op*))
(defconst *caarrt-tomb-sealed* (fn-caarrt-seal *caarrt-tombed* 8 '(66) 1))
(defconst *caarrt-tomb-prepared*
 (fn-caarrt-next *caarrt-tomb-sealed* 9 '(:authority-prepare (66) 1)))
(defconst *caarrt-tomb-published*
 (fn-caarrt-fence *caarrt-tomb-prepared* 10 '(66) 1))
(defconst *caarrt-rebirth-begun*
 (fn-caarrt-next *caarrt-tomb-published* 11 '(:authority-begin (67) 2 8 7)))
(defconst *caarrt-rebirth-a* (fn-cp-nth 6 *caarrt-rebirth-begun*))
(defconst *caarrt-rebirth-op* (fn-caarrt-row-op '(67) 2 12 1))
(defconst *caarrt-rebirth-event*
 (fn-caarrt-event *caarrt-rebirth-begun* 12 *caarrt-rebirth-op*))
; These helpers only construct fixed corruption fixtures. No test predicate
; abbreviates the literal theorem's antecedent or conclusion.
(defun fn-caarrt-prep-replace (a prep)
  (update-nth 5 (update-nth 5 prep (fn-cp-nth 5 a)) a))
(defun fn-caarrt-head-replace (a head)
  (let ((prep (fn-cp-nth 5 (fn-cp-nth 5 a))))
    (fn-caarrt-prep-replace a (update-nth 2 (list head) prep))))
(defconst *caarrt-no-namespace-a*
 (fn-caarrt-prep-replace *caarrt-new-a*
   (update-nth 6 nil (fn-cp-nth 5 (fn-cp-nth 5 *caarrt-new-a*)))))
(defconst *caarrt-wrong-phase-a*
 (fn-caarrt-prep-replace *caarrt-retain-a*
   (update-nth 1 :reverse (fn-cp-nth 5 (fn-cp-nth 5 *caarrt-retain-a*)))))
(defconst *caarrt-original-head*
 (car (fn-cp-nth 2 (fn-cp-nth 5 (fn-cp-nth 5 *caarrt-retain-a*)))))
(defconst *caarrt-bad-token-a*
 (fn-caarrt-head-replace *caarrt-retain-a*
   (update-nth 2 (append (fn-cp-nth 2 *caarrt-original-head*) '(0))
               *caarrt-original-head*)))
(defconst *caarrt-empty-name-a*
 (fn-caarrt-head-replace *caarrt-retain-a*
   (update-nth 1 nil *caarrt-original-head*)))
(defconst *caarrt-invalid-codec-op* (fn-caarrt-row-op '(65) 0 2 2))
(defconst *caarrt-wide-op* (fn-caarrt-row-op '(65) 0 4294967296 1))
(defconst *caarrt-wide-event*
 (fn-caarrt-event *caarrt-begun* 4294967296 *caarrt-wide-op*))

;@positive fn-caarr-row-plan-establishes-binding
(defthm caarrt-actual-new-row-complete-positive
 (let* ((a *caarrt-new-a*) (event *caarrt-new-event*) (op *caarrt-new-op*)
        (p (fn-cp-nth 5 a)) (prep (fn-cp-nth 5 p))
        (old (fn-cp-nth 2 prep)) (head (if (consp old) (car old) nil))
        (name (fn-cp-nth 3 op)) (plan (fn-caa-row-plan a event op)))
  (and
       (fn-cac-operationp op)
       (fn-cp-authority-namespacep (fn-cp-nth 6 prep))
       (fn-cp-uintp (fn-cp-nth 2 event))
       (implies (and head (equal name (fn-cp-nth 1 head))
                         (fn-cp-nth 3 head))
                    (fn-cp-account-creationp (fn-cp-nth 2 head) (fn-cp-nth 4 p)))
       (equal (car plan) :stage)
       (fn-caar-bindingp
       (fn-cp-nth 1 plan)
       (list :account-binding (fn-cp-nth 1 plan) (fn-cp-nth 2 plan))
       (max (nfix (fn-cp-nth 4 p)) (1+ (nfix (fn-cp-nth 2 event)))))
       (fn-cac-eventp event)
       (equal (len (fn-cp-nth 2 (fn-cp-nth 1 plan))) 48)
       (equal (fn-cp-creation-coordinate (fn-cp-nth 2 (fn-cp-nth 1 plan))) 2)
       (equal (len (fn-cp-nth 4 (fn-cp-nth 1 plan))) 145)))
 :rule-classes nil)

;@positive fn-caarr-row-plan-establishes-binding
(defthm caarrt-actual-retained-row-complete-positive
 (let* ((a *caarrt-retain-a*) (event *caarrt-retain-event*) (op *caarrt-retain-op*)
        (p (fn-cp-nth 5 a)) (prep (fn-cp-nth 5 p))
        (old (fn-cp-nth 2 prep)) (head (if (consp old) (car old) nil))
        (name (fn-cp-nth 3 op)) (plan (fn-caa-row-plan a event op)))
  (and
       (fn-cac-operationp op)
       (fn-cp-authority-namespacep (fn-cp-nth 6 prep))
       (fn-cp-uintp (fn-cp-nth 2 event))
       (implies (and head (equal name (fn-cp-nth 1 head))
                         (fn-cp-nth 3 head))
                    (fn-cp-account-creationp (fn-cp-nth 2 head) (fn-cp-nth 4 p)))
       (equal (car plan) :stage)
       (fn-caar-bindingp
       (fn-cp-nth 1 plan)
       (list :account-binding (fn-cp-nth 1 plan) (fn-cp-nth 2 plan))
       (max (nfix (fn-cp-nth 4 p)) (1+ (nfix (fn-cp-nth 2 event)))))
       (fn-cac-eventp event)
       (equal (fn-cp-nth 2 (fn-cp-nth 1 plan)) (fn-cp-nth 2 head))
       (equal (fn-cp-creation-coordinate (fn-cp-nth 2 (fn-cp-nth 1 plan))) 2)
       (equal (len (fn-cp-nth 4 (fn-cp-nth 1 plan))) 145)))
 :rule-classes nil)

;@positive fn-caarr-row-plan-establishes-binding
(defthm caarrt-actual-resurrected-row-complete-positive
 (let* ((a *caarrt-rebirth-a*) (event *caarrt-rebirth-event*) (op *caarrt-rebirth-op*)
        (p (fn-cp-nth 5 a)) (prep (fn-cp-nth 5 p))
        (old (fn-cp-nth 2 prep)) (head (if (consp old) (car old) nil))
        (name (fn-cp-nth 3 op)) (plan (fn-caa-row-plan a event op)))
  (and
       (fn-cac-operationp op)
       (fn-cp-authority-namespacep (fn-cp-nth 6 prep))
       (fn-cp-uintp (fn-cp-nth 2 event))
       (implies (and head (equal name (fn-cp-nth 1 head))
                         (fn-cp-nth 3 head))
                    (fn-cp-account-creationp (fn-cp-nth 2 head) (fn-cp-nth 4 p)))
       (equal (car plan) :stage)
       (fn-caar-bindingp
       (fn-cp-nth 1 plan)
       (list :account-binding (fn-cp-nth 1 plan) (fn-cp-nth 2 plan))
       (max (nfix (fn-cp-nth 4 p)) (1+ (nfix (fn-cp-nth 2 event)))))
       (fn-cac-eventp event) head (null (fn-cp-nth 3 head))
       (not (equal (fn-cp-nth 2 (fn-cp-nth 1 plan)) (fn-cp-nth 2 head)))
       (equal (fn-cp-creation-coordinate (fn-cp-nth 2 (fn-cp-nth 1 plan))) 12)))
 :rule-classes nil)

;@hypothesis-removal fn-caarr-row-plan-establishes-binding
(defthm caarrt-corrupted-flag-codec-removal
 (let* ((a *caarrt-new-a*) (event *caarrt-new-event*) (op *caarrt-invalid-codec-op*)
        (p (fn-cp-nth 5 a)) (prep (fn-cp-nth 5 p))
        (old (fn-cp-nth 2 prep)) (head (if (consp old) (car old) nil))
        (name (fn-cp-nth 3 op)) (plan (fn-caa-row-plan a event op)))
  (and
       (not (fn-cac-operationp op))
       (fn-cp-authority-namespacep (fn-cp-nth 6 prep))
       (fn-cp-uintp (fn-cp-nth 2 event))
       (implies (and head (equal name (fn-cp-nth 1 head))
                         (fn-cp-nth 3 head))
                    (fn-cp-account-creationp (fn-cp-nth 2 head) (fn-cp-nth 4 p)))
       (equal (car plan) :stage)
       (not (fn-caar-bindingp
       (fn-cp-nth 1 plan)
       (list :account-binding (fn-cp-nth 1 plan) (fn-cp-nth 2 plan))
       (max (nfix (fn-cp-nth 4 p)) (1+ (nfix (fn-cp-nth 2 event))))))))
 :rule-classes nil)

;@hypothesis-removal fn-caarr-row-plan-establishes-binding
(defthm caarrt-corrupted-namespace-removal
 (let* ((a *caarrt-no-namespace-a*) (event *caarrt-new-event*) (op *caarrt-new-op*)
        (p (fn-cp-nth 5 a)) (prep (fn-cp-nth 5 p))
        (old (fn-cp-nth 2 prep)) (head (if (consp old) (car old) nil))
        (name (fn-cp-nth 3 op)) (plan (fn-caa-row-plan a event op)))
  (and
       (fn-cac-operationp op)
       (not (fn-cp-authority-namespacep (fn-cp-nth 6 prep)))
       (fn-cp-uintp (fn-cp-nth 2 event))
       (implies (and head (equal name (fn-cp-nth 1 head))
                         (fn-cp-nth 3 head))
                    (fn-cp-account-creationp (fn-cp-nth 2 head) (fn-cp-nth 4 p)))
       (equal (car plan) :stage)
       (not (fn-caar-bindingp
       (fn-cp-nth 1 plan)
       (list :account-binding (fn-cp-nth 1 plan) (fn-cp-nth 2 plan))
       (max (nfix (fn-cp-nth 4 p)) (1+ (nfix (fn-cp-nth 2 event))))))))
 :rule-classes nil)

;@hypothesis-removal fn-caarr-row-plan-establishes-binding
(defthm caarrt-outside-current-creation-codec-removal
 (let* ((a *caarrt-new-a*) (event *caarrt-wide-event*) (op *caarrt-wide-op*)
        (p (fn-cp-nth 5 a)) (prep (fn-cp-nth 5 p))
        (old (fn-cp-nth 2 prep)) (head (if (consp old) (car old) nil))
        (name (fn-cp-nth 3 op)) (plan (fn-caa-row-plan a event op)))
  (and
       (fn-cac-operationp op)
       (fn-cp-authority-namespacep (fn-cp-nth 6 prep))
       (not (fn-cp-uintp (fn-cp-nth 2 event)))
       (implies (and head (equal name (fn-cp-nth 1 head))
                         (fn-cp-nth 3 head))
                    (fn-cp-account-creationp (fn-cp-nth 2 head) (fn-cp-nth 4 p)))
       (equal (car plan) :stage)
       (not (fn-caar-bindingp
       (fn-cp-nth 1 plan)
       (list :account-binding (fn-cp-nth 1 plan) (fn-cp-nth 2 plan))
       (max (nfix (fn-cp-nth 4 p)) (1+ (nfix (fn-cp-nth 2 event))))))))
 :rule-classes nil)

;@hypothesis-removal fn-caarr-row-plan-establishes-binding
(defthm caarrt-corrupted-retained-token-removal
 (let* ((a *caarrt-bad-token-a*) (event *caarrt-retain-event*) (op *caarrt-retain-op*)
        (p (fn-cp-nth 5 a)) (prep (fn-cp-nth 5 p))
        (old (fn-cp-nth 2 prep)) (head (if (consp old) (car old) nil))
        (name (fn-cp-nth 3 op)) (plan (fn-caa-row-plan a event op)))
  (and
       (fn-cac-operationp op)
       (fn-cp-authority-namespacep (fn-cp-nth 6 prep))
       (fn-cp-uintp (fn-cp-nth 2 event))
       (not (implies (and head (equal name (fn-cp-nth 1 head))
                         (fn-cp-nth 3 head))
                    (fn-cp-account-creationp (fn-cp-nth 2 head) (fn-cp-nth 4 p))))
       (equal (car plan) :stage)
       (not (fn-caar-bindingp
       (fn-cp-nth 1 plan)
       (list :account-binding (fn-cp-nth 1 plan) (fn-cp-nth 2 plan))
       (max (nfix (fn-cp-nth 4 p)) (1+ (nfix (fn-cp-nth 2 event))))))))
 :rule-classes nil)

;@hypothesis-removal fn-caarr-row-plan-establishes-binding
(defthm caarrt-corrupted-phase-stage-removal
 (let* ((a *caarrt-wrong-phase-a*) (event *caarrt-retain-event*) (op *caarrt-retain-op*)
        (p (fn-cp-nth 5 a)) (prep (fn-cp-nth 5 p))
        (old (fn-cp-nth 2 prep)) (head (if (consp old) (car old) nil))
        (name (fn-cp-nth 3 op)) (plan (fn-caa-row-plan a event op)))
  (and
       (fn-cac-operationp op)
       (fn-cp-authority-namespacep (fn-cp-nth 6 prep))
       (fn-cp-uintp (fn-cp-nth 2 event))
       (implies (and head (equal name (fn-cp-nth 1 head))
                         (fn-cp-nth 3 head))
                    (fn-cp-account-creationp (fn-cp-nth 2 head) (fn-cp-nth 4 p)))
       (not (equal (car plan) :stage))
       (not (fn-caar-bindingp
       (fn-cp-nth 1 plan)
       (list :account-binding (fn-cp-nth 1 plan) (fn-cp-nth 2 plan))
       (max (nfix (fn-cp-nth 4 p)) (1+ (nfix (fn-cp-nth 2 event))))))))
 :rule-classes nil)

;@positive fn-caarr-tombstone-plan-establishes-binding
(defthm caarrt-actual-tombstone-complete-positive
 (let* ((a *caarrt-retain-a*) (event *caarrt-tomb-event*) (op *caarrt-tomb-op*)
        (p (fn-cp-nth 5 a)) (prep (fn-cp-nth 5 p))
        (old (fn-cp-nth 2 prep)) (head (if (consp old) (car old) nil))
        (plan (fn-caa-tombstone-plan a event op)))
  (and
       (fn-cp-account-creationp (fn-cp-nth 2 head) (fn-cp-nth 4 p))
       (fn-cai-namep (fn-cp-nth 1 head) *fn-auth-max-name-octets*)
       (equal (car plan) :stage)
       (fn-caar-bindingp
       (fn-cp-nth 1 plan)
       (list :account-binding (fn-cp-nth 1 plan) (fn-cp-nth 2 plan))
       (max (nfix (fn-cp-nth 4 p)) (1+ (nfix (fn-cp-nth 2 event)))))
       (fn-cac-operationp op) (fn-cac-eventp event)
       (null (fn-cp-nth 3 (fn-cp-nth 1 plan)))
       (null (fn-cp-nth 4 (fn-cp-nth 1 plan))) (null (fn-cp-nth 2 plan))
       (equal (fn-cp-nth 2 (fn-cp-nth 1 plan)) (fn-cp-nth 2 head))))
 :rule-classes nil)

;@hypothesis-removal fn-caarr-tombstone-plan-establishes-binding
(defthm caarrt-corrupted-tombstone-token-removal
 (let* ((a *caarrt-bad-token-a*) (event *caarrt-tomb-event*) (op *caarrt-tomb-op*)
        (p (fn-cp-nth 5 a)) (prep (fn-cp-nth 5 p))
        (old (fn-cp-nth 2 prep)) (head (if (consp old) (car old) nil))
        (plan (fn-caa-tombstone-plan a event op)))
  (and
       (not (fn-cp-account-creationp (fn-cp-nth 2 head) (fn-cp-nth 4 p)))
       (fn-cai-namep (fn-cp-nth 1 head) *fn-auth-max-name-octets*)
       (equal (car plan) :stage)
       (not (fn-caar-bindingp
       (fn-cp-nth 1 plan)
       (list :account-binding (fn-cp-nth 1 plan) (fn-cp-nth 2 plan))
       (max (nfix (fn-cp-nth 4 p)) (1+ (nfix (fn-cp-nth 2 event))))))))
 :rule-classes nil)

;@hypothesis-removal fn-caarr-tombstone-plan-establishes-binding
(defthm caarrt-corrupted-tombstone-name-removal
 (let* ((a *caarrt-empty-name-a*) (event *caarrt-tomb-event*) (op '(:authority-tombstone (66) 1 nil 2))
        (p (fn-cp-nth 5 a)) (prep (fn-cp-nth 5 p))
        (old (fn-cp-nth 2 prep)) (head (if (consp old) (car old) nil))
        (plan (fn-caa-tombstone-plan a event op)))
  (and
       (fn-cp-account-creationp (fn-cp-nth 2 head) (fn-cp-nth 4 p))
       (not (fn-cai-namep (fn-cp-nth 1 head) *fn-auth-max-name-octets*))
       (equal (car plan) :stage)
       (not (fn-caar-bindingp
       (fn-cp-nth 1 plan)
       (list :account-binding (fn-cp-nth 1 plan) (fn-cp-nth 2 plan))
       (max (nfix (fn-cp-nth 4 p)) (1+ (nfix (fn-cp-nth 2 event))))))))
 :rule-classes nil)

;@hypothesis-removal fn-caarr-tombstone-plan-establishes-binding
(defthm caarrt-corrupted-tombstone-phase-removal
 (let* ((a *caarrt-wrong-phase-a*) (event *caarrt-tomb-event*) (op *caarrt-tomb-op*)
        (p (fn-cp-nth 5 a)) (prep (fn-cp-nth 5 p))
        (old (fn-cp-nth 2 prep)) (head (if (consp old) (car old) nil))
        (plan (fn-caa-tombstone-plan a event op)))
  (and
       (fn-cp-account-creationp (fn-cp-nth 2 head) (fn-cp-nth 4 p))
       (fn-cai-namep (fn-cp-nth 1 head) *fn-auth-max-name-octets*)
       (not (equal (car plan) :stage))
       (not (fn-caar-bindingp
       (fn-cp-nth 1 plan)
       (list :account-binding (fn-cp-nth 1 plan) (fn-cp-nth 2 plan))
       (max (nfix (fn-cp-nth 4 p)) (1+ (nfix (fn-cp-nth 2 event))))))))
 :rule-classes nil)

; Executable counterparts of the proved literal witness formulas.
;@positive fn-caarr-row-plan-establishes-binding
(assert-event (let* ((a *caarrt-new-a*) (event *caarrt-new-event*) (op *caarrt-new-op*)
        (p (fn-cp-nth 5 a)) (prep (fn-cp-nth 5 p))
        (old (fn-cp-nth 2 prep)) (head (if (consp old) (car old) nil))
        (name (fn-cp-nth 3 op)) (plan (fn-caa-row-plan a event op)))
  (and
       (fn-cac-operationp op)
       (fn-cp-authority-namespacep (fn-cp-nth 6 prep))
       (fn-cp-uintp (fn-cp-nth 2 event))
       (implies (and head (equal name (fn-cp-nth 1 head))
                         (fn-cp-nth 3 head))
                    (fn-cp-account-creationp (fn-cp-nth 2 head) (fn-cp-nth 4 p)))
       (equal (car plan) :stage)
       (fn-caar-bindingp
       (fn-cp-nth 1 plan)
       (list :account-binding (fn-cp-nth 1 plan) (fn-cp-nth 2 plan))
       (max (nfix (fn-cp-nth 4 p)) (1+ (nfix (fn-cp-nth 2 event)))))
       (fn-cac-eventp event)
       (equal (len (fn-cp-nth 2 (fn-cp-nth 1 plan))) 48)
       (equal (fn-cp-creation-coordinate (fn-cp-nth 2 (fn-cp-nth 1 plan))) 2)
       (equal (len (fn-cp-nth 4 (fn-cp-nth 1 plan))) 145))))

;@positive fn-caarr-row-plan-establishes-binding
(assert-event (let* ((a *caarrt-retain-a*) (event *caarrt-retain-event*) (op *caarrt-retain-op*)
        (p (fn-cp-nth 5 a)) (prep (fn-cp-nth 5 p))
        (old (fn-cp-nth 2 prep)) (head (if (consp old) (car old) nil))
        (name (fn-cp-nth 3 op)) (plan (fn-caa-row-plan a event op)))
  (and
       (fn-cac-operationp op)
       (fn-cp-authority-namespacep (fn-cp-nth 6 prep))
       (fn-cp-uintp (fn-cp-nth 2 event))
       (implies (and head (equal name (fn-cp-nth 1 head))
                         (fn-cp-nth 3 head))
                    (fn-cp-account-creationp (fn-cp-nth 2 head) (fn-cp-nth 4 p)))
       (equal (car plan) :stage)
       (fn-caar-bindingp
       (fn-cp-nth 1 plan)
       (list :account-binding (fn-cp-nth 1 plan) (fn-cp-nth 2 plan))
       (max (nfix (fn-cp-nth 4 p)) (1+ (nfix (fn-cp-nth 2 event)))))
       (fn-cac-eventp event)
       (equal (fn-cp-nth 2 (fn-cp-nth 1 plan)) (fn-cp-nth 2 head))
       (equal (fn-cp-creation-coordinate (fn-cp-nth 2 (fn-cp-nth 1 plan))) 2)
       (equal (len (fn-cp-nth 4 (fn-cp-nth 1 plan))) 145))))

;@positive fn-caarr-row-plan-establishes-binding
(assert-event (let* ((a *caarrt-rebirth-a*) (event *caarrt-rebirth-event*) (op *caarrt-rebirth-op*)
        (p (fn-cp-nth 5 a)) (prep (fn-cp-nth 5 p))
        (old (fn-cp-nth 2 prep)) (head (if (consp old) (car old) nil))
        (name (fn-cp-nth 3 op)) (plan (fn-caa-row-plan a event op)))
  (and
       (fn-cac-operationp op)
       (fn-cp-authority-namespacep (fn-cp-nth 6 prep))
       (fn-cp-uintp (fn-cp-nth 2 event))
       (implies (and head (equal name (fn-cp-nth 1 head))
                         (fn-cp-nth 3 head))
                    (fn-cp-account-creationp (fn-cp-nth 2 head) (fn-cp-nth 4 p)))
       (equal (car plan) :stage)
       (fn-caar-bindingp
       (fn-cp-nth 1 plan)
       (list :account-binding (fn-cp-nth 1 plan) (fn-cp-nth 2 plan))
       (max (nfix (fn-cp-nth 4 p)) (1+ (nfix (fn-cp-nth 2 event)))))
       (fn-cac-eventp event) head (null (fn-cp-nth 3 head))
       (not (equal (fn-cp-nth 2 (fn-cp-nth 1 plan)) (fn-cp-nth 2 head)))
       (equal (fn-cp-creation-coordinate (fn-cp-nth 2 (fn-cp-nth 1 plan))) 12))))

;@hypothesis-removal fn-caarr-row-plan-establishes-binding
(assert-event (let* ((a *caarrt-new-a*) (event *caarrt-new-event*) (op *caarrt-invalid-codec-op*)
        (p (fn-cp-nth 5 a)) (prep (fn-cp-nth 5 p))
        (old (fn-cp-nth 2 prep)) (head (if (consp old) (car old) nil))
        (name (fn-cp-nth 3 op)) (plan (fn-caa-row-plan a event op)))
  (and
       (not (fn-cac-operationp op))
       (fn-cp-authority-namespacep (fn-cp-nth 6 prep))
       (fn-cp-uintp (fn-cp-nth 2 event))
       (implies (and head (equal name (fn-cp-nth 1 head))
                         (fn-cp-nth 3 head))
                    (fn-cp-account-creationp (fn-cp-nth 2 head) (fn-cp-nth 4 p)))
       (equal (car plan) :stage)
       (not (fn-caar-bindingp
       (fn-cp-nth 1 plan)
       (list :account-binding (fn-cp-nth 1 plan) (fn-cp-nth 2 plan))
       (max (nfix (fn-cp-nth 4 p)) (1+ (nfix (fn-cp-nth 2 event)))))))))

;@hypothesis-removal fn-caarr-row-plan-establishes-binding
(assert-event (let* ((a *caarrt-no-namespace-a*) (event *caarrt-new-event*) (op *caarrt-new-op*)
        (p (fn-cp-nth 5 a)) (prep (fn-cp-nth 5 p))
        (old (fn-cp-nth 2 prep)) (head (if (consp old) (car old) nil))
        (name (fn-cp-nth 3 op)) (plan (fn-caa-row-plan a event op)))
  (and
       (fn-cac-operationp op)
       (not (fn-cp-authority-namespacep (fn-cp-nth 6 prep)))
       (fn-cp-uintp (fn-cp-nth 2 event))
       (implies (and head (equal name (fn-cp-nth 1 head))
                         (fn-cp-nth 3 head))
                    (fn-cp-account-creationp (fn-cp-nth 2 head) (fn-cp-nth 4 p)))
       (equal (car plan) :stage)
       (not (fn-caar-bindingp
       (fn-cp-nth 1 plan)
       (list :account-binding (fn-cp-nth 1 plan) (fn-cp-nth 2 plan))
       (max (nfix (fn-cp-nth 4 p)) (1+ (nfix (fn-cp-nth 2 event)))))))))

;@hypothesis-removal fn-caarr-row-plan-establishes-binding
(assert-event (let* ((a *caarrt-new-a*) (event *caarrt-wide-event*) (op *caarrt-wide-op*)
        (p (fn-cp-nth 5 a)) (prep (fn-cp-nth 5 p))
        (old (fn-cp-nth 2 prep)) (head (if (consp old) (car old) nil))
        (name (fn-cp-nth 3 op)) (plan (fn-caa-row-plan a event op)))
  (and
       (fn-cac-operationp op)
       (fn-cp-authority-namespacep (fn-cp-nth 6 prep))
       (not (fn-cp-uintp (fn-cp-nth 2 event)))
       (implies (and head (equal name (fn-cp-nth 1 head))
                         (fn-cp-nth 3 head))
                    (fn-cp-account-creationp (fn-cp-nth 2 head) (fn-cp-nth 4 p)))
       (equal (car plan) :stage)
       (not (fn-caar-bindingp
       (fn-cp-nth 1 plan)
       (list :account-binding (fn-cp-nth 1 plan) (fn-cp-nth 2 plan))
       (max (nfix (fn-cp-nth 4 p)) (1+ (nfix (fn-cp-nth 2 event)))))))))

;@hypothesis-removal fn-caarr-row-plan-establishes-binding
(assert-event (let* ((a *caarrt-bad-token-a*) (event *caarrt-retain-event*) (op *caarrt-retain-op*)
        (p (fn-cp-nth 5 a)) (prep (fn-cp-nth 5 p))
        (old (fn-cp-nth 2 prep)) (head (if (consp old) (car old) nil))
        (name (fn-cp-nth 3 op)) (plan (fn-caa-row-plan a event op)))
  (and
       (fn-cac-operationp op)
       (fn-cp-authority-namespacep (fn-cp-nth 6 prep))
       (fn-cp-uintp (fn-cp-nth 2 event))
       (not (implies (and head (equal name (fn-cp-nth 1 head))
                         (fn-cp-nth 3 head))
                    (fn-cp-account-creationp (fn-cp-nth 2 head) (fn-cp-nth 4 p))))
       (equal (car plan) :stage)
       (not (fn-caar-bindingp
       (fn-cp-nth 1 plan)
       (list :account-binding (fn-cp-nth 1 plan) (fn-cp-nth 2 plan))
       (max (nfix (fn-cp-nth 4 p)) (1+ (nfix (fn-cp-nth 2 event)))))))))

;@hypothesis-removal fn-caarr-row-plan-establishes-binding
(assert-event (let* ((a *caarrt-wrong-phase-a*) (event *caarrt-retain-event*) (op *caarrt-retain-op*)
        (p (fn-cp-nth 5 a)) (prep (fn-cp-nth 5 p))
        (old (fn-cp-nth 2 prep)) (head (if (consp old) (car old) nil))
        (name (fn-cp-nth 3 op)) (plan (fn-caa-row-plan a event op)))
  (and
       (fn-cac-operationp op)
       (fn-cp-authority-namespacep (fn-cp-nth 6 prep))
       (fn-cp-uintp (fn-cp-nth 2 event))
       (implies (and head (equal name (fn-cp-nth 1 head))
                         (fn-cp-nth 3 head))
                    (fn-cp-account-creationp (fn-cp-nth 2 head) (fn-cp-nth 4 p)))
       (not (equal (car plan) :stage))
       (not (fn-caar-bindingp
       (fn-cp-nth 1 plan)
       (list :account-binding (fn-cp-nth 1 plan) (fn-cp-nth 2 plan))
       (max (nfix (fn-cp-nth 4 p)) (1+ (nfix (fn-cp-nth 2 event)))))))))

;@positive fn-caarr-tombstone-plan-establishes-binding
(assert-event (let* ((a *caarrt-retain-a*) (event *caarrt-tomb-event*) (op *caarrt-tomb-op*)
        (p (fn-cp-nth 5 a)) (prep (fn-cp-nth 5 p))
        (old (fn-cp-nth 2 prep)) (head (if (consp old) (car old) nil))
        (plan (fn-caa-tombstone-plan a event op)))
  (and
       (fn-cp-account-creationp (fn-cp-nth 2 head) (fn-cp-nth 4 p))
       (fn-cai-namep (fn-cp-nth 1 head) *fn-auth-max-name-octets*)
       (equal (car plan) :stage)
       (fn-caar-bindingp
       (fn-cp-nth 1 plan)
       (list :account-binding (fn-cp-nth 1 plan) (fn-cp-nth 2 plan))
       (max (nfix (fn-cp-nth 4 p)) (1+ (nfix (fn-cp-nth 2 event)))))
       (fn-cac-operationp op) (fn-cac-eventp event)
       (null (fn-cp-nth 3 (fn-cp-nth 1 plan)))
       (null (fn-cp-nth 4 (fn-cp-nth 1 plan))) (null (fn-cp-nth 2 plan))
       (equal (fn-cp-nth 2 (fn-cp-nth 1 plan)) (fn-cp-nth 2 head)))))

;@hypothesis-removal fn-caarr-tombstone-plan-establishes-binding
(assert-event (let* ((a *caarrt-bad-token-a*) (event *caarrt-tomb-event*) (op *caarrt-tomb-op*)
        (p (fn-cp-nth 5 a)) (prep (fn-cp-nth 5 p))
        (old (fn-cp-nth 2 prep)) (head (if (consp old) (car old) nil))
        (plan (fn-caa-tombstone-plan a event op)))
  (and
       (not (fn-cp-account-creationp (fn-cp-nth 2 head) (fn-cp-nth 4 p)))
       (fn-cai-namep (fn-cp-nth 1 head) *fn-auth-max-name-octets*)
       (equal (car plan) :stage)
       (not (fn-caar-bindingp
       (fn-cp-nth 1 plan)
       (list :account-binding (fn-cp-nth 1 plan) (fn-cp-nth 2 plan))
       (max (nfix (fn-cp-nth 4 p)) (1+ (nfix (fn-cp-nth 2 event)))))))))

;@hypothesis-removal fn-caarr-tombstone-plan-establishes-binding
(assert-event (let* ((a *caarrt-empty-name-a*) (event *caarrt-tomb-event*) (op '(:authority-tombstone (66) 1 nil 2))
        (p (fn-cp-nth 5 a)) (prep (fn-cp-nth 5 p))
        (old (fn-cp-nth 2 prep)) (head (if (consp old) (car old) nil))
        (plan (fn-caa-tombstone-plan a event op)))
  (and
       (fn-cp-account-creationp (fn-cp-nth 2 head) (fn-cp-nth 4 p))
       (not (fn-cai-namep (fn-cp-nth 1 head) *fn-auth-max-name-octets*))
       (equal (car plan) :stage)
       (not (fn-caar-bindingp
       (fn-cp-nth 1 plan)
       (list :account-binding (fn-cp-nth 1 plan) (fn-cp-nth 2 plan))
       (max (nfix (fn-cp-nth 4 p)) (1+ (nfix (fn-cp-nth 2 event)))))))))

;@hypothesis-removal fn-caarr-tombstone-plan-establishes-binding
(assert-event (let* ((a *caarrt-wrong-phase-a*) (event *caarrt-tomb-event*) (op *caarrt-tomb-op*)
        (p (fn-cp-nth 5 a)) (prep (fn-cp-nth 5 p))
        (old (fn-cp-nth 2 prep)) (head (if (consp old) (car old) nil))
        (plan (fn-caa-tombstone-plan a event op)))
  (and
       (fn-cp-account-creationp (fn-cp-nth 2 head) (fn-cp-nth 4 p))
       (fn-cai-namep (fn-cp-nth 1 head) *fn-auth-max-name-octets*)
       (not (equal (car plan) :stage))
       (not (fn-caar-bindingp
       (fn-cp-nth 1 plan)
       (list :account-binding (fn-cp-nth 1 plan) (fn-cp-nth 2 plan))
       (max (nfix (fn-cp-nth 4 p)) (1+ (nfix (fn-cp-nth 2 event)))))))))
