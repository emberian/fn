; Whole-antecedent witnesses and two omitted-preservation controls on the
; actual executor.  No replacement loop is used.
(in-package "ACL2")
(include-book "../books/executor-contracts")
(include-book "std/testing/must-fail" :dir :system)

(defun fn2-ect-service-ready (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-sched (fn2-core-sched fn2-core)))
    (ready) (fn2-sched-service-ready 0 fn2-sched) ready))
(defun fn2-ect-service-set (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-sched (fn2-core-sched fn2-core)))
    (fn2-sched) (fn2-sched-set-service 0 1 fn2-sched) fn2-core))

(defun fn2-ect-witnesses-core (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((fn2-core (fn2-init-executor *fn2-profile-tiny* :echo nil fn2-core))
       (pre (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)))
       ((mv status obs visits actions fn2-core) (fn2-turn fn2-core))
       (positive (and pre (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                      (eq status :more) (equal obs 0) (< 0 visits) (< 0 actions)))
       (fn2-core (fn2-exec-set-turn-steps 0 fn2-core))
       (account-pre (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                         (equal (fn2-exec-turn-steps fn2-core) 0)))
       (fn2-core (fn2-exec-account-work 0 1 fn2-core))
       (account-negative (and account-pre (equal (fn2-exec-turn-steps fn2-core) 1)))
       (fn2-core (fn2-ect-service-set fn2-core))
       (service-pre (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                         (fn2-ect-service-ready fn2-core)))
       ((mv & & & & & fn2-core) (fn2-exec-service 0 0 0 fn2-core)))
    (mv (list positive account-negative
              (and service-pre (not (fn2-ect-service-ready fn2-core)))) fn2-core)))
(defun fn2-ect-witnesses ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (result fn2-core) (fn2-ect-witnesses-core fn2-core) result)))
(assert-event (equal (fn2-ect-witnesses) '(t t t)))

; Removing either obligation cannot be repaired by the turn induction.
; These are rejected functional instances, paired with the concrete
; before/after counterexamples above (proof failure alone is not evidence).
(defun-nx fn2-ect-no-account-inv (g c)
  (declare (ignorable g))
  (equal (fn2-exec-turn-steps c) 0))
(defun-nx fn2-ect-no-account-rel (tag args g before after)
  (declare (ignorable args))
  (or (equal tag 'fn2-exec-account-work)
      (implies (fn2-ect-no-account-inv g before) (fn2-ect-no-account-inv g after))))
(defun-nx fn2-ect-no-service-inv (g c)
  (declare (ignorable g))
  (fn2-ect-service-ready c))
(defun-nx fn2-ect-no-service-rel (tag args g before after)
  (declare (ignorable args))
  (or (equal tag 'fn2-exec-clear-service)
      (implies (fn2-ect-no-service-inv g before) (fn2-ect-no-service-inv g after))))
(set-prover-step-limit 10000)
(must-fail
 (defthm fn2-ect-account-omission
   (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                 (fn2-ect-no-account-inv g fn2-core))
            (fn2-ect-no-account-inv g (mv-nth 4 (fn2-turn fn2-core))))
   :hints (("Goal" :use ((:functional-instance fn2-executor-inv-turn
                           (fn2-executor-inv fn2-ect-no-account-inv)
                           (fn2-executor-rel fn2-ect-no-account-rel)))
            :in-theory (disable fn2-corep fn2-core-wfp fn2-turn fn2-exec-turn-steps)
            :do-not-induct t))))
(must-fail
 (defthm fn2-ect-service-omission
   (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                 (fn2-ect-no-service-inv g fn2-core))
            (fn2-ect-no-service-inv g (mv-nth 4 (fn2-turn fn2-core))))
   :hints (("Goal" :use ((:functional-instance fn2-executor-inv-turn
                           (fn2-executor-inv fn2-ect-no-service-inv)
                           (fn2-executor-rel fn2-ect-no-service-rel)))
            :in-theory (disable fn2-corep fn2-core-wfp fn2-turn fn2-ect-service-ready)
            :do-not-induct t))))

;; THE DISPATCH FRAME's controls (assembly-dispatch.lisp). A connection kind
;; holds no batch membership, so its stub's frame excludes the commit table:
;; an attachment writing a commit row's reply count is refused by name, and
;; its defattach fails the stub's -ARM-KIDS constraint, while a refusing
;; attachment outside the commit children is accepted by both.
(set-prover-step-limit nil)
(defun fn2-ect-refuser (id budget fn2-core)
  (declare (xargs :stobjs fn2-core
                  :guard (and (fn2-core-wfp fn2-core) (fn2-machine-idp id fn2-core)
                              (equal (fn2-machine-kind id fn2-core) *fn2-conn-kind*)))
           (ignore budget))
  (fn2-machine-refuse-phase id fn2-core))
(fn2-core-preserves fn2-ect-refuser (id budget fn2-core) :position 4 :rows nil)
(defun fn2-ect-commit-writer (id budget fn2-core)
  (declare (xargs :stobjs fn2-core
                  :guard (and (fn2-core-wfp fn2-core) (fn2-machine-idp id fn2-core)
                              (equal (fn2-machine-kind id fn2-core) *fn2-conn-kind*)))
           (ignore budget))
  (let ((fn2-core (fn2-commit-write+cb-acks id 1 fn2-core)))
    (fn2-machine-refuse-phase id fn2-core)))
(fn2-core-preserves fn2-ect-commit-writer (id budget fn2-core) :position 4 :rows nil)
(make-event (value (cons 'progn (fn2-dc-forms (fn2-dc-todo '(fn2-ect-refuser fn2-ect-commit-writer) 'fn2-conn (w state) nil 64)
                                              'fn2-conn))))
(assert-event (let ((e (fn2-dispatch-frame-children 'fn2-conn (w state))))
                (and (not (member 9 e)) (member 9 (fn2-dispatch-frame-children 'fn2-txn (w state)))
                     (member 9 (cdr (assoc-equal '(fn2-conn . fn2-ect-commit-writer) (table-alist 'fn2-dc-kids (w state))))))))
(make-event (value (fn2-dc-frame-check 'fn2-conn-run-stub 'fn2-ect-refuser 'fn2-conn (fn2-dispatch-frame-children 'fn2-conn (w state)) (w state))))
(must-fail
 (make-event (value (fn2-dc-frame-check 'fn2-conn-run-stub 'fn2-ect-commit-writer 'fn2-conn (fn2-dispatch-frame-children 'fn2-conn (w state)) (w state)))))
(make-event (value (cons 'progn (fn2-ctf-dir-forms '(fn2-ect-refuser fn2-ect-commit-writer) 'fn2-conn))))
(make-event (value (fn2-dc-frame-kids 'fn2-ect-refuser 4 '(id budget fn2-core)
                                       (fn2-dispatch-frame-children 'fn2-conn (w state)) 'fn2-conn "-DISPATCH-KIDS" (w state))))
(in-theory (enable fn2-machine-observe-fn2-conn-default-arm-kids fn2-machine-observe-fn2-conn-default-ctf-dir
                    fn2-machine-observe-fn2-conn-default-ops-pool))
;; the refusing run keeps the rows the commit kind holds (its held chain)
(make-event (value (cons 'progn (fn2-dh-chain-forms (fn2-dh-postorder-new '(fn2-ect-refuser) (w state)) 'fn2-conn))))
(make-event (value (fn2-dh-claim-form 'fn2-conn-run-stub 'fn2-ect-refuser 4 (w state))))
(defattach (fn2-conn-run-stub fn2-ect-refuser)
           (fn2-machine-observe-fn2-conn-stub fn2-machine-observe-fn2-conn-default)
           (fn2-conn-arm-charge-ok-p-stub fn2-conn-arm-charge-ok-p-default)
           (fn2-conn-arm-bound-stub fn2-conn-arm-bound-default))
(must-fail
 (defattach (fn2-conn-run-stub fn2-ect-commit-writer)
            (fn2-machine-observe-fn2-conn-stub fn2-machine-observe-fn2-conn-default)
            (fn2-conn-arm-charge-ok-p-stub fn2-conn-arm-charge-ok-p-default)
            (fn2-conn-arm-bound-stub fn2-conn-arm-bound-default)))

;; THE OBSERVE STUB's ops-and-pool frame (FN2-DISPATCH-OPS-POOL): an observe
;; attachment issuing a Close owned by the commit kind writes a commit-owned
;; op row and the outbox, so its footprint check is refused naming
;; FN2-ISSUE-CLOSE, and its defattach fails the stub's -OPS-POOL constraint
;; (its KIDS and directory contracts proved, so that constraint alone fails);
;; the refusing default meets it.
(defun fn2-ect-op-writer (id event outcome reason count aux0 aux1 fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core))
           (ignore event outcome reason count aux0 aux1))
  (mv-let (code slot gen fn2-core) (fn2-issue-close 0 0 *fn2-commit-kind* id 0 0 fn2-core)
    (declare (ignore code slot gen))
    (mv *fn2-none* fn2-core)))
(fn2-core-preserves fn2-ect-op-writer (id event outcome reason count aux0 aux1 fn2-core) :position 1 :rows nil)
(make-event (value (cons 'progn (fn2-dc-forms (fn2-dc-todo '(fn2-ect-op-writer) 'fn2-conn (w state) nil 64) 'fn2-conn))))
(assert-event (subsetp-equal (fn2-dispatch-ops-pool-children (w state))
                             (cdr (assoc-equal '(fn2-conn . fn2-ect-op-writer) (table-alist 'fn2-dc-kids (w state))))))
(make-event (value (fn2-dc-frame-check 'fn2-machine-observe-fn2-conn-stub 'fn2-ect-op-writer 'fn2-conn
                                       (fn2-dispatch-frame-children 'fn2-conn (w state)) (w state))))
(must-fail
 (make-event (value (fn2-dispatch-ops-pool-form 'fn2-machine-observe-fn2-conn-stub 'fn2-ect-op-writer 'fn2-conn
                                                (fn2-dispatch-frame-children 'fn2-conn (w state)) (w state)))))
(make-event (value (cons 'progn (fn2-ctf-dir-forms '(fn2-ect-op-writer) 'fn2-conn))))
(make-event (value (fn2-dc-frame-kids 'fn2-ect-op-writer 1 '(id event outcome reason count aux0 aux1 fn2-core)
                                       (fn2-dispatch-frame-children 'fn2-conn (w state)) 'fn2-conn "-DISPATCH-KIDS" (w state))))
(must-fail
 (defattach (fn2-conn-run-stub fn2-ect-refuser)
            (fn2-machine-observe-fn2-conn-stub fn2-ect-op-writer)
            (fn2-conn-arm-charge-ok-p-stub fn2-conn-arm-charge-ok-p-default)
            (fn2-conn-arm-bound-stub fn2-conn-arm-bound-default)))
;; THE RUN STUB's held frame (FN2-DISPATCH-HELD): a connection run issuing a
;; Close owned by the commit kind may write a row the commit kind holds, so
;; its held claim is refused naming FN2-ISSUE-CLOSE (the issue's owner kind
;; is the commit kind's), and its defattach fails the stub's -DISPATCH-HELD
;; constraint (its KIDS and directory contracts proved, so that constraint
;; alone fails); the refusing run above meets it.
(defun fn2-ect-commit-closer (id budget fn2-core)
  (declare (xargs :stobjs fn2-core
                  :guard (and (fn2-core-wfp fn2-core) (fn2-machine-idp id fn2-core)
                              (equal (fn2-machine-kind id fn2-core) *fn2-conn-kind*)))
           (ignore budget))
  (mv-let (code slot gen fn2-core) (fn2-issue-close 0 0 *fn2-commit-kind* id 0 0 fn2-core)
    (declare (ignore code slot gen))
    (fn2-machine-refuse-phase id fn2-core)))
(fn2-core-preserves fn2-ect-commit-closer (id budget fn2-core) :position 4 :rows nil)
(make-event (value (cons 'progn (fn2-dc-forms (fn2-dc-todo '(fn2-ect-commit-closer) 'fn2-conn (w state) nil 64) 'fn2-conn))))
(make-event (value (fn2-dc-frame-check 'fn2-conn-run-stub 'fn2-ect-commit-closer 'fn2-conn
                                       (fn2-dispatch-frame-children 'fn2-conn (w state)) (w state))))
(make-event (value (cons 'progn (fn2-ctf-dir-forms '(fn2-ect-commit-closer) 'fn2-conn))))
(make-event (value (fn2-dc-frame-kids 'fn2-ect-commit-closer 4 '(id budget fn2-core)
                                       (fn2-dispatch-frame-children 'fn2-conn (w state)) 'fn2-conn "-DISPATCH-KIDS" (w state))))
(make-event (value (cons 'progn (fn2-dh-chain-forms (fn2-dh-postorder-new '(fn2-ect-commit-closer) (w state)) 'fn2-conn))))
(assert-event
 (let ((bad (fn2-dh-bad-hyps (fn2-dh-all-hyps (fn2-dh-facts 'fn2-ect-commit-closer (w state))) *fn2-commit-kind*)))
   (and (consp bad) (equal (cadr (car bad)) 'fn2-issue-close))))
(must-fail
 (make-event (value (fn2-dh-claim-form 'fn2-conn-run-stub 'fn2-ect-commit-closer 4 (w state)))))
(must-fail
 (defattach (fn2-conn-run-stub fn2-ect-commit-closer)
            (fn2-machine-observe-fn2-conn-stub fn2-machine-observe-fn2-conn-default)
            (fn2-conn-arm-charge-ok-p-stub fn2-conn-arm-charge-ok-p-default)
            (fn2-conn-arm-bound-stub fn2-conn-arm-bound-default)))
