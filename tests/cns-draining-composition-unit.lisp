; Actual initializer -> public take -> cancel -> final reclaim. These
; direct application controls do not import the reference/Q1 world.
(in-package "ACL2")
(include-book "../books/cns-draining-composition")
(include-book "cns-draining-count-counterexample")

(make-event
 (let* ((fn 'fn2-machine-take-fn2-cns)
        (formals (getpropc fn 'formals nil (w state)))
        (actuals (append (kwote-lst (list *fn2-none* *fn2-none* 0 1 0 0 4 *fn2-none* 0))
                         '(fn2-core))))
   (if (or (not (equal formals '(waiter ctl ctl-gen request fpos flen fkind tx-slot tx-gen fn2-core)))
           (not (equal (getpropc fn 'stobjs-out nil (w state)) '(nil nil nil fn2-core))))
       (er soft 'fn2-cns-take-served-guard "Actual CNS take ABI changed.")
     (value
      `(defun fn2-cns-take-served-guard (fn2-core)
         (declare (xargs :stobjs fn2-core :verify-guards nil))
         ,(sublis-var (pairlis$ formals actuals) (getpropc fn 'guard t (w state))))))))

(defun fn2-cns-reservation-observedp (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-machines (fn2-core-machines fn2-core))) (yes)
    (fn2-machines-partition-reservedp *fn2-cns-admission-ordinal* fn2-machines) yes))
(defun fn2-cns-reservation-served-run (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((profile *fn2-cns-drain-profile*)
       (supported (fn2-core-profilep profile))
       (fn2-core (fn2-core-init profile fn2-core))
       (entry (and (fn2-corep fn2-core) (fn2-cns-take-served-guard fn2-core)
                   (fn2-cns-draining-reservedp (fn2-test-core-snapshot fn2-core))
                   (fn2-cns-reservation-observedp fn2-core)))
       ((mv code id & fn2-core)
        (fn2-machine-take-fn2-cns *fn2-none* *fn2-none* 0 1 0 0 4 *fn2-none* 0 fn2-core))
       (taken (and (eq code :ok) (fn2-cns-reservation-observedp fn2-core)))
       ((mv & & & & fn2-core) (fn2-cns-run id 4 fn2-core))
       (cancelled (and (equal (fn2-cns-row-phase id fn2-core) *fn2-cns-state-draining*)
                       (fn2-cns-reservation-observedp fn2-core)))
       (before (fn2-test-core-snapshot fn2-core))
       (whole-h (and (fn2-cns-drain-counted-basep before fn2-core)
                     (fn2-cns-draining-domainp id before)))
       ((mv b s d r fn2-core) (fn2-cns-run id 4 fn2-core))
       (after (fn2-test-core-snapshot fn2-core)))
    (mv (and supported entry taken cancelled whole-h
             (fn2-cns-draining-resultp id before b s d r after)
             (fn2-cns-reservation-observedp fn2-core)) fn2-core)))
(defun fn2-cns-reservation-served-control ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (yes fn2-core) (fn2-cns-reservation-served-run fn2-core) yes)))
(assert-event (fn2-cns-reservation-served-control))
; The old WFP-only removals remain live controls for the actual semantic
; accounting and partition-reservation hypotheses; they are not relabeled
; as initialized-state failures or atomic rollback guarantees.
(assert-event (and (fn2-cns-drain-without-pool-accounting)
                   (fn2-cns-drain-without-reservation)))
