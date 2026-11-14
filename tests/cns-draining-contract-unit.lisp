; Actual taken rows, full snapshots, independent application effects.
(in-package "ACL2")
(include-book "../books/cns-draining-contract")
(include-book "../books/assembly-attach")
(include-book "core-snapshot-support")
(include-book "../sim/check-trace")

(defconst *fn2-cns-drain-profile*
  (put-assoc-equal :cns 2
    (put-assoc-equal :pool-classes '((16 . 4096)) *fn2-profile-tiny*)))

(defun fn2-cns-drain-setup-profile (profile held fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((supported (fn2-core-profilep profile))
       (fn2-core (fn2-core-init profile fn2-core))
       ((mv c0 id gen fn2-core)
        (fn2-machine-take-fn2-cns *fn2-none* *fn2-none* 0 1 0 0 4 *fn2-none* 0 fn2-core))
       ((mv c1 sibling & fn2-core)
        (fn2-machine-take-fn2-cns *fn2-none* *fn2-none* 0 2 0 0 4 *fn2-none* 0 fn2-core))
       ((unless (and (eq c0 :ok) (eq c1 :ok))) (mv nil id sibling fn2-core))
       ; An admitted request whose carrier disappeared takes the real
       ; decode -> cancel -> draining path. No phase is forged here.
       ((mv & & & & fn2-core) (fn2-cns-run id 4 fn2-core))
       (entered (and (equal (fn2-cns-row-phase id fn2-core) *fn2-cns-state-draining*)
                     (not (fn2-core-stopped-p fn2-core))))
       ((mv tc0 & fn2-core) (fn2-cns-arm-wait-timer id 20 fn2-core))
       ((mv tc1 & fn2-core) (fn2-cns-arm-wait-timer sibling 40 fn2-core))
       ((mv wc fn2-core) (fn2-core-write (fn2-cns-row-ws-slot sibling fn2-core)
                          (fn2-cns-row-ws-gen sibling fn2-core) 0 77 *fn2-cns-kind* sibling
                          (fn2-cns-row-generation sibling fn2-core) fn2-core))
       ((mv lc lslot lgen fn2-core)
        (if held (fn2-core-reserve 0 *fn2-cns-kind* id gen fn2-core)
          (mv :ok *fn2-none* 0 fn2-core)))
       ; HELD deliberately exercises defensive logical input coverage:
       ; current hand/cancel edges release this lease before draining.
       (fn2-core (if held
                     (fn2-cns-put-core id (lease *fn2-cns-lease-held*) (lslot lslot) (lgen lgen))
                   fn2-core)))
    (mv (and supported entered (eq tc0 :ok) (eq tc1 :ok) (eq wc :ok) (eq lc :ok)) id sibling fn2-core)))
(defun fn2-cns-drain-setup (held fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (fn2-cns-drain-setup-profile *fn2-cns-drain-profile* held fn2-core))

(defun fn2-cns-drain-pool-semanticp (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (yes)
    (fn2-pool-semanticp fn2-pool) yes))
(defun fn2-cns-drain-counted-basep (before fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core) (natp 4)
       (fn2-cns-draining-reservedp before)
       (fn2-cns-drain-pool-semanticp fn2-core)))
(defun fn2-cns-drain-fixture (held fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* (((mv setup id sibling fn2-core) (fn2-cns-drain-setup held fn2-core))
       (before (fn2-test-core-snapshot fn2-core))
       (pre (and setup (fn2-cns-drain-counted-basep before fn2-core)
                 (not (equal id sibling)) (fn2-cns-draining-domainp id before)))
       ((mv b s d r fn2-core) (fn2-cns-run id 4 fn2-core))
       (after (fn2-test-core-snapshot fn2-core)))
    (mv (list pre (fn2-cns-draining-resultp id before b s d r after)
              id sibling b s d r)
        fn2-core)))
(defun fn2-cns-drain-positive ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (ok fn2-core)
      (mv-let (held fn2-core) (fn2-cns-drain-fixture t fn2-core)
        (mv-let (final fn2-core) (fn2-cns-drain-fixture nil fn2-core)
          (mv (and (equal (take 2 held) '(t t))
                   (equal (take 2 final) '(t t))) fn2-core))) ok)))
(assert-event (fn2-cns-drain-positive))

; Full-H/C runtime controls for the actual timer operation. The bounds
; removal keeps core type, well-formedness and natural id, while the real
; operation refuses without changing the complete image.
(defun fn2-cns-clear-law-run (bounded fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* (((mv setup id & fn2-core) (fn2-cns-drain-setup nil fn2-core))
       (before (fn2-test-core-snapshot fn2-core))
       (sched (fn2-cns-drain-child 'fn2-sched before))
       (rows (fn2-cns-drain-get 'fn2-sched-rows sched))
       (target (if bounded id rows))
       (base (and setup (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                  (natp target)))
       (bound (< target rows))
       ((mv code fn2-core) (fn2-cns-clear-wait-timer target fn2-core))
       (after (fn2-test-core-snapshot fn2-core))
       (conclusion
        (equal (list code after)
               (list :ok (fn2-cns-drain-put-child 'fn2-sched
                           (fn2-cns-drain-cleared-sched target sched) before)))))
    (mv (and base (if bounded (and bound conclusion)
                    (and (not bound) (not conclusion) (eq code :bounds)
                         (equal before after)))) fn2-core)))
(defun fn2-cns-clear-positive ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (ok fn2-core) (fn2-cns-clear-law-run t fn2-core) ok)))
(defun fn2-cns-clear-without-bound ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (ok fn2-core) (fn2-cns-clear-law-run nil fn2-core) ok)))
(assert-event (and (fn2-cns-clear-positive) (fn2-cns-clear-without-bound)))

; A supported profile whose first generation is also its last exercises
; retirement through actual admission, without forging row ownership.
(defun fn2-cns-drain-retirement-run (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((profile (put-assoc-equal :generation-limit 1 *fn2-cns-drain-profile*))
       ((mv setup id & fn2-core) (fn2-cns-drain-setup-profile profile nil fn2-core))
       (before (fn2-test-core-snapshot fn2-core))
       (pre (and setup (fn2-profilep profile) (fn2-cns-drain-counted-basep before fn2-core)
                 (fn2-cns-draining-domainp id before)))
       ((mv b s d r fn2-core) (fn2-cns-run id 4 fn2-core))
       (after (fn2-test-core-snapshot fn2-core)))
    (mv (and pre (fn2-cns-draining-resultp id before b s d r after)
             (equal (fn2-cns-row-phase id fn2-core) *fn2-cns-state-retired*)) fn2-core)))
(defun fn2-cns-drain-retirement-control ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (ok fn2-core) (fn2-cns-drain-retirement-run fn2-core) ok)))
(assert-event (fn2-cns-drain-retirement-control))

(defun fn2-cns-drain-negative-run (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* (((mv setup id sibling fn2-core) (fn2-cns-drain-setup nil fn2-core))
       (before (fn2-test-core-snapshot fn2-core))
       (pre (and setup (fn2-cns-drain-counted-basep before fn2-core)
                 (fn2-cns-draining-domainp id before)))
       ((mv b s d r fn2-core) (fn2-cns-run id 4 fn2-core))
       (after (fn2-test-core-snapshot fn2-core))
       (sched (fn2-cns-drain-child 'fn2-sched after))
       (bad (fn2-cns-drain-put-child 'fn2-sched
              (fn2-cns-drain-put-cell 'fn2-sched-deadline sibling *fn2-no-deadline* sched) after)))
    (mv (and pre
             (fn2-cns-draining-resultp id before b s d r after)
             (not (fn2-cns-draining-resultp id before b s d r bad))) fn2-core)))
(defun fn2-cns-drain-negative ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (ok fn2-core) (fn2-cns-drain-negative-run fn2-core) ok)))
(assert-event (fn2-cns-drain-negative))

(defun fn2-cns-drain-refusal-run (stage fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* (((mv setup id & fn2-core) (fn2-cns-drain-setup nil fn2-core))
       (good (fn2-test-core-snapshot fn2-core))
       (fn2-core (if (eq stage :name)
                     (fn2-cns-put-core id (ns-gen (+ 1 (fn2-cns-row-ns-gen id fn2-core))))
                   (fn2-cns-put-core id (ws-gen (+ 1 (fn2-cns-row-ws-gen id fn2-core))))))
       (before (fn2-test-core-snapshot fn2-core))
       (pre (and setup (fn2-cns-drain-counted-basep before fn2-core)
                 (fn2-cns-draining-domainp id good)
                 (not (fn2-cns-draining-domainp id before))))
       ((mv b s d r fn2-core) (fn2-cns-run id 4 fn2-core))
       (after (fn2-test-core-snapshot fn2-core)))
    (mv (and pre (fn2-cns-draining-refusal-resultp id before stage b s d r after)
             (not (fn2-cns-draining-resultp id before b s d r after))) fn2-core)))
(defun fn2-cns-drain-refusal-control ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (ok fn2-core)
      (mv-let (ws fn2-core) (fn2-cns-drain-refusal-run :workspace fn2-core)
        (mv-let (ns fn2-core) (fn2-cns-drain-refusal-run :name fn2-core)
          (mv (and ws ns) fn2-core))) ok)))
(assert-event (fn2-cns-drain-refusal-control))

; Positive asserts the complete admitted held-law antecedent and conclusion.
; Removal retains every other premise, falsifies the removed lease premise
; and falsifies the conclusion with the real final cleanup transition.
(defun fn2-cns-drain-held-law-run (held fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* (((mv setup id & fn2-core) (fn2-cns-drain-setup held fn2-core))
       (base (and setup (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                  (equal (fn2-cns-snapshot-read-code id fn2-core) :ok)
                  (equal (fn2-cns-row-phase id fn2-core) *fn2-cns-state-draining*)))
       (clause (equal (fn2-cns-row-lease id fn2-core) *fn2-cns-lease-held*))
       (before (fn2-cns-drain-child 'fn2-sched (fn2-test-core-snapshot fn2-core)))
       ((mv & & & & fn2-core) (fn2-cns-run id 4 fn2-core))
       (conclusion (equal before (fn2-cns-drain-child 'fn2-sched
                                    (fn2-test-core-snapshot fn2-core)))))
    (mv (and base (if held (and clause conclusion)
                    (and (not clause) (not conclusion)))) fn2-core)))
(defun fn2-cns-drain-held-witness ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (ok fn2-core) (fn2-cns-drain-held-law-run t fn2-core) ok)))
(defun fn2-cns-drain-without-held-counterexample ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (ok fn2-core) (fn2-cns-drain-held-law-run nil fn2-core) ok)))
(fn2-assert-owed-teeth fn2-cns-draining-held-scheduler-contract)

; Q1 is exercised separately from the independent oracle, using its real
; per-case lockstep checker and a reference copied before the transition.
(defun fn2-cns-drain-q1-run (fn2-core fn2-ref-core)
  (declare (xargs :stobjs (fn2-core fn2-ref-core) :verify-guards nil))
  (b* (((mv setup id & fn2-core) (fn2-cns-drain-setup nil fn2-core))
       (fn2-core (fn2-exec-wake id fn2-core))
       (fn2-ref-core (fn2-ref-reset *fn2-cns-drain-profile* fn2-core fn2-ref-core))
       (lists (fn2-ref-lists-of-core (fn2-profile-weights *fn2-cns-drain-profile*) fn2-core))
       ((mv verdict & & & & & & tallies fn2-core fn2-ref-core)
        (fn2-check-trace-cases-turn *fn2-cns-drain-profile* (nth 1 lists) (nth 2 lists)
                                  fn2-core fn2-ref-core)))
    (mv (list setup verdict (cdr (assoc-equal '(:run fn2-cns :draining) (car tallies))))
        fn2-core fn2-ref-core)))
(defun fn2-cns-drain-q1-control ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (result fn2-core)
      (with-local-stobj fn2-ref-core
        (mv-let (result fn2-core fn2-ref-core) (fn2-cns-drain-q1-run fn2-core fn2-ref-core)
          (mv result fn2-core))) result)))
(assert-event (let ((r (fn2-cns-drain-q1-control)))
                (and (car r) (eq (cadr r) :pass) (posp (caddr r)))))
