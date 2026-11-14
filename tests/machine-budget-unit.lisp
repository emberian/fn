; The shared generated WORK entry reaches Close after a wake and row write.
; Descriptor admission must precede every one of those effects.
; All child recognizers, guards and natural-budget hypotheses hold. Zero budget
; yields unchanged; one descriptor of budget preserves the original successful issue.
; Commit72907f069 preserves the executable pre-fix violation with the same antecedent.
(in-package "ACL2")
(include-book "machine-arms-probe-fixture")
(include-book "std/testing/must-fail" :dir :system)

(make-event
 (mv-let (errs subs events)
   (fn2-arms-subs 'fn2-arms-probe (fn2-machine-declared 'fn2-arms-probe :subarms (w state)) nil nil nil :children (w state))
   (mv-let (errs conts runs)
    (fn2-arms-arms 'fn2-arms-probe
      (list (assoc-eq :work (fn2-machine-declared 'fn2-arms-probe :arms (w state))))
      nil subs nil nil errs :children (w state) nil)
    (declare (ignore conts))
    (if errs (er soft 'machine-budget-unit "~x0" errs)
      (value (cons 'progn (append events runs)))))))

(defun fn2-budget-fixture-run (budget fn2-arms-probe fn2-machines fn2-pool fn2-ops fn2-control)
 (declare (xargs :stobjs (fn2-arms-probe fn2-machines fn2-pool fn2-ops fn2-control) :verify-guards nil))
 (b* ((fn2-arms-probe (fn2-arms-probe-prepare 1 0 1 fn2-arms-probe))
      (fn2-arms-probe (fn2-arms-probe-put 0 (generation 1) (phase *fn2-arms-probe-state-work*) (cap-index 7) (cap-nonce 9) (tgt 0)))
      (fn2-machines (fn2-machines-columns-init 1 fn2-machines))
      (fn2-machines (fn2-machines-put 0 (kind 4) (slot 0)))
      (fn2-pool (fn2-pool-init '((2 . 64)) 1 100 fn2-pool))
      (fn2-ops (fn2-ops-init *fn2-profile-tiny* fn2-ops))
      (fn2-control (fn2-control-init *fn2-profile-tiny* fn2-control))
      (hyps (and (natp budget) (fn2-arms-probep fn2-arms-probe) (fn2-machinesp fn2-machines)
                 (fn2-poolp fn2-pool) (fn2-opsp fn2-ops) (fn2-controlp fn2-control)
                 (fn2-arms-probe-wfp fn2-arms-probe) (fn2-machines-wfp fn2-machines)
                 (fn2-pool-wfp fn2-pool) (fn2-ops-wfp fn2-ops) (fn2-control-wfp fn2-control)
                 (< 0 (fn2-arms-probe-rows fn2-arms-probe)) (< 0 (fn2-machines-rows fn2-machines))))
      (before (list (fn2-arms-probe-wfp fn2-arms-probe) (fn2-machines-wfp fn2-machines)
                    (fn2-pool-wfp fn2-pool) (fn2-ops-wfp fn2-ops) (fn2-control-wfp fn2-control)
                    (fn2-ops-queued fn2-ops) (fn2-ops-free-count fn2-ops)
                    (fn2-arms-probe-phase 0 fn2-arms-probe) (fn2-arms-probe-pending 0 fn2-arms-probe)))
      ((mv bytes steps descriptors runnable fn2-arms-probe fn2-machines fn2-pool fn2-ops fn2-control)
       (fn2-arms-probe-run-work-children 0 0 4 0 budget fn2-arms-probe fn2-machines fn2-pool fn2-ops fn2-control))
      ((mv peek op gen) (fn2-outbox-peek 0 fn2-ops)))
  (mv (list budget hyps before (list bytes steps descriptors runnable)
            (list (fn2-arms-probe-wfp fn2-arms-probe) (fn2-machines-wfp fn2-machines)
                    (fn2-pool-wfp fn2-pool) (fn2-ops-wfp fn2-ops) (fn2-control-wfp fn2-control)
                    (fn2-ops-queued fn2-ops) (fn2-ops-free-count fn2-ops)
                    (fn2-arms-probe-phase 0 fn2-arms-probe) (fn2-arms-probe-pending 0 fn2-arms-probe)
                    (fn2-control-stop-reason fn2-control))
            (list peek op gen)) fn2-arms-probe fn2-machines fn2-pool fn2-ops fn2-control)))

(defun fn2-budget-fixture (budget) (declare (xargs :verify-guards nil)) (with-local-stobj fn2-arms-probe (mv-let (answer fn2-arms-probe) (with-local-stobj fn2-machines (mv-let (answer fn2-arms-probe fn2-machines) (with-local-stobj fn2-pool (mv-let (answer fn2-arms-probe fn2-machines fn2-pool) (with-local-stobj fn2-ops (mv-let (answer fn2-arms-probe fn2-machines fn2-pool fn2-ops) (with-local-stobj fn2-control (mv-let (answer fn2-arms-probe fn2-machines fn2-pool fn2-ops fn2-control) (fn2-budget-fixture-run budget fn2-arms-probe fn2-machines fn2-pool fn2-ops fn2-control) (mv answer fn2-arms-probe fn2-machines fn2-pool fn2-ops))) (mv answer fn2-arms-probe fn2-machines fn2-pool))) (mv answer fn2-arms-probe fn2-machines))) (mv answer fn2-arms-probe))) answer)))
(assert-event
 (equal (fn2-budget-fixture 0)
        '(0 t (t t t t t 0 8 1 0) (0 1 0 t) (t t t t t 0 8 1 0 0) (:bounds 0 0))))
(assert-event
 (equal (fn2-budget-fixture 1)
        '(1 t (t t t t t 0 8 1 0) (0 12 1 nil) (t t t t t 1 7 2 1 0) (:ok 0 1))))

; The generated implementation satisfies a joint quantitative interface even
; when the input control is stopped. No stopped-output exception is assumed.
(defthm fn2-budget-generated-quantities (implies (and (fn2-arms-probep fn2-arms-probe) (fn2-machinesp fn2-machines) (fn2-poolp fn2-pool) (fn2-opsp fn2-ops) (fn2-controlp fn2-control) (and (fn2-arms-probe-wfp fn2-arms-probe) (fn2-machines-wfp fn2-machines) (fn2-pool-wfp fn2-pool) (fn2-ops-wfp fn2-ops) (fn2-control-wfp fn2-control) (natp slot) (< slot (fn2-arms-probe-rows fn2-arms-probe)) (natp id) (< id (fn2-machines-rows fn2-machines))))
 (and (natp (mv-nth 0 (fn2-arms-probe-run-work-children id slot kind ordinal budget fn2-arms-probe fn2-machines fn2-pool fn2-ops fn2-control))) (natp (mv-nth 1 (fn2-arms-probe-run-work-children id slot kind ordinal budget fn2-arms-probe fn2-machines fn2-pool fn2-ops fn2-control))) (natp (mv-nth 2 (fn2-arms-probe-run-work-children id slot kind ordinal budget fn2-arms-probe fn2-machines fn2-pool fn2-ops fn2-control)))
      (<= (mv-nth 0 (fn2-arms-probe-run-work-children id slot kind ordinal budget fn2-arms-probe fn2-machines fn2-pool fn2-ops fn2-control)) 4096) (<= (mv-nth 1 (fn2-arms-probe-run-work-children id slot kind ordinal budget fn2-arms-probe fn2-machines fn2-pool fn2-ops fn2-control)) 32)
      (<= (mv-nth 2 (fn2-arms-probe-run-work-children id slot kind ordinal budget fn2-arms-probe fn2-machines fn2-pool fn2-ops fn2-control)) (nfix budget)))) :hints (("Goal" :in-theory (enable fn2-arms-probe-run-work-children fn2-arms-probe-sub-close-children))))

(defthm fn2-budget-short-preserves-all (implies (< (nfix budget) 1) (and (equal (mv-nth 4 (fn2-arms-probe-run-work-children id slot kind ordinal budget fn2-arms-probe fn2-machines fn2-pool fn2-ops fn2-control)) fn2-arms-probe) (equal (mv-nth 5 (fn2-arms-probe-run-work-children id slot kind ordinal budget fn2-arms-probe fn2-machines fn2-pool fn2-ops fn2-control)) fn2-machines) (equal (mv-nth 6 (fn2-arms-probe-run-work-children id slot kind ordinal budget fn2-arms-probe fn2-machines fn2-pool fn2-ops fn2-control)) fn2-pool) (equal (mv-nth 7 (fn2-arms-probe-run-work-children id slot kind ordinal budget fn2-arms-probe fn2-machines fn2-pool fn2-ops fn2-control)) fn2-ops) (equal (mv-nth 8 (fn2-arms-probe-run-work-children id slot kind ordinal budget fn2-arms-probe fn2-machines fn2-pool fn2-ops fn2-control)) fn2-control))) :hints (("Goal" :in-theory (enable fn2-arms-probe-run-work-children fn2-arms-probe-sub-close-children))))

(encapsulate
 (((fn2-budget-run-hook * * * * * fn2-arms-probe fn2-machines fn2-pool fn2-ops fn2-control) => (mv * * * * fn2-arms-probe fn2-machines fn2-pool fn2-ops fn2-control) :formals (id slot kind ordinal budget fn2-arms-probe fn2-machines fn2-pool fn2-ops fn2-control) :guard (and (fn2-arms-probe-wfp fn2-arms-probe) (fn2-machines-wfp fn2-machines) (fn2-pool-wfp fn2-pool) (fn2-ops-wfp fn2-ops) (fn2-control-wfp fn2-control) (natp slot) (< slot (fn2-arms-probe-rows fn2-arms-probe)) (natp id) (< id (fn2-machines-rows fn2-machines)))))
 (local (defun fn2-budget-run-hook (id slot kind ordinal budget fn2-arms-probe fn2-machines fn2-pool fn2-ops fn2-control) (declare (xargs :stobjs (fn2-arms-probe fn2-machines fn2-pool fn2-ops fn2-control) :guard (and (fn2-arms-probe-wfp fn2-arms-probe) (fn2-machines-wfp fn2-machines) (fn2-pool-wfp fn2-pool) (fn2-ops-wfp fn2-ops) (fn2-control-wfp fn2-control) (natp slot) (< slot (fn2-arms-probe-rows fn2-arms-probe)) (natp id) (< id (fn2-machines-rows fn2-machines)))) (ignore id slot kind ordinal budget)) (mv 0 1 0 t fn2-arms-probe fn2-machines fn2-pool fn2-ops fn2-control)))
 (defthm fn2-budget-run-hook-quantities (implies (and (fn2-arms-probep fn2-arms-probe) (fn2-machinesp fn2-machines) (fn2-poolp fn2-pool) (fn2-opsp fn2-ops) (fn2-controlp fn2-control) (and (fn2-arms-probe-wfp fn2-arms-probe) (fn2-machines-wfp fn2-machines) (fn2-pool-wfp fn2-pool) (fn2-ops-wfp fn2-ops) (fn2-control-wfp fn2-control) (natp slot) (< slot (fn2-arms-probe-rows fn2-arms-probe)) (natp id) (< id (fn2-machines-rows fn2-machines))))
 (and (natp (mv-nth 0 (fn2-budget-run-hook id slot kind ordinal budget fn2-arms-probe fn2-machines fn2-pool fn2-ops fn2-control))) (natp (mv-nth 1 (fn2-budget-run-hook id slot kind ordinal budget fn2-arms-probe fn2-machines fn2-pool fn2-ops fn2-control))) (natp (mv-nth 2 (fn2-budget-run-hook id slot kind ordinal budget fn2-arms-probe fn2-machines fn2-pool fn2-ops fn2-control)))
      (<= (mv-nth 0 (fn2-budget-run-hook id slot kind ordinal budget fn2-arms-probe fn2-machines fn2-pool fn2-ops fn2-control)) 4096) (<= (mv-nth 1 (fn2-budget-run-hook id slot kind ordinal budget fn2-arms-probe fn2-machines fn2-pool fn2-ops fn2-control)) 32)
      (<= (mv-nth 2 (fn2-budget-run-hook id slot kind ordinal budget fn2-arms-probe fn2-machines fn2-pool fn2-ops fn2-control)) (nfix budget)))))
 (defthm fn2-budget-run-hook-effect
  (implies (and (fn2-arms-probep fn2-arms-probe) (fn2-machinesp fn2-machines)
                (fn2-poolp fn2-pool) (fn2-opsp fn2-ops) (fn2-controlp fn2-control)
                (fn2-arms-probe-wfp fn2-arms-probe) (fn2-machines-wfp fn2-machines)
                (fn2-pool-wfp fn2-pool) (fn2-ops-wfp fn2-ops) (fn2-control-wfp fn2-control)
                (natp slot) (< slot (fn2-arms-probe-rows fn2-arms-probe))
                (natp id) (< id (fn2-machines-rows fn2-machines)))
   (equal
    (nth *fn2-ops-queued* (mv-nth 7 (fn2-budget-run-hook id slot kind ordinal budget fn2-arms-probe fn2-machines fn2-pool fn2-ops fn2-control)))
    (+ (nth *fn2-ops-queued* fn2-ops)
       (mv-nth 2 (fn2-budget-run-hook id slot kind ordinal budget fn2-arms-probe fn2-machines fn2-pool fn2-ops fn2-control)))))))

(defattach (fn2-budget-run-hook fn2-arms-probe-run-work-children) :hints (("Goal" :use (fn2-budget-generated-quantities fn2-arms-probe-run-work-children-descriptor-effect) :in-theory (theory 'minimal-theory))))

(defun fn2-budget-malicious (id slot kind ordinal budget fn2-arms-probe fn2-machines fn2-pool fn2-ops fn2-control) (declare (xargs :stobjs (fn2-arms-probe fn2-machines fn2-pool fn2-ops fn2-control) :guard (and (fn2-arms-probe-wfp fn2-arms-probe) (fn2-machines-wfp fn2-machines) (fn2-pool-wfp fn2-pool) (fn2-ops-wfp fn2-ops) (fn2-control-wfp fn2-control) (natp slot) (< slot (fn2-arms-probe-rows fn2-arms-probe)) (natp id) (< id (fn2-machines-rows fn2-machines)))) (ignore id slot kind ordinal)) (mv 0 1 (+ 1 (nfix budget)) nil fn2-arms-probe fn2-machines fn2-pool fn2-ops fn2-control))

(must-fail (defattach (fn2-budget-run-hook fn2-budget-malicious)))

(assert-event
 (let ((required (fn2-arm-get :descriptors (fn2-machine-declared 'fn2-arms-probe :budget (w state)))))
  (and (<= required (fn2-profile-aturn *fn2-profile-tiny*))
       (<= required (fn2-profile-qa *fn2-profile-tiny*))
       (<= required (fn2-profile-aturn *fn2-profile-concrete*))
       (<= required (fn2-profile-qa *fn2-profile-concrete*)))))

; The admission yield is a real zero-effect staying path. Without it the
; outer run's next-phase certificate would turn a retry into a stop.
(make-event
 (mv-let (errs subs events)
  (fn2-arms-subs 'fn2-arms-probe (fn2-machine-declared 'fn2-arms-probe :subarms (w state)) nil nil nil :children (w state))
  (declare (ignore events))
  (mv-let (from refusal steps)
   (fn2-arms-options (cdr (assoc-eq :work (fn2-machine-declared 'fn2-arms-probe :arms (w state)))))
   (declare (ignore from))
   (mv-let (err code acc)
    (fn2-arms-steps steps
      (fn2-arms-arm-knowledge 'fn2-arms-probe '(:work)
        (fn2-decl-set :site "WORK" (fn2-arms-env 'fn2-arms-probe :work nil refusal subs t (w state)))) nil 100000)
    (declare (ignore code))
    (let ((contract (fn2-arms-contract 'fn2-arms-probe :work nil nil acc (w state))))
     (if (and (not errs) (not err)
              (member-eq :work (fn2-arm-get :next contract))
              (member-equal '((:work) :stay nil nil nil nil) (fn2-arm-get :paths contract)))
         (value '(value-triple :admission-retry-path))
       (er soft 'machine-budget-unit "Missing admission retry contract: ~x0" contract)))))))

; Numeric accounting alone accepts zero-reporting; the effect constraint refuses it.
(defun fn2-budget-underreport (id slot kind ordinal budget fn2-arms-probe fn2-machines fn2-pool fn2-ops fn2-control) (declare (xargs :stobjs (fn2-arms-probe fn2-machines fn2-pool fn2-ops fn2-control) :guard (and (fn2-arms-probe-wfp fn2-arms-probe) (fn2-machines-wfp fn2-machines) (fn2-pool-wfp fn2-pool) (fn2-ops-wfp fn2-ops) (fn2-control-wfp fn2-control) (natp slot) (< slot (fn2-arms-probe-rows fn2-arms-probe)) (natp id) (< id (fn2-machines-rows fn2-machines)))) (ignorable id slot kind ordinal))
 (mv-let (bytes steps descriptors runnable fn2-arms-probe fn2-machines fn2-pool fn2-ops fn2-control)
  (fn2-arms-probe-run-work-children id slot kind ordinal budget fn2-arms-probe fn2-machines fn2-pool fn2-ops fn2-control)
  (declare (ignore descriptors))
  (mv bytes steps 0 runnable fn2-arms-probe fn2-machines fn2-pool fn2-ops fn2-control)))

(must-fail (defattach (fn2-budget-run-hook fn2-budget-underreport)))
