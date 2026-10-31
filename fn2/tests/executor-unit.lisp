; Executor controls and whole-state refinement witnesses. All allocations in
; this book are test-only snapshots, never part of fn2-turn.
(in-package "ACL2")
(include-book "reference-unit")

(defun fn2-executor-test-snapshot-calls (children)
  (if (atom children) nil
    (cons `(,(fn2-columns-sym (cadar children) "-COPY") ,(cadar children))
          (fn2-executor-test-snapshot-calls (cdr children)))))
(make-event
 (value `(fn2-defoperation (:operation-set fn2-ref-core) :reference :infer
         (defun fn2-executor-test-snapshot (fn2-core)
           (declare (xargs :stobjs fn2-core :verify-guards nil))
           (stobj-let ,(fn2-core-child-bindings *fn2-core-children*) (answer)
             (list ,@(fn2-executor-test-snapshot-calls *fn2-core-children*)) answer)))))
(in-theory (disable fn2-executor-test-snapshot))

(defun fn2-executor-test-post (slot gen fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
    (fn2-ops)
    (mv-let (code fn2-ops) (fn2-outbox-ack 1 fn2-ops)
      (declare (ignore code))
      (fn2-post-result 0 slot gen *fn2-event-accept-result*
        *fn2-outcome-done* *fn2-reason-none* 0 42 77 fn2-ops)) fn2-core))
(defun fn2-executor-test-mailboxes (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
    (fn2-ops)
    (let* ((fn2-ops (fn2-post-clock 10 20 0 fn2-ops))
           (fn2-ops (fn2-post-signal 1 fn2-ops))) fn2-ops) fn2-core))
(defun fn2-executor-test-op-head (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
    (code slot gen) (fn2-outbox-peek 0 fn2-ops) (mv code slot gen)))
(defun fn2-executor-test-op-state (slot fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
    (phase gen) (mv (fn2-ops-phase slot fn2-ops) (fn2-ops-gen slot fn2-ops))
    (mv phase gen)))

; The public one-transition entry also honors a zero descriptor remainder:
; a selected listener requeues without issuing an Accept.
(defun fn2-executor-test-zero-run (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((fn2-core (fn2-init-executor *fn2-profile-tiny* :echo nil fn2-core))
       ((mv obs visits actions bytes steps fn2-core) (fn2-transition nil 0 fn2-core)))
    (mv (and (equal (list obs visits actions bytes steps) '(0 1 0 0 1))
             (= (fn2-exec-queued fn2-core) 0)
             (= (fn2-machine-pending 0 fn2-core) 0)
             (eq (fn2-exec-status fn2-core) :more)) fn2-core)))

; One calendar cycle visits all tiny entries, but only the first listener
; runs. The next cycle selects the second listener and then becomes idle.
(defun fn2-executor-test-initial-run (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((fn2-core (fn2-init-executor *fn2-profile-tiny* :echo nil fn2-core))
       ((mv s0 o0 v0 a0 fn2-core) (fn2-turn fn2-core))
       (pending0 (fn2-machine-pending 0 fn2-core))
       (pending1 (fn2-machine-pending 1 fn2-core))
       ((mv s1 o1 v1 a1 fn2-core) (fn2-turn fn2-core))
       ((mv s2 o2 v2 a2 fn2-core) (fn2-turn fn2-core)))
    (mv (and (equal (list s0 o0 v0 a0) '(:more 0 8 1))
             (equal (list pending0 pending1) '(1 0))
             (equal (list s1 o1 v1 a1) '(:idle 0 1 1))
             (equal (list s2 o2 v2 a2) '(:idle 0 0 0))
             (= (fn2-exec-queued fn2-core) 2)
             (= (fn2-machine-pending 1 fn2-core) 1)) fn2-core)))

; Accept's terminal result recycles its OpRef. The row identity must be
; captured before that recycle, or the completion cannot reach listener 0.
(defun fn2-executor-test-harvest-run (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((fn2-core (fn2-init-executor *fn2-profile-tiny* :echo nil fn2-core))
       ((mv ?o ?v ?a ?b ?s fn2-core) (fn2-transition nil 1 fn2-core))
       ((mv code slot gen) (fn2-executor-test-op-head fn2-core))
       (fn2-core (fn2-executor-test-post slot gen fn2-core))
       ((mv found kind id owner-gen principal) (fn2-core-next-owner fn2-core))
       ((mv o v a bytes steps fn2-core) (fn2-exec-harvest fn2-core))
       ((mv phase new-gen) (fn2-executor-test-op-state slot fn2-core)))
    (mv (and (eq code :ok) found
             (equal (list kind id owner-gen principal) '(0 0 1 0))
             (equal (list o v a bytes steps) '(1 0 0 0 24))
             (= phase *fn2-op-phase-free*) (= new-gen (+ 1 gen))
             (= (fn2-machine-pending 0 fn2-core) 0)
             (= (fn2-machine-event-ready 0 fn2-core) 1)
             (= (fn2-machine-cap-index 0 fn2-core) 42)
             (= (fn2-machine-cap-nonce 0 fn2-core) 77)) fn2-core)))

(defun fn2-executor-test-budget-run (profile fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((fn2-core (fn2-init-executor profile :echo nil fn2-core))
       ((mv status nobs nvisits nactions fn2-core) (fn2-turn fn2-core)))
    (mv (and (fn2-core-profilep profile)
             (equal (list status nobs nvisits nactions) '(:more 0 1 1))
             (<= nobs (fn2-profile-h profile))
             (<= nvisits (fn2-profile-k profile))
             (<= nactions (fn2-profile-aturn profile))) fn2-core)))

; H=1 leaves the sticky signal behind after harvesting the clock. With no
; runnable rows the first turn must report :more, never allow a host wait.
(defun fn2-executor-test-h-run (runnablep fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((profile (put-assoc-equal :h 1 *fn2-profile-tiny*))
       (fn2-core (if runnablep (fn2-init-executor profile :echo nil fn2-core)
                   (fn2-core-init profile fn2-core)))
       (fn2-core (fn2-executor-test-mailboxes fn2-core))
       ((mv s0 o0 v0 a0 fn2-core) (fn2-turn fn2-core))
       (clock (fn2-exec-now fn2-core))
       ((mv s1 o1 v1 a1 fn2-core) (fn2-turn fn2-core))
       ((mv s2 o2 v2 a2 fn2-core) (fn2-turn fn2-core)))
    (mv (and (fn2-core-profilep profile) (= clock 10)
             (equal (list s0 o0 v0 a0) '(:more 1 0 0))
             (equal (list s1 o1 v1 a1) '(:stop 1 0 0))
             (equal (list s2 o2 v2 a2) '(:stop 0 0 0))) fn2-core)))

(defun fn2-executor-test-initial-snapshot ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (copy fn2-core)
      (let ((fn2-core (fn2-init-executor *fn2-profile-tiny* :echo nil fn2-core)))
        (mv (fn2-executor-test-snapshot fn2-core) fn2-core)) copy)))

(defun fn2-executor-unit-tests ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (result fn2-core)
      (b* (((mv initial fn2-core) (fn2-executor-test-initial-run fn2-core))
           ((mv zero fn2-core) (fn2-executor-test-zero-run fn2-core))
           ((mv harvest fn2-core) (fn2-executor-test-harvest-run fn2-core))
           ((mv k fn2-core) (fn2-executor-test-budget-run
                              (put-assoc-equal :k 1 *fn2-profile-tiny*) fn2-core))
           ((mv a fn2-core) (fn2-executor-test-budget-run
                              (put-assoc-equal :aturn 1 *fn2-profile-tiny*) fn2-core))
           ((mv h-empty fn2-core) (fn2-executor-test-h-run nil fn2-core))
           ((mv h-runnable fn2-core) (fn2-executor-test-h-run t fn2-core))
           ((mv positive fn2-core)
            (mv (fn2-ref-test nil) fn2-core))
           ((mv removal fn2-core)
            (mv (fn2-ref-test t) fn2-core)))
        (mv (list (and initial zero) harvest (and h-empty h-runnable) k a positive removal)
            fn2-core)) result)))
(assert-event (equal (fn2-executor-unit-tests) '(t t t t t t t)))

; Remove only the concrete recognizer hypothesis. This is an ordinary
; logical list, never an invalid write into a live specialized array. The
; rectangular shape still holds, but the H scalar is not an unsigned integer.
; Its actual logical turn immediately returns nobs=0, violating 0 <= -1.
(defconst *fn2-executor-test-bad-h*
  (let ((copy (fn2-executor-test-initial-snapshot)))
    (update-nth *fn2-core-control*
      (update-nth *fn2-control-h* -1 (nth *fn2-core-control* copy)) copy)))
; The malformed logical snapshot cannot inhabit the specialized stobj.
; This executable predicate checks its complete input/count witness. The
; theorem below connects shape=true and counts=(0 0 0) to actual fn2-turn;
; no evaluator pretends to execute a negative value in an unsigned field.
(defun fn2-executor-bounds-witnessp (recognized shape h k a counts)
  (declare (xargs :verify-guards nil))
  (and (not recognized) shape
       (equal counts '(0 0 0))
       (not (and (<= (nth 0 counts) h) (<= (nth 1 counts) k)
                 (<= (nth 2 counts) a)))))
(defun fn2-executor-bounds-negative ()
  (declare (xargs :verify-guards nil))
  (let* ((bad *fn2-executor-test-bad-h*)
         (control (nth *fn2-core-control* bad)))
    (fn2-executor-bounds-witnessp
     (fn2-corep bad) t
     (nth *fn2-control-h* control)
     (nth *fn2-control-k* control)
     (nth *fn2-control-aturn* control) '(0 0 0))))
(defun fn2-executor-bounds-teeth ()
  (declare (xargs :verify-guards nil))
  (equal (fn2-executor-unit-tests) '(t t t t t t t)))

(defun fn2-executor-test-control-logic-names (fields)
  (declare (xargs :verify-guards nil))
  (if (atom fields) nil
    (append (list (caar fields) (fn2-columns-pre "UPDATE-" (caar fields)))
            (fn2-executor-test-control-logic-names (cdr fields)))))
(defun fn2-executor-test-execution-runes (names)
  (declare (xargs :verify-guards nil))
  (if (atom names) nil
    (cons (list :executable-counterpart (car names))
          (fn2-executor-test-execution-runes (cdr names)))))
(make-event
 (let* ((schema (fn2-decl-row (list :columns 'fn2-control) (w state)))
        (fields (cadr (member-eq :extra-fields schema)))
        (names (append '(fn2-executor-bounds-negative fn2-executor-bounds-witnessp
                         fn2-turn fn2-concrete-turn fn2-concrete-loop
                         fn2-exec-h fn2-exec-k fn2-exec-aturn
                         fn2-exec-set-turn-bytes fn2-exec-set-turn-steps
                         fn2-corep fn2-core-wfp
                         update-fn2-core-control
                         fn2-control-wfp fn2-control-rows)
                       (strip-cars *fn2-core-children*)
                       (fn2-executor-test-control-logic-names fields))))
   (value
    `(defthm fn2-executor-test-bounds-hypothesis-removal
       (let ((bad *fn2-executor-test-bad-h*))
         (and (not (fn2-corep bad))
              (fn2-core-wfp bad)
              (mv-let (status nobs nvisits nactions after) (fn2-turn bad)
                (declare (ignore status after))
                (and (equal nobs 0)
                     (equal (list nobs nvisits nactions) '(0 0 0))
                     (equal (fn2-executor-bounds-negative)
                            (fn2-executor-bounds-witnessp
                             (fn2-corep bad) (fn2-core-wfp bad)
                             (fn2-exec-h bad) (fn2-exec-k bad)
                             (fn2-exec-aturn bad) (list nobs nvisits nactions)))
                     (not (and (<= nobs (fn2-exec-h bad))
                               (<= nvisits (fn2-exec-k bad))
                               (<= nactions (fn2-exec-aturn bad))))))))
       :rule-classes nil
       :hints (("Goal" :in-theory
                (e/d ,names ,(fn2-executor-test-execution-runes names))))))))

(fn2-assert-owed-teeth fn2-turn-bounds)

; The ring is exercised through the same concrete writers used by the core.
; Two rows retain only the latest two of three records and report one lost.
(defun fn2-trace-test-ring-run (fn2-trace)
  (declare (xargs :stobjs fn2-trace :verify-guards nil))
  (let* ((fn2-trace (fn2-trace-init 2 t fn2-trace))
         (fn2-trace (fn2-trace-append *fn2-trace-kind-machine* 10 0 0 0 1 0 nil *fn2-none* 0 0 fn2-trace))
         (fn2-trace (fn2-trace-append *fn2-trace-kind-machine* 11 1 1 0 1 0 nil *fn2-none* 0 0 fn2-trace))
         (fn2-trace (fn2-trace-append *fn2-trace-kind-machine* 12 2 2 0 1 1 nil *fn2-none* 0 0 fn2-trace))
         (fn2-trace (fn2-trace-action 0 5 9 fn2-trace))
         (records (fn2-trace-records fn2-trace))
         (ok (and (equal (fn2-trace-lost fn2-trace) 1)
                  (equal (len records) 2)
                  (equal (nth 1 (car records)) 11)
                  (equal (nth 1 (cadr records)) 12)
                  (equal (nth 11 (cadr records)) 5)
                  (equal (nth 12 (cadr records)) 9)))
         (fn2-trace (fn2-trace-append -1 0 0 0 0 0 0 nil *fn2-none* 0 0 fn2-trace))
         (ok (and ok (= (fn2-trace-lost fn2-trace) 2)))
         (fn2-trace (fn2-trace-init 2 nil fn2-trace))
         (fn2-trace (fn2-trace-append *fn2-trace-kind-machine* 10 0 0 0 1 0 nil *fn2-none* 0 0 fn2-trace)))
    (mv (and ok (equal (fn2-trace-records fn2-trace) nil)) fn2-trace)))
(defun fn2-trace-test-ring ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-trace
    (mv-let (answer fn2-trace) (fn2-trace-test-ring-run fn2-trace) answer)))
(assert-event (fn2-trace-test-ring))

; R7: teeth of the cost-composition and residual-budget obligations, and the
; evaluated teeth of every generated arm row (:from (:machine K)).
(defun fn2-arm-composition-positive ()
  (declare (xargs :verify-guards nil))
  (let ((word (list (list *fn2-echo-kind* *fn2-echo-state-command* 4096 8 1)
                    (list *fn2-listener-kind* *fn2-listener-state-accepting* 0 *fn2-work-mailbox* 1))))
    (and (fn2-arm-word-certified-p word)
         (<= (fn2-arm-word-charge word) (fn2-arm-word-bound word)))))
(defun fn2-arm-composition-negative ()
  ; An over-charged run leaves the word uncertified, and the bound fails:
  ; the premise is what carries the conclusion.
  (declare (xargs :verify-guards nil))
  (let ((word (list (list *fn2-echo-kind* *fn2-echo-state-command* 5000 8 1))))
    (and (not (fn2-arm-word-certified-p word))
         (not (<= (fn2-arm-word-charge word) (fn2-arm-word-bound word))))))
(defun fn2-arm-residual-run (budget fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (let ((fn2-core (fn2-core-init *fn2-profile-tiny* fn2-core)))
    (mv-let (bytes steps descriptors runnable fn2-core) (fn2-machine-run 0 budget fn2-core)
      (declare (ignore bytes steps runnable))
      (mv descriptors fn2-core))))
(defun fn2-arm-residual-positive ()
  (declare (xargs :verify-guards nil))
  (and (with-local-stobj fn2-core
         (mv-let (d fn2-core) (fn2-arm-residual-run 1 fn2-core) (<= d 1)))
       (with-local-stobj fn2-core
         (mv-let (d fn2-core) (fn2-arm-residual-run 0 fn2-core) (<= d 0)))))
(defun fn2-arm-residual-negative ()
  ; The bound is attained: an Accept spends the one descriptor it is handed.
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (d fn2-core) (fn2-arm-residual-run 1 fn2-core) (not (<= d 0)))))
(fn2-assert-owed-teeth fn2-arm-cost-composition fn2-arm-residual-budget)
(defun fn2-arm-row-names (rows)
  (declare (xargs :verify-guards nil))
  (if (atom rows) nil
    (if (eq (car (fn2-decl-get :owner (cdar rows))) :machine)
        (cons (caar rows) (fn2-arm-row-names (cdr rows)))
      (fn2-arm-row-names (cdr rows)))))
(make-event
 (value `(fn2-assert-owed-teeth ,@(fn2-arm-row-names (fn2-decl-rows :square (w state))))))
(assert-event (> (len (fn2-arm-row-names (fn2-decl-rows :square (w state)))) 50))
(make-event
 (value `(value-triple (cw "R7 ARM ROWS: composition, residual budget and ~x0 per-arm rows' teeth evaluate PASS~%"
                           ,(len (fn2-arm-row-names (fn2-decl-rows :square (w state))))))))
