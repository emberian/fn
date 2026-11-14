; Independent, proof-only application semantics for the served CNS cleanup.
; The checking side is list arithmetic: no handler, release, reclaim or timer
; operation is called. Schema metadata supplies positions, never decisions.
(in-package "ACL2")
(include-book "assembly-callbacks-e-cns")

(defun fn2-cns-drain-number-fields (fields index)
  (declare (xargs :verify-guards nil))
  (if (atom fields) nil
    (cons (cons (caar fields) index)
          (fn2-cns-drain-number-fields (cdr fields) (+ 1 (nfix index))))))
(defun fn2-cns-drain-column-names (name columns)
  (declare (xargs :verify-guards nil))
  (if (atom columns) nil
    (cons (fn2-columns-col-name name (caar columns))
          (fn2-cns-drain-column-names name (cdr columns)))))
(defun fn2-cns-drain-schema (rows)
  (declare (xargs :verify-guards nil))
  (if (atom rows) nil
    (let* ((name (caar rows)) (schema (cdar rows))
           (fields (append (pairlis$ (fn2-cns-drain-column-names name (fn2-decl-get :columns schema)) nil)
                     (list (list (fn2-columns-sym name "-ROWS")))
                     (fn2-decl-get :extra-fields schema))))
      (append (fn2-cns-drain-number-fields fields 0)
              (fn2-cns-drain-schema (cdr rows))))))
(make-event
 (value `(defconst *fn2-cns-drain-fields*
           ',(fn2-cns-drain-schema (fn2-decl-rows :columns (w state))))))
(make-event
 (value `(defconst *fn2-cns-drain-children*
           ',(pairlis$ (strip-cadrs *fn2-core-children*)
                       (fn2-cns-drain-number-fields *fn2-core-children* 0)))))

; Ordinary lists on both sides; these helpers do not use mutable stobjs.
(defun fn2-cns-drain-index (field)
  (cdr (assoc-eq field *fn2-cns-drain-fields*)))
(defun fn2-cns-drain-get (field table)
  (nth (fn2-cns-drain-index field) table))
(defun fn2-cns-drain-cell (field slot table)
  (nth slot (fn2-cns-drain-get field table)))
(defun fn2-cns-drain-put (field value table)
  (update-nth (fn2-cns-drain-index field) value table))
(defun fn2-cns-drain-put-cell (field slot value table)
  (fn2-cns-drain-put field
    (update-nth slot value (fn2-cns-drain-get field table)) table))
(defun fn2-cns-drain-child-index (name)
  (cdr (cdr (assoc-eq name *fn2-cns-drain-children*))))
(defun fn2-cns-drain-child (name core)
  (nth (fn2-cns-drain-child-index name) core))
(defun fn2-cns-drain-put-child (name child core)
  (update-nth (fn2-cns-drain-child-index name) child core))
(defun fn2-cns-drain-put-cells (writes slot table)
  (if (atom writes) table
    (fn2-cns-drain-put-cells (cdr writes) slot
      (fn2-cns-drain-put-cell (caar writes) slot (cadar writes) table))))

; The domain spells out ownership and release admissibility independently.
(defun fn2-cns-drain-releasablep (slot gen id ogen pool)
  (and (natp slot) (< slot (fn2-cns-drain-get 'fn2-pool-rows pool))
       (equal (fn2-cns-drain-cell 'fn2-pool-gen slot pool) gen)
       (equal (fn2-cns-drain-cell 'fn2-pool-state slot pool) *fn2-pool-state-workspace*)
       (equal (fn2-cns-drain-cell 'fn2-pool-owner-kind slot pool) *fn2-cns-kind*)
       (equal (fn2-cns-drain-cell 'fn2-pool-owner-slot slot pool) id)
       (equal (fn2-cns-drain-cell 'fn2-pool-owner-gen slot pool) ogen)
       (equal (fn2-cns-drain-cell 'fn2-pool-out-count slot pool) 0)
       (< (fn2-cns-drain-get 'fn2-pool-retired-count pool)
          (fn2-cns-drain-get 'fn2-pool-rows pool))
       (let ((class (fn2-cns-drain-cell 'fn2-pool-class slot pool)))
         (and (natp class) (< class (fn2-cns-drain-get 'fn2-pool-nclasses pool))
              (< (fn2-cns-drain-cell 'fn2-pool-class-counts class pool)
                 (fn2-cns-drain-get 'fn2-pool-rows pool))))))

; A specification of a successful release, including its complete frame.
; Backing bytes and owner metadata survive release; only liveness changes.
(defun fn2-cns-drain-released-pool (slot pool)
  (let ((gen (fn2-cns-drain-cell 'fn2-pool-gen slot pool)))
    (if (>= gen (fn2-cns-drain-get 'fn2-pool-gen-limit pool))
        (fn2-cns-drain-put 'fn2-pool-retired-count
          (+ 1 (fn2-cns-drain-get 'fn2-pool-retired-count pool))
          (fn2-cns-drain-put-cell 'fn2-pool-state slot *fn2-pool-state-retired* pool))
      (let* ((class (fn2-cns-drain-cell 'fn2-pool-class slot pool))
             (head (fn2-cns-drain-cell 'fn2-pool-class-heads class pool))
             (count (fn2-cns-drain-cell 'fn2-pool-class-counts class pool))
             (pool (fn2-cns-drain-put-cells
                    (list (list 'fn2-pool-gen (+ 1 gen))
                          (list 'fn2-pool-state *fn2-pool-state-free*)
                          (list 'fn2-pool-next-free head) (list 'fn2-pool-fill 0)) slot pool))
             (pool (fn2-cns-drain-put-cell 'fn2-pool-class-heads class slot pool)))
        (fn2-cns-drain-put-cell 'fn2-pool-class-counts class (+ 1 count) pool)))))

(defun fn2-cns-draining-domainp (id before)
  (let* ((dir (fn2-cns-drain-child 'fn2-machines before))
         (own (fn2-cns-drain-child 'fn2-cns before))
         (pool (fn2-cns-drain-child 'fn2-pool before))
         (ctl (fn2-cns-drain-child 'fn2-control before))
         (sched (fn2-cns-drain-child 'fn2-sched before))
         (slot (fn2-cns-drain-cell 'fn2-machines-slot id dir))
         (gen (fn2-cns-drain-cell 'fn2-cns-generation slot own)))
    (and (natp id) (< id (fn2-cns-drain-get 'fn2-machines-rows dir))
         (< id (fn2-cns-drain-get 'fn2-sched-rows sched))
         (natp slot) (< slot (fn2-cns-drain-get 'fn2-cns-rows own))
         (equal (fn2-cns-drain-cell 'fn2-machines-kind id dir) *fn2-cns-kind*)
         (equal (fn2-cns-drain-cell 'fn2-cns-phase slot own) *fn2-cns-state-draining*)
         (equal (fn2-cns-drain-cell 'fn2-cns-stopped slot own) 0)
         (equal (fn2-cns-drain-cell 'fn2-cns-pending slot own) 0)
         (equal (fn2-cns-drain-cell 'fn2-cns-edge slot own) *fn2-none*)
         (member-equal (fn2-cns-drain-cell 'fn2-cns-lease slot own)
                       (list *fn2-cns-lease-none* *fn2-cns-lease-held*))
         (equal (fn2-cns-drain-get 'fn2-control-stop ctl) 0)
         (< 0 (fn2-cns-drain-cell 'fn2-machines-active-count *fn2-cns-admission-ordinal* dir))
         (if (equal (fn2-cns-drain-cell 'fn2-cns-lease slot own) *fn2-cns-lease-held*)
             (fn2-cns-drain-releasablep
               (fn2-cns-drain-cell 'fn2-cns-lslot slot own)
               (fn2-cns-drain-cell 'fn2-cns-lgen slot own) id gen pool)
           (and (not (equal (fn2-cns-drain-cell 'fn2-cns-ws-slot slot own)
                            (fn2-cns-drain-cell 'fn2-cns-ns-slot slot own)))
                (fn2-cns-drain-releasablep
                  (fn2-cns-drain-cell 'fn2-cns-ws-slot slot own)
                  (fn2-cns-drain-cell 'fn2-cns-ws-gen slot own) id gen pool)
                (fn2-cns-drain-releasablep
                  (fn2-cns-drain-cell 'fn2-cns-ns-slot slot own)
                  (fn2-cns-drain-cell 'fn2-cns-ns-gen slot own) id gen pool))))))

; One live reservation leaves room for its reusable credit. Retirement can
; reduce the sum; admission and reusable reclamation preserve it.
(defun fn2-cns-draining-reservedp (before)
  (let* ((dir (fn2-cns-drain-child 'fn2-machines before))
         (active (fn2-cns-drain-cell 'fn2-machines-active-count *fn2-cns-admission-ordinal* dir))
         (credits (fn2-cns-drain-cell 'fn2-machines-admission-credits *fn2-cns-admission-ordinal* dir))
         (capacity (fn2-cns-drain-cell 'fn2-machines-connection-count *fn2-cns-admission-ordinal* dir)))
    (and (natp active) (natp credits) (natp capacity)
         (<= (+ active credits) capacity))))

(defun fn2-cns-drain-cleared-sched (id sched)
  (let* ((old (fn2-cns-drain-cell 'fn2-sched-deadline id sched))
         (count (fn2-cns-drain-get 'fn2-sched-armed-timers sched))
         (next (if (and (< old *fn2-no-deadline*) (< 0 count)) (- count 1) count))
         (sched (fn2-cns-drain-put-cell 'fn2-sched-deadline id *fn2-no-deadline* sched))
         (sched (fn2-cns-drain-put-cell 'fn2-sched-expired id 0 sched))
         (sched (fn2-cns-drain-put 'fn2-sched-armed-timers next sched)))
    (if (equal next 0)
        (fn2-cns-drain-put 'fn2-sched-earliest-deadline *fn2-no-deadline* sched)
      sched)))

(defun fn2-cns-draining-expected (id before)
  (let* ((dir (fn2-cns-drain-child 'fn2-machines before))
         (own (fn2-cns-drain-child 'fn2-cns before))
         (pool (fn2-cns-drain-child 'fn2-pool before))
         (slot (fn2-cns-drain-cell 'fn2-machines-slot id dir)))
    (if (equal (fn2-cns-drain-cell 'fn2-cns-lease slot own) *fn2-cns-lease-held*)
        (let* ((pool (fn2-cns-drain-released-pool (fn2-cns-drain-cell 'fn2-cns-lslot slot own) pool))
               (own (fn2-cns-drain-put-cells
                      (list (list 'fn2-cns-lease *fn2-cns-lease-none*)
                            (list 'fn2-cns-lslot *fn2-none*) (list 'fn2-cns-lgen 0)) slot own))
               (after (fn2-cns-drain-put-child 'fn2-pool pool
                        (fn2-cns-drain-put-child 'fn2-cns own before))))
          (list 0 *fn2-work-transition* 0 t after))
      (let* ((gen (fn2-cns-drain-cell 'fn2-cns-generation slot own))
             (retire (>= gen (fn2-cns-drain-get 'fn2-machines-gen-limit dir)))
             (head (fn2-cns-drain-cell 'fn2-machines-free-head *fn2-cns-admission-ordinal* dir))
             (pool (fn2-cns-drain-released-pool (fn2-cns-drain-cell 'fn2-cns-ws-slot slot own) pool))
             (pool (fn2-cns-drain-released-pool (fn2-cns-drain-cell 'fn2-cns-ns-slot slot own) pool))
             (own (fn2-cns-drain-put-cells
                    (list (list 'fn2-cns-generation (if retire gen (+ 1 gen)))
                          (list 'fn2-cns-phase (if retire *fn2-cns-state-retired* *fn2-cns-state-free*))
                          (list 'fn2-cns-ctl *fn2-none*) (list 'fn2-cns-ctl-gen 0)
                          (list 'fn2-cns-edge *fn2-none*) (list 'fn2-cns-txn *fn2-none*) (list 'fn2-cns-txn-gen 0)
                          (list 'fn2-cns-upload *fn2-none*) (list 'fn2-cns-upload-gen 0)
                          (list 'fn2-cns-tx-slot *fn2-none*) (list 'fn2-cns-tx-gen 0)
                          (list 'fn2-cns-ws-slot *fn2-none*) (list 'fn2-cns-ws-gen 0)
                          (list 'fn2-cns-ns-slot *fn2-none*) (list 'fn2-cns-ns-gen 0)
                          (list 'fn2-cns-next-free head) (list 'fn2-cns-deadline 0)) slot own))
             (dir (fn2-cns-drain-put-cell 'fn2-machines-wait-reason id *fn2-wait-none* dir))
             (dir (fn2-cns-drain-put-cell 'fn2-machines-active-count *fn2-cns-admission-ordinal*
                    (- (fn2-cns-drain-cell 'fn2-machines-active-count *fn2-cns-admission-ordinal* dir) 1) dir))
             (dir (if retire dir
                    (fn2-cns-drain-put-cell 'fn2-machines-admission-credits *fn2-cns-admission-ordinal*
                      (+ 1 (fn2-cns-drain-cell 'fn2-machines-admission-credits *fn2-cns-admission-ordinal* dir))
                      (fn2-cns-drain-put-cell 'fn2-machines-free-head *fn2-cns-admission-ordinal* id dir))))
             (sched (fn2-cns-drain-cleared-sched id (fn2-cns-drain-child 'fn2-sched before)))
             (after (fn2-cns-drain-put-child 'fn2-sched sched
                      (fn2-cns-drain-put-child 'fn2-machines dir
                        (fn2-cns-drain-put-child 'fn2-pool pool
                          (fn2-cns-drain-put-child 'fn2-cns own before))))))
        (list 0 *fn2-work-release* 0 nil after)))))

(defun fn2-cns-draining-resultp (id before bytes steps descriptors runnable after)
  (equal (list bytes steps descriptors runnable after)
         (fn2-cns-draining-expected id before)))

; Cleanup is sequential. A failure of NS preserves the already completed
; WS release. No row reclamation or timer clear precedes either refusal.
(defun fn2-cns-draining-refusal-resultp (id before stage bytes steps descriptors runnable after)
  (let* ((dir (fn2-cns-drain-child 'fn2-machines before))
         (slot (fn2-cns-drain-cell 'fn2-machines-slot id dir))
         (own (fn2-cns-drain-child 'fn2-cns before))
         (pool (fn2-cns-drain-child 'fn2-pool before))
         (pool (if (eq stage :name)
                   (fn2-cns-drain-released-pool (fn2-cns-drain-cell 'fn2-cns-ws-slot slot own) pool)
                 pool))
         (ctl (fn2-cns-drain-child 'fn2-control before))
         (ctl (fn2-cns-drain-put 'fn2-control-stop 1
                (fn2-cns-drain-put 'fn2-control-stop-reason *fn2-stop-reason-pool-release* ctl)))
         (expected (fn2-cns-drain-put-child 'fn2-control ctl
                     (fn2-cns-drain-put-child 'fn2-pool pool before))))
    (and (member-eq stage '(:workspace :name))
         (equal (list bytes steps descriptors runnable after)
                (list 0 *fn2-work-state* 0 nil expected)))))

; Complete scheduler output/effect refinement, including all sibling rows.
(defthm fn2-cns-drain-clear-scheduler-by-definition
  (implies (and (natp id) (< id (fn2-sched-rows sched)))
    (equal (mv-nth 1 (fn2-sched-clear-deadline id sched))
           (fn2-cns-drain-cleared-sched id sched)))
  :rule-classes nil
  :hints (("Goal" :in-theory
    (enable fn2-sched-clear-deadline fn2-sched-rows
      fn2-sched-deadline fn2-sched-set-deadline fn2-sched-set-expired
      update-fn2-sched-deadline$ai update-fn2-sched-expired$ai
      fn2-sched-armed-timers fn2-sched-earliest-deadline
      update-fn2-sched-armed-timers update-fn2-sched-earliest-deadline
      fn2-cns-drain-cleared-sched fn2-cns-drain-put-cell
      fn2-cns-drain-put fn2-cns-drain-cell fn2-cns-drain-get
      fn2-cns-drain-index))))
; Even a failed held-lease release cannot alter any timer/queue. The lease
; premise is necessary: the final draining step clears its own timer.
(defthm fn2-cns-draining-held-keeps-timer
  (implies (and (fn2-corep core) (fn2-core-wfp core)
                (equal (fn2-cns-snapshot-read-code id core) :ok)
                (equal (fn2-cns-row-lease id core) *fn2-cns-lease-held*))
    (equal (fn2-core-sched (mv-nth 4 (fn2-cns-run-draining id budget core)))
           (fn2-core-sched core)))
  :rule-classes nil
  :hints (("Goal"
           :in-theory
           (e/d (fn2-cns-run-draining fn2-cns-lease-release
                 fn2-cns-write+lslot+lgen+lease fn2-core-stop
                 fn2-machine-refuse-write fn2-core-sched
                 update-fn2-core-pool update-fn2-core-control update-fn2-cns-table)
                (fn2-cns-snapshot-read-code fn2-core-release-children
                 fn2-control-record-stop)))))
(defthm fn2-cns-run-draining-held-keeps-timer
  (implies (and (fn2-corep core) (fn2-core-wfp core)
                (equal (fn2-cns-snapshot-read-code id core) :ok)
                (equal (fn2-cns-row-phase id core) *fn2-cns-state-draining*)
                (equal (fn2-cns-row-lease id core) *fn2-cns-lease-held*))
    (equal (fn2-core-sched (mv-nth 4 (fn2-cns-run id budget core)))
           (fn2-core-sched core)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn2-cns-draining-held-keeps-timer))
           :in-theory
           (e/d (fn2-cns-run fn2-machine-contract-check fn2-core-stop
                 fn2-core-sched update-fn2-core-control)
                (fn2-cns-run-draining fn2-cns-snapshot-read-code
                 fn2-cns-row-phase fn2-cns-row-lease fn2-cns-arm-ok-p
                 fn2-control-record-stop)))))
(defthm-owed fn2-cns-draining-held-scheduler-contract (id budget core)
  (implies (and (fn2-corep core) (fn2-core-wfp core)
                (equal (fn2-cns-snapshot-read-code id core) :ok)
                (equal (fn2-cns-row-phase id core) *fn2-cns-state-draining*)
                (equal (fn2-cns-row-lease id core) *fn2-cns-lease-held*))
    (equal (fn2-core-sched (mv-nth 4 (fn2-cns-run id budget core)))
           (fn2-core-sched core)))
  :schema :invariant :claim :semantic
  :boundary :unreachable-in-composition
  :teeth (fn2-cns-drain-held-witness fn2-cns-drain-without-held-counterexample)
  :doc "unreachable-in-composition (source-audited, reachability proof pending): hand/cancel release held leases before entering draining. This defensive actual-run theorem preserves all scheduler state on a held-lease input; it is not public served-path coverage. Removing the premise admits the timer-clearing final step.")
(fn2-owed-discharge fn2-cns-draining-held-scheduler-contract
                    fn2-cns-run-draining-held-keeps-timer)

; Refuted draft retained verbatim as a proposition, not an active obligation.
; Two owned slots plus count<rows does not imply two releases have room:
; tests/cns-draining-count-counterexample.lisp executes the complete H/not-C.
(defun-nx fn2-cns-draining-uncounted-claim (id budget core)
  (implies (and (fn2-corep core) (fn2-core-wfp core)
                (natp budget) (fn2-cns-draining-domainp id core))
    (mv-let (b s d r after) (fn2-cns-run id budget core)
      (fn2-cns-draining-resultp id core b s d r after))))

; Callers must carry accounting and reservations, not rescan the whole state
; while serving. Their entry/preservation links remain separate obligations.
; These full-H/C runtime controls are not yet formula-bound by the current
; witness generator; the universal claim remains explicitly owed.
(defthm-owed fn2-cns-draining-counted-independent (id budget core)
  (implies (and (fn2-corep core) (fn2-core-wfp core)
                (natp budget) (fn2-cns-draining-domainp id core)
                (fn2-cns-draining-reservedp core)
                (fn2-pool-semanticp (fn2-core-pool core)))
    (mv-let (b s d r after) (fn2-cns-run id budget core)
      (fn2-cns-draining-resultp id core b s d r after)))
  :schema :invariant :claim :semantic
  :teeth (fn2-cns-drain-positive fn2-cns-drain-without-pool-accounting
          fn2-cns-drain-without-reservation
          fn2-cns-drain-refusal-control fn2-cns-drain-negative)
  :case (:run fn2-cns :draining) :boundary :application-reclamation
  :doc "Given pool accounting and partition reservations, actual CNS draining releases exactly its owned resources, preserves siblings, clears its incarnation timer and returns reusable credit. Held/draining is defensive unreachable-in-composition input coverage; successful final reclaim is the served case. Universal proof and caller invariant links remain owed.")
