; Independent, proof-only application semantics for the served CNS cleanup.
; The checking side is list arithmetic: no handler, release, reclaim or timer
; operation is called. Schema metadata supplies positions, never decisions.
(in-package "ACL2")
(include-book "assembly-attach")

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

; Full served-domain admission and proof are the destination. The separate
; universal theorem is intentionally not replaced by fixture success.
(defthm-owed fn2-cns-draining-independent (id budget core)
  (implies (and (fn2-corep core) (fn2-core-wfp core)
                (natp budget) (fn2-cns-draining-domainp id core))
    (mv-let (b s d r after) (fn2-cns-run id budget core)
      (fn2-cns-draining-resultp id core b s d r after)))
  :schema :invariant :claim :semantic
  :teeth (fn2-cns-drain-positive fn2-cns-drain-negative)
  :doc "Served CNS draining releases only owned resources, preserves siblings, clears its incarnation timer and returns exactly its reusable credit; held lease is an intermediate step.")
