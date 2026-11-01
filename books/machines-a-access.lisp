; Bounded machine field access through the parent. Generated checked writers
; expose total, scalar APIs; no nested child remains borrowed during I/O.
(in-package "ACL2")
(include-book "core")

(defmacro fn2-machine-access-events ()
 '(progn
; The grant service's owner-declared sources (defwait, machines.lisp): per
; registered wait kind, its ready/grant pair constrained with the liveness
; and shape facts and attached to defaults that grant nothing; the owner
; attaches its own pair in its callbacks section.
(make-event (value (cons 'progn (fn2-machine-wait-source-events (fn2-machine-waits (w state)) (w state)))))
(make-event
 (value `(defthm fn2-machine-core-child-shapes
           (implies (fn2-core-wfp fn2-core)
                    (and ,@(fn2-machine-child-shapes *fn2-core-children*))))))
; A batched own-row write reattaches one well-shaped child: core.lisp's
; FN2-CORE-WFP-OF-UPDATE-FN2-<KIND>-TABLE keeps every callback guard from
; reopening the parent representation.
(in-theory (disable fn2-machines-rows
                    fn2-core-wfp
                    fn2-ops-free-count fn2-ops-reserved-credits fn2-ops-queued
                    fn2-ops-out-slot-length fn2-pool-nclasses
                    fn2-pool-class-counts-length fn2-pool-class-countsi
                    fn2-pool-cap fn2-pool-out-count))

(make-event (value `(in-theory (disable ,@(fn2-machine-row-readers (fn2-machine-names (w state)))))))

(defun fn2-machine-idp (id fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-machines (fn2-core-machines fn2-core)))
    (yes) (and (natp id) (< id (fn2-machines-rows fn2-machines))) yes))
(defthm fn2-machine-idp-bounds
  (implies (fn2-machine-idp id fn2-core)
           (and (natp id) (< id (fn2-machines-rows (fn2-core-machines fn2-core)))))
  :rule-classes (:rewrite :forward-chaining))
(in-theory (disable fn2-machine-idp))

(defmacro fn2-machine-index-access (field width)
  (let* ((reader (fn2-columns-col-name 'fn2-machines field))
         (get (fn2-columns-col-name 'fn2-machine field)))
    `(progn
       (in-theory (disable ,reader))
       ,@(fn2-machine-checked-reader-events get '(id)
           '(if (fn2-machine-idp id fn2-core) :ok :bounds)
           `(stobj-let ((fn2-machines (fn2-core-machines fn2-core)))
              (answer) (,reader id fn2-machines) answer))
       (defthm ,(fn2-columns-sym get "-NATP")
         (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
                  (natp (,get id fn2-core)))
         :rule-classes :type-prescription
         :hints (("Goal" :use ((:instance ,(fn2-columns-sym reader "-NATP")
                                (i id) (fn2-machines (fn2-core-machines fn2-core)))))))
       (defthm ,(fn2-columns-sym get "-BOUND")
         (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
                  (< (,get id fn2-core) ,(expt 2 width)))
         :rule-classes :linear
         :hints (("Goal" :use ((:instance ,(fn2-columns-sym reader "-BOUND")
                                (i id) (fn2-machines (fn2-core-machines fn2-core)))))))
       (in-theory (disable ,get)))))

(fn2-machine-index-access kind 8)
(fn2-machine-index-access slot 32)
(fn2-machine-scalar-access accept-count 32)
(fn2-machine-scalar-access refusals 60)
; Each admitted kind's partition, indexed by its admission ordinal (D 4.5).
(defmacro fn2-machine-partition-access (field)
  (let* ((reader (fn2-columns-sym (fn2-columns-col-name 'fn2-machines field) "I"))
         (writer (fn2-columns-pre "UPDATE-" reader))
         (get (fn2-columns-col-name 'fn2-machine field))
         (put (fn2-columns-col-name 'fn2-machine (fn2-columns-pre "SET-" field))))
    `(progn
       (in-theory (disable ,reader))
       (defun ,get (ord fn2-core)
         (declare (xargs :stobjs fn2-core :guard (and (fn2-core-wfp fn2-core) (natp ord)
                                                      (< ord *fn2-machine-admitted-max*))))
         (stobj-let ((fn2-machines (fn2-core-machines fn2-core)))
           (answer) (,reader ord fn2-machines) answer))
       (defthm ,(fn2-columns-sym get "-NATP")
         (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core) (natp ord) (< ord *fn2-machine-admitted-max*))
                  (natp (,get ord fn2-core)))
         :rule-classes (:rewrite :type-prescription)
         :hints (("Goal" :use ((:instance ,(fn2-columns-sym reader "-NATP")
                                (i ord) (fn2-machines (fn2-core-machines fn2-core)))))))
       (defthm ,(fn2-columns-sym get "-BOUND")
         (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core) (natp ord) (< ord *fn2-machine-admitted-max*))
                  (< (,get ord fn2-core) 4294967296))
         :rule-classes :linear
         :hints (("Goal" :use ((:instance ,(fn2-columns-sym reader "-BOUND")
                                (i ord) (fn2-machines (fn2-core-machines fn2-core)))))))
       (defun ,put (ord value fn2-core)
         (declare (xargs :stobjs fn2-core :guard (and (fn2-core-wfp fn2-core) (natp ord)
                                                      (< ord *fn2-machine-admitted-max*))))
         ; As the scalar setters: an over-width value stops the core.
         (if (not (unsigned-byte-p 32 value))
             (fn2-core-stop *fn2-stop-reason-machine-write* fn2-core)
           (stobj-let ((fn2-machines (fn2-core-machines fn2-core)))
             (fn2-machines) (,writer ord value fn2-machines) fn2-core)))
       (defthm ,(fn2-columns-sym put "-TYPE")
         (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core) (natp ord)
                       (< ord *fn2-machine-admitted-max*))
                  (fn2-corep (,put ord value fn2-core))))
       (defthm ,(fn2-columns-sym put "-WFP")
         (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core) (natp ord)
                       (< ord *fn2-machine-admitted-max*))
                  (fn2-core-wfp (,put ord value fn2-core))))
       (in-theory (disable ,get ,put)))))
(fn2-machine-partition-access connection-count)
(fn2-machine-partition-access free-head)
(fn2-machine-partition-access active-count)
(fn2-machine-partition-access admission-credits)
(fn2-machine-partition-access admission-head)
(fn2-machine-partition-access admission-tail)
(fn2-machine-scalar-access gen-limit 60)
(fn2-machine-scalar-access wake-id 32)
(fn2-machine-scalar-access pool-wait-id 32)
(fn2-machine-scalar-access wait-head 32)
(fn2-machine-scalar-access wait-tail 32)

(defun fn2-machine-refuse-write (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (fn2-core-stop *fn2-stop-reason-machine-write* fn2-core))
(defthm fn2-machine-refuse-write-type
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
           (fn2-corep (fn2-machine-refuse-write fn2-core))))
(defthm fn2-machine-refuse-write-wfp
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
           (fn2-core-wfp (fn2-machine-refuse-write fn2-core))))
(in-theory (disable fn2-machine-refuse-write))

(make-event
 (value (cons 'progn (append (fn2-machine-directory-field-events *fn2-machine-directory-fields*)
                             (fn2-machine-all-field-events (fn2-machine-names (w state))
                               (fn2-machine-names (w state)) (w state)
                               (strip-cars *fn2-machine-directory-fields*))))))

; The per-kind row readers (K-ROW-<field>) are materialized after this
; section, one book per layer (assembly-rows-a .. -other): fn2-machine-row-events.

(make-event (value (fn2-declare '(:operation-set fn2-machine-resources) nil nil nil)))

; Both resource queues use the dormant row's ready links. Separate FIFO
; heads prevent a row waiter from hiding an operation needed for reclamation.
(defmacro fn2-machine-wait-queue (park grant child-park child-grant &optional ords)
  ; The core faces of the directory's FIFO operations (arm-children.lisp).
  ; ORDS: (ord) when the queue is one per admitted kind.
  `(progn
     (fn2-defoperation (:operation-set fn2-machine-resources) :access (fn2-core)
     (defun ,park (id ,@ords fn2-core)
       (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
       (stobj-let ((fn2-machines (fn2-core-machines fn2-core))
                   (fn2-control (fn2-core-control fn2-core)))
         (fn2-machines fn2-control) (,child-park id ,@ords fn2-machines fn2-control) fn2-core)))
     (fn2-core-preserves ,park (id ,@ords fn2-core) :rows nil :prefix "")
     (fn2-defoperation (:operation-set fn2-machine-resources) :access (id fn2-core)
     (defun ,grant (,@ords fn2-core)
       (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
       (stobj-let ((fn2-machines (fn2-core-machines fn2-core))
                   (fn2-control (fn2-core-control fn2-core)))
         (id fn2-machines fn2-control) (,child-grant ,@ords fn2-machines fn2-control) (mv id fn2-core))))
     (fn2-core-preserves ,grant (,@ords fn2-core) :position 1 :rows nil)))
(fn2-machine-wait-queue fn2-machine-park fn2-machine-grant-op fn2-machines-park fn2-machines-grant-op)
(fn2-machine-wait-queue fn2-machine-park-admission fn2-machine-grant-admission
                        fn2-machines-park-admission fn2-machines-grant-admission (ord))

; A drained row's return to its partition ORD (fn2-machines-reclaim).
(defun fn2-machine-reclaim (id ord retire fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-machines (fn2-core-machines fn2-core))
              (fn2-control (fn2-core-control fn2-core)))
    (fn2-machines fn2-control) (fn2-machines-reclaim id ord retire fn2-machines fn2-control) fn2-core))
(fn2-core-preserves fn2-machine-reclaim (id ord retire fn2-core) :rows nil :prefix "")
; Wake another row (fn2-machines-wake-row).
(defun fn2-machine-wake-row (id fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-machines (fn2-core-machines fn2-core))
              (fn2-control (fn2-core-control fn2-core)))
    (fn2-machines fn2-control) (fn2-machines-wake-row id fn2-machines fn2-control) fn2-core))
(fn2-core-preserves fn2-machine-wake-row (id fn2-core) :rows nil :prefix "")
(defun fn2-machine-waiting-p (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (not (equal (fn2-machine-wait-head fn2-core) *fn2-none*)))
; Whether the pool has COUNT free rows of each (CLASS . COUNT) in NEEDS.
(defun fn2-machine-pool-has-p (needs fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (if (atom needs) t
    (and (consp (car needs)) (natp (caar needs)) (natp (cdar needs))
         (let ((class (caar needs)) (count (cdar needs)))
           (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
             (yes)
             (and (< class (fn2-pool-nclasses fn2-pool))
                  (< class (fn2-pool-class-counts-length fn2-pool))
                  (<= count (fn2-pool-class-countsi class fn2-pool)))
             yes))
         (fn2-machine-pool-has-p (cdr needs) fn2-core))))
; The first partition with a parked taker, a free credit and (for a taken
; kind, A-S7) the pool rows its take reserves, or nil.
(defun fn2-machine-admission-ready-ord (o fn2-core)
  (declare (xargs :stobjs fn2-core :measure (nfix (- *fn2-machine-admitted-max* (nfix o)))
                  :guard (and (fn2-core-wfp fn2-core) (natp o))))
  (if (or (not (natp o)) (>= o *fn2-machine-admitted-max*)) nil
    (if (and (not (equal (fn2-machine-admission-head o fn2-core) *fn2-none*))
             (< 0 (fn2-machine-admission-credits o fn2-core))
             (fn2-machine-pool-has-p (fn2-machine-partition-classes o) fn2-core))
        o
      (fn2-machine-admission-ready-ord (+ 1 o) fn2-core))))
(defthm fn2-machine-admission-ready-ord-range
  (implies (fn2-machine-admission-ready-ord o fn2-core)
           (and (natp (fn2-machine-admission-ready-ord o fn2-core))
                (< (fn2-machine-admission-ready-ord o fn2-core) *fn2-machine-admitted-max*))))
(defun fn2-machine-admission-ready-p (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (if (fn2-machine-admission-ready-ord 0 fn2-core) t nil))

; Only scribe waits for pool capacity: listeners close an accepted capability
; if its admission bundle is unavailable. Its reserved singleton wait link
; is independent of op waiters, so pool exhaustion cannot hide a Close.
(defun fn2-machine-park-pool (id class fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (if (not (fn2-machine-idp id fn2-core)) fn2-core
    (let ((fn2-core (fn2-machine-write-cursor id class fn2-core)))
      (stobj-let ((fn2-machines (fn2-core-machines fn2-core))
                  (fn2-control (fn2-core-control fn2-core)))
        (fn2-machines fn2-control) (fn2-machines-park-pool id fn2-machines fn2-control) fn2-core))))
(fn2-core-preserves fn2-machine-park-pool (id class fn2-core) :rows nil :prefix "")

; The peer record of the observation being delivered (layer doc 4.1.1): the
; ops child's latch, written by every harvest.
(defun fn2-core-observed-peer (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
    (family port w0 w1 w2 w3) (fn2-ops-observed-peer fn2-ops)
    (mv family port w0 w1 w2 w3)))

(defun fn2-machine-op-credit-p (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
    (yes)
    (and (< 0 (fn2-ops-free-count fn2-ops))
         (< (+ (fn2-ops-reserved-credits fn2-ops) (fn2-ops-queued fn2-ops))
            (fn2-ops-out-slot-length fn2-ops)))
    yes))

(defun fn2-machine-pool-credit-p (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (let ((id (fn2-machine-pool-wait-id fn2-core)))
    (and (not (equal id *fn2-none*)) (eq (fn2-machine-cursor-read-code id fn2-core) :ok)
         (let ((class (fn2-machine-cursor id fn2-core)))
         (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
           (yes)
           (and (< class (fn2-pool-nclasses fn2-pool))
                (< class (fn2-pool-class-counts-length fn2-pool))
                (< 0 (fn2-pool-class-countsi class fn2-pool)))
           yes)))))

(make-event
 (value
  `(progn
(defun fn2-machine-grant-ready-p (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (or (and (fn2-machine-waiting-p fn2-core) (fn2-machine-op-credit-p fn2-core))
      (fn2-machine-pool-credit-p fn2-core)
      (fn2-machine-admission-ready-p fn2-core)
      ,@(fn2-machine-wait-ready-calls (fn2-machine-waits (w state)) (w state))))

(defun fn2-machine-grant-one (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (cond ((and (fn2-machine-waiting-p fn2-core) (fn2-machine-op-credit-p fn2-core))
         (fn2-machine-grant-op fn2-core))
        ((fn2-machine-pool-credit-p fn2-core)
         (let* ((id (fn2-machine-pool-wait-id fn2-core))
                (fn2-core (fn2-machine-set-pool-wait-id *fn2-none* fn2-core))
                (fn2-core (fn2-machine-write-wait-reason id *fn2-wait-none* fn2-core)))
           (mv id fn2-core)))
        ((fn2-machine-admission-ready-ord 0 fn2-core)
         (fn2-machine-grant-admission (fn2-machine-admission-ready-ord 0 fn2-core) fn2-core))
        ; The owners' sources (defwait), in registration order: D's ledger
        ; (requests, D7 4/n-a), C's sealer, B's commit batch, D's claims;
        ; each clears its row's wait.
        ,@(fn2-machine-wait-grant-clauses (fn2-machine-waits (w state)) (w state))
        (t (mv *fn2-none* fn2-core)))))))
(fn2-core-preserves fn2-machine-grant-one (fn2-core) :position 1 :rows nil)

(make-event
 (value (cons 'progn
   (fn2-machine-checked-reader-events 'fn2-machine-pool-capacity '(slot)
     '(stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (code)
        (if (and (natp slot) (< slot (fn2-pool-rows fn2-pool))) :ok :bounds) code)
     '(stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (value)
        (fn2-pool-slot-capacity slot fn2-pool) value)))))
(defthm fn2-machine-pool-capacity-natp
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
           (natp (fn2-machine-pool-capacity slot fn2-core)))
  :rule-classes :type-prescription)
(defthm fn2-machine-pool-capacity-natural
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
           (and (integerp (fn2-machine-pool-capacity slot fn2-core))
                (<= 0 (fn2-machine-pool-capacity slot fn2-core))
                (rationalp (fn2-machine-pool-capacity slot fn2-core))
                (acl2-numberp (fn2-machine-pool-capacity slot fn2-core))))
  :hints (("Goal" :use fn2-machine-pool-capacity-natp)))
(in-theory (disable fn2-machine-pool-capacity))

; Harvest has already settled the loan. Mirror the pool's authoritative
; borrow count rather than infer release solely from terminal payload bits:
; a release observation can be posted but not yet harvested at the terminal.
(make-event
 (value (cons 'progn
   (fn2-machine-checked-reader-events 'fn2-machine-pool-borrows '(slot)
     '(stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (code)
        (if (and (natp slot) (< slot (fn2-pool-rows fn2-pool))) :ok :bounds) code)
     '(stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (value)
        (fn2-pool-slot-borrows slot fn2-pool) value)))))
(defthm fn2-machine-pool-borrows-natp
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
           (natp (fn2-machine-pool-borrows slot fn2-core)))
  :rule-classes :type-prescription)
(in-theory (disable fn2-machine-pool-borrows))

(defun fn2-machine-take-wake (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (let* ((id (fn2-machine-wake-id fn2-core))
         (fn2-core (fn2-machine-set-wake-id *fn2-none* fn2-core)))
    (mv id fn2-core)))
(fn2-core-preserves fn2-machine-take-wake (fn2-core) :position 1 :rows nil)
(assert-event
 (fn2-assert-compliant-p
  '(fn2-machine-idp fn2-machine-park fn2-machine-park-pool
    fn2-machine-waiting-p fn2-machine-op-credit-p fn2-machine-pool-credit-p
    fn2-machine-grant-ready-p fn2-machine-grant-one
    fn2-machine-pool-capacity fn2-machine-pool-borrows fn2-machine-take-wake) (w state)))

(defun fn2-machine-refuse-charge ()
  (declare (xargs :guard t))
  (mv 0 0 0))
(make-event
 (value `(defun fn2-machine-charge-kindp (kind)
           (declare (xargs :guard t))
           (member-equal kind ',(strip-cars
              (fn2-machine-charge-arms (fn2-machine-names (w state)) 0))))))
(make-event
 (value `(defun fn2-machine-charge (kind bytes steps descriptors)
           (declare (xargs :guard (and (fn2-machine-charge-kindp kind)
                                      (natp bytes) (natp steps) (natp descriptors))))
           (case kind ,@(fn2-machine-charge-arms (fn2-machine-names (w state)) 0)
             (otherwise (fn2-machine-refuse-charge))))))
(in-theory (disable fn2-machine-charge))

(defun fn2-machine-work-fits-p (kind bytes steps descriptors)
  (declare (xargs :guard (and (natp bytes) (natp steps) (natp descriptors))))
  (if (not (fn2-machine-charge-kindp kind)) nil
    (mv-let (b s d) (fn2-machine-charge kind bytes steps descriptors)
      (and (equal b bytes) (equal s steps) (equal d descriptors)))))
(in-theory (disable fn2-machine-work-fits-p))

; One preflight form for all payload/descriptor continuations. Refusal keeps
; the row, pool, and outbox unchanged, and requeues the same continuation.
(defmacro fn2-machine-with-work (bytes steps descriptors body)
  `(if (and (fn2-machine-idp id fn2-core)
            (fn2-machine-work-fits-p (fn2-machine-kind id fn2-core)
                                    ,bytes ,steps ,descriptors))
       ,body
     (fn2-machine-yield id fn2-core)))

; Input becomes machine-readable at harvest, separately from the issue's
; reserved range and any later verification scan. Peek before recycling.
(defun fn2-machine-next-input-bytes (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (and (fn2-core-wfp fn2-core)
                         (mv-let (ownerp kind id gen principal) (fn2-core-next-owner fn2-core)
                           (declare (ignore kind id gen principal)) ownerp))
                  :guard-hints (("Goal" :use ((:instance fn2-core-ops-type))
                    :in-theory (disable fn2-opsp fn2-ops-post-head
                                        fn2-ops-posted-fifoi fn2-ops-posted-fifo-length)))))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
    (bytes)
    (let ((head (fn2-ops-post-head fn2-ops)))
      (if (or (zp (fn2-ops-post-count fn2-ops))
              (>= head (fn2-ops-posted-fifo-length fn2-ops))) 0
        (let* ((index (fn2-ops-posted-fifoi head fn2-ops))
               (slot (floor index 2)) (cell (mod index 2)))
          (if (not (and (fn2-op-slotp slot fn2-ops) (unsigned-byte-p 1 cell)))
              (prog2$ (hard-error 'fn2-machine-next-input-bytes "Invalid posted cell." nil) 0)
          (mv-let (posted harvested event outcome reason count aux0 aux1)
            (fn2-op-cell cell slot fn2-ops)
            (declare (ignore reason aux0 aux1))
            (if (and (equal posted 1) (equal harvested 0)
                     (or (equal event *fn2-event-receive-result*)
                         (equal event *fn2-event-read-result*))
                     (or (equal outcome *fn2-outcome-done*)
                         (equal outcome *fn2-outcome-short*)))
                (nfix count) 0))))))
    bytes))
(defthm fn2-machine-next-input-bytes-natp
  (natp (fn2-machine-next-input-bytes fn2-core))
  :rule-classes :type-prescription)
(in-theory (disable fn2-machine-next-input-bytes))

; Package the charge once behind shape lemmas. Inlining this kind test in
; every continuation multiplies preservation branches by the number of kinds.
(make-event
 (value `(defun fn2-machine-finish (id bytes steps descriptors runnable fn2-core)
           (declare (xargs :stobjs fn2-core
                      :guard (and (fn2-core-wfp fn2-core)
                               (or (not (fn2-machine-idp id fn2-core))
                                (case (fn2-machine-kind id fn2-core)
                                 ,@(fn2-machine-charge-guards (fn2-machine-names (w state)) (w state) 0)
                                 (otherwise t))))))
           (if (and (fn2-machine-idp id fn2-core)
                    (fn2-machine-charge-kindp (fn2-machine-kind id fn2-core)))
               (mv-let (used-bytes used-steps used-descriptors)
                 (fn2-machine-charge (fn2-machine-kind id fn2-core) bytes steps descriptors)
                 (mv used-bytes used-steps used-descriptors runnable fn2-core))
             (mv-let (used-bytes used-steps used-descriptors)
               (fn2-machine-refuse-charge)
               (let ((fn2-core (fn2-machine-refuse-write fn2-core)))
                 (mv used-bytes used-steps used-descriptors nil fn2-core)))))))
(fn2-core-preserves fn2-machine-finish (id bytes steps descriptors runnable fn2-core) :position 4 :rows nil)
(in-theory (disable fn2-machine-charge-kindp))

(defun fn2-machine-idle (id fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (fn2-machine-result 0 *fn2-work-empty* 0 nil fn2-core))
(fn2-core-preserves fn2-machine-idle (id fn2-core) :position 4 :rows nil)
(defun fn2-machine-yield (id fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (fn2-machine-result 0 *fn2-work-empty* 0 t fn2-core))
(fn2-core-preserves fn2-machine-yield (id fn2-core) :position 4 :rows nil)
; The arm contract asserted after every run and handler (R7): OK is the
; kind's certificate on the run's charge and the row's next phase. Its shape
; is proved once here, so the generated run entries do not re-prove it.
(defun fn2-machine-contract-check (ok bytes steps descriptors runnable fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (if ok (mv bytes steps descriptors runnable fn2-core)
    (let ((fn2-core (fn2-core-stop *fn2-stop-reason-machine-contract* fn2-core)))
      (mv bytes steps descriptors nil fn2-core))))
(fn2-core-preserves fn2-machine-contract-check (ok bytes steps descriptors runnable fn2-core) :position 4 :rows nil)
(defun fn2-machine-observe-contract-check (ok wake fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (if ok (mv wake fn2-core)
    (let ((fn2-core (fn2-core-stop *fn2-stop-reason-machine-contract* fn2-core)))
      (mv *fn2-none* fn2-core))))
(fn2-core-preserves fn2-machine-observe-contract-check (ok wake fn2-core) :position 1 :rows nil)
(defun fn2-machine-refuse-phase (id fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  ; Named invalid-phase refusal; retained stopped evidence, never an idle arm.
  (let ((fn2-core (fn2-core-stop *fn2-stop-reason-machine-phase* fn2-core)))
    (fn2-machine-result 0 *fn2-work-empty* 0 nil fn2-core)))
(fn2-core-preserves fn2-machine-refuse-phase (id fn2-core) :position 4 :rows nil)
(in-theory (disable fn2-machines-kind-basesi))
(defun fn2-machine-kind-base (kind fn2-core)
  (declare (xargs :stobjs fn2-core :guard (and (fn2-core-wfp fn2-core) (unsigned-byte-p 8 kind))))
  (stobj-let ((fn2-machines (fn2-core-machines fn2-core)))
    (id) (if (unsigned-byte-p 8 kind) (fn2-machines-kind-basesi kind fn2-machines)
           (prog2$ (hard-error 'fn2-machine-kind-base "Invalid machine kind." nil) *fn2-none*)) id))
(defthm fn2-machine-kind-base-natp
  (implies (fn2-corep fn2-core) (natp (fn2-machine-kind-base kind fn2-core)))
  :rule-classes :type-prescription
  :hints (("Goal" :use (fn2-core-machines-type
                        (:instance fn2-machines-kind-basesi-natp
                          (i kind) (fn2-machines (fn2-core-machines fn2-core)))))))
(in-theory (disable fn2-machine-kind-base))
(defun fn2-machine-scribe-id (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (fn2-machine-kind-base *fn2-scribe-kind* fn2-core))
(in-theory (disable fn2-machine-scribe-id))


; Initialization policy belongs to listeners and is copied to each admitted
; connection. No echo/discard policy lives in the shared directory.
(defun fn2-listener-mode-rows (left mode fn2-listener)
  (declare (xargs :stobjs fn2-listener :measure (nfix left)
                  :guard (and (fn2-listener-wfp fn2-listener) (natp left)
                              (<= left (fn2-listener-rows fn2-listener)) (unsigned-byte-p 1 mode))))
  (if (zp left) fn2-listener
    (let ((fn2-listener (fn2-listener-set-mode (- left 1) mode fn2-listener)))
      (fn2-listener-mode-rows (- left 1) mode fn2-listener))))
(defthm fn2-listener-mode-rows-type
  (implies (and (fn2-listenerp fn2-listener) (fn2-listener-wfp fn2-listener)
                (natp left) (<= left (fn2-listener-rows fn2-listener)) (unsigned-byte-p 1 mode))
           (fn2-listenerp (fn2-listener-mode-rows left mode fn2-listener))))
(defthm fn2-listener-mode-rows-wfp
  (implies (and (fn2-listener-wfp fn2-listener) (natp left)
                (<= left (fn2-listener-rows fn2-listener)) (unsigned-byte-p 1 mode))
           (fn2-listener-wfp (fn2-listener-mode-rows left mode fn2-listener))))
(in-theory (disable fn2-listener-mode-rows))
(defun fn2-listener-set-mode-all (mode fn2-core)
  (declare (xargs :stobjs fn2-core :guard (and (fn2-core-wfp fn2-core) (unsigned-byte-p 1 mode))))
  (if (not (unsigned-byte-p 1 mode)) (fn2-machine-refuse-write fn2-core)
    (stobj-let ((fn2-listener (fn2-listener-table fn2-core))) (fn2-listener)
      (fn2-listener-mode-rows (fn2-listener-rows fn2-listener) mode fn2-listener) fn2-core)))
(defthm fn2-listener-set-mode-all-type
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
           (fn2-corep (fn2-listener-set-mode-all mode fn2-core)))
  :hints (("Goal" :use ((:instance fn2-listener-mode-rows-type
                         (fn2-listener (fn2-listener-table fn2-core))
                         (left (fn2-listener-rows (fn2-listener-table fn2-core)))))
                  :in-theory (enable fn2-core-wfp))))
(defthm fn2-listener-set-mode-all-wfp
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
           (fn2-core-wfp (fn2-listener-set-mode-all mode fn2-core)))
  :hints (("Goal" :in-theory (enable fn2-core-wfp))))
(in-theory (disable fn2-listener-set-mode-all))
; The admitted kind every listener admits into (D 4.5), from the profile.
(defun fn2-listener-target-rows (left target fn2-listener)
  (declare (xargs :stobjs fn2-listener :measure (nfix left)
                  :guard (and (fn2-listener-wfp fn2-listener) (natp left)
                              (<= left (fn2-listener-rows fn2-listener)) (unsigned-byte-p 8 target))))
  (if (zp left) fn2-listener
    (let ((fn2-listener (fn2-listener-set-target (- left 1) target fn2-listener)))
      (fn2-listener-target-rows (- left 1) target fn2-listener))))
(defthm fn2-listener-target-rows-type
  (implies (and (fn2-listenerp fn2-listener) (fn2-listener-wfp fn2-listener)
                (natp left) (<= left (fn2-listener-rows fn2-listener)) (unsigned-byte-p 8 target))
           (fn2-listenerp (fn2-listener-target-rows left target fn2-listener))))
(defthm fn2-listener-target-rows-wfp
  (implies (and (fn2-listener-wfp fn2-listener) (natp left)
                (<= left (fn2-listener-rows fn2-listener)) (unsigned-byte-p 8 target))
           (fn2-listener-wfp (fn2-listener-target-rows left target fn2-listener))))
(in-theory (disable fn2-listener-target-rows))
(defun fn2-listener-set-target-all (target fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (if (not (and (natp target) (< target *fn2-machine-admitted-max*))) (fn2-machine-refuse-write fn2-core)
    (stobj-let ((fn2-listener (fn2-listener-table fn2-core))) (fn2-listener)
      (fn2-listener-target-rows (fn2-listener-rows fn2-listener) target fn2-listener) fn2-core)))
(defthm fn2-listener-set-target-all-type
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
           (fn2-corep (fn2-listener-set-target-all target fn2-core)))
  :hints (("Goal" :use ((:instance fn2-listener-target-rows-type
                         (fn2-listener (fn2-listener-table fn2-core))
                         (left (fn2-listener-rows (fn2-listener-table fn2-core)))))
                  :in-theory (enable fn2-core-wfp))))
(defthm fn2-listener-set-target-all-wfp
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
           (fn2-core-wfp (fn2-listener-set-target-all target fn2-core)))
  :hints (("Goal" :in-theory (enable fn2-core-wfp))))
(in-theory (disable fn2-listener-set-target-all))

; Each listener's principal slot (D7's S1), from the profile key
; :listener-principals, one slot per listener in listener order (default 0):
; its Accept bookings go to that principal, and the admitted row copies it.
; A slot that is not a principal of the calendar makes the listener's first
; wake stop the core (:wake-bounds).
(defun fn2-listener-principal-rows (left slots fn2-listener)
  (declare (xargs :stobjs fn2-listener :measure (nfix left)
                  :guard (and (fn2-listener-wfp fn2-listener) (natp left)
                              (<= left (fn2-listener-rows fn2-listener)))))
  (if (zp left) fn2-listener
    (let* ((slot (nth (- left 1) (true-list-fix slots)))
           (fn2-listener (fn2-listener-set-principal-slot (- left 1)
                           (if (unsigned-byte-p 16 slot) slot 0) fn2-listener)))
      (fn2-listener-principal-rows (- left 1) slots fn2-listener))))
(defthm fn2-listener-principal-rows-type
  (implies (and (fn2-listenerp fn2-listener) (fn2-listener-wfp fn2-listener)
                (natp left) (<= left (fn2-listener-rows fn2-listener)))
           (fn2-listenerp (fn2-listener-principal-rows left slots fn2-listener))))
(defthm fn2-listener-principal-rows-wfp
  (implies (and (fn2-listener-wfp fn2-listener) (natp left)
                (<= left (fn2-listener-rows fn2-listener)))
           (fn2-listener-wfp (fn2-listener-principal-rows left slots fn2-listener))))
(in-theory (disable fn2-listener-principal-rows))
(defun fn2-listener-set-principals (slots fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-listener (fn2-listener-table fn2-core))) (fn2-listener)
    (fn2-listener-principal-rows (fn2-listener-rows fn2-listener) slots fn2-listener) fn2-core))
(defthm fn2-listener-set-principals-type
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
           (fn2-corep (fn2-listener-set-principals slots fn2-core)))
  :hints (("Goal" :use ((:instance fn2-listener-principal-rows-type
                         (fn2-listener (fn2-listener-table fn2-core))
                         (left (fn2-listener-rows (fn2-listener-table fn2-core)))))
                  :in-theory (enable fn2-core-wfp))))
(defthm fn2-listener-set-principals-wfp
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
           (fn2-core-wfp (fn2-listener-set-principals slots fn2-core)))
  :hints (("Goal" :in-theory (enable fn2-core-wfp))))
(in-theory (disable fn2-listener-set-principals))

(fn2-resolve :access)
))
