; Bounded machine field access through the parent. Generated checked writers
; expose total, scalar APIs; no nested child remains borrowed during I/O.
(in-package "ACL2")
(include-book "core")

(make-event
 (value `(defthm fn2-machine-core-child-shapes
           (implies (fn2-core-wfp fn2-core)
                    (and ,@(fn2-machine-child-shapes *fn2-core-children*))))))
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
(in-theory (disable fn2-machine-idp))

(defmacro fn2-machine-index-access (field width)
  (let* ((reader (fn2-columns-col-name 'fn2-machines field))
         (get (fn2-columns-col-name 'fn2-machine field)))
    `(progn
       (in-theory (disable ,reader))
       (defun ,get (id fn2-core)
         (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
         (stobj-let ((fn2-machines (fn2-core-machines fn2-core)))
           (answer)
           (if (and (natp id) (< id (fn2-machines-rows fn2-machines)))
               (,reader id fn2-machines) 0)
           answer))
       (defthm ,(fn2-columns-sym get "-NATP")
         (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
                  (natp (,get id fn2-core)))
         :rule-classes :type-prescription)
       (defthm ,(fn2-columns-sym get "-BOUND")
         (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
                  (< (,get id fn2-core) ,(expt 2 width)))
         :rule-classes :linear)
       (in-theory (disable ,get)))))

(fn2-machine-index-access kind 8)
(fn2-machine-index-access slot 32)

(make-event
 (value (cons 'progn (fn2-machine-all-field-events (fn2-machine-names (w state))
                       (fn2-machine-names (w state)) (w state) nil))))

(fn2-machine-scalar-access accept-count 32)
(fn2-machine-scalar-access connection-count 32)
(fn2-machine-scalar-access free-head 32)
(fn2-machine-scalar-access null-free-head 32)
(fn2-machine-scalar-access active-count 32)
(fn2-machine-scalar-access gen-limit 60)
(fn2-machine-scalar-access echo-mode 1)
(fn2-machine-scalar-access wake-id 32)
(fn2-machine-scalar-access pool-wait-id 32)
(fn2-machine-scalar-access wait-head 32)
(fn2-machine-scalar-access wait-tail 32)

(defmacro fn2-machine-core-shape (name args)
  `(progn
     (defthm ,(fn2-columns-sym name "-TYPE")
       (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
                (fn2-corep (,name ,@args fn2-core))))
     (defthm ,(fn2-columns-sym name "-WFP")
       (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
                (fn2-core-wfp (,name ,@args fn2-core))))
     (in-theory (disable ,name))))

(defun fn2-machine-park (id fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (if (or (not (fn2-machine-idp id fn2-core))
          (equal (fn2-machine-wait-reason id fn2-core) 2)) fn2-core
    (let* ((tail (fn2-machine-wait-tail fn2-core))
           (fn2-core (fn2-machine-put id
                       (wait-reason 2) (ready-prev tail) (ready-next 4294967295)))
           (fn2-core (if (equal tail 4294967295)
                         (fn2-machine-set-wait-head id fn2-core)
                       (fn2-machine-set-ready-next tail id fn2-core)))
           (fn2-core (fn2-machine-set-wait-tail id fn2-core)))
      fn2-core)))
(fn2-machine-core-shape fn2-machine-park (id))

(defun fn2-machine-waiting-p (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (not (equal (fn2-machine-wait-head fn2-core) 4294967295)))

(defun fn2-machine-grant-op (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (let ((id (fn2-machine-wait-head fn2-core)))
    (if (equal id 4294967295) (mv id fn2-core)
      (let* ((next (fn2-machine-ready-next id fn2-core))
             (fn2-core (fn2-machine-set-wait-head next fn2-core))
             (fn2-core (if (equal next 4294967295)
                           (fn2-machine-set-wait-tail 4294967295 fn2-core)
                         (fn2-machine-set-ready-prev next 4294967295 fn2-core)))
             (fn2-core (fn2-machine-put id
                         (wait-reason 0) (ready-prev 4294967295)
                         (ready-next 4294967295))))
        (mv id fn2-core)))))
(fn2-core-shape-lemmas fn2-machine-grant-op () 1)

; Only scribe waits for pool capacity: listeners close an accepted capability
; if its admission bundle is unavailable. Its reserved singleton wait link
; is independent of op waiters, so pool exhaustion cannot hide a Close.
(defun fn2-machine-park-pool (id class fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (if (not (fn2-machine-idp id fn2-core)) fn2-core
    (let ((fn2-core (fn2-machine-put id (wait-reason 3) (cursor class))))
      (fn2-machine-set-pool-wait-id id fn2-core))))
(fn2-machine-core-shape fn2-machine-park-pool (id class))

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
  (let* ((id (fn2-machine-pool-wait-id fn2-core))
         (class (fn2-machine-cursor id fn2-core)))
    (and (not (equal id 4294967295))
         (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
           (yes)
           (and (< class (fn2-pool-nclasses fn2-pool))
                (< class (fn2-pool-class-counts-length fn2-pool))
                (< 0 (fn2-pool-class-countsi class fn2-pool)))
           yes))))

(defun fn2-machine-grant-ready-p (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (or (and (fn2-machine-waiting-p fn2-core) (fn2-machine-op-credit-p fn2-core))
      (fn2-machine-pool-credit-p fn2-core)))

(defun fn2-machine-grant-one (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (cond ((and (fn2-machine-waiting-p fn2-core) (fn2-machine-op-credit-p fn2-core))
         (fn2-machine-grant-op fn2-core))
        ((fn2-machine-pool-credit-p fn2-core)
         (let* ((id (fn2-machine-pool-wait-id fn2-core))
                (fn2-core (fn2-machine-set-pool-wait-id 4294967295 fn2-core))
                (fn2-core (fn2-machine-set-wait-reason id 0 fn2-core)))
           (mv id fn2-core)))
        (t (mv 4294967295 fn2-core))))
(fn2-core-shape-lemmas fn2-machine-grant-one () 1)

(defun fn2-machine-pool-capacity (slot fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
    (cap)
    (if (and (natp slot) (< slot (fn2-pool-rows fn2-pool)))
        (fn2-pool-cap slot fn2-pool) 0)
    cap))
(defthm fn2-machine-pool-capacity-natp
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
           (natp (fn2-machine-pool-capacity slot fn2-core)))
  :rule-classes :type-prescription)
(in-theory (disable fn2-machine-pool-capacity))

; Harvest has already settled the loan. Mirror the pool's authoritative
; borrow count rather than infer release solely from terminal payload bits:
; a release observation can be posted but not yet harvested at the terminal.
(defun fn2-machine-pool-borrows (slot fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
    (count)
    (if (and (natp slot) (< slot (fn2-pool-rows fn2-pool)))
        (fn2-pool-out-count slot fn2-pool) 0)
    count))
(defthm fn2-machine-pool-borrows-natp
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
           (natp (fn2-machine-pool-borrows slot fn2-core)))
  :rule-classes :type-prescription)
(in-theory (disable fn2-machine-pool-borrows))

(defun fn2-machine-take-wake (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (let* ((id (fn2-machine-wake-id fn2-core))
         (fn2-core (fn2-machine-set-wake-id 4294967295 fn2-core)))
    (mv id fn2-core)))
(fn2-core-shape-lemmas fn2-machine-take-wake () 1)
(assert-event
 (fn2-profile-exports-compliant-p
  '(fn2-machine-idp fn2-machine-park fn2-machine-park-pool
    fn2-machine-waiting-p fn2-machine-op-credit-p fn2-machine-pool-credit-p
    fn2-machine-grant-ready-p fn2-machine-grant-one
    fn2-machine-pool-capacity fn2-machine-pool-borrows fn2-machine-take-wake) (w state)))

; Layer A's four declarations share this quantum. The charge call is inside
; every return from a continuation; guard verification checks the caps there.
(make-event
 (value `(defun fn2-machine-charge (kind bytes steps descriptors)
           (declare (xargs :guard
                      (case kind ,@(fn2-machine-charge-guards (fn2-machine-names (w state)) (w state) 0)
                        (otherwise (and (natp bytes) (natp steps) (natp descriptors))))))
           (case kind ,@(fn2-machine-charge-arms (fn2-machine-names (w state)) 0)
             (otherwise (mv bytes steps descriptors))))))

(defun fn2-machine-idle (id fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (fn2-machine-result 0 1 0 nil fn2-core))
(fn2-core-shape-lemmas fn2-machine-idle (id) 4)
(defun fn2-machine-yield (id fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (fn2-machine-result 0 1 0 t fn2-core))
(fn2-core-shape-lemmas fn2-machine-yield (id) 4)
(defun fn2-machine-refuse-phase (id fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  ; Named invalid-phase refusal; retained stopped evidence, never an idle arm.
  (let ((fn2-core (fn2-machine-set-stopped id 1 fn2-core)))
    (fn2-machine-result 0 1 0 nil fn2-core)))
(fn2-core-shape-lemmas fn2-machine-refuse-phase (id) 4)
(defun fn2-machine-scribe-id (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-sched (fn2-core-sched fn2-core)))
    (id) (fn2-sched-scribe-index fn2-sched) id))
(in-theory (disable fn2-machine-scribe-id))
