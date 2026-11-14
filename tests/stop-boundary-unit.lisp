; Teeth of FN2-ENV-STEP-REFUSES-WHEN-STOPPED (books/stop-boundary.lisp): one core,
; admitted and turned until its outbox holds the commit's first actions, then
; offered (:take) and (:admit 2 0) through fn2-env-step itself.
(in-package "ACL2")
(include-book "../books/stop-boundary")

; B's commit profile (tests/commit-durable-all-unit.lisp's fn2-cda-profile).
(defconst *fn2-sbu-profile*
  (let* ((p *fn2-profile-tiny*)
         (p (put-assoc-equal :sim-sectors (* 5 *fn2-storage-extent-units*) p))
         (p (put-assoc-equal :extent-slots 5 p))
         (p (put-assoc-equal :pool-classes (append (fn2-profile-pool-classes p) '((8 . 4096))) p)))
    (put-assoc-equal :commit-barrier-mode 0 p)))

; Turn until the outbox holds an action (at most FUEL turns).
(defun fn2-sbu-turn-to-outbox (fuel fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix fuel)))
  (if (or (zp fuel) (< 0 (fn2-host-outbox-queued fn2-core))) fn2-core
    (mv-let (entry fn2-core) (fn2-env-step '(:turn) nil nil nil fn2-core)
      (declare (ignore entry))
      (fn2-sbu-turn-to-outbox (- fuel 1) fn2-core))))

; (stop queued-before take-entry queued-after pick-before pick-after), STOPP
; stopping the core (fn2-core-stop, the executor's own record) before the offers.
(defun fn2-sbu-execute (stopp fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((fn2-core (fn2-init-executor *fn2-sbu-profile* :echo nil fn2-core))
       ((mv & & fn2-core) (fn2-env-steps '((:epoch 1) (:admit 2 0))
                                         (fn2-env-commit-ids *fn2-sbu-profile*) nil nil fn2-core))
       (fn2-core (fn2-sbu-turn-to-outbox 64 fn2-core))
       (fn2-core (if stopp (fn2-core-stop *fn2-stop-reason-machine-phase* fn2-core) fn2-core))
       (queued (fn2-host-outbox-queued fn2-core))
       ((mv pick & &) (fn2-commit-pick fn2-core))
       ((mv entry fn2-core) (fn2-env-step '(:take) nil nil nil fn2-core))
       (queued-after (fn2-host-outbox-queued fn2-core))
       ((mv & fn2-core) (fn2-env-step '(:admit 2 0) nil nil nil fn2-core))
       ((mv pick-after & &) (fn2-commit-pick fn2-core)))
    (mv (list (fn2-exec-stop fn2-core) queued (and entry (car entry)) queued-after pick pick-after)
        fn2-core)))
(defun fn2-sbu-case (stopp)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (result fn2-core) (fn2-sbu-execute stopp fn2-core) result)))
(make-event `(defconst *fn2-sbu-stopped* ',(fn2-sbu-case t)))
(make-event `(defconst *fn2-sbu-running* ',(fn2-sbu-case nil)))

;; Positive: the stopped core (stop bit 1) holds a queued action and a free
;; commit row (pick :open), and refuses both: the take logs no entry and the
;; outbox keeps its action; the admission opens no row (pick still :open).
(defun fn2-stop-boundary-positive ()
  (declare (xargs :verify-guards nil))
  (let ((r *fn2-sbu-stopped*))
    (and (equal (nth 0 r) 1) (posp (nth 1 r))
         (null (nth 2 r)) (equal (nth 3 r) (nth 1 r))
         (eq (nth 4 r) :open) (eq (nth 5 r) :open))))
;; Stop removed: the same core, not stopped, takes the action (a :take entry,
;; the outbox one shorter) and admits the batch (the second row taken:
;; :exhausted). Without the hypothesis the statement is false.
(defun fn2-stop-boundary-stop-removal ()
  (declare (xargs :verify-guards nil))
  (let ((r *fn2-sbu-running*))
    (and (equal (nth 0 r) 0) (posp (nth 1 r))
         (eq (nth 2 r) :take) (equal (nth 3 r) (- (nth 1 r) 1))
         (eq (nth 4 r) :open) (eq (nth 5 r) :exhausted))))
(assert-event (fn2-stop-boundary-positive))
(assert-event (fn2-stop-boundary-stop-removal))

;; Durability rows and FN2-ENV-INV across a post-stop suffix:
;; Positive (stopped): FN2-ENV-ROWS and FN2-ENV-INV stay intact across take,
;; admit, turn, clock and epoch steps; no new batch is acknowledged.
;; Stop removed (running): the same suffix mutates FN2-ENV-ROWS (admitting the
;; second batch).
(defun fn2-sbu-inv-execute (stopp fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((ids (fn2-env-commit-ids *fn2-sbu-profile*))
       (fn2-core (fn2-init-executor *fn2-sbu-profile* :echo nil fn2-core))
       ((mv rlog acked fn2-core)
        (fn2-env-steps '((:epoch 1) (:admit 2 0)) ids nil nil fn2-core))
       (fn2-core (if stopp (fn2-core-stop *fn2-stop-reason-machine-phase* fn2-core) fn2-core))
       (rows-before (fn2-env-rows ids fn2-core))
       (inv-before (fn2-env-inv ids acked (reverse rlog) fn2-core))
       ((mv rlog2 acked2 fn2-core)
        (fn2-env-steps '((:take) (:admit 2 0) (:turn) (:clock 10 10 0) (:epoch 2))
                       ids rlog acked fn2-core))
       (rows-after (fn2-env-rows ids fn2-core))
       (inv-after (fn2-env-inv ids acked2 (reverse rlog2) fn2-core)))
    (mv (list (fn2-exec-stop fn2-core) inv-before inv-after
              (equal rows-after rows-before) acked2)
        fn2-core)))
(defun fn2-sbu-inv-case (stopp)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (result fn2-core) (fn2-sbu-inv-execute stopp fn2-core) result)))
(make-event `(defconst *fn2-sbu-inv-stopped* ',(fn2-sbu-inv-case t)))
(make-event `(defconst *fn2-sbu-inv-running* ',(fn2-sbu-inv-case nil)))

(defun fn2-stop-boundary-inv-positive ()
  (declare (xargs :verify-guards nil))
  (let ((s *fn2-sbu-inv-stopped*))
    (and (equal (nth 0 s) 1) (nth 1 s) (nth 2 s) (nth 3 s) (null (nth 4 s)))))
(defun fn2-stop-boundary-inv-stop-removal ()
  (declare (xargs :verify-guards nil))
  (let ((r *fn2-sbu-inv-running*))
    (and (equal (nth 0 r) 0) (not (nth 3 r)))))
(assert-event (fn2-stop-boundary-inv-positive))
(assert-event (fn2-stop-boundary-inv-stop-removal))
