; Q1's per-case teeth (DSL-METATHEORY 3.4, DM3 2/n). For every label of the
; assembled case catalogue, a certified fixture: a tiny-profile core in which
; fn2-q1-label names exactly that case, the reference copied from it, and the
; reference lists read from its scheduler. POSITIVE: one lockstep transition
; (fn2-trace-lockstep, fuel 1: both loops step once under their own named
; stop conditions) labels the case and passes G1 (the five results agree, the
; representation relation holds after it). NEGATIVE: the same successor with
; one reference field the transition does not touch (another kind's row
; generation) perturbed is refused by the relation the square concludes, and
; restoring it makes the relation hold again. The fixtures are built from
; the catalogue, so a label added by a new kind gets its teeth here or fails
; to certify. A fixture is a state the labeller classifies, not necessarily
; one a scenario reaches; reachable cases are exercised by the A4 hook.
(in-package "ACL2")
(include-book "../sim/check-trace")

(defconst *fn2-q1-teeth-profile*
  (put-assoc-equal :pool-classes '((8 . 4096) (4 . 65536)) *fn2-profile-tiny*))

(defun fn2-q1-teeth-position (x xs)
  (declare (xargs :guard t))
  (cond ((atom xs) nil)
        ((equal x (car xs)) 0)
        (t (let ((n (fn2-q1-teeth-position x (cdr xs)))) (and n (+ 1 n))))))
(defun fn2-q1-teeth-kind (name)
  (declare (xargs :verify-guards nil))
  (fn2-q1-teeth-position name (strip-cars *fn2-q1-phases*)))
(defun fn2-q1-teeth-phase (name phase)
  (declare (xargs :verify-guards nil))
  (fn2-q1-teeth-position phase (cdr (assoc-eq name *fn2-q1-phases*))))
; The first action whose terminal event is EVENT (cell 0); borrow release is cell 1 of a Send.
(defun fn2-q1-teeth-action (event left)
  (declare (xargs :verify-guards nil :measure (nfix left)))
  (if (zp left) nil
    (let ((a (- *fn2-action-count* left)))
      (if (equal (fn2-terminal-event a) event) a (fn2-q1-teeth-action event (- left 1))))))
(defun fn2-q1-teeth-accepting-phase (kind event left)
  (declare (xargs :verify-guards nil :measure (nfix left)))
  (if (zp left) nil
    (let ((p (- left 1)))
      (if (fn2-machine-observe-accepts-p kind p event) p
        (fn2-q1-teeth-accepting-phase kind event (- left 1))))))

(defun fn2-q1-teeth-drain (left fn2-core)
  ; Empty every principal FIFO and clear the service flags: the fixture
  ; starts from a scheduler with nothing runnable.
  (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix left)))
  (if (zp left) fn2-core
    (let ((fn2-core
           (stobj-let ((fn2-sched (fn2-core-sched fn2-core))) (fn2-sched)
             (mv-let (code id fn2-sched) (fn2-sched-pop-head (mod (- left 1) (max 1 (fn2-sched-nprincipals fn2-sched))) fn2-sched)
               (declare (ignore code id)) fn2-sched)
             fn2-core)))
      (fn2-q1-teeth-drain (- left 1) fn2-core))))
(defun fn2-q1-teeth-sched (cursor service fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-sched (fn2-core-sched fn2-core))) (fn2-sched)
    (let* ((fn2-sched (update-fn2-sched-servicesi 0 0 fn2-sched))
           (fn2-sched (update-fn2-sched-servicesi 1 0 fn2-sched))
           (fn2-sched (update-fn2-sched-servicesi 2 0 fn2-sched))
           (fn2-sched (update-fn2-sched-servicesi 3 0 fn2-sched))
           (fn2-sched (if service (update-fn2-sched-servicesi service 1 fn2-sched) fn2-sched)))
      (update-fn2-sched-cursor cursor fn2-sched))
    fn2-core))
; Post a terminal (cell 0) or borrow-release (cell 1) result for EVENT on op
; slot 0, owned by machine ID (generation GEN), as a submitted operation.
(defun fn2-q1-teeth-post (id kind gen event fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (let* ((borrow (equal event *fn2-event-borrow-released*))
         (action (if borrow *fn2-action-send* (fn2-q1-teeth-action event *fn2-action-count*))))
    (stobj-let ((fn2-ops (fn2-core-ops fn2-core))) (fn2-ops)
      (let* ((opgen (fn2-ops-gen 0 fn2-ops))
             (fn2-ops (fn2-ops-put 0 (phase *fn2-op-phase-submitted*) (kind action)
                                   (owner-kind kind) (owner-slot id) (owner-gen gen) (principal 0)
                                   (may-release (if borrow 1 0)) (range-len 0))))
        (fn2-post-result (if borrow 1 0) 0 opgen event *fn2-outcome-done* *fn2-reason-none* 0 0 0 fn2-ops))
      fn2-core)))

; Build the fixture for LABEL: (mv lists fn2-core fn2-ref-core).
(defun fn2-q1-teeth-fixture (label fn2-core fn2-ref-core)
  (declare (xargs :stobjs (fn2-core fn2-ref-core) :verify-guards nil))
  (b* ((profile *fn2-q1-teeth-profile*)
       (fn2-core (fn2-init-executor profile :echo t fn2-core))
       (fn2-core (fn2-q1-teeth-drain (* 4 (fn2-machine-index-count profile)) fn2-core))
       (p (fn2-profile-p profile))
       (tag (car label))
       (name (if (member-eq tag '(:run :observe)) (cadr label) nil))
       (kind (if name (fn2-q1-teeth-kind name) 0))
       (id (if name (fn2-machine-global-id kind 0 profile) 0))
       (gen (fn2-machine-generation id fn2-core))
       (event (and (eq tag :observe) (fn2-event-keyword->code (caddr label))))
       (fn2-core
        (case tag
          (:run (let ((fn2-core (fn2-machine-write-phase id (fn2-q1-teeth-phase name (caddr label)) fn2-core)))
                  (fn2-exec-wake id fn2-core)))
          (:observe
           (let ((fn2-core (fn2-machine-write-phase
                            id (fn2-q1-teeth-accepting-phase kind event (len (cdr (nth kind *fn2-q1-phases*))))
                            fn2-core)))
             (fn2-q1-teeth-post id kind gen event fn2-core)))
          (:router (fn2-q1-teeth-post 0 0 (+ 1 (fn2-machine-generation 0 fn2-core))
                                      *fn2-event-accept-result* fn2-core))
          (otherwise
           (if (equal label '(:executor :clock))
               (stobj-let ((fn2-ops (fn2-core-ops fn2-core))) (fn2-ops) (fn2-post-clock 5 5 1 fn2-ops) fn2-core)
             (if (equal label '(:executor :signal))
                 (stobj-let ((fn2-ops (fn2-core-ops fn2-core))) (fn2-ops) (fn2-post-signal 1 fn2-ops) fn2-core)
               fn2-core)))))
       ; Executor labels select from the calendar: a service by its entry
       ; (positions P..P+3 of the tiny calendar), an empty principal by
       ; principal 0's entry while a service makes the core eligible.
       (service (cond ((equal (take 2 label) '(:executor :service)) (caddr label))
                      ((equal label '(:executor :empty-principal)) 0)
                      (t nil)))
       (cursor (if (and service (not (equal label '(:executor :empty-principal)))) (+ p service) 0))
       (fn2-core (fn2-q1-teeth-sched cursor service fn2-core))
       (fn2-ref-core (fn2-ref-reset profile fn2-core fn2-ref-core))
       (fn2-ref-core (fn2-ref-import-boundary fn2-core fn2-ref-core))
       (flags (stobj-let ((fn2-sched (fn2-core-sched fn2-core))) (flags)
                (list (fn2-sched-servicesi 0 fn2-sched) (fn2-sched-servicesi 1 fn2-sched)
                      (fn2-sched-servicesi 2 fn2-sched) (fn2-sched-servicesi 3 fn2-sched))
                flags))
       (lists (list (fn2-ref-calendar (fn2-profile-weights profile)) cursor
                    (nth 2 (fn2-ref-lists-of-core (fn2-profile-weights profile) fn2-core)) flags nil)))
    (mv lists fn2-core fn2-ref-core)))

; One transition in lockstep from the fixture: (mv label failure cases difference-after-perturbation
; difference-after-restoring).
(defun fn2-q1-teeth-run (label fn2-core fn2-ref-core)
  (declare (xargs :stobjs (fn2-core fn2-ref-core) :verify-guards nil))
  (b* (((mv lists fn2-core fn2-ref-core) (fn2-q1-teeth-fixture label fn2-core fn2-ref-core))
       (named (fn2-q1-label lists fn2-core))
       (h (fn2-exec-h fn2-core)) (k (fn2-exec-k fn2-core)) (a (fn2-exec-aturn fn2-core))
       (fn2-core (fn2-exec-set-turn-bytes 0 fn2-core))
       (fn2-core (fn2-exec-set-turn-steps 0 fn2-core))
       (fn2-ref-core (fn2-exec-set-turn-bytes 0 fn2-ref-core))
       (fn2-ref-core (fn2-exec-set-turn-steps 0 fn2-ref-core))
       ((mv failure cases & & & & & & & lists fn2-core fn2-ref-core)
        (fn2-trace-lockstep 1 h k a 0 0 0 h k a 0 0 0 lists nil nil fn2-core fn2-ref-core))
       ; Perturb a row the transition does not touch: the scribe's, or the
       ; first listener's when the case is the scribe's own.
       (other (if (and (consp (cdr label)) (eq (cadr label) 'fn2-scribe))
                  (fn2-machine-global-id (fn2-q1-teeth-kind 'fn2-listener) 0 *fn2-q1-teeth-profile*)
                (fn2-machine-global-id (fn2-q1-teeth-kind 'fn2-scribe) 0 *fn2-q1-teeth-profile*)))
       (old (fn2-machine-generation other fn2-ref-core))
       (fn2-ref-core (fn2-machine-write-generation other (+ 1 old) fn2-ref-core))
       (perturbed (fn2-ref-difference fn2-core fn2-ref-core lists))
       (fn2-ref-core (fn2-machine-write-generation other old fn2-ref-core))
       (restored (fn2-ref-difference fn2-core fn2-ref-core lists)))
    (mv (list named failure cases perturbed restored) fn2-core fn2-ref-core)))
(defun fn2-q1-teeth (label)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (answer fn2-core)
      (with-local-stobj fn2-ref-core
        (mv-let (answer fn2-core fn2-ref-core) (fn2-q1-teeth-run label fn2-core fn2-ref-core)
          (mv answer fn2-core)))
      answer)))
(defun fn2-q1-teeth-positive (label)
  (declare (xargs :verify-guards nil))
  (let ((r (fn2-q1-teeth label)))
    (and (equal (nth 0 r) label) (null (nth 1 r)) (equal (nth 2 r) (list (cons label 1))))))
(defun fn2-q1-teeth-negative (label)
  (declare (xargs :verify-guards nil))
  (let ((r (fn2-q1-teeth label)))
    (and (equal (nth 0 r) label) (consp (nth 3 r)) (null (nth 4 r)))))

(defun fn2-q1-teeth-events (cases index)
  (declare (xargs :verify-guards nil))
  (if (atom cases) nil
    (let ((id (fn2-q1-id index)))
      (list* `(defun ,(fn2-columns-sym id "-POSITIVE") ()
                (declare (xargs :verify-guards nil))
                (fn2-q1-teeth-positive ',(car cases)))
             `(defun ,(fn2-columns-sym id "-NEGATIVE") ()
                (declare (xargs :verify-guards nil))
                (fn2-q1-teeth-negative ',(car cases)))
             (fn2-q1-teeth-events (cdr cases) (+ 1 index))))))
(make-event (value (cons 'progn (fn2-q1-teeth-events *fn2-q1-catalogue* 0))))
(defun fn2-q1-teeth-names (n)
  (declare (xargs :verify-guards nil))
  (if (zp n) nil (append (fn2-q1-teeth-names (- n 1)) (list (fn2-q1-id (- n 1))))))
(make-event (value `(fn2-assert-owed-teeth ,@(fn2-q1-teeth-names (len *fn2-q1-catalogue*)))))
