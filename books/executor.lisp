; Concrete dispatcher over the intrusive scheduler. No fusion.
(in-package "ACL2")
(include-book "executor-wake")
(include-book "executor-services")
(include-book "assembly")
(include-book "executor-reservation")
(include-book "executor-loop-events")

(fn2-executor-loop-events)

;; Genesis (MACHINE-FORM G3, C gap 5): each kind's :genesis arm runs once on
;; each of its rows at init, from the row's initial phase, so a row's first
;; writes and moves are an arm's; a runnable answer wakes the row. No turn is
;; running: the arm's charge is its bound, checked against the kind's caps at
;; defmachine-run, and nothing is charged. A directory row whose kind does not
;; read stops the core.
(defun fn2-exec-genesis-clauses (names code world)
  (declare (xargs :verify-guards nil))
  (if (atom names) nil
    (let ((gen (fn2-machine-property (car names) :genesis-arm world))
          (budget (fn2-machine-property (car names) :budget world)))
      (append (and gen
                   `((,code (mv-let (bytes steps descriptors runnable fn2-core)
                              (,(cadr (car gen)) id ,(nfix (fn2-arm-get :bytes budget)) fn2-core)
                              (declare (ignore bytes steps descriptors))
                              (if runnable (fn2-exec-wake id fn2-core) fn2-core)))))
              (fn2-exec-genesis-clauses (cdr names) (+ 1 code) world)))))
(make-event
 `(defun fn2-exec-genesis-row (id fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (if (not (eq (fn2-machine-kind-read-code id fn2-core) :ok))
        (fn2-core-stop *fn2-stop-reason-machine-phase* fn2-core)
      (if (and (equal (fn2-machine-kind id fn2-core) *fn2-listener-kind*)
               (eq (fn2-boot-snapshot-read-code (fn2-machine-kind-base *fn2-boot-kind* fn2-core) fn2-core) :ok))
          fn2-core
       (case (fn2-machine-kind id fn2-core)
        ,@(fn2-exec-genesis-clauses (fn2-machine-names (w state)) 0 (w state))
        (otherwise fn2-core))))))
(fn2-core-preserves fn2-exec-genesis-row (id fn2-core) :rows nil :prefix "")
(defun fn2-exec-genesis (left id fn2-core)
  (declare (xargs :stobjs fn2-core :measure (nfix left)
                  :guard (and (fn2-core-wfp fn2-core) (natp left) (natp id))))
  (if (zp left) fn2-core
    (let ((fn2-core (fn2-exec-genesis-row id fn2-core)))
      (fn2-exec-genesis (- left 1) (+ 1 (nfix id)) fn2-core))))
(fn2-core-preserves fn2-exec-genesis (left id fn2-core) :rows nil :prefix "")
(defun fn2-exec-rows (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-machines (fn2-core-machines fn2-core))) (n) (fn2-machines-rows fn2-machines) n))

; Bookings the listeners hold (D7's S1): a listener with an Accept outstanding
; holds one :connection-row booking on its principal for the connection it is
; waiting for, so at quiescence a principal's hold is its live connections plus
; these (D 13.5). Read by D's checkers; the executor never calls it.
(defun fn2-listener-bookings-from (left id p fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix left)))
  (if (zp left) 0
    (+ (if (and (eq (fn2-machine-account-ref-read-code id fn2-core) :ok)
                (equal (fn2-machine-account-ref id fn2-core) p)) 1 0)
       (fn2-listener-bookings-from (- left 1) (+ 1 (nfix id)) p fn2-core))))
(defun fn2-listener-bookings (p fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (fn2-listener-bookings-from (fn2-machine-accept-count fn2-core)
                              (fn2-machine-kind-base *fn2-listener-kind* fn2-core) p fn2-core))

;; Layer C's genesis (the profile's group directory, S-GROUP; the sealer's
;; seal row, C1c) right after the core init; a refusal stops the core before
;; anything runs.
(defun fn2-init-engine (profile fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (mv-let (genesis fn2-core) (fn2-engine-genesis profile fn2-core)
    (if (eq genesis :ok) fn2-core (fn2-core-stop *fn2-stop-reason-engine-genesis* fn2-core))))
(defthm fn2-init-engine-type
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)) (fn2-corep (fn2-init-engine profile fn2-core))))
(defthm fn2-init-engine-wfp
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)) (fn2-core-wfp (fn2-init-engine profile fn2-core))))
(in-theory (disable fn2-init-engine))

; The kind a listener admits a :local peer into (D 4.5): the profile's
; :listener-local-target when it names one, else its :listener-targets.
(defun fn2-listener-local-target-name (profile)
  (declare (xargs :guard t))
  (if (and (alistp profile) (assoc-equal :listener-local-target profile))
      (fn2-profile-get :listener-local-target profile)
    (fn2-profile-get :listener-targets profile)))

(defun fn2-init-executor (profile mode scribe-p fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-profilep profile)
    :guard-hints (("Goal" :use
      (:instance fn2-machine-kind-base-natp (kind *fn2-listener-kind*)
        (fn2-core (fn2-listener-set-mode-all (if (eq mode :null) 0 1)
                    (fn2-init-engine profile (fn2-core-init profile fn2-core)))))))))
  (b* ((fn2-core (fn2-core-init profile fn2-core))
       (fn2-core (fn2-init-engine profile fn2-core))
       (fn2-core (fn2-listener-set-mode-all (if (eq mode :null) 0 1) fn2-core))
       (fn2-core (fn2-listener-set-target-all
                  (fn2-machine-admission-ordinal-of (fn2-profile-get :listener-targets profile))
                  (fn2-machine-admission-ordinal-of (fn2-listener-local-target-name profile))
                  fn2-core))
       (fn2-core (fn2-listener-set-principals (fn2-profile-get :listener-principals profile) fn2-core))
       (fn2-core (fn2-exec-genesis (fn2-exec-rows fn2-core) 0 fn2-core))
       (fn2-core (if scribe-p (fn2-scribe-start fn2-core) fn2-core))
       ((mv wake fn2-core) (fn2-machine-take-wake fn2-core)))
    (fn2-exec-wake wake fn2-core)))

; The supplied genesis configuration is staged only in volatile C rows.
; On an image boot it cannot serve until the boot machine has matched every
; persisted genesis unit, recovered/replayed the journal and fenced its epoch.
(defun fn2-image-profile (profile)
 (declare (xargs :guard t))
 (put-assoc-equal :image-boot t (if (alistp profile) profile nil)))

(defun fn2-image-sizep (size extents groups)
 (declare (xargs :guard t))
 (and (unsigned-byte-p 60 size) (equal (mod size 4096) 0)
      (unsigned-byte-p 32 extents) (posp extents) (unsigned-byte-p 32 groups)
      (<= (+ (* 12288 extents) (* 4096 (+ groups 3))) size)))

(defun fn2-image-create-request (size profile)
 (declare (xargs :guard t))
 (if (fn2-image-sizep size (fn2-b-capacity :extent-slots 16 profile)
                      (len (fn2-profile-get :groups profile))) :ok :geometry))

(defun fn2-boot-start (create size fn2-core)
 (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
 (b* ((id (fn2-machine-kind-base *fn2-boot-kind* fn2-core))
      ((unless (and (eq (fn2-boot-snapshot-read-code id fn2-core) :ok)
                    (equal (fn2-machine-phase id fn2-core) *fn2-boot-state-free*)
                    (unsigned-byte-p 60 size) (equal (mod size 4096) 0)))
       (mv :geometry fn2-core))
      ((mv base total) (stobj-let ((fn2-boot-config (fn2-core-boot-config fn2-core))) (base total)
                        (mv (* 12288 (nfix (fn2-boot-config-extents fn2-boot-config)))
                            (fn2-boot-config-count fn2-boot-config)) (mv base total)))
      ((unless (fn2-image-sizep size (/ base 12288) total)) (mv :geometry fn2-core))
      (gen (fn2-machine-generation id fn2-core))
      (class (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (class) (fn2-pool-class-for 4096 fn2-pool) class))
      ((unless class) (mv :window fn2-core))
      ((mv code slot sgen fn2-core) (fn2-core-reserve class *fn2-boot-kind* id gen fn2-core))
      ((unless (and (eq code :ok) (unsigned-byte-p 32 slot) (unsigned-byte-p 60 sgen))) (mv :window fn2-core))
      ((mv code rx rgen fn2-core) (fn2-core-reserve class *fn2-boot-kind* id gen fn2-core))
      ((unless (and (eq code :ok) (unsigned-byte-p 32 rx) (unsigned-byte-p 60 rgen))) (mv :window fn2-core))
      (fn2-core (fn2-boot-put-core id (phase *fn2-boot-state-prepare*)
                  (pool-slot slot) (pool-gen sgen) (rx-slot rx) (rx-gen rgen)
                  (create (if create 1 0)) (image-size size) (base base) (total total)
                  (index 0) (stage 0) (epoch0 0) (epoch1 0) (principal-slot 0)))
      ((mv code fn2-core) (fn2-recovery-ready id fn2-core)))
  (mv (if (member-eq code '(:ok :already)) :ok :bounds) fn2-core)))
(fn2-core-preserves fn2-boot-start (create size fn2-core) :position 1 :rows nil)

(defun fn2-boot-status (fn2-core)
 (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
 (let ((id (fn2-machine-kind-base *fn2-boot-kind* fn2-core)))
  (cond ((not (eq (fn2-boot-snapshot-read-code id fn2-core) :ok)) :disabled)
        ((not (equal (fn2-core-stop-reason fn2-core) 0)) :failed)
        ((equal (fn2-machine-phase id fn2-core) *fn2-boot-state-ready*) :ready)
        (t :booting))))

(assert-event
 (fn2-assert-compliant-p
  '(fn2-image-profile fn2-image-sizep fn2-image-create-request fn2-boot-start fn2-boot-status)
  (w state)))

(defthm-owed fn2-turn-bounds (core)
  (implies (and (fn2-corep core) (fn2-core-wfp core))
    (mv-let (status nobs nvisits nactions after) (fn2-turn core)
      (declare (ignore status after))
      (and (<= nobs (fn2-exec-h core)) (<= nvisits (fn2-exec-k core))
           (<= nactions (fn2-exec-aturn core)))))
  :schema :bound :from (:operation fn2-turn)
  :teeth (fn2-executor-bounds-teeth fn2-executor-bounds-negative)
  :doc "Owed simultaneous observation, calendar-visit and descriptor bounds over fn2-turn.")

; The turn bound as composition (HIGHER-STRUCTURES entry 9): a word of
; machine runs, each charged within its arm's certificate, costs at most the
; sum of the arms' declared bounds; T3's bound is this lemma's instance with
; at most K runs. Its partner is the residual budget: a run handed the turn's
; remaining descriptor budget never spends more than it (Lawvere's
; spent + c <= A iff c <= A - spent, with truncated subtraction covering
; exhaustion: an exhausted budget admits only zero-descriptor runs).
; A word element is (kind phase bytes steps descriptors).
(defun fn2-arm-word-certified-p (word)
  (declare (xargs :verify-guards nil))
  (if (atom word) t
    (and (true-listp (car word)) (equal (len (car word)) 5)
         (fn2-machine-arm-charge-ok-p (nth 0 (car word)) (nth 1 (car word))
                                      (nth 2 (car word)) (nth 3 (car word)) (nth 4 (car word)))
         (fn2-arm-word-certified-p (cdr word)))))
(defun fn2-arm-word-charge (word)
  (declare (xargs :verify-guards nil))
  (if (atom word) 0
    (+ (nfix (and (consp (car word)) (nth 2 (car word))))
       (nfix (and (consp (car word)) (nth 3 (car word))))
       (fn2-arm-word-charge (cdr word)))))
(defun fn2-arm-word-bound (word)
  (declare (xargs :verify-guards nil))
  (if (atom word) 0
    (+ (nfix (and (consp (car word)) (fn2-machine-arm-bound (nth 0 (car word)) (nth 1 (car word)))))
       (fn2-arm-word-bound (cdr word)))))
(defthm-owed fn2-arm-cost-composition (word)
  (implies (fn2-arm-word-certified-p word)
           (<= (fn2-arm-word-charge word) (fn2-arm-word-bound word)))
  :schema :bound :from (:operation fn2-turn)
  :teeth (fn2-arm-composition-positive fn2-arm-composition-negative)
  :doc "Runs charged within their arm certificates compose: the word's bytes and steps are at most the sum of its arms' declared bounds.")
(defthm-owed fn2-arm-residual-budget (id budget core)
  (implies (and (fn2-corep core) (fn2-core-wfp core) (natp budget))
           (<= (mv-nth 2 (fn2-machine-run id budget core)) budget))
  :schema :bound :from (:operation fn2-turn)
  :teeth (fn2-arm-residual-positive fn2-arm-residual-negative)
  :doc "A machine run handed the turn's residual descriptor budget spends at most that budget; an exhausted budget admits no descriptor.")

(assert-event
 (fn2-assert-compliant-p
  '(fn2-transition fn2-concrete-loop fn2-concrete-turn fn2-turn fn2-init-executor
    fn2-core-idle-deadline fn2-exec-harvest fn2-exec-mailbox fn2-exec-principal
    fn2-exec-service fn2-exec-account-work) (w state)))

; The executor's case source (DSL-METATHEORY 3.2): the executor is not a
; machine; it contributes seven labels with named selectors over the core in
; which fn2-transition runs with observations allowed. Selectors are
; proof-facing (non-executable); that they partition the non-machine
; transitions under the loop invariant is owed by the correspondence.
(defun-nx fn2-exec-select-clock (fn2-core)
  (and (fn2-exec-observation-p fn2-core) (not (fn2-core-posted-p fn2-core))
       (equal (fn2-ops-clock-posted (fn2-core-ops fn2-core)) 1)))
(defun-nx fn2-exec-select-signal (fn2-core)
  (and (fn2-exec-observation-p fn2-core) (not (fn2-core-posted-p fn2-core))
       (not (equal (fn2-ops-clock-posted (fn2-core-ops fn2-core)) 1))))
(defun-nx fn2-exec-select-visit (kind fn2-core)
  (and (not (fn2-exec-observation-p fn2-core)) (fn2-exec-eligible-p fn2-core)
       (mv-let (visit principal position core) (fn2-exec-visit fn2-core)
         (declare (ignore position))
         (and (equal visit kind)
              (or (not (equal kind *fn2-visit-principal*))
                  (mv-let (code id core) (fn2-exec-pop principal core)
                    (declare (ignore id core)) (not (eq code :ok))))))))
(defun-nx fn2-exec-select-service-0 (fn2-core) (fn2-exec-select-visit *fn2-visit-commit* fn2-core))
(defun-nx fn2-exec-select-service-1 (fn2-core) (fn2-exec-select-visit *fn2-visit-timer* fn2-core))
(defun-nx fn2-exec-select-service-2 (fn2-core) (fn2-exec-select-visit *fn2-visit-notification* fn2-core))
(defun-nx fn2-exec-select-service-3 (fn2-core) (fn2-exec-select-visit *fn2-visit-maintenance* fn2-core))
(defun-nx fn2-exec-select-empty-principal (fn2-core)
  (fn2-exec-select-visit *fn2-visit-principal* fn2-core))
(make-event
 (value (fn2-declare '(:operation-set fn2-executor-cases)
          '(:cases ((:executor :clock) (:executor :signal)
                    (:executor :service 0) (:executor :service 1)
                    (:executor :service 2) (:executor :service 3)
                    (:executor :empty-principal))
            :selectors (((:executor :clock) fn2-exec-select-clock)
                        ((:executor :signal) fn2-exec-select-signal)
                        ((:executor :service 0) fn2-exec-select-service-0)
                        ((:executor :service 1) fn2-exec-select-service-1)
                        ((:executor :service 2) fn2-exec-select-service-2)
                        ((:executor :service 3) fn2-exec-select-service-3)
                        ((:executor :empty-principal) fn2-exec-select-empty-principal))
            :doc "Clock, signal, four service visits and the empty principal visit.")
          nil nil)))
