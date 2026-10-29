; Concrete dispatcher over the intrusive scheduler. No fusion.
(in-package "ACL2")
(include-book "executor-wake")
(include-book "assembly")

(defun fn2-exec-eligible-p (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (or (fn2-exec-runnable-p fn2-core) (fn2-exec-wake-p fn2-core)))

(defun fn2-turn-status (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (cond ((= 1 (fn2-exec-stop fn2-core)) :stop)
        ((or (fn2-exec-observation-p fn2-core) (fn2-exec-eligible-p fn2-core)) :more)
        (t :idle)))

(defun fn2-exec-harvest (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (b* (((mv & kind id gen principal) (fn2-core-next-owner fn2-core))
       (start (fn2-exec-queued fn2-core))
       ((mv delivered & & & event outcome reason count aux0 aux1 fn2-core)
        (fn2-harvest-one fn2-core))
       ((unless delivered) (mv 1 0 0 0 24 fn2-core))
       ((mv wake fn2-core)
        (fn2-machine-observe kind id gen event outcome reason count aux0 aux1 fn2-core))
       (fn2-core (fn2-exec-wake wake fn2-core))
       (fn2-core (fn2-exec-record 0 wake principal 0 0 24 0 nil 4294967295 start fn2-core)))
    (mv 1 0 0 0 24 fn2-core)))
(fn2-core-shape-lemmas fn2-exec-harvest () 5)

(defun fn2-exec-mailbox (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)
                  :guard-hints (("Goal" :in-theory (enable fn2-core-wfp)))))
  (b* ((clockp (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
                (yes) (= 1 (fn2-ops-clock-posted fn2-ops)) yes))
       (start (fn2-exec-queued fn2-core))
       (fn2-core
        (if clockp
            (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
              (posted mono real flags fn2-ops) (fn2-take-clock fn2-ops)
              (let ((unused-posted posted) (unused-real real) (unused-flags flags))
                (declare (ignore unused-posted unused-real unused-flags))
                (fn2-exec-clock mono fn2-core)))
          (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
            (bits fn2-ops) (fn2-take-signal fn2-ops)
            (if (< 0 (nfix bits)) (fn2-core-stop *fn2-stop-reason-signal* fn2-core) fn2-core))))
       (fn2-core (fn2-exec-record (if clockp 3 4) 4294967295 0 0 0 8 0
                                 nil 4294967295 start fn2-core)))
    (mv 1 0 0 0 8 fn2-core)))
(fn2-exec-direct-shape fn2-exec-mailbox () 5)

(defun fn2-exec-principal (principal position budget fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (b* ((start (fn2-exec-queued fn2-core))
       ((mv code id fn2-core) (fn2-exec-pop principal fn2-core))
       ((unless (eq code :ok))
        (let ((fn2-core (fn2-exec-record 1 4294967295 principal position
                          0 1 0 nil 4294967295 start fn2-core)))
          (mv 0 1 0 0 1 fn2-core)))
       ((mv bytes steps actions runnable fn2-core) (fn2-machine-run id budget fn2-core))
       ((mv wake fn2-core) (fn2-machine-take-wake fn2-core))
       ; New work enters before the running machine's tail requeue. The
       ; trace checker reconstructs this order without consulting links.
       (fn2-core (fn2-exec-wake wake fn2-core))
       (fn2-core (if runnable (fn2-exec-wake id fn2-core) fn2-core))
       (fn2-core (fn2-exec-record 1 id principal position bytes steps actions
                                 runnable wake start fn2-core)))
    (mv 0 1 actions bytes steps fn2-core)))
(fn2-core-shape-lemmas fn2-exec-principal (principal position budget) 5)

(defun fn2-exec-service (service position budget fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (b* ((start (fn2-exec-queued fn2-core))
       (fn2-core (fn2-exec-clear-service service fn2-core))
       ((mv wake fn2-core)
        (if (and (equal service 1) (fn2-exec-grant-p fn2-core))
            (fn2-machine-grant-one fn2-core) (mv 4294967295 fn2-core)))
       ((mv actions fn2-core)
        (if (and (equal service 1) (natp budget) (< 0 budget))
            (fn2-exec-arm fn2-core) (mv 0 fn2-core)))
       (fn2-core (fn2-exec-wake wake fn2-core))
       (fn2-core (fn2-exec-record 2 4294967295 service position 0
                    (if (and (equal wake 4294967295) (equal actions 0)) 1 24) actions nil wake start fn2-core)))
    (mv 0 1 actions 0 (if (and (equal wake 4294967295) (equal actions 0)) 1 24) fn2-core)))
(fn2-core-shape-lemmas fn2-exec-service (service position budget) 5)

; Observation order is the posted FIFO, then the coalesced clock mailbox,
; then sticky signals. Each turn stops at the first exhausted budget.
; Every empty calendar entry still consumes one visit.
(defun fn2-transition (allow-observation action-budget fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (cond
   ((and allow-observation (fn2-exec-observation-p fn2-core))
    (if (fn2-core-posted-p fn2-core)
        (fn2-exec-harvest fn2-core) (fn2-exec-mailbox fn2-core)))
   ((fn2-exec-eligible-p fn2-core)
    (mv-let (kind principal position fn2-core) (fn2-exec-visit fn2-core)
      (if (equal kind 0)
          (fn2-exec-principal principal position action-budget fn2-core)
        (fn2-exec-service (nfix (- (nfix kind) 1)) position action-budget fn2-core))))
   (t (mv 0 0 0 0 0 fn2-core))))
(fn2-core-shape-lemmas fn2-transition (allow-observation action-budget) 5)

(defun fn2-exec-account-work (bytes steps fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (let ((b (+ (nfix bytes) (fn2-exec-turn-bytes fn2-core)))
        (s (+ (nfix steps) (fn2-exec-turn-steps fn2-core))))
    (if (and (unsigned-byte-p 60 b) (unsigned-byte-p 60 s))
        (let* ((fn2-core (fn2-exec-set-turn-bytes b fn2-core))
               (fn2-core (fn2-exec-set-turn-steps s fn2-core))) fn2-core)
      (fn2-core-stop *fn2-stop-reason-work-overflow* fn2-core))))
(fn2-machine-core-shape fn2-exec-account-work (bytes steps))

(in-theory (disable fn2-turn-status fn2-exec-eligible-p
                    fn2-exec-observation-p fn2-exec-runnable-p))

(defun fn2-concrete-loop (fuel h k a nobs nvisits nactions fn2-core)
  (declare (xargs :stobjs fn2-core :measure (nfix fuel)
                  :guard (and (fn2-core-wfp fn2-core) (natp fuel)
                              (natp h) (natp k) (natp a) (natp nobs)
                              (natp nvisits) (natp nactions))))
  (cond
   ((or (zp fuel) (>= nobs h) (>= nvisits k) (>= nactions a)
        (= 1 (fn2-exec-stop fn2-core))
        (and (or (>= nobs h) (not (fn2-exec-observation-p fn2-core)))
             (not (fn2-exec-eligible-p fn2-core))))
    (mv (fn2-turn-status fn2-core) nobs nvisits nactions fn2-core))
   (t
    (b* (((mv obs visits actions bytes steps fn2-core)
          (fn2-transition (< nobs h) (- a nactions) fn2-core))
         (fn2-core (fn2-exec-account-work bytes steps fn2-core)))
      (fn2-concrete-loop (- fuel 1) h k a (+ nobs (nfix obs))
                           (+ nvisits (nfix visits)) (+ nactions (nfix actions)) fn2-core)))))
(fn2-core-shape-lemmas fn2-concrete-loop (fuel h k a nobs nvisits nactions) 4)

(defun fn2-concrete-turn (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (let* ((h (fn2-exec-h fn2-core)) (k (fn2-exec-k fn2-core))
         (a (fn2-exec-aturn fn2-core))
         (fn2-core (fn2-exec-set-turn-bytes 0 fn2-core))
         (fn2-core (fn2-exec-set-turn-steps 0 fn2-core)))
    (fn2-concrete-loop (+ h k) h k a 0 0 0 fn2-core)))
(fn2-core-shape-lemmas fn2-concrete-turn () 4)

(defun fn2-turn (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (fn2-concrete-turn fn2-core))
(fn2-core-shape-lemmas fn2-turn () 4)

(defun fn2-exec-start-listeners (left id fn2-core)
  (declare (xargs :stobjs fn2-core :measure (nfix left)
                  :guard (and (fn2-core-wfp fn2-core) (natp left) (natp id))))
  (if (zp left) fn2-core
    (let ((fn2-core (fn2-exec-wake id fn2-core)))
      (fn2-exec-start-listeners (- left 1) (+ id 1) fn2-core))))
(fn2-machine-core-shape fn2-exec-start-listeners (left id))

(defun fn2-init-executor (profile mode scribe-p fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-profilep profile)))
  (b* ((fn2-core (fn2-core-init profile fn2-core))
       (fn2-core (fn2-listener-set-mode-all (if (eq mode :null) 0 1) fn2-core))
       (fn2-core (fn2-exec-start-listeners (fn2-machine-accept-count fn2-core)
                   (fn2-machine-kind-base *fn2-listener-kind* fn2-core) fn2-core))
       (fn2-core (if scribe-p (fn2-scribe-start fn2-core) fn2-core))
       ((mv wake fn2-core) (fn2-machine-take-wake fn2-core)))
    (fn2-exec-wake wake fn2-core)))

(defthm-owed fn2-turn-bounds (core)
  (implies (and (fn2-corep core) (fn2-core-wfp core))
    (mv-let (status nobs nvisits nactions after) (fn2-turn core)
      (declare (ignore status after))
      (and (<= nobs (fn2-exec-h core)) (<= nvisits (fn2-exec-k core))
           (<= nactions (fn2-exec-aturn core)))))
  :teeth (fn2-executor-bounds-teeth fn2-executor-bounds-negative)
  :doc "Owed simultaneous observation, calendar-visit and descriptor bounds over fn2-turn.")

(assert-event
 (fn2-profile-exports-compliant-p
  '(fn2-transition fn2-concrete-loop fn2-concrete-turn fn2-turn fn2-init-executor
    fn2-core-idle-deadline fn2-exec-harvest fn2-exec-mailbox fn2-exec-principal
    fn2-exec-service fn2-exec-account-work) (w state)))
