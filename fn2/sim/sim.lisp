; Seeded asynchronous completions and process-death composition.
(in-package "ACL2")
(include-book "sim-adapter-base")

; A submitted write can reach the device before its completion is observed.
; Repeated random selection among remaining flights admits every permutation;
; the independent keep bit admits every subset. FUA has no success yet, so
; these bytes remain pending and may tear with the rest of the volatile cache.
(defthm fn2-sim-set-fua-ready
  (implies (and (fn2-sim-ready fn2-sim) (natp slot) (< slot (fn2-sim-rows fn2-sim)))
           (fn2-sim-ready (fn2-sim-set-fua slot value fn2-sim))))
(defthm fn2-sim-set-active-ready
  (implies (and (fn2-sim-ready fn2-sim) (natp slot) (< slot (fn2-sim-rows fn2-sim)))
           (fn2-sim-ready (fn2-sim-set-active slot value fn2-sim))))

(in-theory (disable fn2-sim-ready fn2-core-wfp))

(defun fn2-sim-crash-flight-one (fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own)
                  :guard (and (fn2-core-wfp fn2-core) (fn2-sim-ready fn2-sim)
                              (fn2-own-wfp fn2-own))))
  (b* (((mv word fn2-sim) (fn2-sim-random fn2-sim))
       ((mv found slot) (fn2-sim-find-write (fn2-sim-rows fn2-sim) (floor word 2) fn2-sim))
       ((when (not (and found (natp slot) (< slot (fn2-sim-rows fn2-sim)))))
        (mv nil fn2-core fn2-sim fn2-own))
       (fn2-sim (fn2-sim-set-fua slot 0 fn2-sim))
       ((mv & & & fn2-core fn2-sim fn2-own)
        (if (= (mod word 2) 1)
            (fn2-sim-physical slot 26 word fn2-core fn2-sim fn2-own)
          (mv :ok 0 0 fn2-core fn2-sim fn2-own)))
       (fn2-sim (fn2-sim-set-active slot 0 fn2-sim)))
    (mv t fn2-core fn2-sim fn2-own)))
(fn2-sim-adapter-shape fn2-sim-crash-flight-one () 1 2 3 1)
(fn2-sim-adapter-shape fn2-sim-crash-flight-one () 1 2 3 2)
(fn2-sim-adapter-shape fn2-sim-crash-flight-one () 1 2 3 3)
(fn2-sim-adapter-shape fn2-sim-crash-flight-one () 1 2 3 4)
(fn2-sim-adapter-shape fn2-sim-crash-flight-one () 1 2 3 5)
(fn2-sim-adapter-shape fn2-sim-crash-flight-one () 1 2 3 6)
(fn2-sim-adapter-shape fn2-sim-crash-flight-one () 1 2 3 7)

(defun fn2-sim-crash-flight-writes (left fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :measure (nfix left)
                  :guard (and (fn2-core-wfp fn2-core) (fn2-sim-ready fn2-sim)
                              (fn2-own-wfp fn2-own) (natp left))))
  (if (zp left) (mv fn2-core fn2-sim fn2-own)
    (mv-let (found fn2-core fn2-sim fn2-own)
      (fn2-sim-crash-flight-one fn2-core fn2-sim fn2-own)
      (if found
          (fn2-sim-crash-flight-writes (- left 1) fn2-core fn2-sim fn2-own)
        (mv fn2-core fn2-sim fn2-own)))))
(fn2-sim-adapter-shape fn2-sim-crash-flight-writes (left) 0 1 2 1)
(fn2-sim-adapter-shape fn2-sim-crash-flight-writes (left) 0 1 2 2)
(fn2-sim-adapter-shape fn2-sim-crash-flight-writes (left) 0 1 2 3)
(fn2-sim-adapter-shape fn2-sim-crash-flight-writes (left) 0 1 2 4)
(fn2-sim-adapter-shape fn2-sim-crash-flight-writes (left) 0 1 2 5)
(fn2-sim-adapter-shape fn2-sim-crash-flight-writes (left) 0 1 2 6)
(fn2-sim-adapter-shape fn2-sim-crash-flight-writes (left) 0 1 2 7)

(defthm fn2-sim-ready-disk-projection
 (implies (fn2-sim-ready fn2-sim)
          (fn2-sim-storage-wfp (nth *fn2-sim-disk* fn2-sim)))
 :rule-classes (:rewrite :forward-chaining)
 :hints (("Goal" :in-theory (enable fn2-sim-ready))))
(defthm fn2-sim-ready-update-disk
 (implies (and (fn2-sim-ready fn2-sim) (fn2-sim-storage-wfp child))
          (fn2-sim-ready (update-fn2-sim-disk child fn2-sim)))
 :hints (("Goal" :in-theory (enable fn2-sim-ready))))
(defthm fn2-sim-ready-update-deaths
 (implies (fn2-sim-ready fn2-sim)
          (fn2-sim-ready (update-fn2-sim-deaths value fn2-sim)))
 :hints (("Goal" :in-theory (enable fn2-sim-ready))))
(defthm fn2-sim-ready-update-wake-pending
 (implies (fn2-sim-ready fn2-sim)
          (fn2-sim-ready (update-fn2-sim-wake-pending value fn2-sim)))
 :hints (("Goal" :in-theory (enable fn2-sim-ready))))
(defthm fn2-sim-ready-update-wake-deadline
 (implies (fn2-sim-ready fn2-sim)
          (fn2-sim-ready (update-fn2-sim-wake-deadline value fn2-sim)))
 :hints (("Goal" :in-theory (enable fn2-sim-ready))))
(defthm fn2-sim-ready-update-wake-observation-gen
 (implies (fn2-sim-ready fn2-sim)
          (fn2-sim-ready (update-fn2-sim-wake-observation-gen value fn2-sim)))
 :hints (("Goal" :in-theory (enable fn2-sim-ready))))
(defun fn2-sim-crash-state (fn2-sim)
  (declare (xargs :stobjs fn2-sim :guard (fn2-sim-ready fn2-sim)
                  :guard-hints (("Goal" :in-theory (enable fn2-sim-storage-rows)))))
  (b* ((deaths (fn2-sim-deaths fn2-sim))
       (units (stobj-let ((fn2-sim-storage (fn2-sim-disk fn2-sim)))
                (n) (floor (fn2-sim-storage-rows fn2-sim-storage) 512) n))
       (fn2-sim (fn2-sim-crash-units units fn2-sim))
       (fn2-sim (stobj-let ((fn2-sim-storage (fn2-sim-disk fn2-sim))
                            (fn2-sim-network (fn2-sim-net fn2-sim)))
                  (fn2-sim-storage fn2-sim-network)
                  (let* ((fn2-sim-storage (fn2-storage-crash-reset fn2-sim-storage))
                         (fn2-sim-network (fn2-network-restart fn2-sim-network)))
                    (mv fn2-sim-storage fn2-sim-network))
                  fn2-sim))
       (fn2-sim (fn2-sim-clear-flights 0 fn2-sim))
       (fn2-sim (update-fn2-sim-wake-pending 0 fn2-sim))
       (fn2-sim (update-fn2-sim-wake-deadline 0 fn2-sim))
       (fn2-sim (update-fn2-sim-wake-observation-gen 0 fn2-sim))
       (fn2-sim (update-fn2-sim-deaths (min #xffffffff (+ 1 deaths)) fn2-sim)))
    fn2-sim))
(fn2-sim-shape fn2-sim-crash-state (fn2-sim) nil)
(in-theory (disable fn2-sim-ready fn2-core-wfp))

(defthm fn2-sim-crash-flight-writes-core-car-type
 (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
               (fn2-simp fn2-sim) (fn2-sim-ready fn2-sim)
               (fn2-ownp fn2-own) (fn2-own-wfp fn2-own))
          (fn2-corep (car (fn2-sim-crash-flight-writes left fn2-core fn2-sim fn2-own))))
 :hints (("Goal" :use fn2-sim-crash-flight-writes-core-type
                 :in-theory (disable fn2-sim-crash-flight-writes-core-type))))
(defun fn2-sim-crash (profile fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own)
                  :guard (and (fn2-core-wfp fn2-core) (fn2-sim-ready fn2-sim)
                              (fn2-own-wfp fn2-own))))
  (if (not (fn2-core-profilep profile)) (mv fn2-core fn2-sim fn2-own)
    (b* (((mv fn2-core fn2-sim fn2-own)
          (fn2-sim-crash-flight-writes (fn2-sim-rows fn2-sim) fn2-core fn2-sim fn2-own))
         (fn2-sim (fn2-sim-crash-state fn2-sim))
         (fn2-sim (fn2-sim-land 15 fn2-sim))
         (fn2-own (fn2-own-restart fn2-own))
         (fn2-core (fn2-core-init profile fn2-core)))
      (mv fn2-core fn2-sim fn2-own))))
(fn2-sim-adapter-shape fn2-sim-crash (profile) 0 1 2)


; ACL2 normalizes the first result of a multiple-value call to CAR.
(defthm fn2-sim-crash-core-car-shape
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                (fn2-simp fn2-sim) (fn2-sim-ready fn2-sim)
                (fn2-ownp fn2-own) (fn2-own-wfp fn2-own))
           (and (fn2-corep (car (fn2-sim-crash profile fn2-core fn2-sim fn2-own)))
                (fn2-core-wfp (car (fn2-sim-crash profile fn2-core fn2-sim fn2-own)))))
  :hints (("Goal" :use (fn2-sim-crash-core-type fn2-sim-crash-core-wfp)
                   :in-theory (disable fn2-sim-crash-core-type fn2-sim-crash-core-wfp))))

(assert-event (eq (symbol-class 'fn2-sim-crash (w state)) :common-lisp-compliant))

(in-theory (enable fn2-sim-ready fn2-core-wfp))

(defun fn2-sim-result-outcome (kind code count len)
  (declare (xargs :guard (and (natp count) (natp len))))
  (cond ((eq code :cancelled) *fn2-outcome-cancelled*)
        ((and (equal kind *fn2-action-write*) (< count len)) *fn2-outcome-failed*)
        ((or (eq code :ok) (eq code :eof)
             (and (< 0 count) (or (equal kind *fn2-action-send*) (equal kind *fn2-action-receive*))))
         (if (and (< count len) (or (equal kind *fn2-action-send*) (equal kind *fn2-action-read*)))
             *fn2-outcome-short* *fn2-outcome-done*))
        (t *fn2-outcome-failed*)))
(defthm fn2-sim-result-outcome-type
  (unsigned-byte-p 8 (fn2-sim-result-outcome kind code count len)))
(in-theory (disable fn2-sim-result-outcome))
(defun fn2-sim-result-reason (kind code outcome)
  (declare (xargs :guard t))
  (if (not (equal outcome *fn2-outcome-failed*)) *fn2-reason-none*
    (cond ((equal kind *fn2-action-accept*) *fn2-reason-exhausted*)
          ((equal kind *fn2-action-connect*) *fn2-reason-refused*)
          ((or (equal kind *fn2-action-receive*) (equal kind *fn2-action-send*))
           (if (eq code :reset) *fn2-reason-reset* *fn2-reason-closed*))
          ((equal kind *fn2-action-tls-start*) *fn2-reason-handshake*)
          ((equal kind *fn2-action-write*)
           (cond ((eq code :no-space) *fn2-reason-no-space*)
                 ((eq code :ok) *fn2-reason-uncertain*)
                 (t *fn2-reason-io*)))
          (t *fn2-reason-io*))))

(defthm fn2-sim-result-reason-type
  (unsigned-byte-p 8 (fn2-sim-result-reason kind code outcome)))
(in-theory (disable fn2-sim-result-reason))

(defun fn2-sim-save-terminal (slot outcome reason count aux0 aux1 fn2-sim)
  (declare (xargs :stobjs fn2-sim :guard (fn2-sim-ready fn2-sim)))
  (if (not (and (natp slot) (< slot (fn2-sim-rows fn2-sim))
                (unsigned-byte-p 8 outcome) (unsigned-byte-p 8 reason)
                (unsigned-byte-p 32 count) (unsigned-byte-p 32 aux0)
                (unsigned-byte-p 32 aux1)))
      fn2-sim
    (let* ((fn2-sim (fn2-sim-set-terminal-outcome slot outcome fn2-sim))
           (fn2-sim (fn2-sim-set-terminal-reason slot reason fn2-sim))
           (fn2-sim (fn2-sim-set-terminal-count slot count fn2-sim))
           (fn2-sim (fn2-sim-set-terminal-aux0 slot aux0 fn2-sim)))
      (fn2-sim-set-terminal-aux1 slot aux1 fn2-sim))))
(fn2-sim-shape fn2-sim-save-terminal (slot outcome reason count aux0 aux1 fn2-sim) nil)
(fn2-sim-rows-frame fn2-sim-save-terminal (slot outcome reason count aux0 aux1 fn2-sim) nil)

(in-theory (disable fn2-sim-ready fn2-core-wfp))

(defthm fn2-sim-set-last-gen-ready
  (implies (and (fn2-sim-ready fn2-sim) (natp slot) (< slot (fn2-sim-rows fn2-sim)))
           (fn2-sim-ready (fn2-sim-set-last-gen slot value fn2-sim)))
  :hints (("Goal" :in-theory (enable fn2-sim-ready))))
(defthm fn2-sim-set-due-ready
  (implies (and (fn2-sim-ready fn2-sim) (natp slot) (< slot (fn2-sim-rows fn2-sim)))
           (fn2-sim-ready (fn2-sim-set-due slot value fn2-sim)))
  :hints (("Goal" :in-theory (enable fn2-sim-ready))))

(defun fn2-sim-terminal-post
  (slot gen event outcome reason count aux0 aux1 fault word now release early
        fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own)
                  :guard (and (fn2-core-wfp fn2-core) (fn2-sim-ready fn2-sim)
                              (fn2-own-wfp fn2-own)
                              (natp slot) (< slot (fn2-sim-rows fn2-sim))
                              (unsigned-byte-p 60 gen) (unsigned-byte-p 60 now)
                              (unsigned-byte-p 32 word)
                              (unsigned-byte-p 8 outcome) (unsigned-byte-p 8 reason)
                              (unsigned-byte-p 32 count) (unsigned-byte-p 32 aux0)
                              (unsigned-byte-p 32 aux1))))
  (if (not (and (natp slot) (< slot (fn2-sim-rows fn2-sim))
                (unsigned-byte-p 60 gen) (unsigned-byte-p 60 now)
                (unsigned-byte-p 32 word)
                (unsigned-byte-p 8 outcome) (unsigned-byte-p 8 reason)
                (unsigned-byte-p 32 count) (unsigned-byte-p 32 aux0)
                (unsigned-byte-p 32 aux1)))
      (mv nil fn2-core fn2-sim fn2-own)
    (b* ((fn2-sim (fn2-sim-save-terminal slot outcome reason count aux0 aux1 fn2-sim))
         ((mv post-code fn2-core fn2-sim fn2-own)
          (if early
              (fn2-sim-post 1 slot gen *fn2-event-borrow-released* *fn2-outcome-done*
                            *fn2-reason-none* 0 0 0 fault nil fn2-core fn2-sim fn2-own)
            (fn2-sim-post 0 slot gen event outcome reason count aux0 aux1 fault nil
                          fn2-core fn2-sim fn2-own)))
         ((mv & fn2-core fn2-sim fn2-own)
          (if (equal fault 18)
              (fn2-sim-post 0 slot gen event outcome reason count aux0 aux1 fault t
                            fn2-core fn2-sim fn2-own)
            (mv :ok fn2-core fn2-sim fn2-own)))
         (fn2-sim (if (and early (eq post-code :ok)) (fn2-sim-land 25 fn2-sim) fn2-sim))
         (fn2-sim (fn2-sim-set-last-gen slot gen fn2-sim))
         (fn2-sim (fn2-sim-set-active slot (cond (early 3) (release 2) (t 0)) fn2-sim))
         (fn2-sim (fn2-sim-set-due slot
                      (min #xfffffffffffffff (+ 1 (mod word 100) now)) fn2-sim)))
      (mv t fn2-core fn2-sim fn2-own))))
(fn2-sim-adapter-shape fn2-sim-terminal-post
 (slot gen event outcome reason count aux0 aux1 fault word now release early) 1 2 3)

; Scalar interpretation stays opaque in the state-preservation proofs.
(defun fn2-sim-terminal-values (kind code physical-count aux len release cancelled)
  (declare (xargs :guard (natp len)))
  (b* ((count (if (and (unsigned-byte-p 32 physical-count) (<= physical-count len))
                  physical-count 0))
       (outcome (fn2-sim-result-outcome kind code count len))
       (outcome (if (and (equal kind *fn2-action-cancel*) (not (eq code :cancelled)))
                    (if cancelled *fn2-outcome-done* *fn2-outcome-not-found*) outcome))
       (reason (fn2-sim-result-reason kind code outcome))
       (count (if (or (equal kind *fn2-action-accept*) (equal kind *fn2-action-connect*)
                      (and (fn2-sim-input-kindp kind)
                           (or (= outcome *fn2-outcome-failed*) (= outcome *fn2-outcome-cancelled*))))
                  0 count))
       (aux0 (cond ((or (equal kind *fn2-action-accept*) (equal kind *fn2-action-connect*))
                    (if (unsigned-byte-p 32 physical-count) physical-count 0))
                   (release 1) (t 0)))
       (aux1 (if (and (or (equal kind *fn2-action-accept*) (equal kind *fn2-action-connect*))
                      (unsigned-byte-p 32 aux)) aux 0)))
    (mv outcome reason count aux0 aux1)))
(in-theory (disable fn2-sim-terminal-values))
(defthm fn2-sim-terminal-values-outcome-type
  (unsigned-byte-p 8
    (car (fn2-sim-terminal-values kind code physical-count aux len release cancelled)))
  :hints (("Goal" :in-theory (e/d (fn2-sim-terminal-values) (unsigned-byte-p)))))
(defthm fn2-sim-terminal-values-reason-type
  (unsigned-byte-p 8
    (mv-nth 1 (fn2-sim-terminal-values kind code physical-count aux len release cancelled)))
  :hints (("Goal" :in-theory (e/d (fn2-sim-terminal-values) (unsigned-byte-p)))))
(defthm fn2-sim-terminal-values-count-type
  (unsigned-byte-p 32
    (mv-nth 2 (fn2-sim-terminal-values kind code physical-count aux len release cancelled)))
  :hints (("Goal" :in-theory (e/d (fn2-sim-terminal-values) (unsigned-byte-p)))))
(defthm fn2-sim-terminal-values-aux0-type
  (unsigned-byte-p 32
    (mv-nth 3 (fn2-sim-terminal-values kind code physical-count aux len release cancelled)))
  :hints (("Goal" :in-theory (e/d (fn2-sim-terminal-values) (unsigned-byte-p)))))
(defthm fn2-sim-terminal-values-aux1-type
  (unsigned-byte-p 32
    (mv-nth 4 (fn2-sim-terminal-values kind code physical-count aux len release cancelled)))
  :hints (("Goal" :in-theory (e/d (fn2-sim-terminal-values) (unsigned-byte-p)))))


; Interpret one physical result after the byte effects have completed.
(defun fn2-sim-complete-result
  (slot gen kind event len code physical-count aux fault word now release
        fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own)
                  :guard (and (fn2-core-wfp fn2-core) (fn2-sim-ready fn2-sim)
                              (fn2-own-wfp fn2-own)
                              (natp slot) (< slot (fn2-sim-rows fn2-sim))
                              (unsigned-byte-p 60 gen) (unsigned-byte-p 60 now)
                              (unsigned-byte-p 32 word) (natp len))
                  :guard-hints (("Goal" :in-theory (disable unsigned-byte-p)))))
  (b* (((mv cancelled fn2-sim)
        (if (and (equal kind *fn2-action-cancel*) (not (eq code :cancelled)))
            (fn2-sim-cancel-target slot fn2-sim) (mv nil fn2-sim)))
       ((mv outcome reason count aux0 aux1)
        (fn2-sim-terminal-values kind code physical-count aux len release cancelled))
       (early (and release (equal fault 25))))
    (fn2-sim-terminal-post slot gen event outcome reason count aux0 aux1
      fault word now release early fn2-core fn2-sim fn2-own)))
(fn2-sim-adapter-shape fn2-sim-complete-result
 (slot gen kind event len code physical-count aux fault word now release) 1 2 3)

(defun fn2-sim-complete (slot fault word fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own)
                  :guard (and (fn2-core-wfp fn2-core) (fn2-sim-ready fn2-sim)
                              (fn2-own-wfp fn2-own))))
  (if (not (and (natp slot) (< slot (fn2-sim-rows fn2-sim))
                (unsigned-byte-p 32 word) (natp fault)))
      (mv nil fn2-core fn2-sim fn2-own)
    (b* ((active (fn2-sim-active slot fn2-sim))
         (was-cancelled (fn2-sim-cancelled slot fn2-sim))
         (now (fn2-sim-now fn2-sim))
         (gen (fn2-sim-gen slot fn2-sim)) (kind (fn2-sim-kind slot fn2-sim))
         (event (fn2-terminal-event kind))
         (len (fn2-sim-range-len slot fn2-sim))
         (release (and (equal kind *fn2-action-send*) (= (fn2-sim-may-release slot fn2-sim) 1))))
      (cond
       ((= active 2)
        (b* (((mv & fn2-core fn2-sim fn2-own)
              (fn2-sim-post 1 slot gen *fn2-event-borrow-released* *fn2-outcome-done*
                            *fn2-reason-none* 0 0 0 fault nil fn2-core fn2-sim fn2-own))
             (fn2-sim (fn2-sim-set-active slot 0 fn2-sim)))
          (mv t fn2-core fn2-sim fn2-own)))
       ((= active 3)
        (b* ((outcome (fn2-sim-terminal-outcome slot fn2-sim))
             (reason (fn2-sim-terminal-reason slot fn2-sim))
             (count (fn2-sim-terminal-count slot fn2-sim))
             (aux0 (fn2-sim-terminal-aux0 slot fn2-sim))
             (aux1 (fn2-sim-terminal-aux1 slot fn2-sim))
             ((mv & fn2-core fn2-sim fn2-own)
              (fn2-sim-post 0 slot gen event outcome reason count aux0 aux1 fault nil
                            fn2-core fn2-sim fn2-own))
             (fn2-sim (fn2-sim-set-active slot 0 fn2-sim)))
          (mv t fn2-core fn2-sim fn2-own)))
       (t
        (b* (((mv & fn2-core fn2-sim fn2-own)
              (fn2-sim-inject slot fault fn2-core fn2-sim fn2-own))
             ((mv code physical-count aux fn2-core fn2-sim fn2-own)
              (if (= was-cancelled 1)
                  (mv :cancelled 0 0 fn2-core fn2-sim fn2-own)
                (fn2-sim-physical slot fault word fn2-core fn2-sim fn2-own)))
             ((when (and (eq code :would-block) (equal physical-count 0)))
              (let ((fn2-sim (fn2-sim-set-due slot
                              (min #xfffffffffffffff (+ 100 now)) fn2-sim)))
                (mv t fn2-core fn2-sim fn2-own)))
             ((mv found fn2-core fn2-sim fn2-own)
              (fn2-sim-complete-result slot gen kind event len code physical-count aux
                fault word now release fn2-core fn2-sim fn2-own)))
          (mv found fn2-core fn2-sim fn2-own)))))))
(fn2-sim-adapter-shape fn2-sim-complete (slot fault word) 1 2 3 1)
(fn2-sim-adapter-shape fn2-sim-complete (slot fault word) 1 2 3 2)
(fn2-sim-adapter-shape fn2-sim-complete (slot fault word) 1 2 3 3)
(fn2-sim-adapter-shape fn2-sim-complete (slot fault word) 1 2 3 4)
(fn2-sim-adapter-shape fn2-sim-complete (slot fault word) 1 2 3 5)
(fn2-sim-adapter-shape fn2-sim-complete (slot fault word) 1 2 3 6)
(fn2-sim-adapter-shape fn2-sim-complete (slot fault word) 1 2 3 7)
(in-theory (enable fn2-sim-ready fn2-core-wfp))

(defun fn2-sim-client-drain (left cap nonce fn2-sim)
  (declare (xargs :stobjs fn2-sim :measure (nfix left)
                  :guard (and (fn2-sim-ready fn2-sim) (natp left))))
  (if (zp left) fn2-sim
    (stobj-let ((fn2-sim-network (fn2-sim-net fn2-sim)))
      (code byte fn2-sim-network)
      (fn2-network-client-read cap nonce fn2-sim-network)
      (if (not (eq code :ok)) fn2-sim
        (let ((fn2-sim (fn2-sim-record cap nonce 0 258 0 0 byte
                                      (fn2-sim-now fn2-sim) 0 26 fn2-sim)))
          (fn2-sim-client-drain (- left 1) cap nonce fn2-sim))))))
(in-theory (disable fn2-sim-ready))
(fn2-sim-shape fn2-sim-client-drain (left cap nonce fn2-sim) nil)
(fn2-sim-rows-frame fn2-sim-client-drain (left cap nonce fn2-sim) nil)
(in-theory (enable fn2-sim-ready))

; Raw frames match generated projections after their accessors unfold.
(fn2-sim-rows-frame fn2-sim-clock (target fault fn2-sim) nil)
(fn2-sim-rows-frame fn2-sim-choose-fault (fn2-sim) 1)
(fn2-sim-rows-frame fn2-sim-environment (slot fault word fn2-sim) nil)
(in-theory (disable fn2-sim-ready fn2-profile-run-bytes))

(defun fn2-sim-delay-flight (slot fault word fn2-sim)
 (declare (xargs :stobjs fn2-sim :guard (fn2-sim-ready fn2-sim)))
 (if (not (and (natp slot) (< slot (fn2-sim-rows fn2-sim))
                (unsigned-byte-p 32 word)))
     fn2-sim
   (let ((latency (if (equal fault 14)
                   (case (mod word 3) (0 1000) (1 10000) (otherwise 100000)) 100)))
    (let* ((due (min #xfffffffffffffff (+ latency (fn2-sim-now fn2-sim))))
           (fn2-sim (if (and (member-equal fault '(2 14)) (< (fn2-sim-due slot fn2-sim) due))
                        (fn2-sim-land fault fn2-sim) fn2-sim)))
      (fn2-sim-set-due slot due fn2-sim)))))
(in-theory (enable fn2-sim-ready))
(fn2-sim-shape fn2-sim-delay-flight (slot fault word fn2-sim) nil)
(in-theory (disable fn2-sim-ready))

; Posting the clock preserves the parent core without reopening its children.
(defun fn2-sim-post-clock (mono real fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
    (fn2-ops) (fn2-post-clock mono real 1 fn2-ops) fn2-core))
(defthm fn2-sim-post-clock-type
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
           (fn2-corep (fn2-sim-post-clock mono real fn2-core))))
(defthm fn2-sim-post-clock-wfp
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
           (fn2-core-wfp (fn2-sim-post-clock mono real fn2-core))))
(in-theory (disable fn2-sim-post-clock fn2-core-wfp))

; Keep the generated typed reader intact for arithmetic in wake selection.
; Opening it here hides its type behind the composed simulator updates.
(in-theory (disable fn2-sim-due))
(defun fn2-sim-wake-first-p (found slot fn2-sim)
  (declare (xargs :stobjs fn2-sim
                  :guard (and (fn2-sim-ready fn2-sim)
                              (or (not found)
                                  (and (natp slot) (< slot (fn2-sim-rows fn2-sim)))))
                  :guard-hints (("Goal" :use ((:instance fn2-sim-due-natp (i slot)))))))
  (and (= (fn2-sim-wake-pending fn2-sim) 1)
       (or (not found) (<= (fn2-sim-wake-deadline fn2-sim)
                           (fn2-sim-due slot fn2-sim)))))
(in-theory (disable fn2-sim-wake-first-p))

; Each stage carries the existing shape contracts, so composition does not
; repeatedly expand nested simulator states in all six projection proofs.
(defun fn2-sim-advance-flight (found slot fault word fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own)
                  :guard (and (fn2-core-wfp fn2-core) (fn2-sim-ready fn2-sim)
                              (fn2-own-wfp fn2-own)
                              (or (not found)
                                  (and (natp slot) (< slot (fn2-sim-rows fn2-sim)))))))
  (b* ((fn2-sim (fn2-sim-environment slot fault word fn2-sim))
       (quantum (fn2-profile-run-bytes (fn2-sim-profile fn2-sim)))
       (fn2-sim (if found
                    (fn2-sim-client-drain (if (unsigned-byte-p 32 quantum) quantum 0)
                                          (fn2-sim-cap-index slot fn2-sim)
                                          (fn2-sim-cap-nonce slot fn2-sim) fn2-sim)
                  fn2-sim))
       ((when (not found)) (mv nil fn2-core fn2-sim fn2-own))
       ((when (or (equal fault 2) (equal fault 14)))
        (let ((fn2-sim (fn2-sim-delay-flight slot fault word fn2-sim)))
          (mv t fn2-core fn2-sim fn2-own))))
    (fn2-sim-complete slot fault word fn2-core fn2-sim fn2-own)))
(fn2-sim-adapter-shape fn2-sim-advance-flight (found slot fault word) 1 2 3)

(defun fn2-sim-advance-selected (found slot fault word fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own)
                  :guard (and (fn2-core-wfp fn2-core) (fn2-sim-ready fn2-sim)
                              (fn2-own-wfp fn2-own)
                              (or (not found) (and (natp slot) (< slot (fn2-sim-rows fn2-sim)))))))
  (b* ((wake-first (fn2-sim-wake-first-p found slot fn2-sim))
       (target (if wake-first (fn2-sim-wake-deadline fn2-sim)
                 (if found (fn2-sim-due slot fn2-sim) (fn2-sim-now fn2-sim))))
       (fn2-sim (fn2-sim-clock target fault fn2-sim))
       (mono (fn2-sim-now fn2-sim)) (real (fn2-sim-real fn2-sim))
       (fn2-sim (fn2-sim-record 0 0 0 256 0 0 mono real 1 fault fn2-sim))
       (fn2-core (fn2-sim-post-clock mono real fn2-core))
       ((when wake-first)
        (let* ((token (fn2-sim-wake-observation-gen fn2-sim))
               (deadline (fn2-sim-wake-deadline fn2-sim))
               (fn2-sim (update-fn2-sim-wake-pending 0 fn2-sim))
               (fn2-sim (fn2-sim-record 0 token 0 259 0 0 deadline mono 0 fault fn2-sim)))
          (mv t fn2-core fn2-sim fn2-own))))
    (fn2-sim-advance-flight found slot fault word fn2-core fn2-sim fn2-own)))
(fn2-sim-adapter-shape fn2-sim-advance-selected (found slot fault word) 1 2 3)

; Flight selection stays valid across the fault draw.
(fn2-sim-rows-frame fn2-sim-choose-flight-fault (slot fn2-sim) 1)

(defun fn2-sim-advance (fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own)
                  :guard (and (fn2-core-wfp fn2-core) (fn2-sim-ready fn2-sim)
                              (fn2-own-wfp fn2-own))))
  (b* (((mv found slot) (fn2-sim-next-flight fn2-sim))
       ((mv fault fn2-sim) (if found (fn2-sim-choose-flight-fault slot fn2-sim) (mv 26 fn2-sim)))
       ((mv word fn2-sim) (fn2-sim-random fn2-sim))
       (fn2-sim (fn2-sim-record 0 0 0 257 0 0 word (fn2-sim-now fn2-sim) 0 fault fn2-sim))
       ((when (equal fault 15))
        (let ((profile (fn2-sim-profile fn2-sim)))
          (mv-let (fn2-core fn2-sim fn2-own) (fn2-sim-crash profile fn2-core fn2-sim fn2-own)
            (mv t fn2-core fn2-sim fn2-own)))))
    (fn2-sim-advance-selected found slot fault word fn2-core fn2-sim fn2-own)))
(fn2-sim-adapter-shape fn2-sim-advance () 1 2 3)

(assert-event
 (fn2-profile-exports-compliant-p
  '(fn2-sim-amount fn2-sim-redirect fn2-sim-client-feed fn2-sim-client-drain
    fn2-sim-unused-op fn2-sim-find-write fn2-sim-crash-flight-writes
    fn2-sim-transfer fn2-sim-post fn2-sim-register fn2-sim-take-one
    fn2-sim-take-prefix fn2-sim-take fn2-sim-physical fn2-sim-cancel-target
    fn2-sim-inject fn2-sim-environment fn2-sim-crash-units fn2-sim-crash
    fn2-sim-crash-flight-one fn2-sim-crash-state fn2-sim-save-terminal
    fn2-sim-terminal-values fn2-sim-terminal-post fn2-sim-complete-result fn2-sim-delay-flight fn2-sim-post-clock
    fn2-sim-result-outcome fn2-sim-result-reason fn2-sim-complete fn2-sim-wake-first-p
    fn2-sim-advance-flight fn2-sim-advance-selected fn2-sim-advance)
  (w state)))
