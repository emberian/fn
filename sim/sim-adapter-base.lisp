; Seeded asynchronous adapter. Byte effects live in sim-transfer; all core
; mutations go through the common outstanding-table and pool interface.
(in-package "ACL2")
(include-book "sim-state")
(include-book "sim-transfer")

(in-theory (disable fn2-core-wfp fn2-sim-ready))

; Select from the chosen flight's classes, not the world's entire menu.
(defun fn2-sim-flight-classes (kind active release)
  (declare (xargs :guard t))
  (cond ((not (equal active 1)) `(,*fn2-fault-delay* ,*fn2-fault-crash* ,*fn2-fault-monotonic-jump* ,*fn2-fault-realtime-back*))
        ((equal kind *fn2-action-receive*) `(,*fn2-fault-delay* ,*fn2-fault-crash* ,*fn2-fault-monotonic-jump* ,*fn2-fault-realtime-back* ,*fn2-fault-duplicate* ,*fn2-fault-stale* ,*fn2-fault-forged* ,*fn2-fault-overcount* ,*fn2-fault-malformed* ,*fn2-fault-fragment* ,*fn2-fault-reset* ,*fn2-fault-half-open*))
        ((equal kind *fn2-action-send*)
         (if (equal release 1) `(,*fn2-fault-delay* ,*fn2-fault-crash* ,*fn2-fault-monotonic-jump* ,*fn2-fault-realtime-back* ,*fn2-fault-duplicate* ,*fn2-fault-stale* ,*fn2-fault-forged* ,*fn2-fault-overcount* ,*fn2-fault-malformed* ,*fn2-fault-short-send* ,*fn2-fault-reset* ,*fn2-fault-nonreading* ,*fn2-fault-release-order*) `(,*fn2-fault-delay* ,*fn2-fault-crash* ,*fn2-fault-monotonic-jump* ,*fn2-fault-realtime-back* ,*fn2-fault-duplicate* ,*fn2-fault-stale* ,*fn2-fault-forged* ,*fn2-fault-overcount* ,*fn2-fault-malformed* ,*fn2-fault-short-send* ,*fn2-fault-reset* ,*fn2-fault-nonreading*)))
        ((equal kind *fn2-action-read*) `(,*fn2-fault-delay* ,*fn2-fault-crash* ,*fn2-fault-monotonic-jump* ,*fn2-fault-realtime-back* ,*fn2-fault-duplicate* ,*fn2-fault-stale* ,*fn2-fault-forged* ,*fn2-fault-overcount* ,*fn2-fault-malformed* ,*fn2-fault-read-io* ,*fn2-fault-bitrot* ,*fn2-fault-misread* ,*fn2-fault-dead* ,*fn2-fault-fail-slow*))
        ((equal kind *fn2-action-write*) `(,*fn2-fault-delay* ,*fn2-fault-crash* ,*fn2-fault-monotonic-jump* ,*fn2-fault-realtime-back* ,*fn2-fault-duplicate* ,*fn2-fault-stale* ,*fn2-fault-forged* ,*fn2-fault-overcount* ,*fn2-fault-malformed* ,*fn2-fault-bitrot* ,*fn2-fault-miswrite* ,*fn2-fault-tear* ,*fn2-fault-no-space* ,*fn2-fault-dead* ,*fn2-fault-fail-slow* ,*fn2-fault-short-write*))
        ((equal kind *fn2-action-fence*) `(,*fn2-fault-delay* ,*fn2-fault-crash* ,*fn2-fault-monotonic-jump* ,*fn2-fault-realtime-back* ,*fn2-fault-duplicate* ,*fn2-fault-stale* ,*fn2-fault-forged* ,*fn2-fault-overcount* ,*fn2-fault-malformed* ,*fn2-fault-bitrot* ,*fn2-fault-lying-flush* ,*fn2-fault-tear* ,*fn2-fault-dead* ,*fn2-fault-fail-slow* ,*fn2-fault-flush-io*))
        (t `(,*fn2-fault-delay* ,*fn2-fault-crash* ,*fn2-fault-monotonic-jump* ,*fn2-fault-realtime-back* ,*fn2-fault-duplicate* ,*fn2-fault-stale* ,*fn2-fault-forged* ,*fn2-fault-overcount* ,*fn2-fault-malformed*))))
(defun fn2-sim-flight-candidate (kind active release word)
  (declare (xargs :guard (natp word)))
  (let ((classes (fn2-sim-flight-classes kind active release)))
    (nfix (nth (mod word (len classes)) classes))))
(local (defthm fn2-sim-nth-cons
  (equal (nth n (cons a b)) (if (zp n) a (nth (- n 1) b)))
  :hints (("Goal" :expand ((nth n (cons a b)))))))
(defthm fn2-sim-flight-candidate-bound
  (< (fn2-sim-flight-candidate kind active release word) *fn2-fault-count*)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn2-sim-flight-candidate fn2-sim-flight-classes nth))))
(in-theory (disable fn2-sim-flight-candidate fn2-sim-flight-classes))
(local (in-theory (disable fn2-sim-nth-cons)))
(defthm fn2-sim-probability-candidate-type
  (implies (fn2-simp fn2-sim)
    (natp (nth (fn2-sim-flight-candidate kind active release word)
               (nth *fn2-sim-probabilitiesi* fn2-sim))))
  :rule-classes :type-prescription
  :hints (("Goal" :use ((:instance fn2-sim-probabilitiesi-natp
                            (i (fn2-sim-flight-candidate kind active release word)))) :in-theory (enable fn2-sim-ready))))
(defun fn2-sim-choose-flight-fault (slot fn2-sim)
  (declare (xargs :stobjs fn2-sim :guard (fn2-sim-ready fn2-sim)
                  :guard-hints (("Goal" :use ((:instance fn2-sim-random-state-type)
                                               (:instance fn2-sim-random-ready))
                                        :in-theory (e/d (fn2-sim-ready) (fn2-sim-random-state-type fn2-sim-random-ready))))))
  (if (not (and (natp slot) (< slot (fn2-sim-rows fn2-sim)))) (mv *fn2-fault-none* fn2-sim)
    (b* ((kind (fn2-sim-kind slot fn2-sim))
         (active (fn2-sim-active slot fn2-sim))
         (release (fn2-sim-may-release slot fn2-sim))
         ((mv word fn2-sim) (fn2-sim-random fn2-sim))
         (forced (fn2-sim-forced-fault fn2-sim))
         (candidate (if (< forced *fn2-fault-none*) forced
                      (fn2-sim-flight-candidate kind active release word)))
         (hit (and (< 0 (fn2-sim-fault-budget fn2-sim))
                   (or (< forced *fn2-fault-none*)
                       (< (mod (floor word *fn2-fault-count*) 256) (fn2-sim-probabilitiesi candidate fn2-sim)))))
         (fn2-sim (update-fn2-sim-forced-fault *fn2-fault-none* fn2-sim))
         (fn2-sim (update-fn2-sim-digest
                    (fn2-sim-fold (fn2-sim-digest fn2-sim) (+ 61440 (if hit candidate *fn2-fault-none*))) fn2-sim))
         (fn2-sim (if hit (update-fn2-sim-fault-budget (- (fn2-sim-fault-budget fn2-sim) 1) fn2-sim) fn2-sim)))
      (mv (if hit candidate *fn2-fault-none*) fn2-sim))))
(fn2-sim-preserves fn2-sim-choose-flight-fault (slot fn2-sim) :forward t
  :hyps ((fn2-simp fn2-sim) (fn2-sim-ready fn2-sim))
  :specs (("-TYPE" fn2-simp 1) ("-READY" fn2-sim-ready 1) ("-WFP" fn2-sim-wfp 1))
  :hints (("Goal" :in-theory (enable fn2-sim-ready))))
(defthm fn2-sim-choose-flight-fault-result
  (implies (fn2-simp fn2-sim)
    (and (natp (mv-nth 0 (fn2-sim-choose-flight-fault slot fn2-sim)))
         (<= (mv-nth 0 (fn2-sim-choose-flight-fault slot fn2-sim)) *fn2-fault-none*)))
  :hints (("Goal" :in-theory (enable fn2-sim-choose-flight-fault fn2-sim-ready))))
(defthm fn2-sim-choose-flight-fault-rows
  (equal (fn2-sim-rows (mv-nth 1 (fn2-sim-choose-flight-fault slot fn2-sim)))
         (fn2-sim-rows fn2-sim))
  :hints (("Goal" :in-theory (enable fn2-sim-choose-flight-fault fn2-sim-rows fn2-sim-random fn2-sim-ready))))

(defthm fn2-sim-land-raw-rows
  (equal (nth *fn2-sim-rows* (fn2-sim-land fault fn2-sim)) (nth *fn2-sim-rows* fn2-sim))
  :hints (("Goal" :in-theory (enable fn2-sim-land fn2-sim-ready))))

; Peek is read-only: frame proofs need its result, not its queue branches.
; Keep composition on the child boundary, independent of included theories.
(local
 (defthm fn2-sim-update-ops-wfp
   (implies (and (fn2-core-wfp core) (fn2-ops-wfp ops))
            (fn2-core-wfp (update-fn2-core-ops ops core)))
   :hints (("Goal" :in-theory (enable fn2-core-wfp)))))
(local (in-theory (disable fn2-storage-fence-admission fn2-outbox-peek)))

(defthm fn2-sim-cap-u60-type
  (implies (natp x) (unsigned-byte-p 60 (min *fn2-u60-max* x))))
(defthm fn2-sim-cap-u32-type
  (implies (natp x) (unsigned-byte-p 32 (min #xffffffff x))))
(in-theory (disable min fn2-action-completionp fn2-terminal-event))

(defthm fn2-sim-core-ops-type-forward
  (implies (fn2-corep fn2-core) (fn2-opsp (fn2-core-ops fn2-core)))
  :rule-classes :forward-chaining
                  :hints (("Goal" :in-theory (enable fn2-core-wfp))))
(defthm fn2-sim-core-pool-type-forward
  (implies (fn2-corep fn2-core) (fn2-poolp (fn2-core-pool fn2-core)))
  :rule-classes :forward-chaining
                  :hints (("Goal" :in-theory (enable fn2-core-wfp))))

(defthm fn2-sim-next-flight-slot-natural
 (implies (and (fn2-simp fn2-sim) (fn2-sim-ready fn2-sim))
  (natp (mv-nth 1 (fn2-sim-next-flight fn2-sim))))
 :rule-classes :type-prescription
 :hints (("Goal" :use fn2-sim-next-flight-types :in-theory (e/d (fn2-sim-ready) (fn2-sim-next-flight-types)))))
(defthm fn2-sim-next-flight-slot-bound
 (implies (and (fn2-simp fn2-sim) (fn2-sim-ready fn2-sim)
               (mv-nth 0 (fn2-sim-next-flight fn2-sim)))
  (< (mv-nth 1 (fn2-sim-next-flight fn2-sim)) (fn2-sim-rows fn2-sim)))
 :rule-classes :linear
 :hints (("Goal" :use fn2-sim-next-flight-types :in-theory (e/d (fn2-sim-ready) (fn2-sim-next-flight-types)))))
(defthm fn2-sim-random-rows
 (equal (fn2-sim-rows (mv-nth 1 (fn2-sim-random fn2-sim))) (fn2-sim-rows fn2-sim))
 :hints (("Goal" :in-theory (enable fn2-sim-random fn2-sim-rows fn2-sim-ready))))
(defthm fn2-sim-choose-fault-rows
 (equal (fn2-sim-rows (mv-nth 1 (fn2-sim-choose-fault fn2-sim))) (fn2-sim-rows fn2-sim))
 :hints (("Goal" :in-theory (enable fn2-sim-choose-fault fn2-sim-rows fn2-sim-ready))))
(defthm fn2-sim-clock-rows
 (equal (fn2-sim-rows (fn2-sim-clock target fault fn2-sim)) (fn2-sim-rows fn2-sim))
 :hints (("Goal" :in-theory (enable fn2-sim-clock fn2-sim-rows fn2-sim-ready))))
(defthm fn2-sim-record-rows
 (equal (fn2-sim-rows (fn2-sim-record op gen cell evkind outcome reason count aux0 aux1 fault fn2-sim)) (fn2-sim-rows fn2-sim))
 :hints (("Goal" :in-theory (enable fn2-sim-record fn2-sim-rows fn2-sim-ready))))

(defthm fn2-sim-ready-network-projection
 (implies (fn2-sim-ready fn2-sim)
          (fn2-sim-network-wfp (nth *fn2-sim-net* fn2-sim)))
 :rule-classes (:rewrite :forward-chaining)
 :hints (("Goal" :in-theory (enable fn2-sim-ready))))
(defthm fn2-sim-ready-update-net
 (implies (and (fn2-sim-ready fn2-sim) (fn2-sim-network-wfp child))
          (fn2-sim-ready (update-fn2-sim-net child fn2-sim)))
 :hints (("Goal" :in-theory (enable fn2-sim-ready))))
(defthm fn2-sim-ready-storage-projection
 (implies (fn2-sim-ready fn2-sim)
          (fn2-sim-storage-wfp (nth *fn2-sim-disk* fn2-sim)))
 :rule-classes (:rewrite :forward-chaining)
 :hints (("Goal" :in-theory (enable fn2-sim-ready))))
(defthm fn2-sim-ready-root-projection
 (implies (fn2-sim-ready fn2-sim) (fn2-sim-wfp fn2-sim))
 :rule-classes (:rewrite :forward-chaining)
 :hints (("Goal" :in-theory (enable fn2-sim-ready))))

; Raw row projections stay stable even when the generated accessor unfolds.

(fn2-sim-preserves fn2-sim-record (op gen cell evkind outcome reason count aux0 aux1 fault fn2-sim) :disable nil
  :specs (("-RAW-ROWS" (lambda (s) (nth *fn2-sim-rows* s)) nil :frame fn2-sim))
  :hints (("Goal" :in-theory (enable fn2-sim-record))))

(defun fn2-sim-post
  (cell slot gen evkind outcome reason count aux0 aux1 fault expected-stray
        fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own)
                  :guard (and (fn2-core-wfp fn2-core) (fn2-sim-ready fn2-sim)
                              (fn2-own-wfp fn2-own))
                  :guard-hints (("Goal" :in-theory (enable fn2-core-wfp fn2-sim-ready)))))
  (b* (((mv family port w0 w1 w2 w3)
        ;; an Accept that completed carries the peer its capability is configured with
        (if (equal outcome *fn2-outcome-done*)
            (stobj-let ((fn2-sim-network (fn2-sim-net fn2-sim)))
              (family port w0 w1 w2 w3)
              (fn2-network-peer aux0 fn2-sim-network)
              (mv family port w0 w1 w2 w3))
          (mv *fn2-peer-family-none* 0 0 0 0 0)))
       ((mv code fn2-core fn2-own)
        (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
          (code fn2-ops fn2-own)
          (fn2-own-post-result cell slot gen evkind outcome reason count aux0 aux1
                               family port w0 w1 w2 w3 expected-stray fn2-ops fn2-own)
          (mv code fn2-core fn2-own)))
       (fn2-sim (fn2-sim-record slot gen cell evkind outcome reason count aux0 aux1 fault fn2-sim))
       (fn2-sim (if (and expected-stray (eq code :ok) (member-equal fault `(,*fn2-fault-duplicate* ,*fn2-fault-stale* ,*fn2-fault-forged* ,*fn2-fault-overcount* ,*fn2-fault-malformed*)))
                    (fn2-sim-land fault fn2-sim) fn2-sim)))
    (mv code fn2-core fn2-sim fn2-own)))

(fn2-sim-preserves fn2-sim-post (cell slot gen evkind outcome reason count aux0 aux1 fault expected-stray fn2-core fn2-sim fn2-own) :part nil
  :carriers ((fn2-core 1 :prefix "-CORE" :hints (("Goal" :in-theory (enable fn2-core-wfp)))) (fn2-sim 2 :invariant fn2-sim-ready :prefix "-SIM" :suffix "-READY" :hints (("Goal" :in-theory (enable fn2-sim-ready)))) (fn2-own 3 :prefix "-OWN"))
  :hints (("Goal" :in-theory (enable fn2-core-wfp fn2-sim-ready))))
(fn2-sim-preserves fn2-sim-post (cell slot gen evkind outcome reason count aux0 aux1 fault expected-stray fn2-core fn2-sim fn2-own) :disable nil
  :specs (("-RAW-ROWS" (lambda (s) (nth *fn2-sim-rows* s)) 2 :frame fn2-sim))
  :hints (("Goal" :in-theory (enable fn2-sim-post))))

(defun fn2-sim-register (slot gen fn2-ops fn2-sim)
  (declare (xargs :stobjs (fn2-ops fn2-sim)
                  :guard (and (fn2-ops-wfp fn2-ops) (fn2-sim-ready fn2-sim))
                  :guard-hints (("Goal" :in-theory (enable fn2-sim-ready)))))
  (if (not (and (natp slot) (< slot (fn2-ops-rows fn2-ops))
                (< slot (fn2-sim-rows fn2-sim)) (unsigned-byte-p 60 gen)))
      fn2-sim
    (b* (((mv word fn2-sim) (fn2-sim-random fn2-sim))
         (kind (fn2-ops-kind slot fn2-ops))
         (fn2-sim (fn2-sim-set-gen slot gen fn2-sim))
         (fn2-sim (fn2-sim-set-kind slot kind fn2-sim))
         (fn2-sim (fn2-sim-set-cancelled slot 0 fn2-sim))
         (fn2-sim (fn2-sim-set-active slot (if (fn2-action-completionp kind) 1 0) fn2-sim))
         (fn2-sim (fn2-sim-set-due slot
                    (min *fn2-u60-max* (+ (fn2-sim-now fn2-sim) 1 (mod word 100))) fn2-sim))
         (fn2-sim (fn2-sim-set-range-slot slot (fn2-ops-range-slot slot fn2-ops) fn2-sim))
         (fn2-sim (fn2-sim-set-range-gen slot (fn2-ops-range-gen slot fn2-ops) fn2-sim))
         (fn2-sim (fn2-sim-set-range-off slot (fn2-ops-range-off slot fn2-ops) fn2-sim))
         (fn2-sim (fn2-sim-set-range-len slot (fn2-ops-range-len slot fn2-ops) fn2-sim))
         (fn2-sim (fn2-sim-set-owner-kind slot (fn2-ops-owner-kind slot fn2-ops) fn2-sim))
         (fn2-sim (fn2-sim-set-owner-slot slot (fn2-ops-owner-slot slot fn2-ops) fn2-sim))
         (fn2-sim (fn2-sim-set-owner-gen slot (fn2-ops-owner-gen slot fn2-ops) fn2-sim))
         (fn2-sim (fn2-sim-set-cap-index slot (fn2-ops-cap-index slot fn2-ops) fn2-sim))
         (fn2-sim (fn2-sim-set-cap-nonce slot (fn2-ops-cap-nonce slot fn2-ops) fn2-sim))
         (fn2-sim (fn2-sim-set-storage-offset slot (fn2-ops-storage-offset slot fn2-ops) fn2-sim))
         (fn2-sim (fn2-sim-set-fua slot (fn2-ops-fua slot fn2-ops) fn2-sim))
         (fn2-sim (fn2-sim-set-may-release slot (fn2-ops-may-release slot fn2-ops) fn2-sim))
         (fn2-sim (fn2-sim-set-cancel-slot slot (fn2-ops-cancel-slot slot fn2-ops) fn2-sim))
         (fn2-sim (fn2-sim-set-cancel-gen slot (fn2-ops-cancel-gen slot fn2-ops) fn2-sim))
         (fn2-sim (if (< kind *fn2-action-count*)
                      (update-fn2-sim-action-countsi kind
                       (min #xffffffff (+ 1 (fn2-sim-action-countsi kind fn2-sim))) fn2-sim)
                    fn2-sim)))
      (cond ((equal kind *fn2-action-arm-wake*)
             (fn2-sim-arm-wake (fn2-ops-wake-deadline slot fn2-ops)
                               (fn2-ops-wake-observation-gen slot fn2-ops) fn2-sim))
            ((equal kind *fn2-action-fence*)
             (stobj-let ((fn2-sim-storage (fn2-sim-disk fn2-sim)))
               (code fn2-sim-storage)
               (fn2-storage-fence-capture slot fn2-sim-storage)
               (let ((ignored code)) (declare (ignore ignored)) fn2-sim)))
            (t fn2-sim)))))
(defthm fn2-sim-register-type
  (implies (and (fn2-opsp fn2-ops) (fn2-ops-wfp fn2-ops)
                (fn2-simp fn2-sim) (fn2-sim-ready fn2-sim))
           (fn2-simp (fn2-sim-register slot gen fn2-ops fn2-sim)))
                  :hints (("Goal" :in-theory (enable fn2-sim-ready))))
(defthm fn2-sim-register-ready
  (implies (and (fn2-opsp fn2-ops) (fn2-ops-wfp fn2-ops)
                (fn2-simp fn2-sim) (fn2-sim-ready fn2-sim))
           (fn2-sim-ready (fn2-sim-register slot gen fn2-ops fn2-sim)))
                  :hints (("Goal" :in-theory (enable fn2-sim-ready))))
(in-theory (disable fn2-sim-register))

(defun fn2-sim-take-one (fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own)
                  :guard (and (fn2-core-wfp fn2-core) (fn2-sim-ready fn2-sim)
                              (fn2-own-wfp fn2-own))
                  :guard-hints (("Goal" :in-theory (enable fn2-core-wfp fn2-sim-ready)))))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core))
              (fn2-ops (fn2-core-ops fn2-core)))
    (found fn2-ops fn2-sim fn2-own)
    (mv-let (code slot gen) (fn2-outbox-peek 0 fn2-ops)
      (if (not (and (eq code :ok) (natp slot) (< slot (fn2-sim-rows fn2-sim))
                    (< slot (fn2-ops-rows fn2-ops)) (= (fn2-sim-active slot fn2-sim) 0)))
          (mv nil fn2-ops fn2-sim fn2-own)
        (b* ((kind (fn2-ops-kind slot fn2-ops))
             ; Refusal is a continuation: retain the outbox head until a
             ; fence slot is free; do not register, ack or post an I/O error.
             (admission
              (if (equal kind *fn2-action-fence*)
                  (stobj-let ((fn2-sim-storage (fn2-sim-disk fn2-sim)))
                    (code) (fn2-storage-fence-admission slot fn2-sim-storage) code)
                :ok))
             ((unless (eq admission :ok)) (mv nil fn2-ops fn2-sim fn2-own))
             (fn2-own (fn2-own-observe-issue-parts slot fn2-pool fn2-ops fn2-own))
             (fn2-sim (fn2-sim-register slot gen fn2-ops fn2-sim))
             ((mv ack fn2-ops) (fn2-outbox-ack 1 fn2-ops))
             ((mv & fn2-ops)
              (if (and (eq ack :ok) (not (fn2-action-completionp kind)))
                  (fn2-op-finish slot gen fn2-ops) (mv :ok fn2-ops))))
          (mv (eq ack :ok) fn2-ops fn2-sim fn2-own))))
    (mv found fn2-core fn2-sim fn2-own)))
(fn2-sim-preserves fn2-sim-take-one (fn2-core fn2-sim fn2-own) :part nil
  :carriers ((fn2-core 1 :prefix "-CORE" :hints (("Goal" :in-theory (enable fn2-core-wfp)))) (fn2-sim 2 :invariant fn2-sim-ready :prefix "-SIM" :suffix "-READY" :hints (("Goal" :in-theory (enable fn2-sim-ready)))) (fn2-own 3 :prefix "-OWN"))
  :hints (("Goal" :in-theory (enable fn2-core-wfp fn2-sim-ready))))

(defun fn2-sim-take-prefix (left taken fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :measure (nfix left)
                  :guard (and (fn2-core-wfp fn2-core) (fn2-sim-ready fn2-sim)
                              (fn2-own-wfp fn2-own) (natp left) (natp taken))))
  (if (zp left) (mv taken fn2-core fn2-sim fn2-own)
    (mv-let (found fn2-core fn2-sim fn2-own) (fn2-sim-take-one fn2-core fn2-sim fn2-own)
      (if (not found) (mv taken fn2-core fn2-sim fn2-own)
        (fn2-sim-take-prefix (- left 1) (+ taken 1) fn2-core fn2-sim fn2-own)))))
(fn2-sim-preserves fn2-sim-take-prefix (left taken fn2-core fn2-sim fn2-own) :part nil
  :carriers ((fn2-core 1 :prefix "-CORE" :hints (("Goal" :in-theory (enable fn2-core-wfp)))) (fn2-sim 2 :invariant fn2-sim-ready :prefix "-SIM" :suffix "-READY") (fn2-own 3 :prefix "-OWN")))

(defun fn2-sim-take (limit fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own)
                  :guard (and (fn2-core-wfp fn2-core) (fn2-sim-ready fn2-sim)
                              (fn2-own-wfp fn2-own))))
  (mv-let (word fn2-sim) (fn2-sim-random fn2-sim)
    (fn2-sim-take-prefix (if (unsigned-byte-p 32 limit) (mod word (+ 1 limit)) 0)
                         0 fn2-core fn2-sim fn2-own)))
(fn2-sim-preserves fn2-sim-take (limit fn2-core fn2-sim fn2-own) :part nil
  :carriers ((fn2-core 1 :prefix "-CORE" :hints (("Goal" :in-theory (enable fn2-core-wfp)))) (fn2-sim 2 :invariant fn2-sim-ready :prefix "-SIM" :suffix "-READY") (fn2-own 3 :prefix "-OWN")))

(defun fn2-sim-client-feed (slot nonce left byte fn2-sim-network)
  (declare (xargs :stobjs fn2-sim-network :measure (nfix left)
                  :guard (and (fn2-sim-network-wfp fn2-sim-network)
                              (natp left) (unsigned-byte-p 8 byte))))
  (if (zp left) fn2-sim-network
    (mv-let (code fn2-sim-network) (fn2-network-client-byte slot nonce byte fn2-sim-network)
      (if (eq code :ok)
          (fn2-sim-client-feed slot nonce (- left 1) (if (= byte 255) 0 (+ byte 1)) fn2-sim-network)
        fn2-sim-network))))
(fn2-sim-network-preserves fn2-sim-client-feed (slot nonce left byte fn2-sim-network) :position nil :prefix "" :rows nil :wfp-type nil)

; One physical operation, before any observation is posted. The scalar return
; describes what happened; a blocked pipe is retained with no synthetic result.
(defun fn2-sim-amount (kind len fault word)
  (declare (xargs :guard (and (natp len) (natp word))))
  (cond ((and (equal fault *fn2-fault-fragment*) (equal kind *fn2-action-receive*) (< 0 len))
         (+ 1 (mod word len)))
        ((or (and (equal fault *fn2-fault-short-send*) (equal kind *fn2-action-send*))
             (and (equal fault *fn2-fault-short-write*) (equal kind *fn2-action-write*)))
         (mod word (+ 1 len)))
        (t (nfix len))))
(defthm fn2-sim-amount-natural
  (implies (and (natp len) (natp word)) (natp (fn2-sim-amount kind len fault word)))
  :rule-classes :type-prescription)
(in-theory (disable fn2-sim-amount))
(defun fn2-sim-redirect (offset nbytes kind fault)
  (declare (xargs :guard (and (natp offset) (natp nbytes))))
  (if (and (< 0 nbytes)
           (or (and (equal fault *fn2-fault-misread*) (equal kind *fn2-action-read*))
               (and (equal fault *fn2-fault-miswrite*) (equal kind *fn2-action-write*))))
      (mod (+ offset *fn2-format-sector-bytes*) nbytes) (nfix offset)))
(defthm fn2-sim-redirect-natural
  (implies (and (natp offset) (natp nbytes))
           (natp (fn2-sim-redirect offset nbytes kind fault)))
  :rule-classes :type-prescription)
(in-theory (disable fn2-sim-redirect))

(in-theory (disable fn2-op-input-kindp fn2-op-output-kindp))

; Does this fence's captured image contain a version it would persist?
(defun fn2-sim-fence-dirty-p (i fence fn2-sim-storage)
  (declare (xargs :stobjs fn2-sim-storage
                  :guard (and (fn2-sim-storage-wfp fn2-sim-storage) (natp i))
                  :guard-hints (("Goal" :in-theory (enable fn2-sim-storage-rows)))
                  :measure (nfix (- (fn2-sim-storage-rows fn2-sim-storage) (nfix i)))))
  (let ((slot (fn2-storage-fence-slot-of fence fn2-sim-storage)))
    (if (or (not slot) (not (natp i)) (not (natp (fn2-sim-storage-rows fn2-sim-storage)))
            (>= i (fn2-sim-storage-rows fn2-sim-storage))) nil
      (let ((j (+ (* slot (fn2-sim-storage-rows fn2-sim-storage)) i)))
        (and (< j (fn2-storage-snapshot-stamp-length fn2-sim-storage))
             (or (< (fn2-sim-storage-durable-stamp i fn2-sim-storage)
                    (fn2-storage-snapshot-stampi j fn2-sim-storage))
                 (fn2-sim-fence-dirty-p (+ i 1) fence fn2-sim-storage)))))))
(in-theory (disable fn2-sim-fence-dirty-p))

(defthm fn2-sim-transfer-count-natural
  (natp (mv-nth 1 (fn2-sim-transfer kind cap nonce rslot rgen off len okind oslot ogen opslot opgen
                    offset redirect stamp fua fault salt i fn2-pool fn2-sim-network fn2-sim-storage fn2-own)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn2-sim-transfer))))

(defun fn2-sim-physical-landed-p (kind fault code count len offset disk-bytes disk-alive dirty-fence lying)
  (declare (xargs :guard (and (acl2-numberp kind) (acl2-numberp fault)
                              (natp count) (natp len) (natp offset) (natp disk-bytes))))
  (cond ((member-equal fault `(,*fn2-fault-fragment* ,*fn2-fault-short-send* ,*fn2-fault-short-write*))
                          (and (eq code :ok) (< count len)
                               (or (and (= fault *fn2-fault-fragment*) (= kind *fn2-action-receive*))
                                   (and (= fault *fn2-fault-short-send*) (= kind *fn2-action-send*))
                                   (and (= fault *fn2-fault-short-write*) (= kind *fn2-action-write*)))))
                         ((member-equal fault `(,*fn2-fault-misread* ,*fn2-fault-miswrite*)) (and (< 0 count) (not (= offset (fn2-sim-redirect offset disk-bytes kind fault)))))
                         ((equal fault *fn2-fault-reset*) (eq code :reset))
                         ((equal fault *fn2-fault-read-io*) (and disk-alive (= kind *fn2-action-read*) (eq code :io)))
                         ((equal fault *fn2-fault-no-space*) (and (= kind *fn2-action-write*) (eq code :no-space)))
                         ((equal fault *fn2-fault-lying-flush*) (and (= kind *fn2-action-fence*) dirty-fence lying (eq code :ok)))
                         ((equal fault *fn2-fault-flush-io*) (and disk-alive (= kind *fn2-action-fence*) (eq code :io)))
                         (t nil)))
(in-theory (disable fn2-sim-physical-landed-p))

; The landing counter changes only parent scalars, independent of child readiness.
(local
 (progn
(defthm fn2-sim-land-parent-type
 (implies (fn2-simp fn2-sim) (fn2-simp (fn2-sim-land fault fn2-sim)))
 :hints (("Goal" :in-theory (enable fn2-sim-land))))
(defthm fn2-sim-land-parent-wfp
 (implies (and (fn2-simp fn2-sim) (fn2-sim-wfp fn2-sim))
  (fn2-sim-wfp (fn2-sim-land fault fn2-sim)))
 :hints (("Goal" :in-theory (enable fn2-sim-land))))

(in-theory (disable fn2-sim-land-type fn2-sim-land-wfp))))

(defun fn2-sim-physical-act (kind cap nonce rslot rgen off len n okind oslot ogen slot gen offset stamp fua fault word lying
                                  fn2-core fn2-sim-network fn2-sim-storage fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim-network fn2-sim-storage fn2-own)
                  :guard (and (fn2-core-wfp fn2-core) (fn2-sim-network-wfp fn2-sim-network)
                              (fn2-sim-storage-wfp fn2-sim-storage) (fn2-own-wfp fn2-own)
                              (natp len) (natp n) (natp off) (natp offset) (natp word)
                              (unsigned-byte-p 60 stamp) (unsigned-byte-p 60 rgen)
                              (unsigned-byte-p 32 word))
                  :guard-hints (("Goal" :in-theory (enable fn2-core-wfp)))))
  (cond
   ((or (fn2-op-input-kindp kind) (fn2-op-output-kindp kind))
    (let* ((nbytes (fn2-sim-storage-rows fn2-sim-storage))
           (redirect (fn2-sim-redirect offset nbytes kind fault)))
      (stobj-let ((fn2-pool (fn2-core-pool fn2-core))
                  (fn2-ops (fn2-core-ops fn2-core)))
        (code count fn2-pool fn2-sim-network fn2-sim-storage fn2-own)
        (let ((fn2-own (if (fn2-op-output-kindp kind)
                          (fn2-own-observe-output-range-parts slot gen rslot rgen off len
                            fn2-pool fn2-ops fn2-own)
                        fn2-own)))
          (fn2-sim-transfer kind cap nonce rslot rgen off n okind oslot ogen slot gen
                            offset redirect stamp fua fault word 0
                            fn2-pool fn2-sim-network fn2-sim-storage fn2-own))
        (mv code count 0 fn2-core fn2-sim-network fn2-sim-storage fn2-own))))
   ((or (equal kind *fn2-action-accept*) (equal kind *fn2-action-connect*))
    (let ((index (if (< 0 (fn2-sim-network-rows fn2-sim-network))
                     (mod word (fn2-sim-network-rows fn2-sim-network)) 0)))
      (mv-let (code nonce fn2-sim-network) (fn2-network-accept index fn2-sim-network)
        (let ((fn2-sim-network
               (if (eq code :ok) (fn2-sim-client-feed index nonce 256 (mod word 256) fn2-sim-network)
                 fn2-sim-network)))
          (mv code index nonce fn2-core fn2-sim-network fn2-sim-storage fn2-own)))))
   ((equal kind *fn2-action-close*)
    (mv-let (code fn2-sim-network)
      (if (equal okind *fn2-listener-kind*)
          (fn2-network-refuse cap nonce fn2-sim-network)
        (fn2-network-close cap nonce fn2-sim-network))
      (declare (ignore code))
      (mv :ok 0 0 fn2-core fn2-sim-network fn2-sim-storage fn2-own)))
   ((equal kind *fn2-action-fence*)
    (mv-let (code fn2-sim-storage)
      (fn2-storage-fence-complete slot (equal fault *fn2-fault-flush-io*) lying fn2-sim-storage)
      (mv code 0 0 fn2-core fn2-sim-network fn2-sim-storage fn2-own)))
   ((and (equal kind *fn2-action-tls-start*) (equal fault *fn2-fault-reset*))
    (mv :handshake 0 0 fn2-core fn2-sim-network fn2-sim-storage fn2-own))
   (t (mv :ok 0 0 fn2-core fn2-sim-network fn2-sim-storage fn2-own))))


; Shape facts of the physical dispatch, stated once; the physical proofs
; below see only these and never expand the six dispatch branches.
(local (in-theory (enable fn2-core-wfp)))
(local
 (defmacro fn2-sim-physical-act-fact (name pred position)
   `(defthm ,name
      (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                    (fn2-sim-networkp fn2-sim-network) (fn2-sim-network-wfp fn2-sim-network)
                    (fn2-sim-storagep fn2-sim-storage) (fn2-sim-storage-wfp fn2-sim-storage)
                    (fn2-ownp fn2-own) (fn2-own-wfp fn2-own)
                    (natp len) (natp n) (natp off) (natp offset) (natp word)
                    (unsigned-byte-p 60 stamp) (unsigned-byte-p 60 rgen) (unsigned-byte-p 32 word))
               (,pred (mv-nth ,position
                       (fn2-sim-physical-act kind cap nonce rslot rgen off len n okind oslot ogen slot gen
                                             offset stamp fua fault word lying
                                             fn2-core fn2-sim-network fn2-sim-storage fn2-own)))))))
(local (fn2-sim-physical-act-fact fn2-sim-physical-act-core-type fn2-corep 3))
(local (fn2-sim-physical-act-fact fn2-sim-physical-act-core-wfp fn2-core-wfp 3))
(local (fn2-sim-physical-act-fact fn2-sim-physical-act-network-type fn2-sim-networkp 4))
(local (fn2-sim-physical-act-fact fn2-sim-physical-act-network-wfp fn2-sim-network-wfp 4))
(local (fn2-sim-physical-act-fact fn2-sim-physical-act-storage-type fn2-sim-storagep 5))
(local (fn2-sim-physical-act-fact fn2-sim-physical-act-storage-wfp fn2-sim-storage-wfp 5))
(local (fn2-sim-physical-act-fact fn2-sim-physical-act-own-type fn2-ownp 6))
(local (fn2-sim-physical-act-fact fn2-sim-physical-act-own-wfp fn2-own-wfp 6))
(local (fn2-sim-physical-act-fact fn2-sim-physical-act-count-natp natp 1))
(local (in-theory (disable fn2-core-wfp)))
(in-theory (disable fn2-sim-physical-act))
(defun fn2-sim-physical (slot fault word fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own)
                  :guard (and (fn2-core-wfp fn2-core) (fn2-sim-ready fn2-sim)
                              (fn2-own-wfp fn2-own))
                  :guard-hints (("Goal" :in-theory (e/d (fn2-sim-storage-rows fn2-core-wfp) (fn2-sim-ready))))))
  (if (not (and (natp slot) (< slot (fn2-sim-rows fn2-sim))
                (unsigned-byte-p 32 word) (natp fault)))
      (mv :invalid 0 0 fn2-core fn2-sim fn2-own)
    (let* ((kind (fn2-sim-kind slot fn2-sim))
           (cap (fn2-sim-cap-index slot fn2-sim)) (nonce (fn2-sim-cap-nonce slot fn2-sim))
           (rslot (fn2-sim-range-slot slot fn2-sim)) (rgen (fn2-sim-range-gen slot fn2-sim))
           (off (fn2-sim-range-off slot fn2-sim)) (len (fn2-sim-range-len slot fn2-sim))
           (okind (fn2-sim-owner-kind slot fn2-sim)) (oslot (fn2-sim-owner-slot slot fn2-sim))
           (ogen (fn2-sim-owner-gen slot fn2-sim)) (gen (fn2-sim-gen slot fn2-sim))
           (offset (fn2-sim-storage-offset slot fn2-sim))
           (stamp (min *fn2-u60-max* (+ 1 (fn2-sim-stamp fn2-sim))))
           (disk-bytes (stobj-let ((fn2-sim-storage (fn2-sim-disk fn2-sim)))
                         (n) (fn2-sim-storage-rows fn2-sim-storage) n))
           (disk-alive (stobj-let ((fn2-sim-storage (fn2-sim-disk fn2-sim)))
                         (alive) (= (fn2-storage-dead fn2-sim-storage) 0) alive))
           (dirty-fence (stobj-let ((fn2-sim-storage (fn2-sim-disk fn2-sim)))
                          (dirty) (and (= fault *fn2-fault-lying-flush*) (= kind *fn2-action-fence*) (fn2-sim-fence-dirty-p 0 slot fn2-sim-storage)) dirty))
           (fua (= (fn2-sim-fua slot fn2-sim) 1))
           (lying (and (equal fault *fn2-fault-lying-flush*) (eq (fn2-sim-profile-name fn2-sim) :broad)))
           (n (fn2-sim-amount kind len fault word))
           (fn2-sim (update-fn2-sim-stamp stamp fn2-sim)))
      (stobj-let ((fn2-sim-network (fn2-sim-net fn2-sim))
                  (fn2-sim-storage (fn2-sim-disk fn2-sim)))
        (code count aux fn2-core fn2-sim-network fn2-sim-storage fn2-own)
        (fn2-sim-physical-act kind cap nonce rslot rgen off len n okind oslot ogen slot gen offset stamp fua fault word lying
                              fn2-core fn2-sim-network fn2-sim-storage fn2-own)
        (let ((fn2-sim
               (if (fn2-sim-physical-landed-p kind fault code count len offset disk-bytes disk-alive dirty-fence lying)
                   (fn2-sim-land fault fn2-sim) fn2-sim)))
          (mv code count aux fn2-core fn2-sim fn2-own))))))
(fn2-sim-preserves fn2-sim-physical (slot fault word fn2-core fn2-sim fn2-own) :part 1
  :carriers ((fn2-core 3 :prefix "-CORE" :hints (("Goal" :in-theory (enable fn2-core-wfp)))) (fn2-sim 4 :invariant fn2-sim-ready :prefix "-SIM" :suffix "-READY" :hints (("Goal" :in-theory (enable fn2-sim-ready)))) (fn2-own 5 :prefix "-OWN"))
  :hints (("Goal" :in-theory (enable fn2-core-wfp fn2-sim-ready))))
(fn2-sim-preserves fn2-sim-physical (slot fault word fn2-core fn2-sim fn2-own) :part 2
  :carriers ((fn2-core 3 :prefix "-CORE" :hints (("Goal" :in-theory (enable fn2-core-wfp)))) (fn2-sim 4 :invariant fn2-sim-ready :prefix "-SIM" :suffix "-READY" :hints (("Goal" :in-theory (enable fn2-sim-ready)))) (fn2-own 5 :prefix "-OWN"))
  :hints (("Goal" :in-theory (enable fn2-core-wfp fn2-sim-ready))))
(fn2-sim-preserves fn2-sim-physical (slot fault word fn2-core fn2-sim fn2-own) :part 3
  :carriers ((fn2-core 3 :prefix "-CORE" :hints (("Goal" :in-theory (enable fn2-core-wfp)))) (fn2-sim 4 :invariant fn2-sim-ready :prefix "-SIM" :suffix "-READY" :hints (("Goal" :in-theory (enable fn2-sim-ready)))) (fn2-own 5 :prefix "-OWN"))
  :hints (("Goal" :in-theory (enable fn2-core-wfp fn2-sim-ready))))
(fn2-sim-preserves fn2-sim-physical (slot fault word fn2-core fn2-sim fn2-own) :part 4
  :carriers ((fn2-core 3 :prefix "-CORE" :hints (("Goal" :in-theory (enable fn2-core-wfp)))) (fn2-sim 4 :invariant fn2-sim-ready :prefix "-SIM" :suffix "-READY" :hints (("Goal" :in-theory (enable fn2-sim-ready)))) (fn2-own 5 :prefix "-OWN"))
  :hints (("Goal" :in-theory (enable fn2-core-wfp fn2-sim-ready))))
(fn2-sim-preserves fn2-sim-physical (slot fault word fn2-core fn2-sim fn2-own) :part 5
  :carriers ((fn2-core 3 :prefix "-CORE" :hints (("Goal" :in-theory (enable fn2-core-wfp)))) (fn2-sim 4 :invariant fn2-sim-ready :prefix "-SIM" :suffix "-READY" :hints (("Goal" :in-theory (enable fn2-sim-ready)))) (fn2-own 5 :prefix "-OWN"))
  :hints (("Goal" :in-theory (enable fn2-core-wfp fn2-sim-ready))))
(fn2-sim-preserves fn2-sim-physical (slot fault word fn2-core fn2-sim fn2-own) :part 6
  :carriers ((fn2-core 3 :prefix "-CORE" :hints (("Goal" :in-theory (enable fn2-core-wfp)))) (fn2-sim 4 :invariant fn2-sim-ready :prefix "-SIM" :suffix "-READY" :hints (("Goal" :in-theory (enable fn2-sim-ready)))) (fn2-own 5 :prefix "-OWN"))
  :hints (("Goal" :in-theory (enable fn2-core-wfp fn2-sim-ready))))
(fn2-sim-preserves fn2-sim-physical (slot fault word fn2-core fn2-sim fn2-own) :part 7
  :carriers ((fn2-core 3 :prefix "-CORE" :hints (("Goal" :in-theory (enable fn2-core-wfp)))) (fn2-sim 4 :invariant fn2-sim-ready :prefix "-SIM" :suffix "-READY" :hints (("Goal" :in-theory (enable fn2-sim-ready)))) (fn2-own 5 :prefix "-OWN"))
  :hints (("Goal" :in-theory (enable fn2-core-wfp fn2-sim-ready))))
(defthm fn2-sim-physical-rows
  (equal (nth *fn2-sim-rows* (mv-nth 4 (fn2-sim-physical slot fault word fn2-core fn2-sim fn2-own)))
         (nth *fn2-sim-rows* fn2-sim))
  :hints (("Goal" :in-theory (enable fn2-sim-physical fn2-core-wfp fn2-sim-ready))))
(defthm fn2-sim-physical-child-shapes
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                (fn2-simp fn2-sim) (fn2-sim-ready fn2-sim)
                (fn2-ownp fn2-own) (fn2-own-wfp fn2-own))
           (and
            (fn2-pool-wfp (fn2-core-pool (mv-nth 3 (fn2-sim-physical slot fault word fn2-core fn2-sim fn2-own))))
            (fn2-ops-wfp (fn2-core-ops (mv-nth 3 (fn2-sim-physical slot fault word fn2-core fn2-sim fn2-own))))
            (fn2-sim-wfp (mv-nth 4 (fn2-sim-physical slot fault word fn2-core fn2-sim fn2-own)))
            (fn2-sim-network-wfp (nth *fn2-sim-net* (mv-nth 4 (fn2-sim-physical slot fault word fn2-core fn2-sim fn2-own))))
            (fn2-sim-storage-wfp (nth *fn2-sim-disk* (mv-nth 4 (fn2-sim-physical slot fault word fn2-core fn2-sim fn2-own))))))
  :hints (("Goal" :use (fn2-sim-physical-core-wfp fn2-sim-physical-sim-ready)
                  :in-theory (e/d (fn2-core-wfp fn2-sim-ready) (fn2-sim-physical-core-wfp fn2-sim-physical-sim-ready)))))

(defun fn2-sim-cancel-target (slot fn2-sim)
  (declare (xargs :stobjs fn2-sim :guard (fn2-sim-ready fn2-sim)
                  :guard-hints (("Goal" :in-theory (enable fn2-sim-ready)))))
  (if (not (and (natp slot) (< slot (fn2-sim-rows fn2-sim))))
      (mv nil fn2-sim)
    (let ((target (fn2-sim-cancel-slot slot fn2-sim))
          (gen (fn2-sim-cancel-gen slot fn2-sim)))
      (if (and (< target (fn2-sim-rows fn2-sim))
               (= (fn2-sim-gen target fn2-sim) gen)
               (= (fn2-sim-active target fn2-sim) 1)
               (not (= (fn2-sim-kind target fn2-sim) *fn2-action-close*)))
          (let* ((fencep (= (fn2-sim-kind target fn2-sim) *fn2-action-fence*))
                 (fn2-sim (fn2-sim-set-cancelled target 1 fn2-sim))
                 ; The cancelled target skips physical completion. Discard
                 ; its snapshot now; its terminal lifecycle remains owed.
                 (fn2-sim
                  (if fencep
                      (stobj-let ((fn2-sim-storage (fn2-sim-disk fn2-sim)))
                        (code fn2-sim-storage)
                        (fn2-storage-fence-complete target t nil fn2-sim-storage)
                        (let ((ignored code)) (declare (ignore ignored)) fn2-sim))
                    fn2-sim)))
            (mv t fn2-sim))
        (mv nil fn2-sim)))))
(fn2-sim-preserves fn2-sim-cancel-target (slot fn2-sim) :forward t
  :hyps ((fn2-simp fn2-sim) (fn2-sim-ready fn2-sim))
  :specs (("-TYPE" fn2-simp 1) ("-READY" fn2-sim-ready 1) ("-WFP" fn2-sim-wfp 1))
  :hints (("Goal" :in-theory (enable fn2-sim-ready))))
(fn2-sim-preserves fn2-sim-cancel-target (slot fn2-sim) :disable nil
  :specs (("-RAW-ROWS" (lambda (s) (nth *fn2-sim-rows* s)) 1 :frame fn2-sim))
  :hints (("Goal" :in-theory (enable fn2-sim-cancel-target))))

(defun fn2-sim-unused-op (left index fn2-ops)
  (declare (xargs :stobjs fn2-ops :measure (nfix left)
                  :guard (and (fn2-ops-wfp fn2-ops) (natp left) (natp index))))
  (if (or (zp left) (>= index (fn2-ops-rows fn2-ops))) (mv *fn2-none* 0)
    (if (= (fn2-ops-phase index fn2-ops) *fn2-op-phase-free*)
        (mv index (fn2-ops-gen index fn2-ops))
      (fn2-sim-unused-op (- left 1) (+ index 1) fn2-ops))))

; Invalid observations are tested BEFORE the genuine terminal. A duplicate is
; tested AFTER it. EXPECTED-STRAY makes OWN compare an exact snapshot, including
; ring contents and counters, independently of the implementation validator.
(defun fn2-sim-inject (slot fault fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own)
                  :guard (and (fn2-core-wfp fn2-core) (fn2-sim-ready fn2-sim)
                              (fn2-own-wfp fn2-own))
                  :guard-hints (("Goal" :in-theory (enable fn2-core-wfp fn2-sim-ready)))))
  (if (not (and (natp slot) (< slot (fn2-sim-rows fn2-sim))
                (member-equal fault `(,*fn2-fault-stale* ,*fn2-fault-forged* ,*fn2-fault-overcount* ,*fn2-fault-malformed*))))
      (mv :ok fn2-core fn2-sim fn2-own)
    (let* ((gen (fn2-sim-gen slot fn2-sim)) (kind (fn2-sim-kind slot fn2-sim))
           (evkind (fn2-terminal-event kind))
           (old-gen (fn2-sim-last-gen slot fn2-sim))
           (bad-gen (if (< old-gen gen) old-gen (if (= gen 0) 1 (- gen 1))))
           (bad-count (if (or (fn2-op-input-kindp kind) (fn2-op-output-kindp kind))
                          (+ 1 (fn2-sim-range-len slot fn2-sim)) 4294967296)))
      (mv-let (unused unused-gen)
        (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
          (unused unused-gen)
          (fn2-sim-unused-op (fn2-ops-rows fn2-ops) 0 fn2-ops)
          (mv unused unused-gen))
        (fn2-sim-post 0 (if (equal fault *fn2-fault-forged*) unused slot)
          (cond ((equal fault *fn2-fault-stale*) bad-gen) ((equal fault *fn2-fault-forged*) unused-gen) (t gen))
          (if (equal fault *fn2-fault-malformed*) 255 evkind) *fn2-outcome-done* *fn2-reason-none*
          (if (equal fault *fn2-fault-overcount*) bad-count 0) 0 0 fault t fn2-core fn2-sim fn2-own)))))
(fn2-sim-preserves fn2-sim-inject (slot fault fn2-core fn2-sim fn2-own) :part nil
  :carriers ((fn2-core 1 :prefix "-CORE" :hints (("Goal" :in-theory (enable fn2-core-wfp)))) (fn2-sim 2 :invariant fn2-sim-ready :prefix "-SIM" :suffix "-READY" :hints (("Goal" :in-theory (enable fn2-sim-ready)))) (fn2-own 3 :prefix "-OWN"))
  :hints (("Goal" :in-theory (enable fn2-core-wfp fn2-sim-ready))))
(fn2-sim-preserves fn2-sim-inject (slot fault fn2-core fn2-sim fn2-own) :disable nil
  :specs (("-RAW-ROWS" (lambda (s) (nth *fn2-sim-rows* s)) 2 :frame fn2-sim))
  :hints (("Goal" :in-theory (enable fn2-sim-inject))))

(in-theory (disable logxor))

; A tear lands only if the selected unit actually changes durable bytes.
(defun fn2-sim-tear-changes-p (i end byte fn2-sim-storage)
  (declare (xargs :stobjs fn2-sim-storage
                  :guard (and (fn2-sim-storage-wfp fn2-sim-storage) (natp i) (natp end))
                  :guard-hints (("Goal" :in-theory (enable fn2-sim-storage-rows)))
                  :measure (nfix (- (nfix end) (nfix i)))))
  (if (or (not (natp i)) (not (natp end)) (>= i end)
          (>= i (fn2-sim-storage-rows fn2-sim-storage))) nil
    (or (and (<= (fn2-sim-storage-durable-stamp i fn2-sim-storage)
                 (fn2-sim-storage-stamp i fn2-sim-storage))
             (not (equal byte (fn2-sim-storage-durable i fn2-sim-storage))))
        (fn2-sim-tear-changes-p (+ i 1) end byte fn2-sim-storage))))
(in-theory (disable fn2-sim-tear-changes-p))

(defun fn2-sim-environment-landed-p (slot fault word fn2-sim)
  (declare (xargs :stobjs fn2-sim :guard (fn2-sim-ready fn2-sim)
                  :guard-hints (("Goal" :in-theory (enable fn2-sim-storage-rows fn2-sim-ready)))))
  (if (not (and (natp slot) (< slot (fn2-sim-rows fn2-sim))
                (unsigned-byte-p 32 word))) nil
    (let ((cap (fn2-sim-cap-index slot fn2-sim)) (nonce (fn2-sim-cap-nonce slot fn2-sim)))
      (stobj-let ((fn2-sim-network (fn2-sim-net fn2-sim))
                  (fn2-sim-storage (fn2-sim-disk fn2-sim)))
        (landed)
        (cond ((member-equal fault `(,*fn2-fault-half-open* ,*fn2-fault-nonreading*))
                       (and (eq (fn2-network-cap-code cap nonce fn2-sim-network) :ok)
                            (if (= fault *fn2-fault-half-open*) (= (fn2-sim-network-half-open cap fn2-sim-network) 0)
                              (= (fn2-sim-network-nonreading cap fn2-sim-network) 0))))
                      ((equal fault *fn2-fault-dead*) (= (fn2-storage-dead fn2-sim-storage) 0))
                      ((equal fault *fn2-fault-bitrot*) (< 0 (fn2-sim-storage-rows fn2-sim-storage)))
                      ((equal fault *fn2-fault-tear*)
                       (and (<= 512 (fn2-sim-storage-rows fn2-sim-storage))
                            (fn2-storage-unit-pendingp (mod word (floor (fn2-sim-storage-rows fn2-sim-storage) 512)) fn2-sim-storage)
                            (let ((start (* 512 (mod word (floor (fn2-sim-storage-rows fn2-sim-storage) 512)))))
                              (fn2-sim-tear-changes-p start (+ start 512)
                                (if (= (mod word 2) 0) 0 (mod word 256)) fn2-sim-storage))))
                      (t nil))
        landed))))
(in-theory (disable fn2-sim-environment-landed-p))

(defun fn2-sim-environment (slot fault word fn2-sim)
  (declare (xargs :stobjs fn2-sim :guard (fn2-sim-ready fn2-sim)
                  :guard-hints (("Goal" :in-theory (enable fn2-sim-storage-rows fn2-sim-ready)))))
  (if (not (and (natp slot) (< slot (fn2-sim-rows fn2-sim))
                (unsigned-byte-p 32 word))) fn2-sim
    (let ((landed (fn2-sim-environment-landed-p slot fault word fn2-sim))
          (cap (fn2-sim-cap-index slot fn2-sim)) (nonce (fn2-sim-cap-nonce slot fn2-sim))
          (reset-range (+ 1 (fn2-sim-range-len slot fn2-sim))))
      (stobj-let ((fn2-sim-network (fn2-sim-net fn2-sim))
                  (fn2-sim-storage (fn2-sim-disk fn2-sim)))
        (fn2-sim-network fn2-sim-storage)
        (let* (
               (fn2-sim-network
                 (if (member-equal fault `(,*fn2-fault-reset* ,*fn2-fault-half-open* ,*fn2-fault-nonreading*))
                     (mv-let (ignored fn2-sim-network)
                       (fn2-network-faults cap nonce (if (equal fault *fn2-fault-half-open*) 1 0) (if (equal fault *fn2-fault-nonreading*) 1 0)
                                            (if (equal fault *fn2-fault-reset*) 1 0) (mod word reset-range) fn2-sim-network)
                       (declare (ignore ignored)) fn2-sim-network)
                   fn2-sim-network))
               (nbytes (fn2-sim-storage-rows fn2-sim-storage))
               (fn2-sim-storage
                (cond ((equal fault *fn2-fault-dead*) (fn2-storage-kill-device fn2-sim-storage))
                      ((and (equal fault *fn2-fault-bitrot*) (< 0 nbytes))
                       (let* ((address (mod word nbytes))
                              (byte (mod (logxor 1 (fn2-sim-storage-durable address fn2-sim-storage)) 256)))
                         (fn2-storage-corrupt-byte address byte fn2-sim-storage)))
                      ((and (equal fault *fn2-fault-tear*) (<= 512 nbytes))
                       (fn2-storage-crash-unit (mod word (floor nbytes 512))
                                               (+ 2 (mod word 2)) (mod word 256) fn2-sim-storage))
                      (t fn2-sim-storage))))
          (mv fn2-sim-network fn2-sim-storage))
        (if landed (fn2-sim-land fault fn2-sim) fn2-sim)))))
(fn2-sim-preserves fn2-sim-environment (slot fault word fn2-sim) :forward t
  :hyps ((fn2-simp fn2-sim) (fn2-sim-ready fn2-sim))
  :specs (("-TYPE" fn2-simp nil) ("-READY" fn2-sim-ready nil) ("-WFP" fn2-sim-wfp nil))
  :hints (("Goal" :in-theory (enable fn2-sim-ready))))
(defthm fn2-sim-environment-rows
 (equal (fn2-sim-rows (fn2-sim-environment slot fault word fn2-sim)) (fn2-sim-rows fn2-sim))
 :hints (("Goal" :in-theory (enable fn2-sim-environment fn2-sim-rows fn2-sim-ready))))

(defun fn2-sim-crash-units (unit fn2-sim)
  (declare (xargs :stobjs fn2-sim :measure (nfix unit)
                  :guard (and (fn2-sim-ready fn2-sim) (natp unit))
                  :guard-hints (("Goal" :in-theory (enable fn2-sim-ready)))))
  (if (or (not (unsigned-byte-p 32 unit)) (zp unit)) fn2-sim
    (mv-let (word fn2-sim) (fn2-sim-random fn2-sim)
      (let ((i (- unit 1)))
        (stobj-let ((fn2-sim-storage (fn2-sim-disk fn2-sim)))
          (fn2-sim-storage)
          (fn2-storage-crash-unit i (mod word 4) (mod (floor word 4) 256) fn2-sim-storage)
          (fn2-sim-crash-units i fn2-sim))))))
(fn2-sim-preserves fn2-sim-crash-units (unit fn2-sim) :forward t
  :hyps ((fn2-simp fn2-sim) (fn2-sim-ready fn2-sim))
  :specs (("-TYPE" fn2-simp nil) ("-READY" fn2-sim-ready nil) ("-WFP" fn2-sim-wfp nil))
  :hints (("Goal" :in-theory (enable fn2-sim-ready))))

(defun fn2-sim-find-write (left index fn2-sim)
  (declare (xargs :stobjs fn2-sim :measure (nfix left)
                  :guard (and (fn2-sim-ready fn2-sim) (natp left) (natp index))
                  :guard-hints (("Goal" :in-theory (enable fn2-sim-ready)))))
  (if (or (zp left) (= (fn2-sim-rows fn2-sim) 0)) (mv nil 0)
    (let ((slot (mod index (fn2-sim-rows fn2-sim))))
      (if (and (= (fn2-sim-active slot fn2-sim) 1)
               (= (fn2-sim-kind slot fn2-sim) *fn2-action-write*))
          (mv t slot)
        (fn2-sim-find-write (- left 1) (+ slot 1) fn2-sim)))))

