(in-package "ACL2")
(include-book "sim-state-data")
(include-book "prng")
(include-book "../books/fnv")

; These raw projection facts seed type reasoning after a child accessor
; unfolds; scalar updates can therefore keep their generated NTH facts.
(defthm fn2-sim-net-nth-type-forward
  (implies (fn2-simp fn2-sim)
           (fn2-sim-networkp (nth *fn2-sim-net* fn2-sim)))
  :rule-classes :forward-chaining
  :hints (("Goal" :use fn2-sim-net-type :in-theory (disable fn2-sim-net-type))))
(defthm fn2-sim-disk-nth-type-forward
  (implies (fn2-simp fn2-sim)
           (fn2-sim-storagep (nth *fn2-sim-disk* fn2-sim)))
  :rule-classes :forward-chaining
  :hints (("Goal" :use fn2-sim-disk-type :in-theory (disable fn2-sim-disk-type))))

; Mirror generated numeric updater raw-read facts; child getters remain open.
(defthm update-fn2-sim-net-raw-nth
  (equal (nth k (update-fn2-sim-net child parent))
         (if (equal (nfix k) *fn2-sim-net*) child (nth k parent)))
  :hints (("Goal" :in-theory (enable update-fn2-sim-net))))
(defthm update-fn2-sim-disk-raw-nth
  (equal (nth k (update-fn2-sim-disk child parent))
         (if (equal (nfix k) *fn2-sim-disk*) child (nth k parent)))
  :hints (("Goal" :in-theory (enable update-fn2-sim-disk))))
(in-theory (disable update-fn2-sim-net update-fn2-sim-disk))

; Nonnumeric init metadata has the same opaque update/raw projection API.
(defmacro fn2-sim-metadata-raw (field index)
  (let ((write (fn2-columns-pre "UPDATE-" field)))
    `(progn
       (defthm ,(fn2-columns-sym write "-RAW-NTH")
         (equal (nth k (,write value parent))
                (if (equal (nfix k) ,index) value (nth k parent)))
         :hints (("Goal" :in-theory (enable ,write))))
       (in-theory (disable ,write)))))
(fn2-sim-metadata-raw fn2-sim-profile *fn2-sim-profile*)
(fn2-sim-metadata-raw fn2-sim-profile-name *fn2-sim-profile-name*)
(fn2-sim-metadata-raw fn2-sim-revision *fn2-sim-revision*)
(fn2-sim-metadata-raw fn2-sim-initial-seed *fn2-sim-initial-seed*)

(defun fn2-sim-random (fn2-sim)
  (declare (xargs :stobjs fn2-sim :guard (fn2-sim-ready fn2-sim)))
  (mv-let (word s0 s1 s2 s3)
    (fn2-prng-next (fn2-sim-s0 fn2-sim) (fn2-sim-s1 fn2-sim)
                   (fn2-sim-s2 fn2-sim) (fn2-sim-s3 fn2-sim))
    (let* ((fn2-sim (update-fn2-sim-s0 s0 fn2-sim))
           (fn2-sim (update-fn2-sim-s1 s1 fn2-sim))
           (fn2-sim (update-fn2-sim-s2 s2 fn2-sim))
           (fn2-sim (update-fn2-sim-s3 s3 fn2-sim)))
      (mv word fn2-sim))))
(defthm fn2-sim-random-word-type
  (unsigned-byte-p 32 (mv-nth 0 (fn2-sim-random fn2-sim))))
(fn2-word-facts fn2-sim-random-word (car (fn2-sim-random fn2-sim)) fn2-sim-random-word-type)
(fn2-sim-preserves fn2-sim-random (fn2-sim) :forward t
  :hyps ((fn2-simp fn2-sim) (fn2-sim-ready fn2-sim))
  :specs (("-TYPE" fn2-simp 1) ("-READY" fn2-sim-ready 1) ("-WFP" fn2-sim-wfp 1)))
(defthm fn2-sim-random-state-type
  (implies (fn2-simp fn2-sim)
           (fn2-simp (mv-nth 1 (fn2-sim-random fn2-sim))))
  :rule-classes (:rewrite (:forward-chaining :trigger-terms ((fn2-sim-random fn2-sim))))
  :hints (("Goal" :in-theory (enable fn2-sim-random))))

; A random draw changes only its four state words. This frame fact keeps
; nested and fixed-array metadata readable in composed guard proofs.
(defthm fn2-sim-random-frame
  (implies (and (not (equal (nfix i) *fn2-sim-s0*))
                (not (equal (nfix i) *fn2-sim-s1*))
                (not (equal (nfix i) *fn2-sim-s2*))
                (not (equal (nfix i) *fn2-sim-s3*)))
           (equal (nth i (mv-nth 1 (fn2-sim-random fn2-sim)))
                  (nth i fn2-sim)))
  :hints (("Goal" :in-theory (enable fn2-sim-random))))

(defun fn2-sim-force-fault (fault fn2-sim)
  (declare (xargs :stobjs fn2-sim :guard (fn2-sim-ready fn2-sim)))
  (update-fn2-sim-forced-fault (if (and (natp fault) (< fault *fn2-fault-none*)) fault *fn2-fault-none*) fn2-sim))
(fn2-sim-preserves fn2-sim-force-fault (fault fn2-sim) :forward t
  :hyps ((fn2-simp fn2-sim) (fn2-sim-ready fn2-sim))
  :specs (("-TYPE" fn2-simp nil) ("-READY" fn2-sim-ready nil) ("-WFP" fn2-sim-wfp nil)))

; FNV-1a-like word folding. A u60 payload is represented by two u32
; fragments, so shifts and multiplication never form a bignum at runtime.
(defun fn2-sim-fold (hash word)
  (declare (xargs :guard (and (unsigned-byte-p 32 hash) (unsigned-byte-p 60 word))))
  (let* ((lo (fn2-u32 word)) (hi (floor word 4294967296))
         (hash (fn2-fnv-step hash lo)))
    (fn2-fnv-step hash hi)))
(defthm fn2-sim-fold-type (unsigned-byte-p 32 (fn2-sim-fold hash word))
  :hints (("Goal" :in-theory (disable unsigned-byte-p logxor))))
(fn2-word-facts fn2-sim-fold (fn2-sim-fold hash word) fn2-sim-fold-type)
(in-theory (disable fn2-sim-fold))

(defthm fn2-sim-fault-mod-natp
 (implies (integerp word) (natp (mod word *fn2-fault-count*)))
 :rule-classes :type-prescription)
(defthm fn2-sim-fault-mod-bound
 (implies (integerp word) (< (mod word *fn2-fault-count*) *fn2-fault-count*))
 :rule-classes :linear)
(defthm fn2-sim-probability-word-type
 (implies (and (fn2-simp fn2-sim) (integerp word))
  (natp (nth (mod word *fn2-fault-count*) (nth *fn2-sim-probabilitiesi* fn2-sim))))
 :rule-classes :type-prescription
 :hints (("Goal" :use ((:instance fn2-sim-probabilitiesi-natp (i (mod word *fn2-fault-count*)))))))
(defthm fn2-sim-hits-word-type
 (implies (and (fn2-simp fn2-sim) (integerp word))
  (natp (nth (mod word *fn2-fault-count*) (nth *fn2-sim-hitsi* fn2-sim))))
 :rule-classes :type-prescription
 :hints (("Goal" :use ((:instance fn2-sim-hitsi-natp (i (mod word *fn2-fault-count*)))))))
(defun fn2-sim-choose-fault (fn2-sim)
  (declare (xargs :stobjs fn2-sim :guard (fn2-sim-ready fn2-sim)
                  :guard-hints (("Goal" :use ((:instance fn2-sim-random-state-type)
                                               (:instance fn2-sim-random-ready))
                                        :in-theory (disable fn2-sim-random-state-type fn2-sim-random-ready)))))
  (mv-let (word fn2-sim) (fn2-sim-random fn2-sim)
    (let* ((forced (fn2-sim-forced-fault fn2-sim))
           (candidate (if (< forced *fn2-fault-none*) forced (mod word *fn2-fault-count*)))
           (coin (mod (floor word *fn2-fault-count*) 256))
           (hit (and (< 0 (fn2-sim-fault-budget fn2-sim))
                     (or (< forced *fn2-fault-none*) (< coin (fn2-sim-probabilitiesi candidate fn2-sim)))))
           (fn2-sim (update-fn2-sim-forced-fault *fn2-fault-none* fn2-sim))
           (fn2-sim (update-fn2-sim-digest
                       (fn2-sim-fold (fn2-sim-digest fn2-sim)
                                      (+ 61440 (if hit candidate *fn2-fault-none*))) fn2-sim)))
      (if (not hit) (mv *fn2-fault-none* fn2-sim)
        (let ((fn2-sim (update-fn2-sim-fault-budget (- (fn2-sim-fault-budget fn2-sim) 1) fn2-sim)))
          (mv candidate fn2-sim))))))

; Coverage is recorded at the effect, never at random selection.
(defun fn2-sim-land (fault fn2-sim)
  (declare (xargs :stobjs fn2-sim :guard t))
  (if (and (natp fault) (< fault *fn2-fault-none*))
      (update-fn2-sim-hitsi fault (min #xffffffff (+ 1 (fn2-sim-hitsi fault fn2-sim))) fn2-sim)
    fn2-sim))
(fn2-sim-preserves fn2-sim-land (fault fn2-sim) :forward t
  :hyps ((fn2-simp fn2-sim) (fn2-sim-ready fn2-sim))
  :specs (("-TYPE" fn2-simp nil) ("-READY" fn2-sim-ready nil) ("-WFP" fn2-sim-wfp nil)))
(fn2-sim-preserves fn2-sim-land (fault fn2-sim) :disable nil
  :specs (("-NET-FRAME" (lambda (s) (nth *fn2-sim-net* s)) nil :frame fn2-sim)
          ("-DISK-FRAME" (lambda (s) (nth *fn2-sim-disk* s)) nil :frame fn2-sim))
  :hints (("Goal" :in-theory (enable fn2-sim-land))))
(defthm fn2-sim-land-rows
  (equal (fn2-sim-rows (fn2-sim-land fault fn2-sim)) (fn2-sim-rows fn2-sim))
  :hints (("Goal" :in-theory (enable fn2-sim-land fn2-sim-rows))))
(defthm fn2-sim-choose-fault-result
  (implies (fn2-simp fn2-sim)
           (and (natp (mv-nth 0 (fn2-sim-choose-fault fn2-sim)))
                (<= (mv-nth 0 (fn2-sim-choose-fault fn2-sim)) *fn2-fault-none*))))
(fn2-sim-preserves fn2-sim-choose-fault (fn2-sim) :forward t
  :hyps ((fn2-simp fn2-sim) (fn2-sim-ready fn2-sim))
  :specs (("-TYPE" fn2-simp 1) ("-READY" fn2-sim-ready 1) ("-WFP" fn2-sim-wfp 1)))

(defun fn2-sim-record (op gen cell evkind outcome reason count aux0 aux1 fault fn2-sim)
  (declare (xargs :stobjs fn2-sim :guard (fn2-sim-ready fn2-sim)))
  (if (not (and (unsigned-byte-p 60 op) (unsigned-byte-p 60 gen)
                (unsigned-byte-p 60 cell) (unsigned-byte-p 60 evkind)
                (unsigned-byte-p 60 outcome) (unsigned-byte-p 60 reason)
                (unsigned-byte-p 60 count) (unsigned-byte-p 60 aux0)
                (unsigned-byte-p 60 aux1) (unsigned-byte-p 60 fault)))
      (update-fn2-sim-lost (min *fn2-u60-max* (+ 1 (fn2-sim-lost fn2-sim))) fn2-sim)
    (let* ((i (mod (fn2-sim-ring-head fn2-sim) *fn2-sim-observation-capacity*))
           (fn2-sim (if (<= *fn2-sim-observation-capacity* (fn2-sim-ring-unread fn2-sim))
                        (update-fn2-sim-lost (min *fn2-u60-max* (+ 1 (fn2-sim-lost fn2-sim))) fn2-sim)
                      (update-fn2-sim-ring-unread (+ 1 (fn2-sim-ring-unread fn2-sim)) fn2-sim)))
           (fn2-sim (update-fn2-sim-ring-opi i op fn2-sim))
           (fn2-sim (update-fn2-sim-ring-geni i gen fn2-sim))
           (fn2-sim (update-fn2-sim-ring-celli i cell fn2-sim))
           (fn2-sim (update-fn2-sim-ring-eventi i evkind fn2-sim))
           (fn2-sim (update-fn2-sim-ring-outcomei i outcome fn2-sim))
           (fn2-sim (update-fn2-sim-ring-reasoni i reason fn2-sim))
           (fn2-sim (update-fn2-sim-ring-counti i count fn2-sim))
           (fn2-sim (update-fn2-sim-ring-aux0i i aux0 fn2-sim))
           (fn2-sim (update-fn2-sim-ring-aux1i i aux1 fn2-sim))
           (fn2-sim (update-fn2-sim-ring-faulti i fault fn2-sim))
           (hash (fn2-sim-digest fn2-sim))
           (hash (fn2-sim-fold hash op))
           (hash (fn2-sim-fold hash gen))
           (hash (fn2-sim-fold hash cell))
           (hash (fn2-sim-fold hash evkind))
           (hash (fn2-sim-fold hash outcome))
           (hash (fn2-sim-fold hash reason))
           (hash (fn2-sim-fold hash count))
           (hash (fn2-sim-fold hash aux0))
           (hash (fn2-sim-fold hash aux1))
           (hash (fn2-sim-fold hash fault))
           (fn2-sim (update-fn2-sim-digest hash fn2-sim))
           (fn2-sim (update-fn2-sim-ring-head (mod (+ i 1) *fn2-sim-observation-capacity*) fn2-sim))
           (fn2-sim (update-fn2-sim-observations
                       (min *fn2-u60-max* (+ 1 (fn2-sim-observations fn2-sim))) fn2-sim)))
      fn2-sim)))
(fn2-sim-preserves fn2-sim-record (op gen cell evkind outcome reason count aux0 aux1 fault fn2-sim) :forward t
  :hyps ((fn2-simp fn2-sim) (fn2-sim-ready fn2-sim))
  :specs (("-TYPE" fn2-simp nil) ("-READY" fn2-sim-ready nil) ("-WFP" fn2-sim-wfp nil)))

(defun fn2-sim-clock (target fault fn2-sim)
  (declare (xargs :stobjs fn2-sim :guard (fn2-sim-ready fn2-sim)))
  (let* ((target (if (unsigned-byte-p 60 target) target (fn2-sim-now fn2-sim)))
         (now (max target (fn2-sim-now fn2-sim)))
         (now (if (equal fault *fn2-fault-monotonic-jump*) (min *fn2-u60-max* (+ now 1000000)) now))
         (real (if (equal fault *fn2-fault-realtime-back*) (max 0 (- (fn2-sim-real fn2-sim) 1000000)) now))
         (fn2-sim (if (or (and (equal fault *fn2-fault-monotonic-jump*) (< (max target (fn2-sim-now fn2-sim)) now))
                          (and (equal fault *fn2-fault-realtime-back*) (< real (fn2-sim-real fn2-sim))))
                       (fn2-sim-land fault fn2-sim) fn2-sim))
         (fn2-sim (update-fn2-sim-now now fn2-sim))
         (fn2-sim (update-fn2-sim-real real fn2-sim)))
    fn2-sim))
(fn2-sim-preserves fn2-sim-clock (target fault fn2-sim) :forward t
  :hyps ((fn2-simp fn2-sim) (fn2-sim-ready fn2-sim))
  :specs (("-TYPE" fn2-simp nil) ("-READY" fn2-sim-ready nil) ("-WFP" fn2-sim-wfp nil)))

; One replaceable ArmWake request survives recycling its descriptor row.
; New clock views may replace an obsolete deadline; repeated requests from
; the same view retain the earliest deadline. Older views cannot postpone it.
(defun fn2-sim-arm-wake (deadline observation-gen fn2-sim)
  (declare (xargs :stobjs fn2-sim :guard (fn2-sim-ready fn2-sim)))
  (if (not (and (unsigned-byte-p 60 deadline)
                (unsigned-byte-p 60 observation-gen))) fn2-sim
    (let ((old-gen (fn2-sim-wake-observation-gen fn2-sim)))
      (if (< observation-gen old-gen) fn2-sim
        (let* ((deadline (if (and (= (fn2-sim-wake-pending fn2-sim) 1)
                                  (= observation-gen old-gen))
                             (min deadline (fn2-sim-wake-deadline fn2-sim))
                           deadline))
               (fn2-sim (update-fn2-sim-wake-pending 1 fn2-sim))
               (fn2-sim (update-fn2-sim-wake-deadline deadline fn2-sim))
               (fn2-sim (update-fn2-sim-wake-observation-gen observation-gen fn2-sim)))
          fn2-sim)))))
(fn2-sim-preserves fn2-sim-arm-wake (deadline observation-gen fn2-sim) :forward t
  :hyps ((fn2-simp fn2-sim) (fn2-sim-ready fn2-sim))
  :specs (("-TYPE" fn2-simp nil) ("-READY" fn2-sim-ready nil) ("-WFP" fn2-sim-wfp nil)))
(fn2-sim-preserves fn2-sim-arm-wake (deadline observation-gen fn2-sim) :disable nil
  :specs (("-NET-FRAME" (lambda (s) (nth *fn2-sim-net* s)) nil :frame fn2-sim)
          ("-DISK-FRAME" (lambda (s) (nth *fn2-sim-disk* s)) nil :frame fn2-sim))
  :hints (("Goal" :in-theory (enable fn2-sim-arm-wake))))
(defthm fn2-sim-arm-wake-rows
  (equal (fn2-sim-rows (fn2-sim-arm-wake deadline observation-gen fn2-sim))
         (fn2-sim-rows fn2-sim))
  :hints (("Goal" :in-theory (enable fn2-sim-arm-wake fn2-sim-rows))))

; O resident rows: a bounded scan. Equal due times keep the rotated first
; choice; the adapter passes a seed-derived start for random tie ordering.
(defun fn2-sim-earliest (left index best found fn2-sim)
  (declare (xargs :stobjs fn2-sim :measure (nfix left)
                  :guard (and (fn2-sim-ready fn2-sim) (natp left) (natp index)
                              (natp best) (booleanp found)
                              (or (not found) (< best (fn2-sim-rows fn2-sim))))))
  (if (or (zp left) (= (fn2-sim-rows fn2-sim) 0)) (mv found best)
    (let* ((i (mod (nfix index) (fn2-sim-rows fn2-sim)))
           (take (and (< 0 (fn2-sim-active i fn2-sim))
                      (or (not found) (< (fn2-sim-due i fn2-sim) (fn2-sim-due best fn2-sim))))))
      (fn2-sim-earliest (- left 1) (+ i 1) (if take i best) (or take found) fn2-sim))))
(defthm fn2-sim-earliest-result
  (implies (and (fn2-simp fn2-sim) (fn2-sim-ready fn2-sim) (natp best)
                (or (not found) (< best (fn2-sim-rows fn2-sim))))
           (and (natp (mv-nth 1 (fn2-sim-earliest left index best found fn2-sim)))
                (implies (mv-nth 0 (fn2-sim-earliest left index best found fn2-sim))
                         (< (mv-nth 1 (fn2-sim-earliest left index best found fn2-sim))
                            (fn2-sim-rows fn2-sim))))))
(defthm fn2-sim-earliest-boolean
  (implies (booleanp found)
           (booleanp (mv-nth 0 (fn2-sim-earliest left index best found fn2-sim)))))
(in-theory (disable fn2-sim-earliest))
(defun fn2-sim-next-flight (fn2-sim)
  (declare (xargs :stobjs fn2-sim :guard (fn2-sim-ready fn2-sim)))
  (fn2-sim-earliest (fn2-sim-rows fn2-sim) (fn2-sim-s0 fn2-sim) 0 nil fn2-sim))
(defthm fn2-sim-next-flight-types
  (implies (and (fn2-simp fn2-sim) (fn2-sim-ready fn2-sim))
           (and (booleanp (mv-nth 0 (fn2-sim-next-flight fn2-sim)))
                (natp (mv-nth 1 (fn2-sim-next-flight fn2-sim)))
                (implies (mv-nth 0 (fn2-sim-next-flight fn2-sim))
                         (< (mv-nth 1 (fn2-sim-next-flight fn2-sim))
                            (fn2-sim-rows fn2-sim)))))
  :hints (("Goal" :use ((:instance fn2-sim-earliest-result
                         (left (fn2-sim-rows fn2-sim)) (index (fn2-sim-s0 fn2-sim))
                         (best 0) (found nil))
                        (:instance fn2-sim-earliest-boolean
                         (left (fn2-sim-rows fn2-sim)) (index (fn2-sim-s0 fn2-sim))
                         (best 0) (found nil)))
                  :in-theory (disable fn2-sim-earliest-result fn2-sim-earliest-boolean))))
(in-theory (disable fn2-sim-next-flight))

(defun fn2-sim-cap (index fn2-sim)
  (declare (xargs :stobjs fn2-sim :guard (fn2-sim-ready fn2-sim)))
  (stobj-let ((fn2-sim-network (fn2-sim-net fn2-sim)))
    (nonce)
    (if (and (natp index) (< index (fn2-sim-network-rows fn2-sim-network)))
        (fn2-sim-network-nonce index fn2-sim-network) 0)
    nonce))
(defthm fn2-sim-cap-type
  (implies (and (fn2-simp fn2-sim) (fn2-sim-ready fn2-sim))
           (unsigned-byte-p 32 (fn2-sim-cap index fn2-sim))))
(in-theory (disable fn2-sim-cap))

; Initialize every runtime-mutated field on reused local stobjs too.
(defun fn2-sim-clear-flights (slot fn2-sim)
  (declare (xargs :stobjs fn2-sim :guard (and (fn2-sim-ready fn2-sim) (natp slot))
                  :measure (nfix (- (nfix (fn2-sim-rows fn2-sim)) (nfix slot)))))
  (if (or (not (natp slot)) (>= slot (nfix (fn2-sim-rows fn2-sim)))) fn2-sim
    (let* (
           (fn2-sim (fn2-sim-set-active slot 0 fn2-sim))
           (fn2-sim (fn2-sim-set-gen slot 0 fn2-sim))
           (fn2-sim (fn2-sim-set-kind slot 0 fn2-sim))
           (fn2-sim (fn2-sim-set-due slot 0 fn2-sim))
           (fn2-sim (fn2-sim-set-range-slot slot 0 fn2-sim))
           (fn2-sim (fn2-sim-set-range-gen slot 0 fn2-sim))
           (fn2-sim (fn2-sim-set-range-off slot 0 fn2-sim))
           (fn2-sim (fn2-sim-set-range-len slot 0 fn2-sim))
           (fn2-sim (fn2-sim-set-owner-kind slot 0 fn2-sim))
           (fn2-sim (fn2-sim-set-owner-slot slot 0 fn2-sim))
           (fn2-sim (fn2-sim-set-owner-gen slot 0 fn2-sim))
           (fn2-sim (fn2-sim-set-cap-index slot 0 fn2-sim))
           (fn2-sim (fn2-sim-set-cap-nonce slot 0 fn2-sim))
           (fn2-sim (fn2-sim-set-storage-offset slot 0 fn2-sim))
           (fn2-sim (fn2-sim-set-fua slot 0 fn2-sim))
           (fn2-sim (fn2-sim-set-may-release slot 0 fn2-sim))
           (fn2-sim (fn2-sim-set-cancel-slot slot 0 fn2-sim))
           (fn2-sim (fn2-sim-set-cancel-gen slot 0 fn2-sim))
           (fn2-sim (fn2-sim-set-last-gen slot 0 fn2-sim))
           (fn2-sim (fn2-sim-set-cancelled slot 0 fn2-sim))
           (fn2-sim (fn2-sim-set-terminal-outcome slot 0 fn2-sim))
           (fn2-sim (fn2-sim-set-terminal-reason slot 0 fn2-sim))
           (fn2-sim (fn2-sim-set-terminal-count slot 0 fn2-sim))
           (fn2-sim (fn2-sim-set-terminal-aux0 slot 0 fn2-sim))
           (fn2-sim (fn2-sim-set-terminal-aux1 slot 0 fn2-sim))
           )
      (fn2-sim-clear-flights (+ 1 slot) fn2-sim))))
(fn2-sim-preserves fn2-sim-clear-flights (slot fn2-sim) :forward t
  :hyps ((fn2-simp fn2-sim) (fn2-sim-ready fn2-sim))
  :specs (("-TYPE" fn2-simp nil) ("-READY" fn2-sim-ready nil) ("-WFP" fn2-sim-wfp nil)))
(fn2-sim-preserves fn2-sim-clear-flights (slot fn2-sim) :disable nil
  :specs (("-NET-FRAME" (lambda (s) (nth *fn2-sim-net* s)) nil :frame fn2-sim)
          ("-DISK-FRAME" (lambda (s) (nth *fn2-sim-disk* s)) nil :frame fn2-sim))
  :hints (("Goal" :in-theory (enable fn2-sim-clear-flights))))

(defun fn2-sim-init-faults (i profile-name fn2-sim)
  (declare (xargs :stobjs fn2-sim :guard (and (fn2-sim-ready fn2-sim) (natp i))
                  :measure (nfix (- *fn2-fault-count* (nfix i)))
                  :guard-hints (("Goal" :use ((:instance fn2-sim-random-state-type)
                                               (:instance fn2-sim-random-ready))
                                        :in-theory (disable fn2-sim-random-state-type fn2-sim-random-ready)))))
  (if (or (not (natp i)) (>= i *fn2-fault-count*)) fn2-sim
    (mv-let (word fn2-sim) (fn2-sim-random fn2-sim)
      (let* ((enabled (and (not (eq profile-name :none))
                           (or (not (eq profile-name :crash-only))
                               (member-equal i (list *fn2-fault-fragment* *fn2-fault-short-send* *fn2-fault-delay* *fn2-fault-tear* *fn2-fault-fail-slow* *fn2-fault-crash* *fn2-fault-release-order*)))))
             (fn2-sim (update-fn2-sim-probabilitiesi i (if enabled (+ 1 (mod word 64)) 0) fn2-sim))
             (fn2-sim (update-fn2-sim-hitsi i 0 fn2-sim)))
        (fn2-sim-init-faults (+ 1 i) profile-name fn2-sim)))))
(fn2-sim-preserves fn2-sim-init-faults (i profile-name fn2-sim) :forward t
  :hyps ((fn2-simp fn2-sim) (fn2-sim-ready fn2-sim))
  :specs (("-TYPE" fn2-simp nil) ("-READY" fn2-sim-ready nil) ("-WFP" fn2-sim-wfp nil)))
(fn2-sim-preserves fn2-sim-init-faults (i profile-name fn2-sim) :disable nil
  :specs (("-NET-FRAME" (lambda (s) (nth *fn2-sim-net* s)) nil :frame fn2-sim)
          ("-DISK-FRAME" (lambda (s) (nth *fn2-sim-disk* s)) nil :frame fn2-sim))
  :hints (("Goal" :in-theory (enable fn2-sim-init-faults))))

(defun fn2-sim-client-seed (left byte fn2-sim-network)
  (declare (xargs :stobjs fn2-sim-network :measure (nfix left)
                  :guard (and (fn2-sim-network-wfp fn2-sim-network)
                              (natp left) (unsigned-byte-p 8 byte))))
  (if (zp left) fn2-sim-network
    (mv-let (code fn2-sim-network) (fn2-network-client-byte 0 1 byte fn2-sim-network)
      (if (not (eq code :ok)) fn2-sim-network
        (fn2-sim-client-seed (- left 1) (mod (+ byte 1) 256) fn2-sim-network)))))
(defthm fn2-sim-client-seed-type
  (implies (and (fn2-sim-networkp fn2-sim-network) (fn2-sim-network-wfp fn2-sim-network))
           (fn2-sim-networkp (fn2-sim-client-seed left byte fn2-sim-network))))
(defthm fn2-sim-client-seed-wfp
  (implies (fn2-sim-network-wfp fn2-sim-network)
           (fn2-sim-network-wfp (fn2-sim-client-seed left byte fn2-sim-network))))
(in-theory (disable fn2-sim-client-seed))

(defun fn2-sim-init-counters (i fn2-sim)
  (declare (xargs :stobjs fn2-sim :guard (and (fn2-sim-ready fn2-sim) (natp i))
                  :measure (nfix (- *fn2-sim-observation-capacity* (nfix i)))))
  (if (or (not (natp i)) (>= i *fn2-sim-observation-capacity*)) fn2-sim
    (let* (
           (fn2-sim (update-fn2-sim-ring-opi i 0 fn2-sim))
           (fn2-sim (update-fn2-sim-ring-geni i 0 fn2-sim))
           (fn2-sim (update-fn2-sim-ring-celli i 0 fn2-sim))
           (fn2-sim (update-fn2-sim-ring-eventi i 0 fn2-sim))
           (fn2-sim (update-fn2-sim-ring-outcomei i 0 fn2-sim))
           (fn2-sim (update-fn2-sim-ring-reasoni i 0 fn2-sim))
           (fn2-sim (update-fn2-sim-ring-counti i 0 fn2-sim))
           (fn2-sim (update-fn2-sim-ring-aux0i i 0 fn2-sim))
           (fn2-sim (update-fn2-sim-ring-aux1i i 0 fn2-sim))
           (fn2-sim (update-fn2-sim-ring-faulti i 0 fn2-sim))
           (fn2-sim (if (< i *fn2-action-count*) (update-fn2-sim-action-countsi i 0 fn2-sim) fn2-sim)))
      (fn2-sim-init-counters (+ 1 i) fn2-sim))))
(fn2-sim-preserves fn2-sim-init-counters (i fn2-sim) :forward t
  :hyps ((fn2-simp fn2-sim) (fn2-sim-ready fn2-sim))
  :specs (("-TYPE" fn2-simp nil) ("-READY" fn2-sim-ready nil) ("-WFP" fn2-sim-wfp nil)))
(fn2-sim-preserves fn2-sim-init-counters (i fn2-sim) :disable nil
  :specs (("-NET-FRAME" (lambda (s) (nth *fn2-sim-net* s)) nil :frame fn2-sim)
          ("-DISK-FRAME" (lambda (s) (nth *fn2-sim-disk* s)) nil :frame fn2-sim))
  :hints (("Goal" :in-theory (enable fn2-sim-init-counters))))

; The finite simulated device is an environment setting, independent of the
; implementation's durable namespace. Tiny runs default to four sectors;
; larger connection profiles default to sixteen. :sim-sectors overrides it.
(defun fn2-sim-sectors (profile)
  (declare (xargs :guard t))
  (if (and (alistp profile) (assoc-equal :sim-sectors profile))
      (fn2-profile-get :sim-sectors profile)
    (if (and (natp (fn2-profile-c profile)) (< 4 (fn2-profile-c profile))) 16 4)))
(in-theory (disable fn2-sim-sectors))

(defun fn2-sim-configp (profile)
  (declare (xargs :guard t))
  (and (fn2-profilep profile) (unsigned-byte-p 32 (fn2-profile-c profile))
       (unsigned-byte-p 60 (* *fn2-sim-network-capacity* (fn2-profile-c profile)))
       (posp (fn2-sim-sectors profile)) (< (fn2-sim-sectors profile) 1048576)
       (< (* *fn2-format-sector-bytes* (fn2-sim-sectors profile) (fn2-profile-fence-slots profile)) #x1000000000000000)))

(local (in-theory (disable fn2-profile-o fn2-profile-c fn2-profile-fence-slots fn2-profile-get)))
(fn2-word-facts fn2-sim-profile-fence-slots (fn2-profile-fence-slots profile) fn2-profile-fence-slots-bounds (fn2-profilep profile))
(fn2-word-facts fn2-sim-profile-o (fn2-profile-o profile) fn2-profile-o-bounds (fn2-profilep profile))

(defun fn2-sim-init (seed profile-name revision profile fn2-sim)
  (declare (xargs :stobjs fn2-sim :guard (and (natp seed) (fn2-sim-configp profile))))
  (let* ((fn2-sim (fn2-sim-columns-init (fn2-profile-o profile) fn2-sim)))
    (stobj-let ((fn2-sim-network (fn2-sim-net fn2-sim))
                (fn2-sim-storage (fn2-sim-disk fn2-sim)))
      (fn2-sim-network fn2-sim-storage)
      (let* ((fn2-sim-network (fn2-network-init (fn2-profile-c profile) *fn2-sim-network-capacity* fn2-sim-network))
             (fn2-sim-storage (fn2-storage-init (fn2-sim-sectors profile) (fn2-profile-fence-slots profile) fn2-sim-storage)))
        (mv-let (code nonce fn2-sim-network) (fn2-network-accept 0 fn2-sim-network)
          (declare (ignore code nonce))
          (let ((fn2-sim-network (fn2-sim-client-seed 256 0 fn2-sim-network)))
            (mv fn2-sim-network fn2-sim-storage))))
      (mv-let (s0 s1 s2 s3) (fn2-prng-seed seed)
        (let* ((fn2-sim (update-fn2-sim-profile profile fn2-sim))
               (fn2-sim (update-fn2-sim-profile-name profile-name fn2-sim))
               (fn2-sim (update-fn2-sim-revision revision fn2-sim))
               (fn2-sim (update-fn2-sim-initial-seed seed fn2-sim))
               (fn2-sim (update-fn2-sim-seed (fn2-u32 seed) fn2-sim))
               (fn2-sim (update-fn2-sim-s0 s0 fn2-sim))
               (fn2-sim (update-fn2-sim-s1 s1 fn2-sim))
               (fn2-sim (update-fn2-sim-s2 s2 fn2-sim))
               (fn2-sim (update-fn2-sim-s3 s3 fn2-sim))
               (fn2-sim (update-fn2-sim-wake-pending 0 fn2-sim))
               (fn2-sim (update-fn2-sim-wake-deadline 0 fn2-sim))
               (fn2-sim (update-fn2-sim-wake-observation-gen 0 fn2-sim))
               (fn2-sim (update-fn2-sim-now 0 fn2-sim))
               (fn2-sim (update-fn2-sim-real 0 fn2-sim))
               (fn2-sim (update-fn2-sim-deaths 0 fn2-sim))
               (fn2-sim (update-fn2-sim-stamp 0 fn2-sim))
               (fn2-sim (update-fn2-sim-fault-budget 128 fn2-sim))
               (fn2-sim (update-fn2-sim-forced-fault *fn2-fault-none* fn2-sim))
               (fn2-sim (update-fn2-sim-digest *fn2-fnv-offset-basis* fn2-sim))
               (fn2-sim (update-fn2-sim-observations 0 fn2-sim))
               (fn2-sim (update-fn2-sim-ring-head 0 fn2-sim))
               (fn2-sim (update-fn2-sim-ring-unread 0 fn2-sim))
               (fn2-sim (update-fn2-sim-lost 0 fn2-sim))
               (fn2-sim (fn2-sim-clear-flights 0 fn2-sim))
               (fn2-sim (fn2-sim-init-counters 0 fn2-sim)))
          (fn2-sim-init-faults 0 profile-name fn2-sim))))))
(defthm fn2-sim-init-type
  (implies (and (fn2-simp fn2-sim) (natp seed) (fn2-sim-configp profile))
           (fn2-simp (fn2-sim-init seed profile-name revision profile fn2-sim))))
(defthm fn2-sim-init-ready
  (implies (and (fn2-simp fn2-sim) (natp seed) (fn2-sim-configp profile))
           (fn2-sim-ready (fn2-sim-init seed profile-name revision profile fn2-sim))))
(in-theory (disable fn2-sim-init fn2-sim-configp))
(assert-event (fn2-assert-compliant-p
               '(fn2-sim-ready fn2-sim-random fn2-sim-force-fault fn2-sim-choose-fault
                 fn2-sim-fold fn2-sim-record fn2-sim-clock fn2-sim-earliest fn2-sim-arm-wake fn2-sim-land
                 fn2-sim-next-flight fn2-sim-cap fn2-sim-clear-flights
                 fn2-sim-init-faults fn2-sim-client-seed fn2-sim-init-counters
                 fn2-sim-sectors fn2-sim-configp fn2-sim-init)
               (w state)))

(local
 (defun fn2-sim-state-fixture ()
   (declare (xargs :guard t))
   (with-local-stobj fn2-sim
     (mv-let (ok fn2-sim)
       (let* ((fn2-sim (fn2-sim-init 73 :broad "state-fixture" *fn2-profile-tiny* fn2-sim))
              (initial (and (fn2-sim-ready fn2-sim)
                            (equal (fn2-sim-rows fn2-sim) 8)
                            (equal (fn2-sim-cap 0 fn2-sim) 1)))
              (fn2-sim (fn2-sim-force-fault *fn2-fault-stale* fn2-sim)))
         (mv-let (fault fn2-sim) (fn2-sim-choose-fault fn2-sim)
           (let* ((chosen (and (equal fault *fn2-fault-stale*) (equal (fn2-sim-fault-budget fn2-sim) 127)
                               (equal (fn2-sim-hitsi *fn2-fault-stale* fn2-sim) 0)))
                  (fn2-sim (fn2-sim-record 1 2 0 3 0 0 4 0 0 fault fn2-sim))
                  (digest (fn2-sim-digest fn2-sim))
                  (recorded (and (equal (fn2-sim-observations fn2-sim) 1)
                                 (equal (fn2-sim-ring-counti 0 fn2-sim) 4)))
                  (fn2-sim (fn2-sim-clock 10000 *fn2-fault-monotonic-jump* fn2-sim))
                  (fn2-sim (fn2-sim-clock 1010000 *fn2-fault-realtime-back* fn2-sim))
                  (clocked (and (equal (fn2-sim-now fn2-sim) 1010000)
                                (equal (fn2-sim-real fn2-sim) 10000)))
                  (fn2-sim (fn2-sim-init 73 :broad "state-fixture" *fn2-profile-tiny* fn2-sim))
                  (fn2-sim (fn2-sim-force-fault *fn2-fault-stale* fn2-sim)))
             (mv-let (fault fn2-sim) (fn2-sim-choose-fault fn2-sim)
               (let ((fn2-sim (fn2-sim-record 1 2 0 3 0 0 4 0 0 fault fn2-sim)))
                 (mv (and initial chosen recorded clocked (equal digest (fn2-sim-digest fn2-sim)))
                     fn2-sim))))))
       ok))))
(local (assert-event (fn2-sim-state-fixture)))

(local
 (defun fn2-sim-wake-fixture ()
   (declare (xargs :guard t))
   (with-local-stobj fn2-sim
     (mv-let (ok fn2-sim)
       (let* ((fn2-sim (fn2-sim-init 73 :none "wake-fixture" *fn2-profile-tiny* fn2-sim))
              (fn2-sim (fn2-sim-arm-wake 100 4 fn2-sim))
              (fn2-sim (fn2-sim-arm-wake 200 4 fn2-sim))
              (same-view (equal (fn2-sim-wake-deadline fn2-sim) 100))
              (fn2-sim (fn2-sim-arm-wake 20 4 fn2-sim))
              (earlier (equal (fn2-sim-wake-deadline fn2-sim) 20))
              (fn2-sim (fn2-sim-arm-wake 300 5 fn2-sim))
              (replacement (equal (fn2-sim-wake-deadline fn2-sim) 300))
              (fn2-sim (fn2-sim-arm-wake 500 3 fn2-sim)))
         (mv (and same-view earlier replacement
                  (equal (fn2-sim-wake-pending fn2-sim) 1)
                  (equal (fn2-sim-wake-observation-gen fn2-sim) 5)
                  (equal (fn2-sim-wake-deadline fn2-sim) 300)) fn2-sim))
       ok))))
(local (assert-event (fn2-sim-wake-fixture)))
