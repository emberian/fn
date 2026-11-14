; Actual allocator -> frozen row -> fixed-slot packer -> restore reader.
; Freeze phase1/token/actor and construction-ledger ownership below are
; explicit synthetic antecedents, not a C-cut or reservation-closure witness.
; These entry controls do not authenticate page headers or install authority.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "../books/checkpoint-map-pack")
(include-book "../books/checkpoint-restore-read")

; Compare all eight serialized allocation-row fields with the actual allocator,
; never with a separately encoded fixture or caller-selected row description.
(defun fn2-map-roundtrip-row-equal-p (e base fn2-extents fn2-fields)
 (declare (xargs :stobjs (fn2-extents fn2-fields) :verify-guards nil))
 (and
  (equal (fn2-fields-value (+ base *fn2-format-allocation-map-entry-field-extent*) fn2-fields) e)
  (equal (fn2-fields-value (+ base *fn2-format-allocation-map-entry-field-state*) fn2-fields) (fn2-extents-state e fn2-extents))
  (equal (fn2-fields-value (+ base *fn2-format-allocation-map-entry-field-owner-kind*) fn2-fields) (fn2-extents-owner-kind e fn2-extents))
  (equal (fn2-fields-value (+ base *fn2-format-allocation-map-entry-field-owner*) fn2-fields) (fn2-extents-owner-id e fn2-extents))
  (equal (fn2-fields-value (+ base *fn2-format-allocation-map-entry-field-writer-epoch*) fn2-fields) (fn2-extents-epoch e fn2-extents))
  (equal (fn2-fields-value (+ base *fn2-format-allocation-map-entry-field-allocation*) fn2-fields) (fn2-extents-counter e fn2-extents))
  (equal (fn2-fields-value (+ base *fn2-format-allocation-map-entry-field-retirement-commit*) fn2-fields) (fn2-extents-retirement e fn2-extents))
  (equal (fn2-fields-value (+ base *fn2-format-allocation-map-entry-field-next-retired*) fn2-fields) (if (equal (fn2-extents-state e fn2-extents) *fn2-extent-state-retire-pending*) (fn2-extents-next-retired e fn2-extents) *fn2-alloc-none*))
  ))

(defun fn2-map-roundtrip-rows (e left slot gen fn2-extents fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-extents fn2-fields fn2-pool) :verify-guards nil :measure (nfix left)))
 (if (zp left) (mv t fn2-fields fn2-pool)
  (b* (((mv frozen fn2-fields) (fn2-checkpoint-frozen-map-entry e 16 7 1 2 3 fn2-extents fn2-fields))
       ((unless (and (eq frozen :entry) (fn2-map-roundtrip-row-equal-p e 16 fn2-extents fn2-fields)))
        (mv nil fn2-fields fn2-pool))
       ((mv packed fn2-fields fn2-pool) (fn2-checkpoint-map-pack-entry e 0 0 slot gen 7 1 2 3 fn2-extents fn2-fields fn2-pool))
       ((unless (eq packed :ok)) (mv nil fn2-fields fn2-pool))
       ((mv restored fn2-fields) (fn2-checkpoint-restore-entry 2 e 32 slot gen 1 2 3 fn2-fields fn2-pool))
       ((unless (and (eq restored :entry) (fn2-map-roundtrip-row-equal-p e 32 fn2-extents fn2-fields)
                      (fn2-checkpoint-restore-allocation-rowp 32 fn2-fields)))
        (mv nil fn2-fields fn2-pool)))
   (fn2-map-roundtrip-rows (+ 1 e) (- left 1) slot gen fn2-extents fn2-fields fn2-pool))))

(defun fn2-map-roundtrip-control (fn2-extents fn2-checkpoint-construction fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-extents fn2-checkpoint-construction fn2-fields fn2-pool) :verify-guards nil))
 (b* ((fn2-extents (fn2-alloc-init 6 fn2-extents))
      (fn2-checkpoint-construction (fn2-checkpoint-construction-init 6 fn2-checkpoint-construction))
      (fn2-fields (fn2-fields-init 64 fn2-fields))
      (fn2-pool (fn2-pool-init '((1 . 4096)) 1 100 fn2-pool))
      ((mv workspace slot gen fn2-pool) (fn2-pool-reserve 0 1 2 3 fn2-pool))
      ((mv begun fn2-extents) (fn2-alloc-begin-epoch 3 fn2-extents))
      ((mv r0 & e0 ep0 a0 fn2-extents) (fn2-alloc-reserve fn2-extents))
      ((mv r1 & e1 ep1 a1 fn2-extents) (fn2-alloc-reserve fn2-extents))
      ((mv r2 & e2 ep2 a2 fn2-extents) (fn2-alloc-reserve fn2-extents))
      ((mv r3 & e3 & & fn2-extents) (fn2-alloc-reserve fn2-extents))
      ((mv r4 & e4 ep4 a4 fn2-extents) (fn2-alloc-reserve fn2-extents))
      ((mv c0 fn2-extents) (fn2-alloc-commit-allocation e0 ep0 a0 4 101 fn2-extents))
      ((mv c1 fn2-extents) (fn2-alloc-commit-allocation e1 ep1 a1 5 102 fn2-extents))
      ((mv c2 fn2-extents) (fn2-alloc-commit-allocation e2 ep2 a2 6 103 fn2-extents))
      ((mv t0 fn2-extents) (fn2-alloc-retire e0 ep0 a0 11 fn2-extents))
      ((mv t1 fn2-extents) (fn2-alloc-retire e1 ep1 a1 12 fn2-extents))
      ((unless (and (eq workspace :ok) (eq begun :ok)
                     (eq r0 :ok) (eq r1 :ok) (eq r2 :ok) (eq r3 :ok) (eq r4 :ok)
                     (eq c0 :ok) (eq c1 :ok) (eq c2 :ok) (eq t0 :ok) (eq t1 :ok)
                     (= e0 0) (= e1 1) (= e2 2) (= e3 3) (= e4 4)
                     (= (fn2-extents-state 5 fn2-extents) *fn2-extent-state-free*)
                     (= (fn2-extents-state e3 fn2-extents) *fn2-extent-state-reserved*)
                     (= (fn2-extents-owner-kind e3 fn2-extents) 0) (= (fn2-extents-owner-id e3 fn2-extents) 0)
                     (= (fn2-extents-state e2 fn2-extents) *fn2-extent-state-allocated*)
                     (= (fn2-extents-state e0 fn2-extents) *fn2-extent-state-retire-pending*)
                     (= (fn2-extents-next-retired e0 fn2-extents) e1) (posp e1)
                     (= (fn2-extents-next-retired e1 fn2-extents) *fn2-alloc-none*)
                     (= (fn2-alloc-retired-head fn2-extents) e0) (= (fn2-alloc-total-retired fn2-extents) 2)))
       (mv nil fn2-extents fn2-checkpoint-construction fn2-fields fn2-pool))
      ; Synthetic freeze antecedent only; no actual C snapshot is claimed.
      (fn2-extents (update-fn2-alloc-freeze-phase 1 fn2-extents))
      (fn2-extents (update-fn2-alloc-freeze-token 7 fn2-extents))
      (fn2-extents (update-fn2-alloc-freeze-owner-kind 1 fn2-extents))
      (fn2-extents (update-fn2-alloc-freeze-owner-slot 2 fn2-extents))
      (fn2-extents (update-fn2-alloc-freeze-owner-gen 3 fn2-extents))
      ((mv zeroed fn2-pool) (fn2-checkpoint-map-zero *fn2-checkpoint-map-entries-start* 0 slot gen 1 2 3 fn2-pool))
      ((mv roundtrip fn2-fields fn2-pool) (fn2-map-roundtrip-rows 0 6 slot gen fn2-extents fn2-fields fn2-pool))
      ((mv wrong-owner fn2-fields fn2-pool) (fn2-checkpoint-map-pack-entry e0 0 0 slot gen 7 1 9 3 fn2-extents fn2-fields fn2-pool))
      ((mv stale-owner fn2-fields) (fn2-checkpoint-frozen-map-entry e0 0 7 1 2 4 fn2-extents fn2-fields))
      ((mv stale-workspace fn2-fields fn2-pool) (fn2-checkpoint-map-pack-entry e0 0 0 slot (+ 1 gen) 7 1 2 3 fn2-extents fn2-fields fn2-pool))
      ((mv wrong-pack-ordinal fn2-fields fn2-pool) (fn2-checkpoint-map-pack-entry e0 1 0 slot gen 7 1 2 3 fn2-extents fn2-fields fn2-pool))
      ((mv stale-read fn2-fields) (fn2-checkpoint-restore-entry 2 e0 32 slot (+ 1 gen) 1 2 3 fn2-fields fn2-pool))
      ((mv wrong-read-owner fn2-fields) (fn2-checkpoint-restore-entry 2 e0 32 slot gen 1 9 3 fn2-fields fn2-pool))
      ((mv wrong-read-ordinal fn2-fields) (fn2-checkpoint-restore-entry 2 *fn2-checkpoint-map-slots* 32 slot gen 1 2 3 fn2-fields fn2-pool))
      ((unless (and (eq zeroed :ok) roundtrip (eq wrong-owner :owner) (eq stale-owner :owner)
                     (eq stale-workspace :format) (eq wrong-pack-ordinal :ordinal)
                     (eq stale-read :format) (eq wrong-read-owner :format) (eq wrong-read-ordinal :identity)))
       (mv nil fn2-extents fn2-checkpoint-construction fn2-fields fn2-pool))
      ; Corrupt only real fixed-slot padding after the actual generated decoder's
      ; returned end. This is not a synthetic record-body encoder.
      ((mv decoded end fn2-fields) (fn2-format-allocation-map-entry-decode 32 slot gen *fn2-checkpoint-map-entries-start*
                                    (+ *fn2-checkpoint-map-entries-start* *fn2-checkpoint-map-entry-width*) 1 2 3 fn2-fields fn2-pool))
      ((unless (and (eq decoded :ok) (< end (+ *fn2-checkpoint-map-entries-start* *fn2-checkpoint-map-entry-width*))))
       (mv nil fn2-extents fn2-checkpoint-construction fn2-fields fn2-pool))
      ((mv corrupted fn2-pool) (fn2-pool-write slot gen end 1 1 2 3 fn2-pool))
      ((mv bad-padding fn2-fields) (fn2-checkpoint-restore-entry 2 e0 32 slot gen 1 2 3 fn2-fields fn2-pool))
      ((mv repaired fn2-pool) (fn2-pool-write slot gen end 0 1 2 3 fn2-pool))
      ((mv repaired-entry fn2-fields) (fn2-checkpoint-restore-entry 2 e0 32 slot gen 1 2 3 fn2-fields fn2-pool))
      ((unless (and (eq corrupted :ok) (eq bad-padding :padding) (eq repaired :ok) (eq repaired-entry :entry)
                     (fn2-map-roundtrip-row-equal-p e0 32 fn2-extents fn2-fields)))
       (mv nil fn2-extents fn2-checkpoint-construction fn2-fields fn2-pool))
      ; Actual RESERVED handle; synthetic ledger ownership is explicit and is
      ; not a witness that the construction reservation producer executed.
      (fn2-checkpoint-construction (fn2-checkpoint-construction-put e4 (live 1) (token 7)
       (owner-kind 1) (owner-slot 2) (owner-gen 3) (role 6) (ordinal 0) (epoch ep4) (counter a4)))
      ((mv reset fn2-pool) (fn2-pool-reset slot gen 1 2 3 fn2-pool))
      ((mv arena-zero fn2-pool) (fn2-checkpoint-map-zero *fn2-checkpoint-map-entries-start* 0 slot gen 1 2 3 fn2-pool))
      ((mv arena-packed fn2-fields fn2-pool) (fn2-checkpoint-arena-pack-entry e4 0 0 0 slot gen 7 1 2 3 fn2-checkpoint-construction fn2-extents fn2-fields fn2-pool))
      ((mv arena-read fn2-fields) (fn2-checkpoint-restore-entry 5 0 32 slot gen 1 2 3 fn2-fields fn2-pool))
      (arena-equal (and (eq arena-read :entry)
       (= (fn2-fields-value (+ 32 *fn2-format-recovery-arena-entry-field-extent-physical-unit*) fn2-fields) (* e4 *fn2-storage-extent-units*))
       (= (fn2-fields-value (+ 32 *fn2-format-recovery-arena-entry-field-writer-epoch*) fn2-fields) ep4)
       (= (fn2-fields-value (+ 32 *fn2-format-recovery-arena-entry-field-allocation*) fn2-fields) a4)))
      ((mv wrong-ticket fn2-fields) (fn2-checkpoint-frozen-arena-entry e4 1 0 7 1 2 3 fn2-checkpoint-construction fn2-extents fn2-fields))
      (fn2-checkpoint-construction (fn2-checkpoint-construction-put e4 (counter (+ 1 a4))))
      ((mv stale-ticket fn2-fields) (fn2-checkpoint-frozen-arena-entry e4 0 0 7 1 2 3 fn2-checkpoint-construction fn2-extents fn2-fields)))
  (mv (and (eq reset :ok) (eq arena-zero :ok) (eq arena-packed :ok) arena-equal
           (eq wrong-ticket :skip) (eq stale-ticket :conflict))
      fn2-extents fn2-checkpoint-construction fn2-fields fn2-pool)))

(defun fn2-map-roundtrip-control-run ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-extents
  (mv-let (ok fn2-extents)
   (with-local-stobj fn2-checkpoint-construction
    (mv-let (ok fn2-extents fn2-checkpoint-construction)
     (with-local-stobj fn2-fields
      (mv-let (ok fn2-extents fn2-checkpoint-construction fn2-fields)
       (with-local-stobj fn2-pool
        (mv-let (ok fn2-extents fn2-checkpoint-construction fn2-fields fn2-pool)
         (fn2-map-roundtrip-control fn2-extents fn2-checkpoint-construction fn2-fields fn2-pool)
         (mv ok fn2-extents fn2-checkpoint-construction fn2-fields)))
       (mv ok fn2-extents fn2-checkpoint-construction)))
     (mv ok fn2-extents))) ok)))
(assert-event (fn2-map-roundtrip-control-run))

; The rejected original TYPE formula, preserved explicitly for the boundary
; control. It quantified over arbitrary logical source objects while assuming
; only the destination's type/shape. It is not a served-domain contract.
(defun-nx fn2-map-frame-original-type-claim (extent base token okind oslot ogen p f)
 (implies (and (fn2-fieldsp f) (fn2-fields-wfp f))
  (fn2-fieldsp (mv-nth 1 (fn2-checkpoint-frozen-map-entry extent base token okind oslot ogen p f)))))

(defun-nx fn2-map-frame-valid-source ()
 (let* ((p (fn2-alloc-init 1 (create-fn2-extents)))
        (p (mv-nth 1 (fn2-alloc-begin-epoch 3 p)))
        (p (mv-nth 5 (fn2-alloc-reserve p)))
        (p (mv-nth 1 (fn2-alloc-commit-allocation 0 (fn2-extents-epoch 0 p) (fn2-extents-counter 0 p) 1 9 p)))
        (p (mv-nth 1 (fn2-alloc-retire 0 (fn2-extents-epoch 0 p) (fn2-extents-counter 0 p) 11 p)))
        (p (update-fn2-alloc-freeze-phase 1 p))
        (p (update-fn2-alloc-freeze-token 7 p))
        (p (update-fn2-alloc-freeze-owner-kind 1 p))
        (p (update-fn2-alloc-freeze-owner-slot 2 p)))
  (update-fn2-alloc-freeze-owner-gen 3 p)))

; Logical malformed-source controls only: never execute invalid raw objects
; through a host stobj entry. SHAPE=T removes the next-retired array while
; retaining the row count; SHAPE=NIL retains its length but inserts NIL.
; Both cause the actual reader to write NIL into its :u60 destination column.
(defun-nx fn2-map-frame-invalid-source-control (shape)
 (let* ((valid (fn2-map-frame-valid-source))
        (bad (update-nth *fn2-extents-next-retired$ai* (if shape nil (list nil)) valid))
        (f (fn2-fields-init 8 (create-fn2-fields)))
        (result (fn2-checkpoint-frozen-map-entry 0 0 7 1 2 3 bad f)))
  (and (fn2-extentsp valid) (fn2-extents-wfp valid)
       (fn2-fieldsp f) (fn2-fields-wfp f)
       (if shape (and (fn2-extentsp bad) (not (fn2-extents-wfp bad)))
         (and (not (fn2-extentsp bad)) (fn2-extents-wfp bad)))
       (fn2-alloc-copy-ownerp 7 1 2 3 bad)
       (eq (mv-nth 0 result) :entry)
       (equal (fn2-fields-value *fn2-format-allocation-map-entry-field-next-retired* (mv-nth 1 result)) nil)
       (not (fn2-fieldsp (mv-nth 1 result)))
       (not (fn2-map-frame-original-type-claim 0 0 7 1 2 3 bad f)))))

; Ground actual-function witnesses, not failed proof searches. These source
; obligations remain unqualified until the scoped ACL2 gate executes them.
(defthm fn2-map-frame-missing-source-shape-counterexample
 (fn2-map-frame-invalid-source-control t)
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn2-map-frame-invalid-source-control
   fn2-map-frame-original-type-claim fn2-map-frame-valid-source
   fn2-checkpoint-frozen-map-entry fn2-alloc-copy-ownerp fn2-alloc-slotp
   ; The witness is ground. Reduce the actual constructors instead of letting
   ; opaque initialization terms create spurious allocator branches.
   fn2-alloc-init-links fn2-alloc-columns-init fn2-fields-init
   create-fn2-extents create-fn2-fields
   fn2-extentsp fn2-extents-wfp fn2-fieldsp fn2-fields-wfp))))
(defthm fn2-map-frame-missing-source-type-counterexample
 (fn2-map-frame-invalid-source-control nil)
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn2-map-frame-invalid-source-control
   fn2-map-frame-original-type-claim fn2-map-frame-valid-source
   fn2-checkpoint-frozen-map-entry fn2-alloc-copy-ownerp fn2-alloc-slotp
   ; The witness is ground. Reduce the actual constructors instead of letting
   ; opaque initialization terms create spurious allocator branches.
   fn2-alloc-init-links fn2-alloc-columns-init fn2-fields-init
   create-fn2-extents create-fn2-fields
   fn2-extentsp fn2-extents-wfp fn2-fieldsp fn2-fields-wfp))))
