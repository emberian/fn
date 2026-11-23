; Layer B productive checkpoint cut, retirement member submission/installation,
; and pin-gated extent reclamation over child stobjs (fn2-extents,
; fn2-alloc-edges, fn2-retirement-control, fn2-fields, fn2-pool).
(in-package "ACL2")
(include-book "retirement")
(include-book "columns-call-guards")
(include-book "std/util/bstar" :dir :system)
(fn2-book-layer :b)

(defun fn2-crs-shape-claims (outputs call)
 (declare (xargs :verify-guards nil))
 (if (atom outputs) nil
  (let* ((obj (caar outputs)) (at (cadar outputs))
         (value (if at `(mv-nth ,at ,call) call)))
   (append `((,(fn2-columns-sym obj "P") ,value)
             (,(fn2-columns-sym obj "-WFP") ,value)
             (equal (,(fn2-columns-sym obj "-ROWS") ,value) (,(fn2-columns-sym obj "-ROWS") ,obj)))
           (fn2-crs-shape-claims (cdr outputs) call)))))

(defmacro fn2-crs-shape (name call guard outputs)
 `(defthm ,name
   (implies ,guard (and ,@(fn2-crs-shape-claims outputs call)))))

(local (in-theory (disable
 fn2-extentsp fn2-extents-wfp fn2-extents-rows
 fn2-extents-state fn2-extents-retirement fn2-extents-next-retired
 fn2-extents-prev-retired fn2-extents-covered
 fn2-alloc-cut fn2-alloc-coverage fn2-alloc-pending
 fn2-alloc-freeze-phase fn2-alloc-frozenp fn2-alloc-slotp fn2-alloc-link-statep
 fn2-alloc-account)))

(local (defthm fn2-crs-next-retired-u32
 (implies (and (fn2-extentsp fn2-extents) (fn2-extents-wfp fn2-extents)
               (natp i) (< i (fn2-extents-rows fn2-extents)))
          (unsigned-byte-p 32 (fn2-extents-next-retired i fn2-extents)))
 :hints (("Goal" :in-theory (enable unsigned-byte-p integer-range-p)
                 :use (fn2-extents-next-retired-natp fn2-extents-next-retired-bound)))))

(local (defthm fn2-crs-cov-ret-u60
 (implies (fn2-extentsp fn2-extents)
          (and (unsigned-byte-p 60 (fn2-alloc-coverage fn2-extents))
               (implies (and (fn2-extents-wfp fn2-extents) (natp i) (< i (fn2-extents-rows fn2-extents)))
                        (unsigned-byte-p 60 (fn2-extents-retirement i fn2-extents)))))
 :hints (("Goal" :in-theory (enable unsigned-byte-p integer-range-p)
                 :use (fn2-alloc-coverage-bound fn2-extents-retirement-bound
                       fn2-alloc-coverage-natp fn2-extents-retirement-natp)))))

(local (defthm fn2-crs-slotp-u32
 (implies (and (fn2-extents-wfp fn2-extents) (fn2-alloc-slotp i fn2-extents))
          (unsigned-byte-p 32 i))
 :hints (("Goal" :in-theory (enable fn2-alloc-slotp fn2-extents-wfp unsigned-byte-p integer-range-p)))))

(fn2-extents-preserves fn2-alloc-checkpoint-drain (cut budget fn2-extents) :position 1
 :hyps ((fn2-extentsp fn2-extents) (fn2-extents-wfp fn2-extents) (unsigned-byte-p 60 cut))
 :hints (("Goal" :in-theory (enable fn2-alloc-checkpoint-drain fn2-alloc-frozenp fn2-alloc-slotp fn2-alloc-link-statep))))

(fn2-extents-preserves fn2-alloc-checkpoint-advance (cut budget fn2-extents) :position 1
 :hyps ((fn2-extentsp fn2-extents) (fn2-extents-wfp fn2-extents) (unsigned-byte-p 60 cut))
 :hints (("Goal" :in-theory (enable fn2-alloc-checkpoint-advance))))

(fn2-extents-preserves fn2-alloc-release (i epoch counter fn2-extents) :position 1
 :hyps ((fn2-extentsp fn2-extents) (fn2-extents-wfp fn2-extents))
 :hints (("Goal" :in-theory (enable fn2-alloc-release fn2-alloc-release-code)
                 :use ((:instance fn2-alloc-handle-code-ok-slotp)))))

(in-theory (disable fn2-alloc-reclaim-candidate))

; Keep heavy stobj recognizers & callees disabled so composed guards and shape proofs finish in <0.1s.
(local (in-theory (disable
 fn2-alloc-edgesp fn2-alloc-edges-wfp fn2-alloc-edges-rows
 fn2-retirement-controlp fn2-retirement-control-wfp fn2-retirement-control-rows
 fn2-retirement-control-state fn2-retirement-control-slot fn2-retirement-control-gen
 fn2-retirement-control-batch fn2-retirement-control-event
 fn2-retirement-control-owner-kind fn2-retirement-control-owner-slot fn2-retirement-control-owner-gen
 fn2-retirement-control-extent fn2-retirement-control-epoch fn2-retirement-control-allocation
 fn2-retirement-control-allocation-member fn2-retirement-control-installation-member
 fn2-fieldsp fn2-fields-wfp fn2-fields-rows fn2-fields-value
 fn2-poolp fn2-pool-wfp fn2-pool-rows fn2-pool-cap
 fn2-pool-reserve fn2-pool-release fn2-pool-release-countp fn2-pool-class-for
 fn2-alloc-retired-head fn2-alloc-retirement-intent-batch fn2-alloc-handle-code
 fn2-alloc-snapshot-prepare fn2-alloc-snapshot-release
 fn2-alloc-retirement-intent-begin fn2-alloc-retirement-intent-cancel fn2-alloc-retirement-intentp
 fn2-retirement-pack-member fn2-retirement-install
 fn2-format-txn-record-decode fn2-format-retirement-decode)))

; Factor out the 16-column control-row write so composed lifecycle steps verify
; guards in constant time.
(defun fn2-checkpoint-ctl-set-waiting (okind oslot ogen extent epoch allocation slot gen commit event
                                       fn2-retirement-control)
 (declare (xargs :stobjs fn2-retirement-control
  :guard (and (fn2-retirement-control-wfp fn2-retirement-control)
              (< 0 (fn2-retirement-control-rows fn2-retirement-control))
              (unsigned-byte-p 8 okind) (unsigned-byte-p 32 oslot) (unsigned-byte-p 60 ogen)
              (unsigned-byte-p 32 extent) (unsigned-byte-p 60 epoch) (unsigned-byte-p 60 allocation)
              (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
              (unsigned-byte-p 60 commit) (unsigned-byte-p 60 event))
  :guard-hints (("Goal" :in-theory (enable fn2-retirement-control-wfp fn2-retirement-control-rows)))))
 (fn2-retirement-control-put 0 (state *fn2-retirement-state-waiting*)
  (allocation-member 0) (installation-member 0) (installed 0) (count 0)
  (owner-kind okind) (owner-slot oslot) (owner-gen ogen)
  (extent extent) (epoch epoch) (allocation allocation)
  (slot slot) (gen gen) (batch commit) (event event)))

(fn2-retirement-control-preserves fn2-checkpoint-ctl-set-waiting
 (okind oslot ogen extent epoch allocation slot gen commit event fn2-retirement-control)
 :hyps ((fn2-retirement-controlp fn2-retirement-control) (fn2-retirement-control-wfp fn2-retirement-control)
        (< 0 (fn2-retirement-control-rows fn2-retirement-control))
        (unsigned-byte-p 8 okind) (unsigned-byte-p 32 oslot) (unsigned-byte-p 60 ogen)
        (unsigned-byte-p 32 extent) (unsigned-byte-p 60 epoch) (unsigned-byte-p 60 allocation)
        (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
        (unsigned-byte-p 60 commit) (unsigned-byte-p 60 event)))

(defun fn2-checkpoint-retire-member-capacity ()
 (declare (xargs :guard t))
 (+ *fn2-format-txn-record-max-size* *fn2-format-retirement-max-size*))

(local (defthm fn2-crs-pack-member-fields-rows
 (equal (fn2-fields-rows (mv-nth 2 (fn2-retirement-pack-member
                                     extent epoch allocation commit base slot gen off
                                     okind oslot ogen fn2-fields fn2-pool)))
        (fn2-fields-rows fn2-fields))
 :hints (("Goal" :in-theory (enable fn2-retirement-pack-member fn2-format-txn-record-encode fn2-fields-rows)))))

(local (defthm fn2-crs-pack-member-pool-rows
 (implies (and (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
          (equal (fn2-pool-rows (mv-nth 3 (fn2-retirement-pack-member
                                           extent epoch allocation commit base slot gen off
                                           okind oslot ogen fn2-fields fn2-pool)))
                 (fn2-pool-rows fn2-pool)))
 :hints (("Goal" :in-theory (enable fn2-retirement-pack-member)))))

(defun fn2-crs-release-quiet (slot gen okind oslot ogen fn2-pool)
 (declare (xargs :stobjs fn2-pool
  :guard (and (fn2-pool-wfp fn2-pool)
              (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
              (unsigned-byte-p 8 okind) (unsigned-byte-p 32 oslot) (unsigned-byte-p 60 ogen))))
 (if (and (< slot (fn2-pool-rows fn2-pool)) (fn2-pool-release-countp slot fn2-pool))
     (mv-let (rel fn2-pool) (fn2-pool-release slot gen okind oslot ogen fn2-pool)
      (declare (ignore rel))
      fn2-pool)
   fn2-pool))

(fn2-crs-shape fn2-crs-release-quiet-shape
 (fn2-crs-release-quiet slot gen okind oslot ogen fn2-pool)
 (and (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)
      (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
      (unsigned-byte-p 8 okind) (unsigned-byte-p 32 oslot) (unsigned-byte-p 60 ogen))
 ((fn2-pool nil)))

(in-theory (disable fn2-crs-release-quiet))

; ---------------------------------------------------------------------------
; 1. Child-Stobj Retirement Submission (fn2-retirement-submit-children)
;    Reserves workspace, packs framed *record-kind-retirement* member, opens
;    retirement intent on fn2-extents, and marks fn2-retirement-control waiting.

(defun fn2-retirement-submit-children-work (extent epoch allocation commit event base okind oslot ogen
                                            fn2-extents fn2-retirement-control fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-extents fn2-retirement-control fn2-fields fn2-pool)
  :guard (and (fn2-extents-wfp fn2-extents) (fn2-retirement-control-wfp fn2-retirement-control)
              (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))
  :guard-hints (("Goal" :use ((:instance fn2-alloc-handle-code-ok-slotp (i extent) (counter allocation)))
                        :in-theory (enable fn2-alloc-slotp fn2-alloc-frozenp)))))
 (b* (((unless (and (unsigned-byte-p 32 extent) (unsigned-byte-p 60 epoch) (unsigned-byte-p 60 allocation)
                    (posp commit) (unsigned-byte-p 60 commit) (unsigned-byte-p 60 event)
                    (natp base) (<= (+ base *fn2-format-txn-record-num-fields* *fn2-format-retirement-num-fields*)
                                    (fn2-fields-rows fn2-fields))
                    (posp okind) (unsigned-byte-p 8 okind) (unsigned-byte-p 32 oslot) (unsigned-byte-p 60 ogen)
                    (< 0 (fn2-retirement-control-rows fn2-retirement-control))))
       (mv :bounds 0 0 0 fn2-extents fn2-retirement-control fn2-fields fn2-pool))
      ((when (fn2-alloc-frozenp fn2-extents))
       (mv :frozen 0 0 0 fn2-extents fn2-retirement-control fn2-fields fn2-pool))
      ((unless (equal (fn2-retirement-control-state 0 fn2-retirement-control) *fn2-retirement-state-idle*))
       (mv :busy 0 0 0 fn2-extents fn2-retirement-control fn2-fields fn2-pool))
      ((unless (and (eq (fn2-alloc-handle-code extent epoch allocation fn2-extents) :ok)
                    (equal (fn2-extents-state extent fn2-extents) *fn2-extent-state-allocated*)
                    (equal (fn2-alloc-retirement-intent-batch fn2-extents) 0)))
       (mv :state 0 0 0 fn2-extents fn2-retirement-control fn2-fields fn2-pool))
      (class (fn2-pool-class-for (fn2-checkpoint-retire-member-capacity) fn2-pool))
      ((unless (natp class))
       (mv :capacity 0 0 0 fn2-extents fn2-retirement-control fn2-fields fn2-pool))
      ((mv rcode slot gen fn2-pool) (fn2-pool-reserve class okind oslot ogen fn2-pool))
      ((unless (and (eq rcode :ok) (unsigned-byte-p 32 slot) (< slot (fn2-pool-rows fn2-pool))
                    (unsigned-byte-p 60 gen)))
       (mv (if (eq rcode :exhausted) :exhausted :pool) 0 0 0
           fn2-extents fn2-retirement-control fn2-fields fn2-pool))
      ((mv pcode end fn2-fields fn2-pool)
       (fn2-retirement-pack-member extent epoch allocation commit base slot gen 0 okind oslot ogen fn2-fields fn2-pool))
      ((unless (and (eq pcode :ok) (posp end) (unsigned-byte-p 32 end)))
       (let ((fn2-pool (fn2-crs-release-quiet slot gen okind oslot ogen fn2-pool)))
        (mv (if (eq pcode :ok) :bounds pcode) 0 0 0
            fn2-extents fn2-retirement-control fn2-fields fn2-pool)))
      ((mv intent fn2-extents) (fn2-alloc-retirement-intent-begin extent epoch allocation commit fn2-extents))
      ((unless (eq intent :ok))
       (let ((fn2-pool (fn2-crs-release-quiet slot gen okind oslot ogen fn2-pool)))
        (mv intent 0 0 0 fn2-extents fn2-retirement-control fn2-fields fn2-pool)))
      (fn2-retirement-control
       (fn2-checkpoint-ctl-set-waiting okind oslot ogen extent epoch allocation slot gen commit event
                                       fn2-retirement-control)))
  (mv :ok slot gen end fn2-extents fn2-retirement-control fn2-fields fn2-pool)))

(fn2-crs-shape fn2-retirement-submit-children-work-shape
 (fn2-retirement-submit-children-work extent epoch allocation commit event base okind oslot ogen
                                      fn2-extents fn2-retirement-control fn2-fields fn2-pool)
 (and (fn2-extentsp fn2-extents) (fn2-extents-wfp fn2-extents)
      (fn2-retirement-controlp fn2-retirement-control) (fn2-retirement-control-wfp fn2-retirement-control)
      (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)
      (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
 ((fn2-extents 4) (fn2-retirement-control 5) (fn2-fields 6) (fn2-pool 7)))

(in-theory (disable fn2-retirement-submit-children-work))

(defun fn2-retirement-submit-children (extent epoch allocation commit event base okind oslot ogen
                                       fn2-extents fn2-retirement-control fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-extents fn2-retirement-control fn2-fields fn2-pool) :guard t))
 (if (and (fn2-extents-wfp fn2-extents) (fn2-retirement-control-wfp fn2-retirement-control)
          (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))
     (fn2-retirement-submit-children-work extent epoch allocation commit event base okind oslot ogen
                                          fn2-extents fn2-retirement-control fn2-fields fn2-pool)
   (mv :state 0 0 0 fn2-extents fn2-retirement-control fn2-fields fn2-pool)))

(fn2-crs-shape fn2-retirement-submit-children-shape
 (fn2-retirement-submit-children extent epoch allocation commit event base okind oslot ogen
                                 fn2-extents fn2-retirement-control fn2-fields fn2-pool)
 (and (fn2-extentsp fn2-extents) (fn2-extents-wfp fn2-extents)
      (fn2-retirement-controlp fn2-retirement-control) (fn2-retirement-control-wfp fn2-retirement-control)
      (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)
      (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
 ((fn2-extents 4) (fn2-retirement-control 5) (fn2-fields 6) (fn2-pool 7)))
(in-theory (disable fn2-retirement-submit-children))

; ---------------------------------------------------------------------------
; 2. Child-Stobj Retirement Commit Installation & Settlement
;    Decodes the persisted retirement member from (slot, gen, 0..end), verifies
;    control + intent agreement, installs retirement into fn2-extents, releases
;    the member workspace, and returns fn2-retirement-control to :idle.

(defun fn2-retirement-commit-children-work (commit event end base okind oslot ogen
                                            fn2-extents fn2-retirement-control fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-extents fn2-retirement-control fn2-fields fn2-pool)
  :guard (and (fn2-extents-wfp fn2-extents) (fn2-retirement-control-wfp fn2-retirement-control)
              (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))
  :guard-hints ((fn2-columns-guard-hint '(fn2-extents fn2-retirement-control fn2-fields fn2-pool)
                  '(fn2-format-txn-record-decode fn2-format-retirement-decode
                    fn2-alloc-retirement-intentp fn2-retirement-install
                    fn2-pool-release-countp fn2-pool-release)
                  nil world))))
 (b* (((unless (and (posp commit) (unsigned-byte-p 60 commit) (unsigned-byte-p 60 event)
                    (posp end) (unsigned-byte-p 32 end)
                    (natp base) (<= (+ base *fn2-format-txn-record-num-fields* *fn2-format-retirement-num-fields*)
                                    (fn2-fields-rows fn2-fields))
                    (posp okind) (unsigned-byte-p 8 okind) (unsigned-byte-p 32 oslot) (unsigned-byte-p 60 ogen)
                    (< 0 (fn2-retirement-control-rows fn2-retirement-control))))
       (mv :bounds fn2-extents fn2-retirement-control fn2-fields fn2-pool))
      ((unless (and (equal (fn2-retirement-control-state 0 fn2-retirement-control) *fn2-retirement-state-waiting*)
                    (equal (fn2-retirement-control-allocation-member 0 fn2-retirement-control) 0)
                    (equal (fn2-retirement-control-installation-member 0 fn2-retirement-control) 0)
                    (equal (fn2-retirement-control-owner-kind 0 fn2-retirement-control) okind)
                    (equal (fn2-retirement-control-owner-slot 0 fn2-retirement-control) oslot)
                    (equal (fn2-retirement-control-owner-gen 0 fn2-retirement-control) ogen)
                    (equal (fn2-retirement-control-batch 0 fn2-retirement-control) commit)
                    (equal (fn2-retirement-control-event 0 fn2-retirement-control) event)))
       (mv :state fn2-extents fn2-retirement-control fn2-fields fn2-pool))
      (slot (fn2-retirement-control-slot 0 fn2-retirement-control))
      (gen (fn2-retirement-control-gen 0 fn2-retirement-control))
      (extent (fn2-retirement-control-extent 0 fn2-retirement-control))
      (epoch (fn2-retirement-control-epoch 0 fn2-retirement-control))
      (allocation (fn2-retirement-control-allocation 0 fn2-retirement-control))
      ((mv dcode next fn2-fields)
       (fn2-format-txn-record-decode base slot gen 0 end okind oslot ogen fn2-fields fn2-pool))
      (body (+ base *fn2-format-txn-record-num-fields*))
      ((unless (and (eq dcode :ok) (natp next) (< 0 next) (unsigned-byte-p 32 next)
                    (<= (+ body *fn2-format-retirement-num-fields*) (fn2-fields-rows fn2-fields))
                    (equal (fn2-fields-value (+ base *fn2-format-txn-record-field-record-kind*) fn2-fields)
                           *record-kind-retirement*)
                    (equal (+ next (nfix (fn2-fields-value (+ base *fn2-format-txn-record-field-length*) fn2-fields))) end)))
       (mv :format fn2-extents fn2-retirement-control fn2-fields fn2-pool))
      ((mv fcode fend fn2-fields)
       (fn2-format-retirement-decode body slot gen next end okind oslot ogen fn2-fields fn2-pool))
      ((unless (and (eq fcode :ok) (equal fend end)
                    (<= (+ body *fn2-format-retirement-num-fields*) (fn2-fields-rows fn2-fields))
                    (fn2-alloc-retirement-intentp extent epoch allocation fn2-extents)
                    (equal commit (fn2-alloc-retirement-intent-batch fn2-extents))
                    (equal extent (fn2-fields-value (+ body *fn2-format-retirement-field-extent*) fn2-fields))
                    (equal epoch (fn2-fields-value (+ body *fn2-format-retirement-field-writer-epoch*) fn2-fields))
                    (equal allocation (fn2-fields-value (+ body *fn2-format-retirement-field-allocation*) fn2-fields))))
       (mv :format fn2-extents fn2-retirement-control fn2-fields fn2-pool))
      ((mv icode fn2-extents) (fn2-retirement-install commit body fn2-fields fn2-extents))
      ((unless (eq icode :ok))
       (mv icode fn2-extents fn2-retirement-control fn2-fields fn2-pool))
      ((unless (fn2-pool-release-countp slot fn2-pool))
       (let ((fn2-retirement-control (fn2-retirement-control-set-state 0 *fn2-retirement-state-uncertain* fn2-retirement-control)))
        (mv :uncertain fn2-extents fn2-retirement-control fn2-fields fn2-pool)))
      ((mv rel fn2-pool) (fn2-pool-release slot gen okind oslot ogen fn2-pool))
      ((unless (member-eq rel '(:ok :retired)))
       (let ((fn2-retirement-control (fn2-retirement-control-set-state 0 *fn2-retirement-state-uncertain* fn2-retirement-control)))
        (mv :uncertain fn2-extents fn2-retirement-control fn2-fields fn2-pool)))
      (fn2-retirement-control (fn2-retirement-control-set-state 0 *fn2-retirement-state-idle* fn2-retirement-control)))
  (mv :ok fn2-extents fn2-retirement-control fn2-fields fn2-pool)))

(fn2-crs-shape fn2-retirement-commit-children-work-shape
 (fn2-retirement-commit-children-work commit event end base okind oslot ogen
                                      fn2-extents fn2-retirement-control fn2-fields fn2-pool)
 (and (fn2-extentsp fn2-extents) (fn2-extents-wfp fn2-extents)
      (fn2-retirement-controlp fn2-retirement-control) (fn2-retirement-control-wfp fn2-retirement-control)
      (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)
      (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
 ((fn2-extents 1) (fn2-retirement-control 2) (fn2-fields 3) (fn2-pool 4)))

(in-theory (disable fn2-retirement-commit-children-work))

(defun fn2-retirement-commit-children (commit event end base okind oslot ogen
                                       fn2-extents fn2-retirement-control fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-extents fn2-retirement-control fn2-fields fn2-pool) :guard t))
 (if (and (fn2-extents-wfp fn2-extents) (fn2-retirement-control-wfp fn2-retirement-control)
          (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))
     (fn2-retirement-commit-children-work commit event end base okind oslot ogen
                                          fn2-extents fn2-retirement-control fn2-fields fn2-pool)
   (mv :state fn2-extents fn2-retirement-control fn2-fields fn2-pool)))

(fn2-crs-shape fn2-retirement-commit-children-shape
 (fn2-retirement-commit-children commit event end base okind oslot ogen
                                 fn2-extents fn2-retirement-control fn2-fields fn2-pool)
 (and (fn2-extentsp fn2-extents) (fn2-extents-wfp fn2-extents)
      (fn2-retirement-controlp fn2-retirement-control) (fn2-retirement-control-wfp fn2-retirement-control)
      (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)
      (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
 ((fn2-extents 1) (fn2-retirement-control 2) (fn2-fields 3) (fn2-pool 4)))
(in-theory (disable fn2-retirement-commit-children))

; ---------------------------------------------------------------------------
; 3. Composed Checkpoint Snapshot -> Cut -> Retirement Submit/Install -> Release
;    Over (fn2-extents, fn2-alloc-edges, fn2-retirement-control, fn2-fields, fn2-pool)

(defun fn2-checkpoint-cut-step (token cut budget okind oslot ogen fn2-extents)
 (declare (xargs :stobjs fn2-extents :guard t))
 (b* (((unless (fn2-extents-wfp fn2-extents)) (mv :state fn2-extents))
      ((unless (and (posp token) (unsigned-byte-p 60 token)
                    (posp cut) (unsigned-byte-p 60 cut)
                    (integerp budget) (<= 1 budget) (<= budget 32)))
       (mv :bounds fn2-extents))
      ((mv sp fn2-extents) (fn2-alloc-snapshot-prepare token okind oslot ogen fn2-extents))
      ((unless (eq sp :ok)) (mv sp fn2-extents))
      ((mv ac fn2-extents) (fn2-alloc-checkpoint-advance cut budget fn2-extents))
      ((mv sr fn2-extents) (fn2-alloc-snapshot-release token okind oslot ogen fn2-extents)))
  (mv (if (eq sr :ok) ac :uncertain) fn2-extents)))

(fn2-extents-preserves fn2-checkpoint-cut-step (token cut budget okind oslot ogen fn2-extents)
 :position 1 :disable t)

(defun fn2-checkpoint-reclaim-work (token cut budget extent epoch allocation retire-commit event
                                    base okind oslot ogen
                                    fn2-extents fn2-alloc-edges fn2-retirement-control fn2-fields fn2-pool)
 (declare (ignore fn2-alloc-edges)
          (xargs :stobjs (fn2-extents fn2-alloc-edges fn2-retirement-control fn2-fields fn2-pool)
  :guard (and (fn2-extents-wfp fn2-extents) (fn2-alloc-edges-wfp fn2-alloc-edges)
              (fn2-retirement-control-wfp fn2-retirement-control)
              (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))
  :guard-hints (("Goal" :use ((:instance fn2-alloc-handle-code-ok-slotp (i extent) (counter allocation)
                                         (fn2-extents (mv-nth 1 (fn2-alloc-snapshot-prepare token okind oslot ogen fn2-extents)))))
                        :in-theory (enable fn2-alloc-slotp)))))
 (b* (((unless (and (posp token) (unsigned-byte-p 60 token)
                    (posp cut) (unsigned-byte-p 60 cut)
                    (integerp budget) (<= 1 budget) (<= budget 32)
                    (unsigned-byte-p 32 extent) (unsigned-byte-p 60 epoch) (unsigned-byte-p 60 allocation)
                    (posp retire-commit) (unsigned-byte-p 60 retire-commit) (unsigned-byte-p 60 event)
                    (<= retire-commit cut)))
       (mv :bounds fn2-extents fn2-retirement-control fn2-fields fn2-pool))
      ((mv sp fn2-extents) (fn2-alloc-snapshot-prepare token okind oslot ogen fn2-extents))
      ((unless (eq sp :ok))
       (mv sp fn2-extents fn2-retirement-control fn2-fields fn2-pool))
      (hc (fn2-alloc-handle-code extent epoch allocation fn2-extents))
      (st (if (eq hc :ok) (fn2-extents-state extent fn2-extents) 0))
      ((mv rc fn2-extents fn2-retirement-control fn2-fields fn2-pool)
       (cond ((not (eq hc :ok)) (mv hc fn2-extents fn2-retirement-control fn2-fields fn2-pool))
             ((equal st *fn2-extent-state-allocated*)
              (b* (((mv sc & & end fn2-extents fn2-retirement-control fn2-fields fn2-pool)
                    (fn2-retirement-submit-children
                     extent epoch allocation retire-commit event base okind oslot ogen
                     fn2-extents fn2-retirement-control fn2-fields fn2-pool))
                   ((unless (eq sc :ok))
                    (mv sc fn2-extents fn2-retirement-control fn2-fields fn2-pool)))
               (fn2-retirement-commit-children
                retire-commit event end base okind oslot ogen
                fn2-extents fn2-retirement-control fn2-fields fn2-pool)))
             ((equal st *fn2-extent-state-retire-pending*)
              (mv :ok fn2-extents fn2-retirement-control fn2-fields fn2-pool))
             (t (mv :state fn2-extents fn2-retirement-control fn2-fields fn2-pool))))
      ((mv ac fn2-extents)
       (if (eq rc :ok) (fn2-alloc-checkpoint-advance cut budget fn2-extents) (mv rc fn2-extents)))
      ((mv rel fn2-extents)
       (if (eq ac :ok) (fn2-alloc-release extent epoch allocation fn2-extents) (mv ac fn2-extents)))
      ((mv sr fn2-extents) (fn2-alloc-snapshot-release token okind oslot ogen fn2-extents)))
  (mv (if (eq sr :ok) rel :uncertain) fn2-extents fn2-retirement-control fn2-fields fn2-pool)))

(fn2-crs-shape fn2-checkpoint-reclaim-work-shape
 (fn2-checkpoint-reclaim-work token cut budget extent epoch allocation retire-commit event
                              base okind oslot ogen
                              fn2-extents fn2-alloc-edges fn2-retirement-control fn2-fields fn2-pool)
 (and (fn2-extentsp fn2-extents) (fn2-extents-wfp fn2-extents)
      (fn2-retirement-controlp fn2-retirement-control) (fn2-retirement-control-wfp fn2-retirement-control)
      (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)
      (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
 ((fn2-extents 1) (fn2-retirement-control 2) (fn2-fields 3) (fn2-pool 4)))

(in-theory (disable fn2-checkpoint-reclaim-work))

(defun fn2-checkpoint-reclaim-step (token cut budget extent epoch allocation retire-commit event
                                    base okind oslot ogen
                                    fn2-extents fn2-alloc-edges fn2-retirement-control fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-extents fn2-alloc-edges fn2-retirement-control fn2-fields fn2-pool) :guard t))
 (if (and (fn2-extents-wfp fn2-extents) (fn2-alloc-edges-wfp fn2-alloc-edges)
          (fn2-retirement-control-wfp fn2-retirement-control)
          (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))
     (fn2-checkpoint-reclaim-work token cut budget extent epoch allocation retire-commit event
                                  base okind oslot ogen
                                  fn2-extents fn2-alloc-edges fn2-retirement-control fn2-fields fn2-pool)
   (mv :state fn2-extents fn2-retirement-control fn2-fields fn2-pool)))

(fn2-crs-shape fn2-checkpoint-reclaim-step-shape
 (fn2-checkpoint-reclaim-step token cut budget extent epoch allocation retire-commit event
                              base okind oslot ogen
                              fn2-extents fn2-alloc-edges fn2-retirement-control fn2-fields fn2-pool)
 (and (fn2-extentsp fn2-extents) (fn2-extents-wfp fn2-extents)
      (fn2-alloc-edges-wfp fn2-alloc-edges)
      (fn2-retirement-controlp fn2-retirement-control) (fn2-retirement-control-wfp fn2-retirement-control)
      (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)
      (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
 ((fn2-extents 1) (fn2-retirement-control 2) (fn2-fields 3) (fn2-pool 4)))

(in-theory (disable fn2-checkpoint-reclaim-step))

; Bounded FIFO reclamation sweep across retired extents whose retirement <=
; fn2-alloc-cut and active protector pin/lease count is zero.
(defun fn2-checkpoint-reclaim-drain-loop (limit fn2-extents)
 (declare (xargs :stobjs fn2-extents :measure (nfix limit)
  :guard (and (fn2-extents-wfp fn2-extents) (natp limit))
  :guard-hints (("Goal" :use ((:instance fn2-alloc-handle-code-ok-slotp
                                         (i (fn2-alloc-retired-head fn2-extents))
                                         (counter (mv-nth 3 (fn2-alloc-reclaim-candidate
                                                             (fn2-alloc-retired-head fn2-extents) fn2-extents)))))
                        :in-theory (enable fn2-alloc-slotp)))))
 (b* (((when (zp limit)) (mv :more 0 fn2-extents))
      (i (fn2-alloc-retired-head fn2-extents))
      ((mv code & epoch counter &) (fn2-alloc-reclaim-candidate i fn2-extents))
      ((when (eq code :done)) (mv :ok 0 fn2-extents))
      ((unless (eq code :ok)) (mv code 0 fn2-extents))
      ((unless (and (unsigned-byte-p 32 i) (unsigned-byte-p 60 epoch) (unsigned-byte-p 60 counter)))
       (mv :bounds 0 fn2-extents))
      ((mv rcode fn2-extents) (fn2-alloc-release i epoch counter fn2-extents))
      ((unless (eq rcode :ok)) (mv rcode 0 fn2-extents))
      ((mv tail-code reclaimed fn2-extents) (fn2-checkpoint-reclaim-drain-loop (- limit 1) fn2-extents)))
  (mv tail-code (+ 1 (nfix reclaimed)) fn2-extents)))

(fn2-extents-preserves fn2-checkpoint-reclaim-drain-loop (limit fn2-extents)
 :position 2 :disable t)

(defun fn2-checkpoint-reclaim-drain-step (token cut budget limit okind oslot ogen fn2-extents)
 (declare (xargs :stobjs fn2-extents :guard t))
 (b* (((unless (fn2-extents-wfp fn2-extents)) (mv :state 0 fn2-extents))
      ((unless (and (posp token) (unsigned-byte-p 60 token)
                    (posp cut) (unsigned-byte-p 60 cut)
                    (integerp budget) (<= 1 budget) (<= budget 32) (natp limit)))
       (mv :bounds 0 fn2-extents))
      ((mv sp fn2-extents) (fn2-alloc-snapshot-prepare token okind oslot ogen fn2-extents))
      ((unless (eq sp :ok)) (mv sp 0 fn2-extents))
      ((mv ac fn2-extents) (fn2-alloc-checkpoint-advance cut budget fn2-extents))
      ((mv sr fn2-extents) (fn2-alloc-snapshot-release token okind oslot ogen fn2-extents))
      ((unless (eq sr :ok)) (mv :uncertain 0 fn2-extents))
      ((unless (eq ac :ok)) (mv ac 0 fn2-extents)))
  (fn2-checkpoint-reclaim-drain-loop limit fn2-extents)))

(fn2-extents-preserves fn2-checkpoint-reclaim-drain-step (token cut budget limit okind oslot ogen fn2-extents)
 :position 2 :disable t)

; ---------------------------------------------------------------------------
; 4. Pin Safety & Executable Cut-Advance + Reclamation Witness

; Semantic pin safety: when an extent still carries an active protector pin/lease,
; fn2-alloc-release never succeeds and leaves fn2-extents untouched.
(defthm fn2-checkpoint-release-requires-zero-pins
 (implies (and (fn2-extents-wfp fn2-extents)
               (not (fn2-alloc-frozenp fn2-extents))
               (eq (fn2-alloc-handle-code i epoch counter fn2-extents) :ok)
               (= (fn2-extents-state i fn2-extents) *fn2-extent-state-retire-pending*)
               (fn2-alloc-protector i nil fn2-extents))
          (and (not (equal (mv-nth 0 (fn2-alloc-release i epoch counter fn2-extents)) :ok))
               (equal (mv-nth 1 (fn2-alloc-release i epoch counter fn2-extents)) fn2-extents)))
 :hints (("Goal" :in-theory (enable fn2-alloc-release fn2-alloc-release-code
                                    fn2-alloc-protector fn2-alloc-protector-list))))

(defun fn2-checkpoint-reclaim-witness-body (fn2-extents fn2-alloc-edges fn2-retirement-control fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-extents fn2-alloc-edges fn2-retirement-control fn2-fields fn2-pool)
  :verify-guards nil))
 (b* ((fn2-extents (fn2-alloc-init 4 fn2-extents))
      (fn2-alloc-edges (fn2-alloc-edges-init 8 fn2-alloc-edges))
      (fn2-retirement-control (fn2-retirement-control-init 1 fn2-retirement-control))
      (fn2-fields (fn2-fields-init 32 fn2-fields))
      (fn2-pool (fn2-pool-init '((4 . 1024)) 1 10 fn2-pool))
      ((mv ep-code fn2-extents) (fn2-alloc-begin-epoch 1 fn2-extents))
      ((mv r0 & e0 ep0 a0 fn2-extents) (fn2-alloc-reserve fn2-extents))
      ((mv c0 fn2-extents) (fn2-alloc-commit-allocation e0 ep0 a0 1 10 fn2-extents))
      ((mv eadd1 fn2-extents fn2-alloc-edges)
       (fn2-alloc-edge-add 0 50 e0 ep0 a0 :obligation fn2-extents fn2-alloc-edges))
      ((mv eadd2 fn2-extents fn2-alloc-edges)
       (fn2-alloc-edge-add 1 60 e0 ep0 a0 :promised-read fn2-extents fn2-alloc-edges))
      (cut-before (fn2-alloc-cut fn2-extents))
      ((mv blocked-code fn2-extents fn2-retirement-control fn2-fields fn2-pool)
       (fn2-checkpoint-reclaim-step 7 2 8 e0 ep0 a0 2 100 0 1 1 1
                                    fn2-extents fn2-alloc-edges fn2-retirement-control fn2-fields fn2-pool))
      (cut-mid (fn2-alloc-cut fn2-extents))
      (state-mid (fn2-extents-state e0 fn2-extents))
      ((mv d1 fn2-extents fn2-alloc-edges)
       (fn2-alloc-edge-drop 0 50 e0 ep0 a0 :obligation fn2-extents fn2-alloc-edges))
      ((mv d2 fn2-extents fn2-alloc-edges)
       (fn2-alloc-edge-drop 1 60 e0 ep0 a0 :promised-read fn2-extents fn2-alloc-edges))
      ((mv rel-code fn2-extents fn2-retirement-control fn2-fields fn2-pool)
       (fn2-checkpoint-reclaim-step 8 5 8 e0 ep0 a0 2 101 0 1 1 1
                                    fn2-extents fn2-alloc-edges fn2-retirement-control fn2-fields fn2-pool))
      (cut-after (fn2-alloc-cut fn2-extents))
      (state-after (fn2-extents-state e0 fn2-extents)))
  (mv (and (eq ep-code :ok) (eq r0 :ok) (eq c0 :ok)
           (eq eadd1 :ok) (eq eadd2 :ok)
           (= cut-before 0)
           (eq blocked-code :obligation)
           (= state-mid *fn2-extent-state-retire-pending*)
           (= cut-mid 2)
           (eq d1 :ok) (eq d2 :ok)
           (eq rel-code :ok)
           (< cut-before cut-after) (= cut-after 5)
           (= state-after *fn2-extent-state-free*)
           (= (fn2-alloc-total-free fn2-extents) 4)
           (fn2-alloc-invp fn2-extents)
           (fn2-alloc-ownership-invp fn2-extents fn2-alloc-edges))
      fn2-extents fn2-alloc-edges fn2-retirement-control fn2-fields fn2-pool)))

(defun fn2-checkpoint-reclaim-witness-run ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-extents
  (mv-let (ok fn2-extents)
   (with-local-stobj fn2-alloc-edges
    (mv-let (ok fn2-extents fn2-alloc-edges)
     (with-local-stobj fn2-retirement-control
      (mv-let (ok fn2-extents fn2-alloc-edges fn2-retirement-control)
       (with-local-stobj fn2-fields
        (mv-let (ok fn2-extents fn2-alloc-edges fn2-retirement-control fn2-fields)
         (with-local-stobj fn2-pool
          (mv-let (ok fn2-extents fn2-alloc-edges fn2-retirement-control fn2-fields fn2-pool)
           (fn2-checkpoint-reclaim-witness-body fn2-extents fn2-alloc-edges fn2-retirement-control fn2-fields fn2-pool)
           (mv ok fn2-extents fn2-alloc-edges fn2-retirement-control fn2-fields)))
         (mv ok fn2-extents fn2-alloc-edges fn2-retirement-control)))
       (mv ok fn2-extents fn2-alloc-edges)))
     (mv ok fn2-extents)))
   ok)))

(defthm fn2-checkpoint-cut-advances-and-reclaims-witness
 (equal (fn2-checkpoint-reclaim-witness-run) t))

(assert-event
 (fn2-assert-compliant-p
  '(fn2-retirement-submit-children
    fn2-retirement-commit-children
    fn2-checkpoint-cut-step
    fn2-checkpoint-reclaim-step
    fn2-checkpoint-reclaim-drain-step)
  (w state)))
