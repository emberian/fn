; The allocation effect of one persisted retirement record. Both live install
; and ordered recovery use this operation; decoding alone has no effect.
(in-package "ACL2")
(include-book "commit-alloc")
(include-book "format-events")
(fn2-book-layer :b)

; One B-owned lifecycle member may be in flight. The checkpoint worker owns
; the workspace and receives the normal commit wakeup; this row serializes
; producers and retains uncertainty independently of the commit row's reuse.
(defcolumns fn2-retirement-control
 ((state (:enum fn2-retirement-state (:idle :waiting :uncertain :scanning :staged)))
  (owner-kind :u8) (owner-slot :u32) (owner-gen :u60)
  (extent :u32) (epoch :u60) (allocation :u60)
  (slot :u32) (gen :u60) (batch :u60) (event :u60)
  (allocation-member :bool) (installation-member :bool) (candidate :u32) (expected :u32) (journal-ticket :u60) (final-ticket :bool) (token :u60) (scan :u32) (count :u32) (bytes :u32) (installed :u32) (install-offset :u32)))

(fn2-extents-preserves fn2-alloc-retire (i epoch counter commit fn2-extents)
 :position 1
 :hyps ((fn2-extentsp fn2-extents) (fn2-extents-wfp fn2-extents)
        (unsigned-byte-p 60 commit))
 ; Match the existing opaque allocator-account row frame before exposing NTH.
 :hints (("Goal" :in-theory (disable fn2-extents-rows))))

(defun fn2-retirement-install (commit base fn2-fields fn2-extents)
 (declare (xargs :stobjs (fn2-fields fn2-extents)
                 :guard (and (fn2-fields-wfp fn2-fields) (fn2-extents-wfp fn2-extents))))
 (if (not (and (posp commit) (unsigned-byte-p 60 commit) (natp base)
               (<= (+ base *fn2-format-retirement-num-fields*) (fn2-fields-rows fn2-fields))))
     (mv :bounds fn2-extents)
  (let ((i (fn2-fields-value (+ base *fn2-format-retirement-field-extent*) fn2-fields))
        (epoch (fn2-fields-value (+ base *fn2-format-retirement-field-writer-epoch*) fn2-fields))
        (counter (fn2-fields-value (+ base *fn2-format-retirement-field-allocation*) fn2-fields))
        (record-commit (fn2-fields-value (+ base *fn2-format-retirement-field-retirement-commit*) fn2-fields)))
   (cond ((not (equal commit record-commit)) (mv :commit fn2-extents))
         ((not (eq (fn2-alloc-handle-code i epoch counter fn2-extents) :ok))
          (mv :identity fn2-extents))
         ; Resuming installation of the same recorded transition is harmless.
         ; A different retirement is not last-writer-wins and cannot replace it.
         ((= (fn2-extents-state i fn2-extents) *fn2-extent-state-retire-pending*)
          (mv (if (= (fn2-extents-retirement i fn2-extents) commit) :ok :retirement-conflict)
              fn2-extents))
         (t (fn2-alloc-retire i epoch counter commit fn2-extents))))))
(fn2-extents-preserves fn2-retirement-install (commit base fn2-fields fn2-extents)
 :position 1
 :hints (("Goal" :in-theory (disable fn2-extents-rows))))

; A bounded member producer. COMMIT is selected by the live batch planner,
; never supplied by the host. Frame the existing body codec as an ordinary
; txn member: the existing sealed journal stream is the sole write path.
; The retained member length occupies one u60 field. Derive its actual
; codec-size bound once so both guard and carrier proofs share the interface.
(encapsulate ()
 (local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))
 (local
  (defthm fn2-retirement-varsize-coarse-bound
 (<= (fn2-layout-varsize v) (+ 1 (floor (nfix v) 128)))
 :rule-classes :linear
 :hints (("Goal" :induct (fn2-layout-varsize v)
                  :in-theory (e/d (fn2-layout-varsize) (floor))))))
(defthm fn2-format-retirement-size-fits-field
 (implies (and (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)
               (natp base) (<= (+ base 4) (fn2-fields-rows fn2-fields)))
          (< (fn2-format-retirement-size base fn2-fields) (expt 2 60)))
 :rule-classes :linear
 :hints (("Goal" :use ((:instance fn2-retirement-varsize-coarse-bound (v (fn2-fields-value (+ base 0) fn2-fields)))
          (:instance fn2-retirement-varsize-coarse-bound (v (fn2-fields-value (+ base 1) fn2-fields)))
          (:instance fn2-retirement-varsize-coarse-bound (v (fn2-fields-value (+ base 2) fn2-fields)))
          (:instance fn2-retirement-varsize-coarse-bound (v (fn2-fields-value (+ base 3) fn2-fields))))
 :in-theory (e/d (fn2-format-retirement-size fn2-format-retirement-size-extent
 fn2-format-retirement-size-writer-epoch fn2-format-retirement-size-allocation
 fn2-format-retirement-size-retirement-commit)
 (floor fn2-layout-varsize fn2-fields-value fn2-fields-rows fn2-fieldsp fn2-fields-wfp))))))

(defun fn2-retirement-pack-member (extent epoch allocation commit base slot gen off
                                 okind oslot ogen fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-fields fn2-pool)
                 :guard (and (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))))
 (if (not (and (unsigned-byte-p 60 extent) (unsigned-byte-p 60 epoch)
               (unsigned-byte-p 60 allocation) (posp commit) (unsigned-byte-p 60 commit)
               (natp base) (<= (+ base *fn2-format-txn-record-num-fields*
                                  *fn2-format-retirement-num-fields*) (fn2-fields-rows fn2-fields))
               (unsigned-byte-p 32 off) (unsigned-byte-p 8 okind)
               (unsigned-byte-p 32 oslot) (unsigned-byte-p 60 ogen)))
     (mv :bounds 0 fn2-fields fn2-pool)
  (let* ((body (+ base *fn2-format-txn-record-num-fields*))
         (fn2-fields (fn2-fields-set-value (+ body *fn2-format-retirement-field-extent*) extent fn2-fields))
         (fn2-fields (fn2-fields-set-value (+ body *fn2-format-retirement-field-writer-epoch*) epoch fn2-fields))
         (fn2-fields (fn2-fields-set-value (+ body *fn2-format-retirement-field-allocation*) allocation fn2-fields))
         (fn2-fields (fn2-fields-set-value (+ body *fn2-format-retirement-field-retirement-commit*) commit fn2-fields))
         (bytes (fn2-format-retirement-size body fn2-fields))
         (fn2-fields (fn2-fields-set-value (+ base *fn2-format-txn-record-field-record-kind*) *record-kind-retirement* fn2-fields))
         (fn2-fields (fn2-fields-set-value (+ base *fn2-format-txn-record-field-length*) bytes fn2-fields)))
   (mv-let (code next fn2-pool)
    (fn2-format-txn-record-encode base slot gen off okind oslot ogen fn2-fields fn2-pool)
    (if (not (eq code :ok)) (mv code next fn2-fields fn2-pool)
     (mv-let (code end fn2-pool)
      (fn2-format-retirement-encode body slot gen next okind oslot ogen fn2-fields fn2-pool)
      (mv code end fn2-fields fn2-pool)))))))
(fn2-pool-preserves fn2-retirement-pack-member
 (extent epoch allocation commit base slot gen off okind oslot ogen fn2-fields fn2-pool)
 :carriers ((fn2-fields 2 :prefix "-FIELDS") (fn2-pool 3 :prefix "-POOL")))
