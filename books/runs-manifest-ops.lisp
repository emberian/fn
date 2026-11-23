; Layer C allocator-backed run-page addressing, durable page-write descriptors,
; and live fn2-manifest (:id 10) entry codec + fn2-run-installed reconstruction.
(in-package "ACL2")
(include-book "runs-cache-evict")
(include-book "runs-manifest")
(include-book "pool-digest")
(include-book "commit-alloc")
(include-book "commit-geometry")
(include-book "columns-call-guards")
(include-book "std/util/bstar" :dir :system)
(fn2-book-layer :c)

(defconst *fn2-manifest-sid* 10)

(assert-event
 (and (equal *fn2-manifest-entry-num-fields* 12)
      (equal (* *fn2-commit-unit-bytes* *fn2-storage-extent-units*) *fn2-run-page-size*)
      (equal *fn2-storage-extent-bytes* *fn2-run-page-size*)))

; ---------------------------------------------------------------------------
; 1. Extent <-> Physical Unit & Byte Offset Bijection

(defun fn2-run-extent-unit (extent)
 (declare (xargs :guard (natp extent)))
 (* *fn2-storage-extent-units* (nfix extent)))

(defun fn2-run-unit-extent (unit)
 (declare (xargs :guard (natp unit)))
 (floor (nfix unit) *fn2-storage-extent-units*))

(defun fn2-run-extent-byte-offset (extent)
 (declare (xargs :guard (natp extent)))
 (* *fn2-storage-extent-bytes* (nfix extent)))

(defthm fn2-run-extent-unit-u60
 (implies (unsigned-byte-p 32 extent)
          (unsigned-byte-p 60 (fn2-run-extent-unit extent)))
 :hints (("Goal" :in-theory (enable unsigned-byte-p integer-range-p))))

(defthm fn2-run-extent-byte-offset-u60
 (implies (unsigned-byte-p 32 extent)
          (unsigned-byte-p 60 (fn2-run-extent-byte-offset extent)))
 :hints (("Goal" :in-theory (enable unsigned-byte-p integer-range-p))))

(encapsulate ()
 (local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))
 (defthm fn2-run-unit-extent-of-extent-unit
  (equal (fn2-run-unit-extent (fn2-run-extent-unit extent))
         (nfix extent)))

 (defthm fn2-run-extent-unit-injective
  (implies (and (natp e1) (natp e2))
           (equal (equal (fn2-run-extent-unit e1) (fn2-run-extent-unit e2))
                  (equal e1 e2)))))

(in-theory (disable fn2-run-extent-unit fn2-run-unit-extent fn2-run-extent-byte-offset))

; ---------------------------------------------------------------------------
; 2. Durable 64 KiB Page-Write Descriptors

(defcolumns fn2-run-page-writes
 ((state (:enum fn2-run-page-write-state (:free :pending :committed)))
  (extent :u32)
  (unit :u60)
  (byte-offset :u60)
  (epoch :u60)
  (allocation :u60)
  (page-kind :u8)
  (encoded-length :u32)
  (slot :u32)
  (gen :u60)
  (hash-row :u32)))

(local (defthm fn2-rmo-u-from-range
 (implies (and (natp bits) (integerp v) (<= 0 v) (< v (expt 2 bits)))
          (unsigned-byte-p bits v))
 :hints (("Goal" :in-theory (enable unsigned-byte-p integer-range-p)))))

(local (defthm fn2-rmo-u-forward
 (implies (unsigned-byte-p bits v)
          (and (integerp v) (<= 0 v)))
 :rule-classes :forward-chaining
 :hints (("Goal" :in-theory (enable unsigned-byte-p integer-range-p)))))

(local (defthm fn2-rmo-u8-bound
 (implies (unsigned-byte-p 8 v) (< v 256))
 :rule-classes :forward-chaining
 :hints (("Goal" :in-theory (enable unsigned-byte-p integer-range-p)))))

(local (defthm fn2-rmo-u32-bound
 (implies (unsigned-byte-p 32 v) (< v 4294967296))
 :rule-classes :forward-chaining
 :hints (("Goal" :in-theory (enable unsigned-byte-p integer-range-p)))))

(local (defthm fn2-rmo-u60-bound
 (implies (unsigned-byte-p 60 v) (< v 1152921504606846976))
 :rule-classes :forward-chaining
 :hints (("Goal" :in-theory (enable unsigned-byte-p integer-range-p)))))

(local (in-theory (disable
 unsigned-byte-p integer-range-p fn2-digest-rowp
 fn2-extentsp fn2-extents-wfp fn2-extents-rows
 fn2-run-cachep fn2-run-cache-wfp fn2-run-cache-rows
 fn2-run-buildsp fn2-run-builds-wfp fn2-run-builds-rows
 fn2-run-builds-schema fn2-run-builds-height fn2-run-builds-wbase fn2-run-builds-hbase
 fn2-run-builds-okind fn2-run-builds-oslot fn2-run-builds-ogen
 fn2-run-writersp fn2-run-writers-wfp fn2-run-writers-rows
 fn2-run-writers-phase fn2-run-writers-unit fn2-run-writers-epoch fn2-run-writers-counter
 fn2-run-writers-page-kind fn2-run-writers-slot fn2-run-writers-gen
 fn2-run-installedp fn2-run-installed-wfp fn2-run-installed-rows
 fn2-run-page-writesp fn2-run-page-writes-wfp fn2-run-page-writes-rows
 fn2-run-page-writes-state fn2-run-page-writes-extent fn2-run-page-writes-unit
 fn2-run-page-writes-epoch fn2-run-page-writes-allocation
 fn2-run-page-writes-slot fn2-run-page-writes-gen fn2-run-page-writes-hash-row
 fn2-fieldsp fn2-fields-wfp fn2-fields-rows fn2-fields-value
 fn2-fields-ref-slot fn2-fields-ref-gen fn2-fields-ref-off fn2-fields-ref-len
 fn2-poolp fn2-pool-wfp fn2-pool-rows fn2-pool-cap fn2-pool-fill
 fn2-digestsp fn2-digests-wfp fn2-digests-rows
 fn2-pool-reserve fn2-pool-reset fn2-pool-copy-range fn2-pool-truncate fn2-pool-class-for
 fn2-digest-store fn2-digest-copy fn2-rec-fetch fn2-run-zero
 fn2-run-cache-install fn2-run-install fn2-run-install-filter)))

(fn2-fc-shape fn2-run-build-page-kind-shape
 (fn2-run-build-page-kind b level slot gen unit epoch counter page-kind fn2-run-builds fn2-run-writers fn2-pool)
 (and (fn2-run-buildsp fn2-run-builds) (fn2-run-builds-wfp fn2-run-builds)
      (fn2-run-writersp fn2-run-writers) (fn2-run-writers-wfp fn2-run-writers)
      (fn2-run-buildp b fn2-run-builds fn2-run-writers)
      (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
 ((fn2-run-builds 1) (fn2-run-writers 2) (fn2-pool 3)))

(in-theory (disable fn2-run-build-page-kind fn2-run-buildp))

; ---------------------------------------------------------------------------
; 3. Allocator-Backed Page Reservation & Eviction-Safe Pool Allocation

(defun fn2-rmo-cancel-quiet (extent epoch allocation fn2-extents)
 (declare (xargs :stobjs fn2-extents
  :guard (and (fn2-extents-wfp fn2-extents)
              (unsigned-byte-p 32 extent) (unsigned-byte-p 60 epoch) (unsigned-byte-p 60 allocation))))
 (mv-let (ccode fn2-extents)
   (fn2-alloc-cancel-reservation extent epoch allocation fn2-extents)
  (declare (ignore ccode))
  fn2-extents))

(fn2-fc-shape fn2-rmo-cancel-quiet-shape
 (fn2-rmo-cancel-quiet extent epoch allocation fn2-extents)
 (and (fn2-extentsp fn2-extents) (fn2-extents-wfp fn2-extents)
      (unsigned-byte-p 32 extent) (unsigned-byte-p 60 epoch) (unsigned-byte-p 60 allocation))
 ((fn2-extents nil)))

(in-theory (disable fn2-rmo-cancel-quiet))

; Reserve a 64 KiB workspace from fn2-pool, evicting one unpinned cached page on
; :exhausted so nonresident runs never hit a fatal RAM cache-full cliff.
(defun fn2-rmo-reserve-pool-page (okind oslot ogen fn2-run-cache fn2-pool)
 (declare (xargs :stobjs (fn2-run-cache fn2-pool)
  :guard (and (fn2-run-cache-wfp fn2-run-cache) (fn2-pool-wfp fn2-pool)
              (unsigned-byte-p 8 okind) (unsigned-byte-p 32 oslot) (unsigned-byte-p 60 ogen))))
 (b* ((class (fn2-pool-class-for *fn2-run-page-size* fn2-pool))
      ((unless (natp class))
       (mv :capacity 0 0 fn2-run-cache fn2-pool))
      ((mv rcode slot gen fn2-pool) (fn2-pool-reserve class okind oslot ogen fn2-pool))
      ((when (and (eq rcode :ok) (unsigned-byte-p 32 slot) (< slot (fn2-pool-rows fn2-pool))
                  (unsigned-byte-p 60 gen)))
       (mv :ok slot gen fn2-run-cache fn2-pool))
      ((unless (eq rcode :exhausted))
       (mv (if (eq rcode :ok) :bounds rcode) 0 0 fn2-run-cache fn2-pool))
      ((mv ecode fn2-run-cache fn2-pool)
       (fn2-run-cache-evict-one 0 (fn2-run-cache-rows fn2-run-cache) okind oslot ogen fn2-run-cache fn2-pool))
      ((unless (eq ecode :ok))
       (mv :exhausted 0 0 fn2-run-cache fn2-pool))
      ((mv rcode2 slot2 gen2 fn2-pool) (fn2-pool-reserve class okind oslot ogen fn2-pool))
      ((unless (and (eq rcode2 :ok) (unsigned-byte-p 32 slot2) (< slot2 (fn2-pool-rows fn2-pool))
                    (unsigned-byte-p 60 gen2)))
       (mv (if (eq rcode2 :ok) :bounds rcode2) 0 0 fn2-run-cache fn2-pool)))
  (mv :ok slot2 gen2 fn2-run-cache fn2-pool)))

(fn2-fc-shape fn2-rmo-reserve-pool-page-shape
 (fn2-rmo-reserve-pool-page okind oslot ogen fn2-run-cache fn2-pool)
 (and (fn2-run-cachep fn2-run-cache) (fn2-run-cache-wfp fn2-run-cache)
      (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)
      (unsigned-byte-p 8 okind) (unsigned-byte-p 32 oslot) (unsigned-byte-p 60 ogen))
 ((fn2-run-cache 3) (fn2-pool 4)))

(in-theory (disable fn2-rmo-reserve-pool-page))

; Reserve a real extent (EXTENT, EPOCH, ALLOCATION) via fn2-alloc-reserve,
; derive physical sector unit = 16 * EXTENT, clear any unpinned direct-mapped
; cache occupant on UNIT, and reserve a 64 KiB pool workspace (SLOT, GEN).
; Cancels the extent reservation cleanly on any cache/pool refusal.
(defun fn2-run-reserve-page-work (okind oslot ogen fn2-extents fn2-run-cache fn2-pool)
 (declare (xargs :stobjs (fn2-extents fn2-run-cache fn2-pool)
  :guard (and (fn2-extents-wfp fn2-extents) (fn2-run-cache-wfp fn2-run-cache) (fn2-pool-wfp fn2-pool))))
 (b* (((unless (and (unsigned-byte-p 8 okind) (unsigned-byte-p 32 oslot) (unsigned-byte-p 60 ogen)
                    (< 0 (fn2-run-cache-rows fn2-run-cache))))
       (mv :bounds 0 0 0 0 0 0 fn2-extents fn2-run-cache fn2-pool))
      ((mv acode & extent epoch allocation fn2-extents) (fn2-alloc-reserve fn2-extents))
      ((unless (eq acode :ok))
       (mv acode 0 0 0 0 0 0 fn2-extents fn2-run-cache fn2-pool))
      ((unless (and (unsigned-byte-p 32 extent) (unsigned-byte-p 60 epoch) (unsigned-byte-p 60 allocation)))
       (mv :bounds 0 0 0 0 0 0 fn2-extents fn2-run-cache fn2-pool))
      (unit (fn2-run-extent-unit extent))
      ((mv ecode fn2-run-cache fn2-pool)
       (fn2-run-cache-evict-for-unit unit okind oslot ogen fn2-run-cache fn2-pool))
      ((unless (eq ecode :ok))
       (let ((fn2-extents (fn2-rmo-cancel-quiet extent epoch allocation fn2-extents)))
        (mv ecode 0 0 0 0 0 0 fn2-extents fn2-run-cache fn2-pool)))
      ((mv pcode slot gen fn2-run-cache fn2-pool)
       (fn2-rmo-reserve-pool-page okind oslot ogen fn2-run-cache fn2-pool))
      ((unless (and (eq pcode :ok) (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)))
       (let ((fn2-extents (fn2-rmo-cancel-quiet extent epoch allocation fn2-extents)))
        (mv (if (eq pcode :ok) :bounds pcode) 0 0 0 0 0 0 fn2-extents fn2-run-cache fn2-pool))))
  (mv :ok extent unit epoch allocation slot gen fn2-extents fn2-run-cache fn2-pool)))

(fn2-fc-shape fn2-run-reserve-page-work-shape
 (fn2-run-reserve-page-work okind oslot ogen fn2-extents fn2-run-cache fn2-pool)
 (and (fn2-extentsp fn2-extents) (fn2-extents-wfp fn2-extents)
      (fn2-run-cachep fn2-run-cache) (fn2-run-cache-wfp fn2-run-cache)
      (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
 ((fn2-extents 7) (fn2-run-cache 8) (fn2-pool 9)))

(in-theory (disable fn2-run-reserve-page-work))

(defun fn2-run-reserve-page (okind oslot ogen fn2-extents fn2-run-cache fn2-pool)
 (declare (xargs :stobjs (fn2-extents fn2-run-cache fn2-pool) :guard t))
 (if (and (fn2-extents-wfp fn2-extents) (fn2-run-cache-wfp fn2-run-cache) (fn2-pool-wfp fn2-pool))
     (fn2-run-reserve-page-work okind oslot ogen fn2-extents fn2-run-cache fn2-pool)
   (mv :state 0 0 0 0 0 0 fn2-extents fn2-run-cache fn2-pool)))

(fn2-fc-shape fn2-run-reserve-page-shape
 (fn2-run-reserve-page okind oslot ogen fn2-extents fn2-run-cache fn2-pool)
 (and (fn2-extentsp fn2-extents) (fn2-extents-wfp fn2-extents)
      (fn2-run-cachep fn2-run-cache) (fn2-run-cache-wfp fn2-run-cache)
      (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
 ((fn2-extents 7) (fn2-run-cache 8) (fn2-pool 9)))

(defthm fn2-run-reserve-page-unit-bijection
 (let ((res (fn2-run-reserve-page okind oslot ogen fn2-extents fn2-run-cache fn2-pool)))
  (implies (equal (car res) :ok)
           (and (unsigned-byte-p 32 (mv-nth 1 res))
                (unsigned-byte-p 60 (mv-nth 2 res))
                (unsigned-byte-p 60 (mv-nth 3 res))
                (unsigned-byte-p 60 (mv-nth 4 res))
                (unsigned-byte-p 32 (mv-nth 5 res))
                (unsigned-byte-p 60 (mv-nth 6 res))
                (equal (mv-nth 2 res) (fn2-run-extent-unit (mv-nth 1 res)))
                (equal (fn2-run-unit-extent (mv-nth 2 res)) (mv-nth 1 res)))))
 :hints (("Goal" :in-theory (e/d (fn2-run-reserve-page fn2-run-reserve-page-work)
                                 (unsigned-byte-p)))))

(in-theory (disable fn2-run-reserve-page))

; Open level LEVEL of run build B backed by a real reserved allocator extent
; (supporting both ordinary :run-data/:run-index schemas and :manifest sid=10).
(defun fn2-run-build-alloc-page (b level fn2-extents fn2-run-builds fn2-run-writers fn2-run-cache fn2-pool)
 (declare (xargs :stobjs (fn2-extents fn2-run-builds fn2-run-writers fn2-run-cache fn2-pool) :guard t
  :guard-hints ((fn2-columns-guard-hint
                  '(fn2-extents fn2-run-builds fn2-run-writers fn2-run-cache fn2-pool)
                  '(fn2-run-reserve-page fn2-run-build-page-kind fn2-run-pio-release-quiet fn2-rmo-cancel-quiet)
                  '(fn2-run-buildp) world))))
 (b* (((unless (and (fn2-extents-wfp fn2-extents) (fn2-run-builds-wfp fn2-run-builds)
                    (fn2-run-writers-wfp fn2-run-writers) (fn2-run-cache-wfp fn2-run-cache)
                    (fn2-pool-wfp fn2-pool)))
       (mv :state 0 0 0 0 0 0 fn2-extents fn2-run-builds fn2-run-writers fn2-run-cache fn2-pool))
      ((unless (and (fn2-run-buildp b fn2-run-builds fn2-run-writers)
                    (natp b) (< b (fn2-run-builds-rows fn2-run-builds))
                    (natp level) (< level *fn2-run-max-levels*)
                    (< level (fn2-run-builds-height b fn2-run-builds))))
       (mv :bounds 0 0 0 0 0 0 fn2-extents fn2-run-builds fn2-run-writers fn2-run-cache fn2-pool))
      (okind (fn2-run-builds-okind b fn2-run-builds))
      (oslot (fn2-run-builds-oslot b fn2-run-builds))
      (ogen (fn2-run-builds-ogen b fn2-run-builds))
      (sid (fn2-run-builds-schema b fn2-run-builds))
      (page-kind (if (zp level)
                     (if (equal sid *fn2-manifest-sid*) *page-kind-manifest* *page-kind-run-data*)
                   *page-kind-run-index*))
      ((mv rcode extent unit epoch allocation slot gen fn2-extents fn2-run-cache fn2-pool)
       (fn2-run-reserve-page okind oslot ogen fn2-extents fn2-run-cache fn2-pool))
      ((unless (eq rcode :ok))
       (mv rcode 0 0 0 0 0 0 fn2-extents fn2-run-builds fn2-run-writers fn2-run-cache fn2-pool))
      ((mv bcode fn2-run-builds fn2-run-writers fn2-pool)
       (fn2-run-build-page-kind b level slot gen unit epoch allocation page-kind
                                fn2-run-builds fn2-run-writers fn2-pool))
      ((unless (eq bcode :ok))
       (let* ((fn2-pool (fn2-run-pio-release-quiet slot gen okind oslot ogen fn2-pool))
              (fn2-extents (fn2-rmo-cancel-quiet extent epoch allocation fn2-extents)))
        (mv bcode 0 0 0 0 0 0 fn2-extents fn2-run-builds fn2-run-writers fn2-run-cache fn2-pool))))
  (mv :ok extent unit epoch allocation slot gen
      fn2-extents fn2-run-builds fn2-run-writers fn2-run-cache fn2-pool)))

(fn2-fc-shape fn2-run-build-alloc-page-shape
 (fn2-run-build-alloc-page b level fn2-extents fn2-run-builds fn2-run-writers fn2-run-cache fn2-pool)
 (and (fn2-extentsp fn2-extents) (fn2-extents-wfp fn2-extents)
      (fn2-run-buildsp fn2-run-builds) (fn2-run-builds-wfp fn2-run-builds)
      (fn2-run-writersp fn2-run-writers) (fn2-run-writers-wfp fn2-run-writers)
      (fn2-run-cachep fn2-run-cache) (fn2-run-cache-wfp fn2-run-cache)
      (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
 ((fn2-extents 7) (fn2-run-builds 8) (fn2-run-writers 9) (fn2-run-cache 10) (fn2-pool 11)))

(in-theory (disable fn2-run-build-alloc-page))

; ---------------------------------------------------------------------------
; 4. Durable Page-Write Descriptor Emission & Commit

(defun fn2-rmo-write-desc-put (drow extent unit byte-off epoch allocation page-kind slot gen hash-row
                               fn2-run-page-writes)
 (declare (xargs :stobjs fn2-run-page-writes
  :guard (and (fn2-run-page-writes-wfp fn2-run-page-writes)
              (natp drow) (< drow (fn2-run-page-writes-rows fn2-run-page-writes))
              (unsigned-byte-p 32 extent) (unsigned-byte-p 60 unit) (unsigned-byte-p 60 byte-off)
              (unsigned-byte-p 60 epoch) (unsigned-byte-p 60 allocation)
              (unsigned-byte-p 8 page-kind) (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
              (unsigned-byte-p 32 hash-row))))
 (fn2-run-page-writes-put drow
  (state *fn2-run-page-write-state-pending*)
  (extent extent) (unit unit) (byte-offset byte-off)
  (epoch epoch) (allocation allocation) (page-kind page-kind) (encoded-length *fn2-run-page-size*)
  (slot slot) (gen gen) (hash-row hash-row)))

(fn2-fc-shape fn2-rmo-write-desc-put-shape
 (fn2-rmo-write-desc-put drow extent unit byte-off epoch allocation page-kind slot gen hash-row
                         fn2-run-page-writes)
 (and (fn2-run-page-writesp fn2-run-page-writes) (fn2-run-page-writes-wfp fn2-run-page-writes)
      (natp drow) (< drow (fn2-run-page-writes-rows fn2-run-page-writes))
      (unsigned-byte-p 32 extent) (unsigned-byte-p 60 unit) (unsigned-byte-p 60 byte-off)
      (unsigned-byte-p 60 epoch) (unsigned-byte-p 60 allocation)
      (unsigned-byte-p 8 page-kind) (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
      (unsigned-byte-p 32 hash-row))
 ((fn2-run-page-writes nil)))

(in-theory (disable fn2-rmo-write-desc-put))

; Emit a concrete 64 KiB durable page-write descriptor from sealed writer level
; LEVEL of build B and copy its finalized BLAKE3 parent hash into HASH-ROW of
; fn2-digests.
(defun fn2-run-emit-page-write (drow hash-row b level fn2-run-builds fn2-run-writers fn2-digests fn2-run-page-writes)
 (declare (xargs :stobjs (fn2-run-builds fn2-run-writers fn2-digests fn2-run-page-writes) :guard t
  :guard-hints ((fn2-columns-guard-hint
                  '(fn2-run-builds fn2-run-writers fn2-digests fn2-run-page-writes)
                  '(fn2-rmo-write-desc-put fn2-digest-copy fn2-run-unit-extent fn2-run-extent-unit fn2-run-extent-byte-offset)
                  '(fn2-digest-rowp) world))))
 (b* (((unless (and (fn2-run-builds-wfp fn2-run-builds) (fn2-run-writers-wfp fn2-run-writers)
                    (fn2-digests-wfp fn2-digests) (fn2-run-page-writes-wfp fn2-run-page-writes)))
       (mv :state fn2-digests fn2-run-page-writes))
      ((unless (and (natp drow) (< drow (fn2-run-page-writes-rows fn2-run-page-writes))
                    (unsigned-byte-p 32 hash-row) (fn2-digest-rowp hash-row fn2-digests)
                    (natp b) (< b (fn2-run-builds-rows fn2-run-builds))
                    (natp level) (< level *fn2-run-max-levels*)))
       (mv :bounds fn2-digests fn2-run-page-writes))
      ((unless (equal (fn2-run-page-writes-state drow fn2-run-page-writes) *fn2-run-page-write-state-free*))
       (mv :busy fn2-digests fn2-run-page-writes))
      (w (+ (fn2-run-builds-wbase b fn2-run-builds) level))
      (hrow (+ (fn2-run-builds-hbase b fn2-run-builds) level))
      ((unless (and (< w (fn2-run-writers-rows fn2-run-writers))
                    (fn2-digest-rowp hrow fn2-digests)))
       (mv :bounds fn2-digests fn2-run-page-writes))
      ((unless (equal (fn2-run-writers-phase w fn2-run-writers) *fn2-run-writer-phase-sealed*))
       (mv :state fn2-digests fn2-run-page-writes))
      (unit (fn2-run-writers-unit w fn2-run-writers))
      (extent (fn2-run-unit-extent unit))
      ((unless (and (unsigned-byte-p 32 extent) (equal unit (fn2-run-extent-unit extent))))
       (mv :alignment fn2-digests fn2-run-page-writes))
      (byte-off (fn2-run-extent-byte-offset extent))
      (epoch (fn2-run-writers-epoch w fn2-run-writers))
      (allocation (fn2-run-writers-counter w fn2-run-writers))
      (pkind (fn2-run-writers-page-kind w fn2-run-writers))
      (slot (fn2-run-writers-slot w fn2-run-writers))
      (gen (fn2-run-writers-gen w fn2-run-writers))
      (fn2-digests (fn2-digest-copy hash-row hrow fn2-digests))
      (fn2-run-page-writes
       (fn2-rmo-write-desc-put drow extent unit byte-off epoch allocation pkind slot gen hash-row
                               fn2-run-page-writes)))
  (mv :ok fn2-digests fn2-run-page-writes)))

(fn2-fc-shape fn2-run-emit-page-write-shape
 (fn2-run-emit-page-write drow hash-row b level fn2-run-builds fn2-run-writers fn2-digests fn2-run-page-writes)
 (and (fn2-run-buildsp fn2-run-builds) (fn2-run-builds-wfp fn2-run-builds)
      (fn2-run-writersp fn2-run-writers) (fn2-run-writers-wfp fn2-run-writers)
      (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests)
      (fn2-run-page-writesp fn2-run-page-writes) (fn2-run-page-writes-wfp fn2-run-page-writes))
 ((fn2-digests 1) (fn2-run-page-writes 2)))

(in-theory (disable fn2-run-emit-page-write))

; Commit a persisted 64 KiB page-write descriptor DROW: transition its reserved
; extent to :allocated under (OWNER-KIND, OWNER-ID), evict any unpinned cache
; collision on UNIT, install (UNIT, ALLOCATION, SLOT, GEN) into fn2-run-cache,
; and mark DROW :committed.
(defun fn2-run-commit-page-write (drow owner-kind owner-id okind oslot ogen
                                  fn2-extents fn2-run-cache fn2-pool fn2-run-page-writes)
 (declare (xargs :stobjs (fn2-extents fn2-run-cache fn2-pool fn2-run-page-writes) :guard t
  :guard-hints ((fn2-columns-guard-hint
                  '(fn2-extents fn2-run-cache fn2-pool fn2-run-page-writes)
                  '(fn2-run-cache-evict-for-unit fn2-alloc-commit-allocation fn2-run-cache-install)
                  nil world))))
 (b* (((unless (and (fn2-extents-wfp fn2-extents) (fn2-run-cache-wfp fn2-run-cache)
                    (fn2-pool-wfp fn2-pool) (fn2-run-page-writes-wfp fn2-run-page-writes)))
       (mv :state fn2-extents fn2-run-cache fn2-pool fn2-run-page-writes))
      ((unless (and (natp drow) (< drow (fn2-run-page-writes-rows fn2-run-page-writes))
                    (< 0 (fn2-run-cache-rows fn2-run-cache))
                    (unsigned-byte-p 8 owner-kind) (unsigned-byte-p 60 owner-id)
                    (unsigned-byte-p 8 okind) (unsigned-byte-p 32 oslot) (unsigned-byte-p 60 ogen)))
       (mv :bounds fn2-extents fn2-run-cache fn2-pool fn2-run-page-writes))
      ((unless (equal (fn2-run-page-writes-state drow fn2-run-page-writes) *fn2-run-page-write-state-pending*))
       (mv :state fn2-extents fn2-run-cache fn2-pool fn2-run-page-writes))
      (extent (fn2-run-page-writes-extent drow fn2-run-page-writes))
      (unit (fn2-run-page-writes-unit drow fn2-run-page-writes))
      (epoch (fn2-run-page-writes-epoch drow fn2-run-page-writes))
      (allocation (fn2-run-page-writes-allocation drow fn2-run-page-writes))
      (slot (fn2-run-page-writes-slot drow fn2-run-page-writes))
      (gen (fn2-run-page-writes-gen drow fn2-run-page-writes))
      ((mv ecode fn2-run-cache fn2-pool)
       (fn2-run-cache-evict-for-unit unit okind oslot ogen fn2-run-cache fn2-pool))
      ((unless (eq ecode :ok))
       (mv ecode fn2-extents fn2-run-cache fn2-pool fn2-run-page-writes))
      ((mv ccode fn2-extents)
       (fn2-alloc-commit-allocation extent epoch allocation owner-kind owner-id fn2-extents))
      ((unless (eq ccode :ok))
       (mv ccode fn2-extents fn2-run-cache fn2-pool fn2-run-page-writes))
      ((mv icode fn2-run-cache) (fn2-run-cache-install unit allocation slot gen fn2-run-cache))
      ((unless (eq icode :ok))
       (mv icode fn2-extents fn2-run-cache fn2-pool fn2-run-page-writes))
      (fn2-run-page-writes
       (fn2-run-page-writes-set-state drow *fn2-run-page-write-state-committed* fn2-run-page-writes)))
  (mv :ok fn2-extents fn2-run-cache fn2-pool fn2-run-page-writes)))

(fn2-fc-shape fn2-run-commit-page-write-shape
 (fn2-run-commit-page-write drow owner-kind owner-id okind oslot ogen
                            fn2-extents fn2-run-cache fn2-pool fn2-run-page-writes)
 (and (fn2-extentsp fn2-extents) (fn2-extents-wfp fn2-extents)
      (fn2-run-cachep fn2-run-cache) (fn2-run-cache-wfp fn2-run-cache)
      (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)
      (fn2-run-page-writesp fn2-run-page-writes) (fn2-run-page-writes-wfp fn2-run-page-writes))
 ((fn2-extents 1) (fn2-run-cache 2) (fn2-pool 3) (fn2-run-page-writes 4)))

(in-theory (disable fn2-run-commit-page-write))

; Copy the 256-bit parent-held BLAKE3 digest recorded on page-write descriptor
; DROW into digest row DST of fn2-digests.
(defun fn2-run-page-write-extract-hash (drow dst fn2-run-page-writes fn2-digests)
 (declare (xargs :stobjs (fn2-run-page-writes fn2-digests) :guard t
  :guard-hints ((fn2-columns-guard-hint '(fn2-run-page-writes fn2-digests) '(fn2-digest-copy) nil world))))
 (b* (((unless (and (fn2-run-page-writes-wfp fn2-run-page-writes) (fn2-digests-wfp fn2-digests)
                    (natp drow) (< drow (fn2-run-page-writes-rows fn2-run-page-writes))
                    (fn2-digest-rowp dst fn2-digests)))
       (mv :bounds fn2-digests))
      (src (fn2-run-page-writes-hash-row drow fn2-run-page-writes))
      ((unless (fn2-digest-rowp src fn2-digests))
       (mv :bounds fn2-digests))
      (fn2-digests (fn2-digest-copy dst src fn2-digests)))
  (mv :ok fn2-digests)))

(fn2-fc-shape fn2-run-page-write-extract-hash-shape
 (fn2-run-page-write-extract-hash drow dst fn2-run-page-writes fn2-digests)
 (and (fn2-run-page-writesp fn2-run-page-writes) (fn2-run-page-writes-wfp fn2-run-page-writes)
      (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests))
 ((fn2-digests 1)))

(in-theory (disable fn2-run-page-write-extract-hash))

; ---------------------------------------------------------------------------
; 5. Live fn2-manifest (:id 10) Entry Stage, Codec & fn2-run-installed Install

(defun fn2-manifest-pack-capacity ()
 (declare (xargs :guard t))
 (+ 64 *fn2-manifest-entry-max-size*))

(defun fn2-rmo-set-manifest-fields (ebase hslot hgen hoff schema run height entries
                                    root-unit root-epoch root-allocation
                                    filter-unit filter-epoch filter-allocation fn2-fields)
 (declare (xargs :stobjs fn2-fields
  :guard (and (fn2-fields-wfp fn2-fields) (natp ebase)
              (<= (+ ebase *fn2-manifest-entry-num-fields*) (fn2-fields-rows fn2-fields))
              (unsigned-byte-p 32 hslot) (unsigned-byte-p 60 hgen)
              (unsigned-byte-p 32 hoff) (unsigned-byte-p 32 (+ hoff 32))
              (unsigned-byte-p 60 schema) (unsigned-byte-p 60 run)
              (unsigned-byte-p 8 height) (unsigned-byte-p 60 entries)
              (unsigned-byte-p 60 root-unit) (unsigned-byte-p 60 root-epoch) (unsigned-byte-p 60 root-allocation)
              (unsigned-byte-p 60 filter-unit) (unsigned-byte-p 60 filter-epoch) (unsigned-byte-p 60 filter-allocation))))
 (b* ((fn2-fields (fn2-fields-set-value (+ ebase *fn2-manifest-entry-field-schema*) schema fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ ebase *fn2-manifest-entry-field-run*) run fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ ebase *fn2-manifest-entry-field-height*) height fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ ebase *fn2-manifest-entry-field-entries*) entries fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ ebase *fn2-manifest-entry-field-root-unit*) root-unit fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ ebase *fn2-manifest-entry-field-root-epoch*) root-epoch fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ ebase *fn2-manifest-entry-field-root-allocation*) root-allocation fn2-fields))
      (fn2-fields (fn2-fields-put (+ ebase *fn2-manifest-entry-field-root-hash*)
                   (value 1) (ref-slot hslot) (ref-gen hgen) (ref-off hoff) (ref-len 32)))
      (fn2-fields (fn2-fields-set-value (+ ebase *fn2-manifest-entry-field-filter-unit*) filter-unit fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ ebase *fn2-manifest-entry-field-filter-epoch*) filter-epoch fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ ebase *fn2-manifest-entry-field-filter-allocation*) filter-allocation fn2-fields))
      (fn2-fields (fn2-fields-put (+ ebase *fn2-manifest-entry-field-filter-hash*)
                   (value 1) (ref-slot hslot) (ref-gen hgen) (ref-off (+ hoff 32)) (ref-len 32))))
  fn2-fields))

(fn2-fc-shape fn2-rmo-set-manifest-fields-shape
 (fn2-rmo-set-manifest-fields ebase hslot hgen hoff schema run height entries
                              root-unit root-epoch root-allocation
                              filter-unit filter-epoch filter-allocation fn2-fields)
 (and (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields) (natp ebase)
      (<= (+ ebase *fn2-manifest-entry-num-fields*) (fn2-fields-rows fn2-fields))
      (unsigned-byte-p 32 hslot) (unsigned-byte-p 60 hgen)
      (unsigned-byte-p 32 hoff) (unsigned-byte-p 32 (+ hoff 32))
      (unsigned-byte-p 60 schema) (unsigned-byte-p 60 run)
      (unsigned-byte-p 8 height) (unsigned-byte-p 60 entries)
      (unsigned-byte-p 60 root-unit) (unsigned-byte-p 60 root-epoch) (unsigned-byte-p 60 root-allocation)
      (unsigned-byte-p 60 filter-unit) (unsigned-byte-p 60 filter-epoch) (unsigned-byte-p 60 filter-allocation))
 ((fn2-fields nil)))

(in-theory (disable fn2-rmo-set-manifest-fields))

; Stage a live fn2-manifest entry at field base EBASE with digest bytes materialized
; at [HOFF..HOFF+64) of (HSLOT, HGEN). Ready for fn2-run-build-add on sid=10 or
; standalone serialization via fn2-manifest-pack-entry.
(defun fn2-manifest-stage-entry (ebase hslot hgen hoff
                                 schema run height entries
                                 root-unit root-epoch root-allocation root-hrow
                                 filter-p filter-unit filter-epoch filter-allocation filter-hrow
                                 okind oslot ogen fn2-fields fn2-pool fn2-digests)
 (declare (xargs :stobjs (fn2-fields fn2-pool fn2-digests) :guard t))
 (b* (((unless (and (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool) (fn2-digests-wfp fn2-digests)))
       (mv :state fn2-fields fn2-pool))
      ((unless (and (natp ebase) (<= (+ ebase *fn2-manifest-entry-num-fields*) (fn2-fields-rows fn2-fields))
                    (unsigned-byte-p 32 hslot) (< hslot (fn2-pool-rows fn2-pool)) (unsigned-byte-p 60 hgen)
                    (unsigned-byte-p 32 hoff) (unsigned-byte-p 32 (+ hoff 64))
                    (unsigned-byte-p 60 schema) (unsigned-byte-p 60 run)
                    (posp height) (<= height *fn2-run-max-levels*) (unsigned-byte-p 8 height)
                    (unsigned-byte-p 60 entries)
                    (unsigned-byte-p 60 root-unit) (unsigned-byte-p 60 root-epoch) (unsigned-byte-p 60 root-allocation)
                    (fn2-digest-rowp root-hrow fn2-digests)
                    (booleanp filter-p)
                    (or (not filter-p)
                        (and (unsigned-byte-p 60 filter-unit)
                             (unsigned-byte-p 60 filter-epoch)
                             (unsigned-byte-p 60 filter-allocation)
                             (fn2-digest-rowp filter-hrow fn2-digests)))
                    (unsigned-byte-p 8 okind) (unsigned-byte-p 32 oslot) (unsigned-byte-p 60 ogen)))
       (mv :bounds fn2-fields fn2-pool))
      ((mv dcode1 fn2-pool)
       (fn2-digest-store 32 root-hrow hslot hgen hoff okind oslot ogen fn2-digests fn2-pool))
      ((unless (eq dcode1 :ok))
       (mv dcode1 fn2-fields fn2-pool))
      ((mv dcode2 fn2-pool)
       (if filter-p
           (fn2-digest-store 32 filter-hrow hslot hgen (+ hoff 32) okind oslot ogen fn2-digests fn2-pool)
         (fn2-run-zero 32 hslot hgen (+ hoff 32) okind oslot ogen fn2-pool)))
      ((unless (eq dcode2 :ok))
       (mv dcode2 fn2-fields fn2-pool))
      (funit (if filter-p filter-unit 0))
      (fepoch (if filter-p filter-epoch 0))
      (falloc (if filter-p filter-allocation 0))
      (fn2-fields
       (fn2-rmo-set-manifest-fields ebase hslot hgen hoff schema run height entries
                                    root-unit root-epoch root-allocation
                                    funit fepoch falloc fn2-fields)))
  (mv :ok fn2-fields fn2-pool)))

(fn2-fc-shape fn2-manifest-stage-entry-shape
 (fn2-manifest-stage-entry ebase hslot hgen hoff
                           schema run height entries
                           root-unit root-epoch root-allocation root-hrow
                           filter-p filter-unit filter-epoch filter-allocation filter-hrow
                           okind oslot ogen fn2-fields fn2-pool fn2-digests)
 (and (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)
      (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)
      (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests))
 ((fn2-fields 1) (fn2-pool 2)))

(in-theory (disable fn2-manifest-stage-entry))

; Single-workspace serializer for one live fn2-manifest entry: stages digests at
; [0..64), encodes fn2-manifest-entry at offset 64, moves the encoded bytes down
; to 0 via fn2-pool-copy-range, and truncates fill to exact encoded length.
(defun fn2-manifest-pack-entry (ebase slot gen
                                schema run height entries
                                root-unit root-epoch root-allocation root-hrow
                                filter-p filter-unit filter-epoch filter-allocation filter-hrow
                                okind oslot ogen fn2-fields fn2-pool fn2-digests)
 (declare (xargs :stobjs (fn2-fields fn2-pool fn2-digests) :guard t))
 (b* (((unless (and (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool) (fn2-digests-wfp fn2-digests)))
       (mv :state 0 fn2-fields fn2-pool))
      ((unless (and (natp ebase) (<= (+ ebase *fn2-manifest-entry-num-fields*) (fn2-fields-rows fn2-fields))
                    (unsigned-byte-p 32 slot) (< slot (fn2-pool-rows fn2-pool)) (unsigned-byte-p 60 gen)
                    (<= (fn2-manifest-pack-capacity) (fn2-pool-cap slot fn2-pool))
                    (unsigned-byte-p 8 okind) (unsigned-byte-p 32 oslot) (unsigned-byte-p 60 ogen)))
       (mv :bounds 0 fn2-fields fn2-pool))
      ((mv rcode fn2-pool) (fn2-pool-reset slot gen okind oslot ogen fn2-pool))
      ((unless (eq rcode :ok))
       (mv rcode 0 fn2-fields fn2-pool))
      ((mv scode fn2-fields fn2-pool)
       (fn2-manifest-stage-entry ebase slot gen 0
                                 schema run height entries
                                 root-unit root-epoch root-allocation root-hrow
                                 filter-p filter-unit filter-epoch filter-allocation filter-hrow
                                 okind oslot ogen fn2-fields fn2-pool fn2-digests))
      ((unless (eq scode :ok))
       (mv scode 0 fn2-fields fn2-pool))
      ((mv ecode end fn2-pool)
       (fn2-manifest-entry-encode ebase slot gen 64 okind oslot ogen fn2-fields fn2-pool))
      ((unless (and (eq ecode :ok) (natp end) (< 64 end) (unsigned-byte-p 32 end)))
       (mv (if (eq ecode :ok) :format ecode) 0 fn2-fields fn2-pool))
      (length (- end 64))
      ((mv ccode fn2-pool)
       (fn2-pool-copy-range slot gen 64 slot gen 0 length okind oslot ogen fn2-pool))
      ((unless (eq ccode :ok))
       (mv ccode 0 fn2-fields fn2-pool))
      ((mv tcode fn2-pool)
       (fn2-pool-truncate slot gen length okind oslot ogen fn2-pool)))
  (mv tcode (if (eq tcode :ok) length 0) fn2-fields fn2-pool)))

(fn2-fc-shape fn2-manifest-pack-entry-shape
 (fn2-manifest-pack-entry ebase slot gen
                          schema run height entries
                          root-unit root-epoch root-allocation root-hrow
                          filter-p filter-unit filter-epoch filter-allocation filter-hrow
                          okind oslot ogen fn2-fields fn2-pool fn2-digests)
 (and (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)
      (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)
      (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests))
 ((fn2-fields 2) (fn2-pool 3)))

(in-theory (disable fn2-manifest-pack-entry))

(local (defthm fn2-rmo-rec-fetch-preserves-rowp
 (implies (and (fn2-digestsp fn2-digests)
               (fn2-digest-rowp dst fn2-digests)
               (fn2-digest-rowp r fn2-digests))
          (fn2-digest-rowp r (mv-nth 1 (fn2-rec-fetch k dst slot gen off okind oslot ogen fn2-pool fn2-digests))))
 :hints (("Goal" :in-theory (enable fn2-digest-rowp)
                 :use ((:instance fn2-rec-fetch-shape))))))

(defun fn2-manifest-filter-present-p (u e a)
 (declare (xargs :guard (and (natp u) (natp e) (natp a))))
 (or (< 0 u) (< 0 e) (< 0 a)))

(in-theory (disable fn2-manifest-filter-present-p))

(defun fn2-rmo-fetch-entry-digests (rhf fhf root-hdst filter-hdst okind oslot ogen
                                    fn2-fields fn2-pool fn2-digests)
 (declare (xargs :stobjs (fn2-fields fn2-pool fn2-digests)
  :guard (and (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool) (fn2-digests-wfp fn2-digests)
              (natp rhf) (< rhf (fn2-fields-rows fn2-fields))
              (natp fhf) (< fhf (fn2-fields-rows fn2-fields))
              (fn2-digest-rowp root-hdst fn2-digests)
              (fn2-digest-rowp filter-hdst fn2-digests)
              (unsigned-byte-p 8 okind) (unsigned-byte-p 32 oslot) (unsigned-byte-p 60 ogen))))
 (b* (((unless (and (equal (fn2-fields-ref-len rhf fn2-fields) 32)
                    (equal (fn2-fields-ref-len fhf fn2-fields) 32)))
       (mv :format fn2-digests))
      ((mv fcode1 fn2-digests)
       (fn2-rec-fetch 0 root-hdst
                      (fn2-fields-ref-slot rhf fn2-fields)
                      (fn2-fields-ref-gen rhf fn2-fields)
                      (nfix (fn2-fields-ref-off rhf fn2-fields))
                      okind oslot ogen fn2-pool fn2-digests))
      ((unless (eq fcode1 :ok))
       (mv fcode1 fn2-digests)))
  (fn2-rec-fetch 0 filter-hdst
                 (fn2-fields-ref-slot fhf fn2-fields)
                 (fn2-fields-ref-gen fhf fn2-fields)
                 (nfix (fn2-fields-ref-off fhf fn2-fields))
                 okind oslot ogen fn2-pool fn2-digests)))

(fn2-fc-shape fn2-rmo-fetch-entry-digests-shape
 (fn2-rmo-fetch-entry-digests rhf fhf root-hdst filter-hdst okind oslot ogen
                              fn2-fields fn2-pool fn2-digests)
 (and (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)
      (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)
      (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests)
      (natp rhf) (< rhf (fn2-fields-rows fn2-fields))
      (natp fhf) (< fhf (fn2-fields-rows fn2-fields))
      (fn2-digest-rowp root-hdst fn2-digests)
      (fn2-digest-rowp filter-hdst fn2-digests)
      (unsigned-byte-p 8 okind) (unsigned-byte-p 32 oslot) (unsigned-byte-p 60 ogen))
 ((fn2-digests 1)))

(in-theory (disable fn2-rmo-fetch-entry-digests))

; Extract a decoded fn2-manifest-entry from field base EBASE (either decoded
; standalone or delivered by fn2-run-scan-step / fn2-run-lookup-step at
; (+ rb *fn2-run-reader-entry*)) and load its 32-byte root/filter digests into
; ROOT-HDST and FILTER-HDST.
(defun fn2-manifest-read-entry (ebase root-hdst filter-hdst okind oslot ogen
                                fn2-fields fn2-pool fn2-digests)
 (declare (xargs :stobjs (fn2-fields fn2-pool fn2-digests) :guard t))
 (b* (((unless (and (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool) (fn2-digests-wfp fn2-digests)))
       (mv :state 0 0 0 0 0 0 0 nil 0 0 0 fn2-digests))
      ((unless (and (natp ebase) (<= (+ ebase *fn2-manifest-entry-num-fields*) (fn2-fields-rows fn2-fields))
                    (fn2-digest-rowp root-hdst fn2-digests)
                    (fn2-digest-rowp filter-hdst fn2-digests)
                    (not (equal root-hdst filter-hdst))
                    (unsigned-byte-p 8 okind) (unsigned-byte-p 32 oslot) (unsigned-byte-p 60 ogen)))
       (mv :bounds 0 0 0 0 0 0 0 nil 0 0 0 fn2-digests))
      (schema (fn2-fields-value (+ ebase *fn2-manifest-entry-field-schema*) fn2-fields))
      (run (fn2-fields-value (+ ebase *fn2-manifest-entry-field-run*) fn2-fields))
      (height (fn2-fields-value (+ ebase *fn2-manifest-entry-field-height*) fn2-fields))
      (entries (fn2-fields-value (+ ebase *fn2-manifest-entry-field-entries*) fn2-fields))
      (root-unit (fn2-fields-value (+ ebase *fn2-manifest-entry-field-root-unit*) fn2-fields))
      (root-epoch (fn2-fields-value (+ ebase *fn2-manifest-entry-field-root-epoch*) fn2-fields))
      (root-alloc (fn2-fields-value (+ ebase *fn2-manifest-entry-field-root-allocation*) fn2-fields))
      (filter-unit (fn2-fields-value (+ ebase *fn2-manifest-entry-field-filter-unit*) fn2-fields))
      (filter-epoch (fn2-fields-value (+ ebase *fn2-manifest-entry-field-filter-epoch*) fn2-fields))
      (filter-alloc (fn2-fields-value (+ ebase *fn2-manifest-entry-field-filter-allocation*) fn2-fields))
      ((unless (and (unsigned-byte-p 60 schema) (unsigned-byte-p 60 run)
                    (posp height) (<= height *fn2-run-max-levels*) (unsigned-byte-p 8 height)
                    (unsigned-byte-p 60 entries)
                    (unsigned-byte-p 60 root-unit) (unsigned-byte-p 60 root-epoch) (unsigned-byte-p 60 root-alloc)
                    (unsigned-byte-p 60 filter-unit) (unsigned-byte-p 60 filter-epoch) (unsigned-byte-p 60 filter-alloc)))
       (mv :format 0 0 0 0 0 0 0 nil 0 0 0 fn2-digests))
      ((mv fcode fn2-digests)
       (fn2-rmo-fetch-entry-digests (+ ebase *fn2-manifest-entry-field-root-hash*)
                                    (+ ebase *fn2-manifest-entry-field-filter-hash*)
                                    root-hdst filter-hdst okind oslot ogen
                                    fn2-fields fn2-pool fn2-digests))
      ((unless (eq fcode :ok))
       (mv fcode 0 0 0 0 0 0 0 nil 0 0 0 fn2-digests))
      (filter-p (fn2-manifest-filter-present-p filter-unit filter-epoch filter-alloc)))
  (mv :ok schema run height entries root-unit root-epoch root-alloc
      filter-p filter-unit filter-epoch filter-alloc fn2-digests)))

(fn2-fc-shape fn2-manifest-read-entry-shape
 (fn2-manifest-read-entry ebase root-hdst filter-hdst okind oslot ogen
                          fn2-fields fn2-pool fn2-digests)
 (and (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)
      (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)
      (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests))
 ((fn2-digests 12)))

(defthm fn2-manifest-read-entry-ok-props
 (let ((res (fn2-manifest-read-entry ebase root-hdst filter-hdst okind oslot ogen
                                     fn2-fields fn2-pool fn2-digests)))
  (implies (equal (car res) :ok)
           (and (unsigned-byte-p 60 (mv-nth 1 res))
                (unsigned-byte-p 60 (mv-nth 2 res))
                (posp (mv-nth 3 res))
                (<= (mv-nth 3 res) *fn2-run-max-levels*)
                (unsigned-byte-p 60 (mv-nth 4 res))
                (unsigned-byte-p 60 (mv-nth 5 res))
                (unsigned-byte-p 60 (mv-nth 7 res))
                (unsigned-byte-p 60 (mv-nth 9 res))
                (unsigned-byte-p 60 (mv-nth 11 res)))))
 :hints (("Goal" :in-theory (e/d (fn2-manifest-read-entry)
                                 (unsigned-byte-p posp)))))

(in-theory (disable fn2-manifest-read-entry))

; Decode [0..LEN) of workspace (SLOT, GEN) as a standalone fn2-manifest-entry
; and extract its fields + 256-bit root/filter hashes.
(defun fn2-manifest-unpack-entry (ebase slot gen len root-hdst filter-hdst okind oslot ogen
                                  fn2-fields fn2-pool fn2-digests)
 (declare (xargs :stobjs (fn2-fields fn2-pool fn2-digests) :guard t))
 (b* (((unless (and (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool) (fn2-digests-wfp fn2-digests)))
       (mv :state 0 0 0 0 0 0 0 nil 0 0 0 fn2-fields fn2-digests))
      ((unless (and (natp ebase) (<= (+ ebase *fn2-manifest-entry-num-fields*) (fn2-fields-rows fn2-fields))
                    (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
                    (posp len) (unsigned-byte-p 32 len)
                    (unsigned-byte-p 8 okind) (unsigned-byte-p 32 oslot) (unsigned-byte-p 60 ogen)))
       (mv :bounds 0 0 0 0 0 0 0 nil 0 0 0 fn2-fields fn2-digests))
      ((mv dcode next fn2-fields)
       (fn2-manifest-entry-decode ebase slot gen 0 len okind oslot ogen fn2-fields fn2-pool))
      ((unless (and (eq dcode :ok) (equal next len)))
       (mv (if (eq dcode :ok) :format dcode) 0 0 0 0 0 0 0 nil 0 0 0 fn2-fields fn2-digests))
      ((mv rcode schema run height entries root-unit root-epoch root-alloc
           filter-p filter-unit filter-epoch filter-alloc fn2-digests)
       (fn2-manifest-read-entry ebase root-hdst filter-hdst okind oslot ogen fn2-fields fn2-pool fn2-digests)))
  (mv rcode schema run height entries root-unit root-epoch root-alloc
      filter-p filter-unit filter-epoch filter-alloc fn2-fields fn2-digests)))

(fn2-fc-shape fn2-manifest-unpack-entry-shape
 (fn2-manifest-unpack-entry ebase slot gen len root-hdst filter-hdst okind oslot ogen
                            fn2-fields fn2-pool fn2-digests)
 (and (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)
      (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)
      (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests))
 ((fn2-fields 12) (fn2-digests 13)))

(in-theory (disable fn2-manifest-unpack-entry))

; Reconstruct row R of fn2-run-installed directly from a decoded fn2-manifest
; entry at EBASE (so recovery/checkpoints reconstruct live runs without
; replaying from extent 0).
(defun fn2-manifest-install-entry (r ebase root-hdst filter-hdst rslot rgen okind oslot ogen
                                   fn2-fields fn2-pool fn2-digests fn2-run-installed)
 (declare (xargs :stobjs (fn2-fields fn2-pool fn2-digests fn2-run-installed) :guard t))
 (b* (((unless (and (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool)
                    (fn2-digests-wfp fn2-digests) (fn2-run-installed-wfp fn2-run-installed)))
       (mv :state fn2-digests fn2-run-installed))
      ((unless (and (natp r) (< r (fn2-run-installed-rows fn2-run-installed))
                    (unsigned-byte-p 32 rslot) (unsigned-byte-p 60 rgen)
                    (unsigned-byte-p 8 okind) (unsigned-byte-p 32 oslot) (unsigned-byte-p 60 ogen)))
       (mv :bounds fn2-digests fn2-run-installed))
      ((mv rcode schema run height entries root-unit & root-alloc
           filter-p filter-unit & filter-alloc fn2-digests)
       (fn2-manifest-read-entry ebase root-hdst filter-hdst okind oslot ogen fn2-fields fn2-pool fn2-digests))
      ((unless (eq rcode :ok))
       (mv rcode fn2-digests fn2-run-installed))
      (top (- (nfix height) 1))
      ((mv icode fn2-run-installed)
       (fn2-run-install r schema run top rslot rgen root-unit root-alloc entries okind oslot ogen fn2-run-installed))
      ((unless (eq icode :ok))
       (mv icode fn2-digests fn2-run-installed))
      ((mv fcode fn2-run-installed)
       (if filter-p
           (fn2-run-install-filter r filter-unit filter-alloc fn2-run-installed)
         (mv :ok fn2-run-installed))))
  (mv fcode fn2-digests fn2-run-installed)))

(fn2-fc-shape fn2-manifest-install-entry-shape
 (fn2-manifest-install-entry r ebase root-hdst filter-hdst rslot rgen okind oslot ogen
                             fn2-fields fn2-pool fn2-digests fn2-run-installed)
 (and (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)
      (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)
      (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests)
      (fn2-run-installedp fn2-run-installed) (fn2-run-installed-wfp fn2-run-installed))
 ((fn2-digests 1) (fn2-run-installed 2)))

(defthm fn2-manifest-install-entry-establishes-live-run
 (b* (((mv code & inst2)
       (fn2-manifest-install-entry r ebase root-hdst filter-hdst rslot rgen okind oslot ogen
                                   fn2-fields fn2-pool fn2-digests fn2-run-installed))
      ((mv & schema run height entries root-unit & root-alloc & & & & &)
       (fn2-manifest-read-entry ebase root-hdst filter-hdst okind oslot ogen fn2-fields fn2-pool fn2-digests)))
  (implies (and (fn2-run-installedp fn2-run-installed) (fn2-run-installed-wfp fn2-run-installed)
                (equal code :ok))
           (and (equal (fn2-run-installed-state r inst2) *fn2-run-installed-state-live*)
                (equal (fn2-run-installed-schema r inst2) schema)
                (equal (fn2-run-installed-run r inst2) run)
                (equal (fn2-run-installed-top r inst2) (- (nfix height) 1))
                (equal (fn2-run-installed-unit r inst2) root-unit)
                (equal (fn2-run-installed-counter r inst2) root-alloc)
                (equal (fn2-run-installed-entries r inst2) entries))))
 :hints (("Goal" :in-theory (enable fn2-manifest-install-entry fn2-run-install fn2-run-install-filter
                                    fn2-run-installed-rows))))

(in-theory (disable fn2-manifest-install-entry))

; Executable roundtrip witness for fn2-manifest-pack-entry -> fn2-manifest-unpack-entry
; -> fn2-manifest-install-entry.
(defun fn2-manifest-roundtrip-witness-body (fn2-fields fn2-pool fn2-digests fn2-run-installed)
 (declare (xargs :stobjs (fn2-fields fn2-pool fn2-digests fn2-run-installed) :verify-guards nil))
 (b* ((fn2-fields (fn2-fields-init 64 fn2-fields))
      (fn2-pool (fn2-pool-init '((2 . 1024)) 1 10 fn2-pool))
      (fn2-digests (fn2-digests-init 8 fn2-digests))
      (fn2-run-installed (fn2-run-installed-init 4 fn2-run-installed))
      (fn2-digests (fn2-digests-put 0 (w0 #x11223344) (w1 #x55667788) (w2 #x99aabbcc) (w3 #xddeeff00)
                                      (w4 #x01020304) (w5 #x05060708) (w6 #x090a0b0c) (w7 #x0d0e0f10)))
      (fn2-digests (fn2-digests-put 1 (w0 #xa1a2a3a4) (w1 #xb1b2b3b4) (w2 #xc1c2c3c4) (w3 #xd1d2d3d4)
                                      (w4 #xe1e2e3e4) (w5 #xf1f2f3f4) (w6 #x12345678) (w7 #x87654321)))
      ((mv rcode slot gen fn2-pool) (fn2-pool-reserve 0 9 1 1 fn2-pool))
      ((mv pcode bytes fn2-fields fn2-pool)
       (fn2-manifest-pack-entry 0 slot gen 20 7 3 1024
                                48 2 9 0
                                t 64 2 10 1
                                9 1 1 fn2-fields fn2-pool fn2-digests))
      ((mv ucode s-id r-id h ent ru rep ra fp fu fep fa fn2-fields fn2-digests)
       (fn2-manifest-unpack-entry 16 slot gen bytes 2 3 9 1 1 fn2-fields fn2-pool fn2-digests))
      ((mv icode fn2-digests fn2-run-installed)
       (fn2-manifest-install-entry 0 16 4 5 0 0 9 1 1 fn2-fields fn2-pool fn2-digests fn2-run-installed)))
  (mv (and (eq rcode :ok) (eq pcode :ok) (< 0 bytes)
           (eq ucode :ok)
           (= s-id 20) (= r-id 7) (= h 3) (= ent 1024)
           (= ru 48) (= rep 2) (= ra 9)
           (eq fp t) (= fu 64) (= fep 2) (= fa 10)
           (fn2-digest-equal 0 2 fn2-digests)
           (fn2-digest-equal 1 3 fn2-digests)
           (eq icode :ok)
           (= (fn2-run-installed-state 0 fn2-run-installed) *fn2-run-installed-state-live*)
           (= (fn2-run-installed-schema 0 fn2-run-installed) 20)
           (= (fn2-run-installed-run 0 fn2-run-installed) 7)
           (= (fn2-run-installed-top 0 fn2-run-installed) 2)
           (= (fn2-run-installed-unit 0 fn2-run-installed) 48)
           (= (fn2-run-installed-counter 0 fn2-run-installed) 9)
           (= (fn2-run-installed-entries 0 fn2-run-installed) 1024)
           (= (fn2-run-installed-filter 0 fn2-run-installed) 1)
           (= (fn2-run-installed-funit 0 fn2-run-installed) 64)
           (= (fn2-run-installed-fcounter 0 fn2-run-installed) 10))
      fn2-fields fn2-pool fn2-digests fn2-run-installed)))

(defun fn2-manifest-roundtrip-witness-run ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-fields
  (mv-let (ok fn2-fields)
   (with-local-stobj fn2-pool
    (mv-let (ok fn2-fields fn2-pool)
     (with-local-stobj fn2-digests
      (mv-let (ok fn2-fields fn2-pool fn2-digests)
       (with-local-stobj fn2-run-installed
        (mv-let (ok fn2-fields fn2-pool fn2-digests fn2-run-installed)
         (fn2-manifest-roundtrip-witness-body fn2-fields fn2-pool fn2-digests fn2-run-installed)
         (mv ok fn2-fields fn2-pool fn2-digests)))
       (mv ok fn2-fields fn2-pool)))
     (mv ok fn2-fields)))
   ok)))

(defthm fn2-manifest-entry-roundtrip-witness
 (equal (fn2-manifest-roundtrip-witness-run) t))

(assert-event
 (fn2-assert-compliant-p
  '(fn2-run-extent-unit
    fn2-run-unit-extent
    fn2-run-extent-byte-offset
    fn2-run-reserve-page
    fn2-run-build-alloc-page
    fn2-run-emit-page-write
    fn2-run-commit-page-write
    fn2-run-page-write-extract-hash
    fn2-manifest-stage-entry
    fn2-manifest-pack-entry
    fn2-manifest-filter-present-p
    fn2-manifest-read-entry
    fn2-manifest-unpack-entry
    fn2-manifest-install-entry)
  (w state)))
