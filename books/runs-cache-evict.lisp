; Layer C verified run-page cache pin check, eviction, and quiet workspace
; release over child stobjs (fn2-run-cache, fn2-pool).
(in-package "ACL2")
(include-book "runs")
(include-book "columns-call-guards")
(include-book "std/util/bstar" :dir :system)
(fn2-book-layer :c)

(local (defthm fn2-rce-u-from-range
 (implies (and (natp bits) (integerp v) (<= 0 v) (< v (expt 2 bits)))
          (unsigned-byte-p bits v))
 :hints (("Goal" :in-theory (enable unsigned-byte-p integer-range-p)))))

(local (defthm fn2-rce-u-forward
 (implies (unsigned-byte-p bits v)
          (and (integerp v) (<= 0 v)))
 :rule-classes :forward-chaining
 :hints (("Goal" :in-theory (enable unsigned-byte-p integer-range-p)))))

(local (defthm fn2-rce-u8-bound
 (implies (unsigned-byte-p 8 v) (< v 256))
 :rule-classes :forward-chaining
 :hints (("Goal" :in-theory (enable unsigned-byte-p integer-range-p)))))

(local (defthm fn2-rce-u32-bound
 (implies (unsigned-byte-p 32 v) (< v 4294967296))
 :rule-classes :forward-chaining
 :hints (("Goal" :in-theory (enable unsigned-byte-p integer-range-p)))))

(local (defthm fn2-rce-u60-bound
 (implies (unsigned-byte-p 60 v) (< v 1152921504606846976))
 :rule-classes :forward-chaining
 :hints (("Goal" :in-theory (enable unsigned-byte-p integer-range-p)))))

(local (in-theory (disable
 unsigned-byte-p integer-range-p
 fn2-run-cachep fn2-run-cache-wfp fn2-run-cache-rows
 fn2-run-cache-state fn2-run-cache-unit fn2-run-cache-counter fn2-run-cache-slot fn2-run-cache-gen
 fn2-poolp fn2-pool-wfp fn2-pool-rows fn2-pool-cap fn2-pool-base fn2-pool-fill fn2-pool-data-length
 fn2-pool-state fn2-pool-gen fn2-pool-query-ref-count fn2-pool-out-count fn2-pool-credit-group
 fn2-run-cache-row fn2-run-cache-lookup fn2-run-cache-install fn2-run-cache-drop
 fn2-pool-reserve fn2-pool-release fn2-pool-release-countp)))

; A cached page pool slot is pinned when a reader holds a query reference or
; an outbound lease is active on the workspace.
(defun fn2-run-cache-pinned-p (slot fn2-pool)
 (declare (xargs :stobjs fn2-pool
  :guard (and (fn2-pool-wfp fn2-pool) (natp slot) (< slot (fn2-pool-rows fn2-pool)))))
 (or (< 0 (fn2-pool-query-ref-count slot fn2-pool))
     (< 0 (fn2-pool-out-count slot fn2-pool))))

(in-theory (disable fn2-run-cache-pinned-p))

; Quietly release pool workspace (SLOT, GEN) when releasable; leaves fn2-pool
; unchanged otherwise.
(defun fn2-run-pio-release-quiet (slot gen okind oslot ogen fn2-pool)
 (declare (xargs :stobjs fn2-pool
  :guard (and (fn2-pool-wfp fn2-pool)
              (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
              (unsigned-byte-p 8 okind) (unsigned-byte-p 32 oslot) (unsigned-byte-p 60 ogen))))
 (if (and (< slot (fn2-pool-rows fn2-pool)) (fn2-pool-release-countp slot fn2-pool))
     (mv-let (rel fn2-pool) (fn2-pool-release slot gen okind oslot ogen fn2-pool)
      (declare (ignore rel))
      fn2-pool)
   fn2-pool))

(fn2-fc-shape fn2-run-pio-release-quiet-shape
 (fn2-run-pio-release-quiet slot gen okind oslot ogen fn2-pool)
 (and (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)
      (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
      (unsigned-byte-p 8 okind) (unsigned-byte-p 32 oslot) (unsigned-byte-p 60 ogen))
 ((fn2-pool nil)))

(in-theory (disable fn2-run-pio-release-quiet))

; Evict cache row I if occupied (:ready) and unpinned, releasing its 64 KiB
; workspace back to fn2-pool. Refuses :pinned when held, leaving both
; fn2-run-cache and fn2-pool unchanged.
(defun fn2-run-cache-evict-row-work (i okind oslot ogen fn2-run-cache fn2-pool)
 (declare (xargs :stobjs (fn2-run-cache fn2-pool)
  :guard (and (fn2-run-cache-wfp fn2-run-cache) (fn2-pool-wfp fn2-pool))
  :guard-hints ((fn2-columns-guard-hint '(fn2-run-cache fn2-pool)
                  '(fn2-run-cache-pinned-p fn2-pool-release-countp fn2-pool-release)
                  nil world))))
 (b* (((unless (and (natp i) (< i (fn2-run-cache-rows fn2-run-cache))
                    (unsigned-byte-p 8 okind) (unsigned-byte-p 32 oslot) (unsigned-byte-p 60 ogen)))
       (mv :bounds fn2-run-cache fn2-pool))
      ((unless (equal (fn2-run-cache-state i fn2-run-cache) *fn2-run-cache-state-ready*))
       (mv :ok fn2-run-cache fn2-pool))
      (old-slot (fn2-run-cache-slot i fn2-run-cache))
      (old-gen (fn2-run-cache-gen i fn2-run-cache))
      ((unless (< old-slot (fn2-pool-rows fn2-pool)))
       (mv :bounds fn2-run-cache fn2-pool))
      ((when (fn2-run-cache-pinned-p old-slot fn2-pool))
       (mv :pinned fn2-run-cache fn2-pool))
      ((unless (fn2-pool-release-countp old-slot fn2-pool))
       (mv :workspace fn2-run-cache fn2-pool))
      ((mv rcode fn2-pool) (fn2-pool-release old-slot old-gen okind oslot ogen fn2-pool))
      ((unless (member-eq rcode '(:ok :retired)))
       (mv rcode fn2-run-cache fn2-pool))
      (fn2-run-cache (fn2-run-cache-set-state i *fn2-run-cache-state-empty* fn2-run-cache)))
  (mv :ok fn2-run-cache fn2-pool)))

(fn2-run-cache-preserves fn2-run-cache-evict-row-work
 (i okind oslot ogen fn2-run-cache fn2-pool) :position 1 :disable nil)
(fn2-pool-preserves fn2-run-cache-evict-row-work
 (i okind oslot ogen fn2-run-cache fn2-pool) :position 2 :prefix "-POOL-PRESERVES" :disable nil
 :hyps ((fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool) (fn2-run-cachep fn2-run-cache) (fn2-run-cache-wfp fn2-run-cache)))
(in-theory (disable fn2-run-cache-evict-row-work))

(defun fn2-run-cache-evict-row (i okind oslot ogen fn2-run-cache fn2-pool)
 (declare (xargs :stobjs (fn2-run-cache fn2-pool) :guard t))
 (if (and (fn2-run-cache-wfp fn2-run-cache) (fn2-pool-wfp fn2-pool))
     (fn2-run-cache-evict-row-work i okind oslot ogen fn2-run-cache fn2-pool)
   (mv :state fn2-run-cache fn2-pool)))

(fn2-fc-shape fn2-run-cache-evict-row-shape
 (fn2-run-cache-evict-row i okind oslot ogen fn2-run-cache fn2-pool)
 (and (fn2-run-cachep fn2-run-cache) (fn2-run-cache-wfp fn2-run-cache)
      (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
 ((fn2-run-cache 1) (fn2-pool 2)))

(defthm fn2-run-cache-evict-row-fail-unchanged
 (implies (not (equal (mv-nth 0 (fn2-run-cache-evict-row i okind oslot ogen fn2-run-cache fn2-pool)) :ok))
          (equal (mv-nth 1 (fn2-run-cache-evict-row i okind oslot ogen fn2-run-cache fn2-pool))
                 fn2-run-cache))
 :hints (("Goal" :in-theory (enable fn2-run-cache-evict-row fn2-run-cache-evict-row-work))))

(defthm fn2-run-cache-evict-row-pinned-unchanged
 (implies (and (fn2-run-cache-wfp fn2-run-cache) (fn2-pool-wfp fn2-pool)
               (natp i) (< i (fn2-run-cache-rows fn2-run-cache))
               (unsigned-byte-p 8 okind) (unsigned-byte-p 32 oslot) (unsigned-byte-p 60 ogen)
               (equal (fn2-run-cache-state i fn2-run-cache) *fn2-run-cache-state-ready*)
               (< (fn2-run-cache-slot i fn2-run-cache) (fn2-pool-rows fn2-pool))
               (fn2-run-cache-pinned-p (fn2-run-cache-slot i fn2-run-cache) fn2-pool))
          (equal (fn2-run-cache-evict-row i okind oslot ogen fn2-run-cache fn2-pool)
                 (mv :pinned fn2-run-cache fn2-pool)))
 :hints (("Goal" :in-theory (enable fn2-run-cache-evict-row fn2-run-cache-evict-row-work))))

(in-theory (disable fn2-run-cache-evict-row))

; Evict the direct-mapped row (mod UNIT cache-rows) if occupied and unpinned.
(defun fn2-run-cache-evict-for-unit (unit okind oslot ogen fn2-run-cache fn2-pool)
 (declare (xargs :stobjs (fn2-run-cache fn2-pool) :guard t))
 (if (not (and (fn2-run-cache-wfp fn2-run-cache) (fn2-pool-wfp fn2-pool)
               (natp unit) (< 0 (fn2-run-cache-rows fn2-run-cache))))
     (mv :bounds fn2-run-cache fn2-pool)
   (fn2-run-cache-evict-row (fn2-run-cache-row unit fn2-run-cache)
                            okind oslot ogen fn2-run-cache fn2-pool)))

(fn2-fc-shape fn2-run-cache-evict-for-unit-shape
 (fn2-run-cache-evict-for-unit unit okind oslot ogen fn2-run-cache fn2-pool)
 (and (fn2-run-cachep fn2-run-cache) (fn2-run-cache-wfp fn2-run-cache)
      (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
 ((fn2-run-cache 1) (fn2-pool 2)))

(defthm fn2-run-cache-evict-for-unit-fail-unchanged
 (implies (not (equal (mv-nth 0 (fn2-run-cache-evict-for-unit unit okind oslot ogen fn2-run-cache fn2-pool)) :ok))
          (equal (mv-nth 1 (fn2-run-cache-evict-for-unit unit okind oslot ogen fn2-run-cache fn2-pool))
                 fn2-run-cache))
 :hints (("Goal" :in-theory (enable fn2-run-cache-evict-for-unit))))

(in-theory (disable fn2-run-cache-evict-for-unit))

; Evict exact (UNIT, COUNTER) if present; returns :absent when not cached.
(defun fn2-run-cache-evict-unit (unit counter okind oslot ogen fn2-run-cache fn2-pool)
 (declare (xargs :stobjs (fn2-run-cache fn2-pool) :guard t))
 (b* (((unless (and (fn2-run-cache-wfp fn2-run-cache) (fn2-pool-wfp fn2-pool) (natp unit) (natp counter)))
       (mv :bounds fn2-run-cache fn2-pool))
      ((mv hit & &) (fn2-run-cache-lookup unit counter fn2-run-cache))
      ((unless (eq hit :ok))
       (mv :absent fn2-run-cache fn2-pool)))
  (fn2-run-cache-evict-for-unit unit okind oslot ogen fn2-run-cache fn2-pool)))

(fn2-fc-shape fn2-run-cache-evict-unit-shape
 (fn2-run-cache-evict-unit unit counter okind oslot ogen fn2-run-cache fn2-pool)
 (and (fn2-run-cachep fn2-run-cache) (fn2-run-cache-wfp fn2-run-cache)
      (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
 ((fn2-run-cache 1) (fn2-pool 2)))
(in-theory (disable fn2-run-cache-evict-unit))

; Sweep up to K rows starting at I and evict at most one unpinned occupant.
(defun fn2-run-cache-evict-one (i k okind oslot ogen fn2-run-cache fn2-pool)
 (declare (xargs :stobjs (fn2-run-cache fn2-pool) :measure (nfix k)
  :guard (and (fn2-run-cache-wfp fn2-run-cache) (fn2-pool-wfp fn2-pool) (natp i) (natp k))))
 (if (or (zp k) (not (natp i)) (>= i (fn2-run-cache-rows fn2-run-cache)))
     (mv :none fn2-run-cache fn2-pool)
   (if (equal (fn2-run-cache-state i fn2-run-cache) *fn2-run-cache-state-ready*)
       (mv-let (code fn2-run-cache fn2-pool)
         (fn2-run-cache-evict-row i okind oslot ogen fn2-run-cache fn2-pool)
        (if (eq code :ok)
            (mv :ok fn2-run-cache fn2-pool)
          (fn2-run-cache-evict-one (+ 1 i) (- k 1) okind oslot ogen fn2-run-cache fn2-pool)))
     (fn2-run-cache-evict-one (+ 1 i) (- k 1) okind oslot ogen fn2-run-cache fn2-pool))))

(fn2-fc-shape fn2-run-cache-evict-one-shape
 (fn2-run-cache-evict-one i k okind oslot ogen fn2-run-cache fn2-pool)
 (and (fn2-run-cachep fn2-run-cache) (fn2-run-cache-wfp fn2-run-cache)
      (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
 ((fn2-run-cache 1) (fn2-pool 2)))
(in-theory (disable fn2-run-cache-evict-one))

; Sweep K rows starting at I, evicting every unpinned ready occupant while
; skipping pinned rows cleanly. Returns (mv :ok evicted-count cache pool).
(defun fn2-run-cache-evict-unpinned (i k okind oslot ogen fn2-run-cache fn2-pool)
 (declare (xargs :stobjs (fn2-run-cache fn2-pool) :measure (nfix k)
  :guard (and (fn2-run-cache-wfp fn2-run-cache) (fn2-pool-wfp fn2-pool) (natp i) (natp k))))
 (if (or (zp k) (not (natp i)) (>= i (fn2-run-cache-rows fn2-run-cache)))
     (mv :ok 0 fn2-run-cache fn2-pool)
   (if (equal (fn2-run-cache-state i fn2-run-cache) *fn2-run-cache-state-ready*)
       (mv-let (code fn2-run-cache fn2-pool)
         (fn2-run-cache-evict-row i okind oslot ogen fn2-run-cache fn2-pool)
        (cond ((eq code :ok)
               (mv-let (rc cnt fn2-run-cache fn2-pool)
                 (fn2-run-cache-evict-unpinned (+ 1 i) (- k 1) okind oslot ogen fn2-run-cache fn2-pool)
                (mv rc (+ 1 (nfix cnt)) fn2-run-cache fn2-pool)))
              ((eq code :pinned)
               (fn2-run-cache-evict-unpinned (+ 1 i) (- k 1) okind oslot ogen fn2-run-cache fn2-pool))
              (t (mv code 0 fn2-run-cache fn2-pool))))
     (fn2-run-cache-evict-unpinned (+ 1 i) (- k 1) okind oslot ogen fn2-run-cache fn2-pool))))

(fn2-fc-shape fn2-run-cache-evict-unpinned-shape
 (fn2-run-cache-evict-unpinned i k okind oslot ogen fn2-run-cache fn2-pool)
 (and (fn2-run-cachep fn2-run-cache) (fn2-run-cache-wfp fn2-run-cache)
      (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
 ((fn2-run-cache 2) (fn2-pool 3)))
(in-theory (disable fn2-run-cache-evict-unpinned))

(assert-event
 (fn2-assert-compliant-p
  '(fn2-run-cache-pinned-p
    fn2-run-pio-release-quiet
    fn2-run-cache-evict-row
    fn2-run-cache-evict-for-unit
    fn2-run-cache-evict-unit
    fn2-run-cache-evict-one
    fn2-run-cache-evict-unpinned)
  (w state)))
