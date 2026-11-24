(in-package "ACL2")
(include-book "ribbon-hash")
(local (include-book "pool-read-contracts"))
(fn2-book-layer :c)
(local (in-theory (disable fn2-pool-rows fn2-fields-rows fn2-digests-rows fn2-fc-rows fn2-fc-context-rows fn2-b3-rows)))

; ---------------------------------------------------------------------------
; Tables. A build row (PENDING: an insertion that ran out of steps, its
; continuation PS PLO PHI); the band: one row per slot (the coefficient of the
; equation pivoted there, zero when free) and the solved byte.
(defcolumns fn2-ribbon-builds
 ((phase (:enum fn2-ribbon-phase (:idle :clearing :adding :solving :emitting :closing :heading :sealing :sealed)))
  (schema :u60) (run :u60) (seed :u32) (base :u32) (slots :u32) (keys :u32) (added :u32) (i :u32)
  (w :u32) (crow :u32) (hrow :u32) (pending :bool) (ps :u32) (plo :u32) (phi :u32)))
(defcolumns fn2-ribbon-band ((lo :u32) (hi :u32) (z :u8)))

; Insert the equation (hi:lo) at start S: shift out low zero bits, store
; it in a free row, or eliminate against the row pivoted there. A dependent
; equation reduces to zero (:redundant); a homogeneous system never refuses
; one. Each step shifts or eliminates; an elimination's result starts past
; S and ends no later than the row it met, so S only grows and every bit
; stays below the last slot. After FUEL steps the insertion answers :more
; with its continuation (S LO HI).
(defun fn2-ribbon-insert (fuel s lo hi base slots fn2-ribbon-band)
 (declare (xargs :stobjs fn2-ribbon-band :measure (nfix fuel)
  :guard (and (fn2-ribbon-band-wfp fn2-ribbon-band) (natp fuel) (natp s) (natp base) (natp slots)
              (unsigned-byte-p 32 lo) (unsigned-byte-p 32 hi))))
 (cond ((zp fuel) (mv :more s lo hi fn2-ribbon-band))
       ((and (equal lo 0) (equal hi 0)) (mv :redundant s lo hi fn2-ribbon-band))
       ((not (logbitp 0 lo))
        (fn2-ribbon-insert (- fuel 1) (+ 1 s) (fn2-ribbon-shr1 lo hi) (fn2-ribbon-shr hi 1) base slots fn2-ribbon-band))
       ((not (and (< s slots) (< (+ base s) (fn2-ribbon-band-rows fn2-ribbon-band)))) (mv :bounds s lo hi fn2-ribbon-band))
       (t (let* ((r (+ base s)) (rlo (fn2-ribbon-band-lo r fn2-ribbon-band)) (rhi (fn2-ribbon-band-hi r fn2-ribbon-band)))
           (if (and (equal rlo 0) (equal rhi 0))
               (let ((fn2-ribbon-band (fn2-ribbon-band-put r (lo lo) (hi hi)))) (mv :ok s lo hi fn2-ribbon-band))
             (fn2-ribbon-insert (- fuel 1) s (fn2-ribbon-xor32 lo rlo) (fn2-ribbon-xor32 hi rhi) base slots fn2-ribbon-band))))))
(fn2-ribbon-band-preserves fn2-ribbon-insert (fuel s lo hi base slots fn2-ribbon-band) :position 4 :raw-rows t
 :hyps ((fn2-ribbon-bandp fn2-ribbon-band) (fn2-ribbon-band-wfp fn2-ribbon-band) (natp s) (natp base) (unsigned-byte-p 32 lo) (unsigned-byte-p 32 hi)))

; XOR of the solved bytes at R + j for every set bit j of (hi:lo), j from
; J up, K bits in all. A set bit past END is a corrupt band.
(defun fn2-ribbon-dot (k j r end lo hi acc fn2-ribbon-band)
 (declare (xargs :stobjs fn2-ribbon-band :measure (nfix k)
  :guard (and (fn2-ribbon-band-wfp fn2-ribbon-band) (natp k) (natp j) (natp r) (natp end)
              (unsigned-byte-p 32 lo) (unsigned-byte-p 32 hi) (unsigned-byte-p 8 acc))))
 (b* (((when (zp k)) (mv :ok acc))
      (bit (if (< j 32) (logbitp j lo) (logbitp (- j 32) hi)))
      ((unless bit) (fn2-ribbon-dot (- k 1) (+ 1 j) r end lo hi acc fn2-ribbon-band))
      (x (+ r j))
      ((unless (and (< x end) (< x (fn2-ribbon-band-rows fn2-ribbon-band)))) (mv :format acc)))
  (fn2-ribbon-dot (- k 1) (+ 1 j) r end lo hi (fn2-ribbon-xor8 acc (fn2-ribbon-band-z x fn2-ribbon-band)) fn2-ribbon-band)))
(fn2-ribbon-ub fn2-ribbon-dot-type 8 (and (unsigned-byte-p 8 acc) (fn2-ribbon-bandp fn2-ribbon-band))
 (mv-nth 1 (fn2-ribbon-dot k j r end lo hi acc fn2-ribbon-band)))
(in-theory (disable fn2-ribbon-dot))

; Back substitution of rows I-1 down to I-N (relative to BASE; the caller
; keeps N <= I): a pivoted row's byte is the dot of the rows above it, a
; free row's comes from the generator.
(defun fn2-ribbon-solve-rows (n i base end seed fn2-ribbon-band)
 (declare (xargs :stobjs fn2-ribbon-band :measure (nfix n)
  :guard (and (fn2-ribbon-band-wfp fn2-ribbon-band) (natp n) (natp i) (natp base) (natp end)
              (unsigned-byte-p 32 seed))))
 (b* (((when (zp n)) (mv :ok fn2-ribbon-band))
      ((when (zp i)) (mv :bounds fn2-ribbon-band))
      (r (+ base (- i 1)))
      ((unless (and (< r (fn2-ribbon-band-rows fn2-ribbon-band)) (unsigned-byte-p 32 (- i 1)))) (mv :bounds fn2-ribbon-band))
      (lo (fn2-ribbon-band-lo r fn2-ribbon-band)) (hi (fn2-ribbon-band-hi r fn2-ribbon-band))
      ((mv code z) (if (and (equal lo 0) (equal hi 0))
                       (mv :ok (fn2-ribbon-byte (fn2-prng-mix32 (fn2-ribbon-xor32 seed (- i 1)))))
                     (fn2-ribbon-dot 63 1 r end lo hi 0 fn2-ribbon-band)))
      ((unless (eq code :ok)) (mv code fn2-ribbon-band))
      (fn2-ribbon-band (fn2-ribbon-band-set-z r z fn2-ribbon-band)))
  (fn2-ribbon-solve-rows (- n 1) (- i 1) base end seed fn2-ribbon-band)))
(fn2-ribbon-band-preserves fn2-ribbon-solve-rows (n i base end seed fn2-ribbon-band) :position 1 :raw-rows t
 :hyps ((fn2-ribbon-bandp fn2-ribbon-band) (fn2-ribbon-band-wfp fn2-ribbon-band) (natp base) (natp i)))

; Zero rows BASE+I .. BASE+I+N-1.
(defun fn2-ribbon-clear-rows (n i base fn2-ribbon-band)
 (declare (xargs :stobjs fn2-ribbon-band :measure (nfix n)
  :guard (and (fn2-ribbon-band-wfp fn2-ribbon-band) (natp n) (natp i) (natp base))))
 (b* (((when (zp n)) (mv :ok fn2-ribbon-band))
      (r (+ base i))
      ((unless (< r (fn2-ribbon-band-rows fn2-ribbon-band))) (mv :bounds fn2-ribbon-band))
      (fn2-ribbon-band (fn2-ribbon-band-put r (lo 0) (hi 0) (z 0))))
  (fn2-ribbon-clear-rows (- n 1) (+ 1 i) base fn2-ribbon-band)))
(fn2-ribbon-band-preserves fn2-ribbon-clear-rows (n i base fn2-ribbon-band) :position 1 :raw-rows t
 :hyps ((fn2-ribbon-bandp fn2-ribbon-band) (fn2-ribbon-band-wfp fn2-ribbon-band) (natp base) (natp i)))

; Bytes I .. I+N-1 of Z (rows BASE+I ..) written at OFF+I of the page.
(defun fn2-ribbon-emit-bytes (n i base slot gen off okind oslot ogen fn2-ribbon-band fn2-pool)
 (declare (xargs :stobjs (fn2-ribbon-band fn2-pool) :measure (nfix n)
  :guard (and (fn2-ribbon-band-wfp fn2-ribbon-band) (fn2-pool-wfp fn2-pool) (natp n) (natp i)
              (natp base) (natp off))
  :guard-hints ((fn2-columns-call-guard-hint 'fn2-ribbon-emit-bytes nil nil world))))
 (b* (((when (zp n)) (mv :ok fn2-pool))
      (r (+ base i))
      ((unless (< r (fn2-ribbon-band-rows fn2-ribbon-band))) (mv :bounds fn2-pool))
      ((mv code fn2-pool) (fn2-pool-write slot gen (+ off i) (fn2-ribbon-band-z r fn2-ribbon-band) okind oslot ogen fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-pool)))
  (fn2-ribbon-emit-bytes (- n 1) (+ 1 i) base slot gen off okind oslot ogen fn2-ribbon-band fn2-pool)))
(fn2-pool-preserves fn2-ribbon-emit-bytes (n i base slot gen off okind oslot ogen fn2-ribbon-band fn2-pool) :position 1)
