; Range primitives over the pool (R6a1; REVIEW-20261028 finding 8, sprint
; gaps GC1 and GD4): each export checks its handles, owners and bounds once,
; then runs a guard-verified loop over the raw byte array with no per-byte
; re-check. A range's length is its work: callers pass at most their run's
; byte quantum, and a longer job is a continuation across runs.
(in-package "ACL2")
(include-book "pool")
(include-book "fnv")

(defthm fn2-pool-datai-byte
  (implies (and (fn2-poolp fn2-pool) (natp i) (< i (fn2-pool-data-length fn2-pool)))
           (unsigned-byte-p 8 (fn2-pool-datai i fn2-pool)))
  :hints (("Goal" :use ((:instance fn2-pool-datai-natp) (:instance fn2-pool-datai-bound))
           :in-theory (disable fn2-poolp fn2-pool-datai fn2-pool-data-length))))

; ------------------------------------------------------------------------
; Loops over absolute indices into the byte array.
(defun fn2-pool-copy-up (src dst n fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix n)
                  :guard (and (fn2-pool-wfp fn2-pool) (natp src) (natp dst) (natp n)
                              (<= (+ src n) (fn2-pool-data-length fn2-pool))
                              (<= (+ dst n) (fn2-pool-data-length fn2-pool)))))
  (if (zp n) fn2-pool
    (let ((fn2-pool (update-fn2-pool-datai dst (fn2-pool-datai src fn2-pool) fn2-pool)))
      (fn2-pool-copy-up (+ 1 src) (+ 1 dst) (- n 1) fn2-pool))))
; From the end, for an overlapping move to a higher address.
(defun fn2-pool-copy-down (src dst n fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix n)
                  :guard (and (fn2-pool-wfp fn2-pool) (natp src) (natp dst) (natp n)
                              (<= (+ src n) (fn2-pool-data-length fn2-pool))
                              (<= (+ dst n) (fn2-pool-data-length fn2-pool)))))
  (if (zp n) fn2-pool
    (let ((fn2-pool (update-fn2-pool-datai (+ dst n -1) (fn2-pool-datai (+ src n -1) fn2-pool) fn2-pool)))
      (fn2-pool-copy-down src dst (- n 1) fn2-pool))))
(defun fn2-pool-compare-loop (a b i n fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix (- (nfix n) (nfix i)))
                  :guard (and (fn2-pool-wfp fn2-pool) (natp a) (natp b) (natp i) (natp n) (<= i n)
                              (<= (+ a n) (fn2-pool-data-length fn2-pool))
                              (<= (+ b n) (fn2-pool-data-length fn2-pool)))))
  (if (or (not (natp i)) (not (natp n)) (>= i n)) (mv :equal (nfix n))
    (let ((x (fn2-pool-datai (+ a i) fn2-pool)) (y (fn2-pool-datai (+ b i) fn2-pool)))
      (cond ((< x y) (mv :less i))
            ((> x y) (mv :greater i))
            (t (fn2-pool-compare-loop a b (+ 1 i) n fn2-pool))))))
(defun fn2-pool-fold-loop (i n hash fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix n)
                  :guard (and (fn2-pool-wfp fn2-pool) (natp i) (natp n) (unsigned-byte-p 32 hash)
                              (<= (+ i n) (fn2-pool-data-length fn2-pool)))))
  (if (zp n) hash
    (fn2-pool-fold-loop (+ 1 i) (- n 1) (fn2-fnv-step hash (fn2-pool-datai i fn2-pool)) fn2-pool)))
;; The loops change only the byte array: shape and every column survive.
(defthm fn2-pool-data-length-of-update-datai
  (implies (and (natp i) (< i (fn2-pool-data-length fn2-pool)))
           (equal (fn2-pool-data-length (update-fn2-pool-datai i v fn2-pool))
                  (fn2-pool-data-length fn2-pool))))
(defmacro fn2-pool-copy-loop-facts (loop)
  `(progn
     (defthm ,(fn2-columns-sym loop "-SHAPE")
       (implies (and (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool) (natp src) (natp dst) (natp n)
                     (<= (+ src n) (fn2-pool-data-length fn2-pool))
                     (<= (+ dst n) (fn2-pool-data-length fn2-pool)))
                (and (fn2-poolp (,loop src dst n fn2-pool))
                     (fn2-pool-wfp (,loop src dst n fn2-pool))
                     (equal (fn2-pool-data-length (,loop src dst n fn2-pool))
                            (fn2-pool-data-length fn2-pool)))))
     (defthm ,(fn2-columns-sym loop "-FRAME")
       (implies (not (equal k *fn2-pool-datai*))
                (equal (nth k (,loop src dst n fn2-pool)) (nth k fn2-pool))))
     (in-theory (disable ,loop))))
(fn2-pool-copy-loop-facts fn2-pool-copy-up)
(fn2-pool-copy-loop-facts fn2-pool-copy-down)

; Scan targets: a byte value, or *fn2-pool-scan-crlf* for a CR LF pair
; (the parser's line end; both bytes must lie in the range).
(defconst *fn2-pool-scan-crlf* 256)
(defun fn2-pool-scan-loop (a i n target fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix (- (nfix n) (nfix i)))
                  :guard (and (fn2-pool-wfp fn2-pool) (natp a) (natp i) (natp n) (<= i n) (natp target)
                              (<= (+ a n) (fn2-pool-data-length fn2-pool)))))
  (if (or (not (natp i)) (not (natp n)) (>= i n)) (nfix n)
    (let ((x (fn2-pool-datai (+ a i) fn2-pool)))
      (if (if (equal target *fn2-pool-scan-crlf*)
              (and (equal x 13) (< (+ i 1) n) (equal (fn2-pool-datai (+ a i 1) fn2-pool) 10))
            (equal x target))
          i
        (fn2-pool-scan-loop a (+ 1 i) n target fn2-pool)))))

; ------------------------------------------------------------------------
; The exports. Owners are (kind slot gen) triples: a range is readable by its
; slot's owner in :workspace or :leased-out, writable only in :workspace with
; no outstanding loan. Every bound is checked before the first byte.
(defun fn2-pool-range-in (slot off len fn2-pool)
  ; [off, off+len) lies within the slot's filled bytes and the backing array
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp slot)
                                               (< slot (fn2-pool-rows fn2-pool)))))
  (and (natp off) (natp len) (<= (+ off len) (fn2-pool-fill slot fn2-pool))
       (<= (+ (fn2-pool-base slot fn2-pool) off len) (fn2-pool-data-length fn2-pool))))

(fn2-defoperation (:columns fn2-pool) :core :infer
(defun fn2-pool-copy-range (src sgen soff dst dgen doff len okind oslot ogen fn2-pool)
  ; Copy [soff, soff+len) of SRC to DOFF of DST, both owned by (okind oslot
  ; ogen); DOFF may not open a gap past DST's fill. Overlap-safe within one slot.
  (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
  (let ((scode (fn2-pool-readable-code src sgen okind oslot ogen fn2-pool))
        (dcode (fn2-pool-workspace-code dst dgen okind oslot ogen fn2-pool)))
    (cond ((not (eq scode :ok)) (mv scode fn2-pool))
          ((not (eq dcode :ok)) (mv dcode fn2-pool))
          ((not (and (fn2-pool-range-in src soff len fn2-pool)
                     (natp doff) (<= doff (fn2-pool-fill dst fn2-pool))
                     (<= (+ doff len) (fn2-pool-cap dst fn2-pool))
                     (<= (+ (fn2-pool-base dst fn2-pool) doff len) (fn2-pool-data-length fn2-pool))))
           (mv :bounds fn2-pool))
          (t (let* ((from (+ (fn2-pool-base src fn2-pool) soff))
                    (to (+ (fn2-pool-base dst fn2-pool) doff))
                    (new-fill (max (fn2-pool-fill dst fn2-pool) (+ doff len)))
                    (fn2-pool (if (< from to) (fn2-pool-copy-down from to len fn2-pool)
                                (fn2-pool-copy-up from to len fn2-pool)))
                    (fn2-pool (fn2-pool-set-fill dst new-fill fn2-pool)))
               (mv :ok fn2-pool)))))))

(fn2-defoperation (:columns fn2-pool) :core :infer
(defun fn2-pool-compare (s1 g1 off1 k1 os1 og1 s2 g2 off2 k2 os2 og2 len fn2-pool)
  ; Compare two ranges owned by possibly different machines (sprint gap GC1):
  ; :equal, :less or :greater, and the index of the first difference (or LEN).
  (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
  (let ((c1 (fn2-pool-readable-code s1 g1 k1 os1 og1 fn2-pool))
        (c2 (fn2-pool-readable-code s2 g2 k2 os2 og2 fn2-pool)))
    (cond ((not (eq c1 :ok)) (mv c1 :equal 0))
          ((not (eq c2 :ok)) (mv c2 :equal 0))
          ((not (and (fn2-pool-range-in s1 off1 len fn2-pool) (fn2-pool-range-in s2 off2 len fn2-pool)))
           (mv :bounds :equal 0))
          (t (mv-let (result at)
               (fn2-pool-compare-loop (+ (fn2-pool-base s1 fn2-pool) off1) (+ (fn2-pool-base s2 fn2-pool) off2)
                                      0 len fn2-pool)
               (mv :ok result at)))))))

(fn2-defoperation (:columns fn2-pool) :core :infer
(defun fn2-pool-fold (slot gen off len hash okind oslot ogen fn2-pool)
  ; FNV-1a (fn2-fnv-step) of HASH over the range: the scribe's checksum.
  (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
  (let ((code (fn2-pool-readable-code slot gen okind oslot ogen fn2-pool)))
    (cond ((not (eq code :ok)) (mv code 0))
          ((not (and (fn2-pool-range-in slot off len fn2-pool) (unsigned-byte-p 32 hash)))
           (mv :bounds 0))
          (t (mv :ok (fn2-pool-fold-loop (+ (fn2-pool-base slot fn2-pool) off) len hash fn2-pool)))))))

(fn2-defoperation (:columns fn2-pool) :core :infer
(defun fn2-pool-scan (slot gen off len target okind oslot ogen fn2-pool)
  ; The first offset (relative to OFF) of TARGET, a byte or
  ; *fn2-pool-scan-crlf*, within the range; LEN when absent.
  (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
  (let ((code (fn2-pool-readable-code slot gen okind oslot ogen fn2-pool)))
    (cond ((not (eq code :ok)) (mv code 0))
          ((not (and (fn2-pool-range-in slot off len fn2-pool) (natp target)
                     (<= target *fn2-pool-scan-crlf*)))
           (mv :bounds 0))
          (t (mv :ok (fn2-pool-scan-loop (+ (fn2-pool-base slot fn2-pool) off) 0 len target fn2-pool)))))))

(fn2-defoperation (:columns fn2-pool) :core :infer
(defun fn2-pool-drop-prefix (slot gen k cursor limit okind oslot ogen fn2-pool)
  ; Drop the first K filled bytes (a consumed prefix) keeping the tail at
  ; offset 0, as a bounded continuation (sprint gap GD4): move at most LIMIT
  ; tail bytes from CURSOR; :more with the next cursor, or :ok once the tail
  ; is moved and the fill shrunk by K. One slot, no scratch. A reader that
  ; can track its own start offset needs no compaction at all.
  (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
  (let ((code (fn2-pool-workspace-code slot gen okind oslot ogen fn2-pool)))
    (cond ((not (eq code :ok)) (mv code 0 fn2-pool))
          ((not (and (natp k) (natp cursor) (natp limit)
                     (<= k (fn2-pool-fill slot fn2-pool))
                     (<= cursor (- (fn2-pool-fill slot fn2-pool) k))
                     (fn2-pool-range-in slot 0 (fn2-pool-fill slot fn2-pool) fn2-pool)))
           (mv :bounds 0 fn2-pool))
          (t (let* ((tail (- (fn2-pool-fill slot fn2-pool) k))
                    (n (if (< limit (- tail cursor)) limit (- tail cursor)))
                    (base (fn2-pool-base slot fn2-pool))
                    (fn2-pool (fn2-pool-copy-up (+ base k cursor) (+ base cursor) n fn2-pool)))
               (if (< (+ cursor n) tail) (mv :more (+ cursor n) fn2-pool)
                 (let ((fn2-pool (fn2-pool-set-fill slot tail fn2-pool)))
                   (mv :ok tail fn2-pool)))))))))

(fn2-pool-preserves fn2-pool-copy-range (src sgen soff dst dgen doff len okind oslot ogen fn2-pool) :position 1 :disable nil)
(fn2-pool-preserves fn2-pool-drop-prefix (slot gen k cursor limit okind oslot ogen fn2-pool) :position 2 :disable nil)
(assert-event
 (fn2-assert-compliant-p
  '(fn2-pool-copy-up fn2-pool-copy-down fn2-pool-compare-loop fn2-pool-fold-loop fn2-pool-scan-loop
    fn2-pool-copy-range fn2-pool-compare fn2-pool-fold fn2-pool-scan fn2-pool-drop-prefix)
  (w state)))
