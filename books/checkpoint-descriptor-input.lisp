; One canonical descriptor target and immutable digest loader.
; Extracted unchanged from checkpoint-restore; no allocator or serving authority.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "checkpoint")
(include-book "columns-carrier-contracts")
(fn2-book-layer :b)

(defun fn2-checkpoint-restore-read-target (c role cursor extents fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes)
 (declare (xargs :stobjs (fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes)
  :guard (and (fn2-checkpoints-wfp fn2-checkpoints) (fn2-checkpoint-refs-wfp fn2-checkpoint-refs)
              (fn2-checkpoint-bytes-wfp fn2-checkpoint-bytes))))
 (b* (((unless (and (fn2-checkpoint-slotp c fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes)
                     (natp role) (< role 6) (natp cursor) (posp extents)
                     (if (equal role 0)
                       (equal (fn2-checkpoints-state c fn2-checkpoints) *fn2-checkpoint-state-preparing*)
                       (equal (fn2-checkpoints-state c fn2-checkpoints) *fn2-checkpoint-state-checked*))))
       (mv :state 0 0 0))
      (r (+ (* 6 c) role))
      (unit (fn2-checkpoint-refs-physical-unit r fn2-checkpoint-refs))
      (len (fn2-checkpoint-refs-encoded-length r fn2-checkpoint-refs))
      ((unless (and (equal (fn2-checkpoint-refs-storage-domain r fn2-checkpoint-refs) 0)
                     (equal (mod unit *fn2-storage-extent-units*) 0)
                     (< (floor unit *fn2-storage-extent-units*) extents)
                     (posp len) (<= len *fn2-format-page-size*) (< cursor len)
                     (equal (mod cursor *fn2-format-sector-size*) 0)))
       (mv :bounds 0 0 0))
      (n *fn2-format-sector-size*))
  (mv :read (+ (* unit *fn2-format-sector-size*) cursor) n (+ cursor n))))

(defun fn2-checkpoint-restore-load-hash (i r hash fn2-checkpoint-bytes fn2-digests)
 (declare (xargs :stobjs (fn2-checkpoint-bytes fn2-digests) :measure (nfix (- 8 (nfix i)))
  :guard (and (fn2-checkpoint-bytes-wfp fn2-checkpoint-bytes) (natp r)
              (<= (* 32 (+ r 1)) (fn2-checkpoint-bytes-rows fn2-checkpoint-bytes))
              (fn2-digest-rowp hash fn2-digests) (natp i) (<= i 8))))
 (if (or (not (natp i)) (>= i 8)) fn2-digests
  (let* ((at (+ (* 32 r) (* 4 i)))
         (word (+ (fn2-checkpoint-bytes-value at fn2-checkpoint-bytes)
                  (* 256 (fn2-checkpoint-bytes-value (+ at 1) fn2-checkpoint-bytes))
                  (* 65536 (fn2-checkpoint-bytes-value (+ at 2) fn2-checkpoint-bytes))
                  (* 16777216 (fn2-checkpoint-bytes-value (+ at 3) fn2-checkpoint-bytes))))
         (fn2-digests (fn2-digest-set-word hash i word fn2-digests)))
   (fn2-checkpoint-restore-load-hash (+ i 1) r hash fn2-checkpoint-bytes fn2-digests))))

(defcolumns-guarded-contracts fn2-checkpoint-restore-load-hash
 :carriers ((fn2-digests nil :prefix "-DIGESTS")) :rows t
 :hints ((fn2-columns-guard-hint
          '(fn2-checkpoint-bytes fn2-digests)
          '(fn2-digest-set-word) '(fn2-checkpoint-restore-load-hash) world)))
