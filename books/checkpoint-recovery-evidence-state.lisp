; Cold evidence is produced only by checked journal bytes, never by the live
; construction ledger. Rows1..4 retain evidence for the four physical anchors;
; row0 owns one bounded investigation. No selected-base bit is defined here.
(in-package "ACL2")
(include-book "checkpoint")
(include-book "recovery")
(fn2-book-layer :b)
(defcolumns fn2-checkpoint-recovery-evidence
 ((phase (:enum fn2-checkpoint-recovery-evidence-phase
   (:idle :target :load :frame :decode :seal :records :commitment :dependencies :walk :next :complete :uncertain)))
  (candidate :u32) (tag :u60) (ordinal :u32) (total :u32)
  (slot :u32) (gen :u60) (record-slot :u32) (record-gen :u60)
  (owner-kind :u8) (owner-slot :u32) (owner-gen :u60)
  (extent :u32) (epoch :u60) (allocation :u60)
  (journal-history :u60) (journal-incarnation :u60)
  (commit :u60) (first :u60) (last :u60) (event :u60) (previous-event :u60)
  (seal-off :u32) (seal-len :u32) (cursor :u32) (end :u32) (matches :u32)
  (started :bool) (ready :bool) (checkpoint :u60) (cut-commit :u60) (cut-event :u60)
  (descriptor-domain :u60) (descriptor-unit :u60) (descriptor-epoch :u60)
  (descriptor-allocation :u60) (descriptor-kind :u60) (descriptor-length :u60))
 :extra-fields
 ((fn2-checkpoint-recovery-evidence-bytes :type (array (unsigned-byte 8) (896)) :initially 0
   :why "256 job bytes: anchor batch/prior-checkpoint/anchor hashes, parsed immediate predecessor, records/deps/final hashes; four retained160-byte evidence stripes bind batch/prior-checkpoint/anchor/descriptor/immediate-predecessor hashes.")))

(defun fn2-checkpoint-recovery-evidence-fetch (left dst src slot gen okind oslot ogen fn2-pool fn2-checkpoint-recovery-evidence)
 (declare (xargs :stobjs (fn2-pool fn2-checkpoint-recovery-evidence) :measure (nfix left)
  :guard (and (fn2-pool-wfp fn2-pool) (fn2-checkpoint-recovery-evidence-wfp fn2-checkpoint-recovery-evidence)
              (natp left) (<= left 32) (natp dst) (<= (+ dst left) 896) (natp src))))
 (if (zp left) (mv :ok fn2-checkpoint-recovery-evidence)
  (mv-let (code byte) (fn2-pool-read slot gen src okind oslot ogen fn2-pool)
   (if (not (eq code :ok)) (mv code fn2-checkpoint-recovery-evidence)
    (let ((fn2-checkpoint-recovery-evidence (update-fn2-checkpoint-recovery-evidence-bytesi dst byte fn2-checkpoint-recovery-evidence)))
     (fn2-checkpoint-recovery-evidence-fetch (- left 1) (+ dst 1) (+ src 1) slot gen okind oslot ogen fn2-pool fn2-checkpoint-recovery-evidence))))))
(fn2-checkpoint-recovery-evidence-preserves fn2-checkpoint-recovery-evidence-fetch
 (left dst src slot gen okind oslot ogen fn2-pool fn2-checkpoint-recovery-evidence) :position 1)

(defun fn2-checkpoint-recovery-evidence-load (i src dst fn2-checkpoint-recovery-evidence fn2-digests)
 (declare (xargs :stobjs (fn2-checkpoint-recovery-evidence fn2-digests) :measure (nfix (- 8 (nfix i)))
  :guard (and (fn2-checkpoint-recovery-evidence-wfp fn2-checkpoint-recovery-evidence)
              (fn2-digest-rowp dst fn2-digests) (natp i) (<= i 8) (natp src) (<= (+ src 32) 896))))
 (if (or (not (natp i)) (>= i 8)) fn2-digests
  (let* ((at (+ src (* i 4)))
         (word (+ (fn2-checkpoint-recovery-evidence-bytesi at fn2-checkpoint-recovery-evidence)
                  (* 256 (fn2-checkpoint-recovery-evidence-bytesi (+ at 1) fn2-checkpoint-recovery-evidence))
                  (* 65536 (fn2-checkpoint-recovery-evidence-bytesi (+ at 2) fn2-checkpoint-recovery-evidence))
                  (* 16777216 (fn2-checkpoint-recovery-evidence-bytesi (+ at 3) fn2-checkpoint-recovery-evidence))))
         (fn2-digests (fn2-digest-set-word dst i word fn2-digests)))
   (fn2-checkpoint-recovery-evidence-load (+ 1 i) src dst fn2-checkpoint-recovery-evidence fn2-digests))))
(fn2-digests-preserves fn2-checkpoint-recovery-evidence-load
 (i src dst fn2-checkpoint-recovery-evidence fn2-digests) :position 0
 :hyps ((fn2-digest-rowp dst fn2-digests) (natp i) (<= i 8) (natp src) (<= (+ src 32) 896)))

(defun fn2-checkpoint-recovery-evidence-equal (left a b fn2-checkpoint-recovery-evidence)
 (declare (xargs :stobjs fn2-checkpoint-recovery-evidence :measure (nfix left)
  :guard (and (fn2-checkpoint-recovery-evidence-wfp fn2-checkpoint-recovery-evidence)
              (natp left) (<= left 32) (natp a) (natp b) (<= (+ a left) 896) (<= (+ b left) 896))))
 (if (zp left) t
  (and (= (fn2-checkpoint-recovery-evidence-bytesi a fn2-checkpoint-recovery-evidence)
          (fn2-checkpoint-recovery-evidence-bytesi b fn2-checkpoint-recovery-evidence))
       (fn2-checkpoint-recovery-evidence-equal (- left 1) (+ a 1) (+ b 1) fn2-checkpoint-recovery-evidence))))

(defun fn2-checkpoint-recovery-evidence-bound-hash-p (left at src fn2-checkpoint-bytes fn2-checkpoint-recovery-evidence)
 (declare (xargs :stobjs (fn2-checkpoint-bytes fn2-checkpoint-recovery-evidence) :measure (nfix left)
  :guard (and (fn2-checkpoint-bytes-wfp fn2-checkpoint-bytes) (fn2-checkpoint-recovery-evidence-wfp fn2-checkpoint-recovery-evidence)
              (natp left) (<= left 32) (natp at) (<= (+ at left) 32) (natp src)
              (<= (+ src left) (fn2-checkpoint-bytes-rows fn2-checkpoint-bytes)))))
 (if (zp left) t
  (and (= (fn2-checkpoint-bytes-value src fn2-checkpoint-bytes)
          (fn2-checkpoint-recovery-evidence-bytesi (+ 224 at) fn2-checkpoint-recovery-evidence))
       (fn2-checkpoint-recovery-evidence-bound-hash-p (- left 1) (+ at 1) (+ src 1) fn2-checkpoint-bytes fn2-checkpoint-recovery-evidence))))

; An installation match alone is insufficient: all authenticated arena tuples
; must be investigated to exclude a second matching physical batch.
(defun fn2-checkpoint-recovery-evidence-ready-p (c fn2-checkpoint-recovery-evidence)
 (declare (xargs :stobjs fn2-checkpoint-recovery-evidence :guard (fn2-checkpoint-recovery-evidence-wfp fn2-checkpoint-recovery-evidence)))
 (and (natp c) (< c 4) (< (+ 1 c) (fn2-checkpoint-recovery-evidence-rows fn2-checkpoint-recovery-evidence))
      (= (fn2-checkpoint-recovery-evidence-phase (+ 1 c) fn2-checkpoint-recovery-evidence) *fn2-checkpoint-recovery-evidence-phase-complete*)
      (= (fn2-checkpoint-recovery-evidence-ready (+ 1 c) fn2-checkpoint-recovery-evidence) 1)
      (= (fn2-checkpoint-recovery-evidence-candidate (+ 1 c) fn2-checkpoint-recovery-evidence) c)))
