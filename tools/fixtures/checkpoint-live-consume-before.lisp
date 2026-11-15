; Runtime base publication consumes the actual completed pending authority.
; The canonical prefix remains owned by checkpoint root3 source edges. This
; publication neither drops those holds nor grants RELEASE_ALLOCATION authority.
(in-package "ACL2")
(include-book "checkpoint-directory-rebase")
(include-book "event-catalog-live")
(fn2-book-layer :c)

; Fixed representation work: 32 descriptor bytes, 480 frontier words and eight
; predecessor words. There is no work proportional to retained history here.
(defun fn2-directory-rebase-transfer-bytes (i fn2-checkpoint-summary-authority)
 (declare (xargs :stobjs fn2-checkpoint-summary-authority :measure (nfix (- 520 (nfix i)))
  :guard (and (fn2-checkpoint-summary-authority-wfp fn2-checkpoint-summary-authority)
              (natp i) (<= i 520))))
 (if (>= (nfix i) 520) fn2-checkpoint-summary-authority
  (let ((fn2-checkpoint-summary-authority
   (cond ((< i 32) (update-fn2-checkpoint-summary-authority-descriptori i
           (fn2-checkpoint-summary-authority-descriptori (+ 32 i) fn2-checkpoint-summary-authority) fn2-checkpoint-summary-authority))
         ((< i 512) (update-fn2-checkpoint-summary-authority-frontieri (- i 32)
           (fn2-checkpoint-summary-authority-frontieri (+ 480 (- i 32)) fn2-checkpoint-summary-authority) fn2-checkpoint-summary-authority))
         (t (update-fn2-checkpoint-summary-authority-cut-seali (- i 512)
           (fn2-checkpoint-summary-authority-cut-seali (+ 8 (- i 512)) fn2-checkpoint-summary-authority) fn2-checkpoint-summary-authority)))))
   (fn2-directory-rebase-transfer-bytes (+ 1 i) fn2-checkpoint-summary-authority))))

(defun fn2-directory-rebase-seal-p (i fn2-directory-rebase fn2-checkpoint-summary-authority)
 (declare (xargs :stobjs (fn2-directory-rebase fn2-checkpoint-summary-authority) :measure (nfix (- 8 (nfix i)))
  :guard (and (fn2-directory-rebase-wfp fn2-directory-rebase)
              (fn2-checkpoint-summary-authority-wfp fn2-checkpoint-summary-authority) (natp i) (<= i 8))))
 (or (>= (nfix i) 8)
  (and (= (fn2-directory-rebase-seal-wordsi i fn2-directory-rebase)
          (fn2-checkpoint-summary-authority-cut-seali (+ 8 i) fn2-checkpoint-summary-authority))
       (fn2-directory-rebase-seal-p (+ 1 i) fn2-directory-rebase fn2-checkpoint-summary-authority))))

(defun fn2-directory-rebase-base-seal (i row fn2-checkpoint-summary-authority fn2-digests)
 (declare (xargs :stobjs (fn2-checkpoint-summary-authority fn2-digests) :measure (nfix (- 8 (nfix i)))
  :guard (and (fn2-checkpoint-summary-authority-wfp fn2-checkpoint-summary-authority) (fn2-digests-wfp fn2-digests)
              (natp i) (<= i 8) (fn2-digest-rowp row fn2-digests))))
 (if (>= (nfix i) 8) fn2-digests
  (let ((fn2-digests (fn2-digest-set-word row i
         (fn2-checkpoint-summary-authority-cut-seali (+ 8 i) fn2-checkpoint-summary-authority) fn2-digests)))
   (fn2-directory-rebase-base-seal (+ 1 i) row fn2-checkpoint-summary-authority fn2-digests))))

(defun fn2-directory-rebase-consume (token kind owner gen fn2-directory-rebase fn2-checkpoint-summary-authority
 fn2-csnapshot fn2-checkpoint-publication fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-commit-root
 fn2-extents fn2-fc fn2-digests fn2-checkpoint-restore-events fn2-checkpoint-restore-events-work)
 (declare (xargs :stobjs (fn2-directory-rebase fn2-checkpoint-summary-authority fn2-csnapshot fn2-checkpoint-publication
 fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-commit-root fn2-extents fn2-fc fn2-digests fn2-checkpoint-restore-events fn2-checkpoint-restore-events-work)
 :guard (and (fn2-directory-rebase-wfp fn2-directory-rebase) (fn2-checkpoint-summary-authority-wfp fn2-checkpoint-summary-authority)
             (fn2-csnapshot-wfp fn2-csnapshot) (fn2-checkpoint-publication-wfp fn2-checkpoint-publication)
             (fn2-checkpoints-wfp fn2-checkpoints) (fn2-checkpoint-refs-wfp fn2-checkpoint-refs)
             (fn2-checkpoint-bytes-wfp fn2-checkpoint-bytes) (fn2-commit-root-wfp fn2-commit-root)
             (fn2-extents-wfp fn2-extents) (fn2-fc-wfp fn2-fc) (fn2-digests-wfp fn2-digests) (fn2-checkpoint-restore-events-wfp fn2-checkpoint-restore-events)
             (fn2-checkpoint-restore-events-work-wfp fn2-checkpoint-restore-events-work))))
 (b* (((unless (and (unsigned-byte-p 60 token) (posp token) (unsigned-byte-p 8 kind)
                    (unsigned-byte-p 32 owner) (unsigned-byte-p 60 gen)
                    (< 0 (fn2-directory-rebase-rows fn2-directory-rebase))
                    (< 0 (fn2-commit-root-rows fn2-commit-root))
                    (= (fn2-directory-rebase-phase 0 fn2-directory-rebase) *fn2-directory-rebase-phase-source-scanned*)
                    (= token (fn2-directory-rebase-token 0 fn2-directory-rebase))
                    (= kind (fn2-directory-rebase-owner-kind 0 fn2-directory-rebase))
                    (= owner (fn2-directory-rebase-owner-slot 0 fn2-directory-rebase))
                    (= gen (fn2-directory-rebase-owner-gen 0 fn2-directory-rebase))
                    (fn2-csnapshot-ownerp token kind owner gen fn2-csnapshot)
                    (= (fn2-csnapshot-phase 0 fn2-csnapshot) *fn2-csnapshot-phase-held*)
                    (= (fn2-alloc-freeze-phase fn2-extents) 2)
                    (= (fn2-alloc-freeze-token fn2-extents) token)
                    (= (fn2-alloc-freeze-owner-kind fn2-extents) kind)
                    (= (fn2-alloc-freeze-owner-slot fn2-extents) owner)
                    (= (fn2-alloc-freeze-owner-gen fn2-extents) gen)))
       (mv :owner fn2-directory-rebase fn2-checkpoint-summary-authority fn2-commit-root fn2-digests))
      ((unless (and (fn2-checkpoint-summary-authority-row-complete-p 1 fn2-checkpoint-summary-authority fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes)
                    (= (fn2-checkpoint-summary-authority-origin 1 fn2-checkpoint-summary-authority) *fn2-checkpoint-summary-authority-origin-live*)
                    (= (fn2-checkpoint-summary-authority-tag 1 fn2-checkpoint-summary-authority) token)
                    (= (fn2-checkpoint-summary-authority-owner-kind 1 fn2-checkpoint-summary-authority) kind)
                    (= (fn2-checkpoint-summary-authority-owner-slot 1 fn2-checkpoint-summary-authority) owner)
                    (= (fn2-checkpoint-summary-authority-owner-gen 1 fn2-checkpoint-summary-authority) gen)
                    (= (fn2-checkpoint-summary-authority-candidate 1 fn2-checkpoint-summary-authority) (fn2-directory-rebase-candidate 0 fn2-directory-rebase))
                    (= (fn2-checkpoint-summary-authority-checkpoint 1 fn2-checkpoint-summary-authority) (fn2-directory-rebase-checkpoint 0 fn2-directory-rebase))
                    (= (fn2-checkpoint-summary-authority-history 1 fn2-checkpoint-summary-authority) (fn2-directory-rebase-history 0 fn2-directory-rebase))
                    (= (fn2-checkpoint-summary-authority-incarnation 1 fn2-checkpoint-summary-authority) (fn2-directory-rebase-incarnation 0 fn2-directory-rebase))
                    (= (fn2-checkpoint-summary-authority-cut-commit 1 fn2-checkpoint-summary-authority) (fn2-directory-rebase-target 0 fn2-directory-rebase))
                    (= (fn2-checkpoint-summary-authority-cut-event 1 fn2-checkpoint-summary-authority) (fn2-directory-rebase-target-event 0 fn2-directory-rebase))
                    (fn2-directory-rebase-seal-p 0 fn2-directory-rebase fn2-checkpoint-summary-authority)
                    (fn2-event-catalog-subject-p 1 fn2-checkpoint-summary-authority fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-events fn2-checkpoint-restore-events-work)))
       (mv :authority fn2-directory-rebase fn2-checkpoint-summary-authority fn2-commit-root fn2-digests))
      (c (fn2-directory-rebase-candidate 0 fn2-directory-rebase))
      (target (fn2-directory-rebase-target 0 fn2-directory-rebase))
      (installation (fn2-directory-rebase-installation 0 fn2-directory-rebase))
      (base (fn2-directory-rebase-base-batch 0 fn2-directory-rebase))
      (base-seal (* *fn2-digest-stride* (fn2-fc-rows fn2-fc)))
      ((unless (and (fn2-directory-rebase-publishedp c fn2-checkpoint-publication fn2-checkpoints fn2-checkpoint-bytes)
                    (= (fn2-checkpoint-publication-phase 0 fn2-checkpoint-publication) *fn2-checkpoint-publication-phase-complete*)
                    (= (fn2-commit-root-base-batch 0 fn2-commit-root) base)
                    (= (fn2-commit-root-base-event 0 fn2-commit-root) (fn2-directory-rebase-base-event 0 fn2-directory-rebase))
                    (< base target) (<= target installation)
                    (= installation (fn2-checkpoints-installation-commit c fn2-checkpoints))
                    (= installation (fn2-commit-root-installed 0 fn2-commit-root))
                    (= installation (fn2-commit-root-published 0 fn2-commit-root))
                    (= installation (fn2-commit-root-proposed 0 fn2-commit-root))
                    (= (+ 1 (fn2-directory-rebase-installation-event 0 fn2-directory-rebase)) (fn2-commit-root-first-key 0 fn2-commit-root))
                    (= (fn2-directory-rebase-scanned 0 fn2-directory-rebase) (- installation base))
                    (= (fn2-directory-rebase-suffix-scanned 0 fn2-directory-rebase) (- installation target))
                    (= (fn2-directory-rebase-last-event 0 fn2-directory-rebase) (fn2-directory-rebase-installation-event 0 fn2-directory-rebase))
                    (fn2-digest-rowp base-seal fn2-digests)))
       (mv :source fn2-directory-rebase fn2-checkpoint-summary-authority fn2-commit-root fn2-digests))
      ; One atomic installation: prefix source edges, suffix rows, active live
      ; Merkle state and old C query catalog are deliberately untouched.
      (fn2-digests (fn2-directory-rebase-base-seal 0 base-seal fn2-checkpoint-summary-authority fn2-digests))
      (fn2-checkpoint-summary-authority (fn2-directory-rebase-transfer-bytes 0 fn2-checkpoint-summary-authority))
      (fn2-checkpoint-summary-authority (fn2-checkpoint-summary-authority-put 0
       (phase *fn2-checkpoint-summary-authority-phase-complete*) (origin *fn2-checkpoint-summary-authority-origin-live*)
       (tag (fn2-checkpoint-summary-authority-tag 1 fn2-checkpoint-summary-authority)) (candidate c)
       (checkpoint (fn2-checkpoint-summary-authority-checkpoint 1 fn2-checkpoint-summary-authority))
       (cut-commit target) (cut-event (fn2-checkpoint-summary-authority-cut-event 1 fn2-checkpoint-summary-authority))
       (history (fn2-checkpoint-summary-authority-history 1 fn2-checkpoint-summary-authority))
       (incarnation (fn2-checkpoint-summary-authority-incarnation 1 fn2-checkpoint-summary-authority))
       (generation (fn2-checkpoint-summary-authority-generation 1 fn2-checkpoint-summary-authority))
       (catalog-tag (fn2-checkpoint-summary-authority-catalog-tag 1 fn2-checkpoint-summary-authority))
       (source-count (fn2-checkpoint-summary-authority-source-count 1 fn2-checkpoint-summary-authority))
       (source-observation (fn2-checkpoint-summary-authority-source-observation 1 fn2-checkpoint-summary-authority))
       (cursor 488) (owner-kind kind) (owner-slot owner) (owner-gen gen)))
      (fn2-commit-root (fn2-commit-root-put 0 (base-batch target)
       (base-event (fn2-directory-rebase-target-event 0 fn2-directory-rebase)) (base-ready 1)))
      (fn2-checkpoint-summary-authority (fn2-checkpoint-summary-authority-put 1
       (phase *fn2-checkpoint-summary-authority-phase-idle*) (origin *fn2-checkpoint-summary-authority-origin-none*) (cursor 0)))
      (fn2-directory-rebase (fn2-directory-rebase-set-phase 0 *fn2-directory-rebase-phase-committed* fn2-directory-rebase)))
  (mv :committed fn2-directory-rebase fn2-checkpoint-summary-authority fn2-commit-root fn2-digests)))

(defcost fn2-checkpoint-directory-rebase-begin-op :child fn2-directory-rebase-begin :answers t :bytes 128
 :tables (fn2-core-checkpoint-directory-rebase fn2-core-csnapshot fn2-core-checkpoint-publication fn2-core-checkpoints fn2-core-checkpoint-bytes fn2-core-commit-root fn2-core-extents))
(defcost fn2-checkpoint-directory-rebase-step-op :child fn2-directory-rebase-step :answers t :bytes 32
 :tables (fn2-core-checkpoint-directory-rebase fn2-core-csnapshot fn2-core-checkpoint-publication fn2-core-checkpoints fn2-core-checkpoint-bytes fn2-core-commit-root fn2-core-extents fn2-core-alloc-edges fn2-core-ops fn2-core-fc fn2-core-digests))
(defcost fn2-checkpoint-directory-rebase-consume-op :child fn2-directory-rebase-consume :answers t :bytes 4096
 :tables (fn2-core-checkpoint-directory-rebase fn2-core-checkpoint-summary-authority fn2-core-csnapshot fn2-core-checkpoint-publication fn2-core-checkpoints fn2-core-checkpoint-refs fn2-core-checkpoint-bytes fn2-core-commit-root fn2-core-extents fn2-core-fc fn2-core-digests fn2-core-checkpoint-restore-events fn2-core-checkpoint-restore-events-work)
 :doc "Publish exact base C and consume pending authority only after held canonical prefix and complete C+1..J suffix scan; retain every allocator/query/archive hold.")

(fn2-checkpoint-summary-authority-preserves fn2-directory-rebase-transfer-bytes
 (i fn2-checkpoint-summary-authority)
 :hyps ((fn2-checkpoint-summary-authorityp fn2-checkpoint-summary-authority) (fn2-checkpoint-summary-authority-wfp fn2-checkpoint-summary-authority))
 :carriers ((fn2-checkpoint-summary-authority nil :prefix "-0")))

(fn2-digests-preserves fn2-directory-rebase-base-seal
 (i row fn2-checkpoint-summary-authority fn2-digests)
 :hyps ((fn2-checkpoint-summary-authorityp fn2-checkpoint-summary-authority) (fn2-checkpoint-summary-authority-wfp fn2-checkpoint-summary-authority) (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests))
 :carriers ((fn2-digests nil :prefix "-0")))

(fn2-directory-rebase-preserves fn2-directory-rebase-consume
 (token kind owner gen fn2-directory-rebase fn2-checkpoint-summary-authority
 fn2-csnapshot fn2-checkpoint-publication fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-commit-root
 fn2-extents fn2-fc fn2-digests fn2-checkpoint-restore-events fn2-checkpoint-restore-events-work)
 :hyps ((fn2-checkpoint-restore-eventsp fn2-checkpoint-restore-events) (fn2-checkpoint-restore-events-wfp fn2-checkpoint-restore-events) (fn2-checkpoint-restore-events-workp fn2-checkpoint-restore-events-work) (fn2-checkpoint-restore-events-work-wfp fn2-checkpoint-restore-events-work) (fn2-directory-rebasep fn2-directory-rebase) (fn2-directory-rebase-wfp fn2-directory-rebase) (fn2-checkpoint-summary-authorityp fn2-checkpoint-summary-authority) (fn2-checkpoint-summary-authority-wfp fn2-checkpoint-summary-authority) (fn2-csnapshotp fn2-csnapshot) (fn2-csnapshot-wfp fn2-csnapshot) (fn2-checkpoint-publicationp fn2-checkpoint-publication) (fn2-checkpoint-publication-wfp fn2-checkpoint-publication) (fn2-checkpointsp fn2-checkpoints) (fn2-checkpoints-wfp fn2-checkpoints) (fn2-checkpoint-refsp fn2-checkpoint-refs) (fn2-checkpoint-refs-wfp fn2-checkpoint-refs) (fn2-checkpoint-bytesp fn2-checkpoint-bytes) (fn2-checkpoint-bytes-wfp fn2-checkpoint-bytes) (fn2-commit-rootp fn2-commit-root) (fn2-commit-root-wfp fn2-commit-root) (fn2-extentsp fn2-extents) (fn2-extents-wfp fn2-extents) (fn2-fcp fn2-fc) (fn2-fc-wfp fn2-fc) (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests))
 :carriers ((fn2-directory-rebase 1 :prefix "-0") (fn2-checkpoint-summary-authority 2 :prefix "-1") (fn2-commit-root 3 :prefix "-2") (fn2-digests 4 :prefix "-3")))
