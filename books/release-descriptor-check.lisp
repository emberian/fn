; Authenticates the actual captured descriptor Ref. This does not prove its
; historical installation/publication; the exact J member is checked later.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "checkpoint")
(include-book "recovery")
(include-book "release-allocation-state")
(fn2-book-layer :b)
(defun fn2-release-hash-load (i hash fn2-allocation-release fn2-digests)
 (declare (xargs :stobjs (fn2-allocation-release fn2-digests) :measure (nfix (- 8 (nfix i)))
  :guard (and (fn2-allocation-release-wfp fn2-allocation-release) (fn2-digests-wfp fn2-digests)
   (natp i) (<= i 8) (fn2-digest-rowp hash fn2-digests))))
 (if (>= (nfix i) 8) fn2-digests
  (let ((fn2-digests (fn2-digest-set-word hash i (fn2-release-descriptor-word i fn2-allocation-release) fn2-digests)))
   (fn2-release-hash-load (+ i 1) hash fn2-allocation-release fn2-digests))))
(defun fn2-release-hash-current-p (i hash fn2-allocation-release fn2-digests)
 (declare (xargs :stobjs (fn2-allocation-release fn2-digests) :measure (nfix (- 8 (nfix i)))
  :guard (and (fn2-allocation-release-wfp fn2-allocation-release) (fn2-digests-wfp fn2-digests)
   (natp i) (<= i 8) (fn2-digest-rowp hash fn2-digests))))
 (or (>= (nfix i) 8)
  (and (equal (fn2-digest-word hash i fn2-digests) (fn2-release-descriptor-word i fn2-allocation-release))
   (fn2-release-hash-current-p (+ i 1) hash fn2-allocation-release fn2-digests))))
(defmacro fn2-release-desc-mv (code)
 `(mv ,code fn2-allocation-release fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))
(defun fn2-release-descriptor-step (slot gen kind owner generation fn2-allocation-release fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
 (declare (xargs :stobjs (fn2-allocation-release fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
  :guard (and (fn2-allocation-release-wfp fn2-allocation-release) (fn2-fc-wfp fn2-fc) (fn2-fc-context-wfp fn2-fc-context)
   (fn2-b3-wfp fn2-b3) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool) (fn2-digests-wfp fn2-digests))))
 (b* ((row *fn2-rec-checker-row*) (base *fn2-rec-field-base*)
   (hash (fn2-digest-slot row *fn2-fc-hash*)) (geometry (fn2-digest-slot row *fn2-fc-geometry*))
   (previous (fn2-digest-slot row *fn2-fc-previous-seal*))
   ((unless (and (< 0 (fn2-allocation-release-rows fn2-allocation-release))
    (< row (fn2-fc-rows fn2-fc)) (< row (fn2-fc-context-rows fn2-fc-context))
    (fn2-b3-ready row fn2-b3 fn2-digests) (fn2-digest-rowp hash fn2-digests)
    (fn2-digest-rowp geometry fn2-digests) (fn2-digest-rowp previous fn2-digests)
    (<= (+ base (max *fn2-format-page-header-num-fields* *fn2-format-checkpoint-descriptor-num-fields*)) (fn2-fields-rows fn2-fields))
    (= (fn2-allocation-release-phase 0 fn2-allocation-release) *fn2-allocation-release-phase-replaying*)
    (= (fn2-allocation-release-read-purpose 0 fn2-allocation-release) *fn2-allocation-release-read-purpose-descriptor*)
    (= (fn2-allocation-release-read-phase 0 fn2-allocation-release) *fn2-allocation-release-read-phase-loaded*)
    (= (fn2-allocation-release-read-pending 0 fn2-allocation-release) 0)
    (= (fn2-allocation-release-read-unit 0 fn2-allocation-release) (fn2-allocation-release-physical-unit 0 fn2-allocation-release))
    (= (fn2-allocation-release-read-epoch 0 fn2-allocation-release) (fn2-allocation-release-descriptor-epoch 0 fn2-allocation-release))
    (= (fn2-allocation-release-read-allocation 0 fn2-allocation-release) (fn2-allocation-release-descriptor-allocation 0 fn2-allocation-release))
    (= (fn2-allocation-release-read-length 0 fn2-allocation-release) 4096)
    (equal slot (fn2-allocation-release-read-slot 0 fn2-allocation-release))
    (equal gen (fn2-allocation-release-read-gen 0 fn2-allocation-release))
    (equal kind (fn2-allocation-release-owner-kind 0 fn2-allocation-release))
    (equal owner (fn2-allocation-release-owner-slot 0 fn2-allocation-release))
    (equal generation (fn2-allocation-release-owner-gen 0 fn2-allocation-release))
    (eq (fn2-pool-workspace-code slot gen kind owner generation fn2-pool) :ok)
    (= (fn2-pool-fill slot fn2-pool) 4096))) (fn2-release-desc-mv :invalid)))
  (cond
   ((= (fn2-allocation-release-checker-stage 0 fn2-allocation-release) 0)
    (b* (((mv code next fn2-fields) (fn2-format-page-header-decode base slot gen 0 4096 kind owner generation fn2-fields fn2-pool))
     (history (fn2-fields-value (+ base *fn2-format-page-header-field-history*) fn2-fields))
     (incarnation (fn2-fields-value (+ base *fn2-format-page-header-field-incarnation*) fn2-fields))
     ((unless (and (eq code :ok) (natp next) (<= next 4096) (fn2-origin-physicalp history incarnation))) (fn2-release-desc-mv :invalid))
     (fn2-digests (fn2-release-hash-load 0 hash fn2-allocation-release fn2-digests))
     (fn2-fc (fn2-fc-reset row fn2-fc))
     (fn2-fc-context (fn2-fc-context-put row
      (location (fn2-allocation-release-physical-unit 0 fn2-allocation-release))
      (writer-epoch (fn2-allocation-release-descriptor-epoch 0 fn2-allocation-release))
      (allocation (fn2-allocation-release-descriptor-allocation 0 fn2-allocation-release))
      (history history) (incarnation incarnation) (page-kind *page-kind-checkpoint-descriptor*)
      (encoded-length 4096) (hash hash) (geometry geometry) (previous-seal previous)))
     (fn2-allocation-release (fn2-allocation-release-put 0 (history history) (incarnation incarnation) (checker-stage 1)
(checker-phase (fn2-fc-phase row fn2-fc))
(checker-pos (fn2-fc-pos row fn2-fc))
(checker-zero (fn2-fc-zero row fn2-fc))
(checker-pad (fn2-fc-pad row fn2-fc))
(checker-pad-end (fn2-fc-pad-end row fn2-fc))
(checker-geom (fn2-fc-geom row fn2-fc))
(checker-previous-seal-offset (fn2-fc-previous-seal-offset row fn2-fc)))))
     (fn2-release-desc-mv :more)))
   ((= (fn2-allocation-release-checker-stage 0 fn2-allocation-release) 1)
    (b* (((unless (and
(equal (fn2-fc-phase row fn2-fc)
       (fn2-allocation-release-checker-phase 0 fn2-allocation-release))
(equal (fn2-fc-pos row fn2-fc)
       (fn2-allocation-release-checker-pos 0 fn2-allocation-release))
(equal (fn2-fc-zero row fn2-fc)
       (fn2-allocation-release-checker-zero 0 fn2-allocation-release))
(equal (fn2-fc-pad row fn2-fc)
       (fn2-allocation-release-checker-pad 0 fn2-allocation-release))
(equal (fn2-fc-pad-end row fn2-fc)
       (fn2-allocation-release-checker-pad-end 0 fn2-allocation-release))
(equal (fn2-fc-geom row fn2-fc)
       (fn2-allocation-release-checker-geom 0 fn2-allocation-release))
(equal (fn2-fc-previous-seal-offset row fn2-fc)
       (fn2-allocation-release-checker-previous-seal-offset 0
                                                            fn2-allocation-release))
      (equal (fn2-fc-context-location row fn2-fc-context) (fn2-allocation-release-physical-unit 0 fn2-allocation-release))
      (equal (fn2-fc-context-writer-epoch row fn2-fc-context) (fn2-allocation-release-descriptor-epoch 0 fn2-allocation-release))
      (equal (fn2-fc-context-allocation row fn2-fc-context) (fn2-allocation-release-descriptor-allocation 0 fn2-allocation-release))
      (equal (fn2-fc-context-history row fn2-fc-context) (fn2-allocation-release-history 0 fn2-allocation-release))
      (equal (fn2-fc-context-incarnation row fn2-fc-context) (fn2-allocation-release-incarnation 0 fn2-allocation-release))
      (equal (fn2-fc-context-page-kind row fn2-fc-context) *page-kind-checkpoint-descriptor*)
      (equal (fn2-fc-context-encoded-length row fn2-fc-context) 4096)
      (equal (fn2-fc-context-hash row fn2-fc-context) hash)
      (equal (fn2-fc-context-geometry row fn2-fc-context) geometry)
      (equal (fn2-fc-context-previous-seal row fn2-fc-context) previous)
      (fn2-release-hash-current-p 0 hash fn2-allocation-release fn2-digests))) (fn2-release-desc-mv :invalid))
     ((mv code fn2-fc fn2-b3 fn2-fields fn2-pool fn2-digests)
      (fn2-format-run :page nil row slot gen 0 4096 base kind owner generation 4096 fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))
     ((unless (member-eq code '(:more :ok))) (fn2-release-desc-mv :invalid))
     (fn2-allocation-release (fn2-allocation-release-put 0
(checker-phase (fn2-fc-phase row fn2-fc))
(checker-pos (fn2-fc-pos row fn2-fc))
(checker-zero (fn2-fc-zero row fn2-fc))
(checker-pad (fn2-fc-pad row fn2-fc))
(checker-pad-end (fn2-fc-pad-end row fn2-fc))
(checker-geom (fn2-fc-geom row fn2-fc))
(checker-previous-seal-offset (fn2-fc-previous-seal-offset row fn2-fc))))
     ((when (eq code :more)) (fn2-release-desc-mv :more))
     ((mv decoded fn2-fields) (fn2-checkpoint-decode base slot gen 0 4096 kind owner generation fn2-fields fn2-pool))
     (cut (fn2-fields-value (+ base *fn2-format-checkpoint-descriptor-field-cut-commit*) fn2-fields))
     (event (fn2-fields-value (+ base *fn2-format-checkpoint-descriptor-field-cut-event*) fn2-fields))
     ((unless (and (eq decoded :ok)
      (= (fn2-fields-value (+ base *fn2-format-checkpoint-descriptor-field-checkpoint*) fn2-fields) (fn2-allocation-release-checkpoint 0 fn2-allocation-release))
      (<= (fn2-allocation-release-retirement 0 fn2-allocation-release) cut)
      (< cut (fn2-allocation-release-installation-commit 0 fn2-allocation-release))
      (< event (fn2-allocation-release-installation-event 0 fn2-allocation-release)))) (fn2-release-desc-mv :invalid))
     (fn2-allocation-release (fn2-allocation-release-put 0 (cut-commit cut) (cut-event event) (checker-stage 2))))
     (fn2-release-desc-mv :descriptor)))
   (t (fn2-release-desc-mv :invalid)))))

(fn2-allocation-release-preserves fn2-release-descriptor-step (slot gen
      kind
      owner
      generation
      fn2-allocation-release
      fn2-fc
      fn2-fc-context
      fn2-b3
      fn2-fields
      fn2-pool
      fn2-digests)
 :hyps ((fn2-allocation-releasep fn2-allocation-release) (fn2-allocation-release-wfp fn2-allocation-release) (fn2-fcp fn2-fc) (fn2-fc-wfp fn2-fc) (fn2-fc-contextp fn2-fc-context) (fn2-fc-context-wfp fn2-fc-context) (fn2-b3p fn2-b3) (fn2-b3-wfp fn2-b3) (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool) (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests))
 :specs (("-FN2-ALLOCATION-RELEASE-TYPE" fn2-allocation-releasep 1) ("-FN2-ALLOCATION-RELEASE-WFP" fn2-allocation-release-wfp 1) ("-FN2-ALLOCATION-RELEASE-ROWS" fn2-allocation-release-rows 1 :frame fn2-allocation-release)))

(fn2-fc-preserves fn2-release-descriptor-step (slot gen
      kind
      owner
      generation
      fn2-allocation-release
      fn2-fc
      fn2-fc-context
      fn2-b3
      fn2-fields
      fn2-pool
      fn2-digests)
 :hyps ((fn2-allocation-releasep fn2-allocation-release) (fn2-allocation-release-wfp fn2-allocation-release) (fn2-fcp fn2-fc) (fn2-fc-wfp fn2-fc) (fn2-fc-contextp fn2-fc-context) (fn2-fc-context-wfp fn2-fc-context) (fn2-b3p fn2-b3) (fn2-b3-wfp fn2-b3) (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool) (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests))
 :specs (("-FN2-FC-TYPE" fn2-fcp 2) ("-FN2-FC-WFP" fn2-fc-wfp 2) ("-FN2-FC-ROWS" fn2-fc-rows 2 :frame fn2-fc)))

(fn2-fc-context-preserves fn2-release-descriptor-step (slot gen
      kind
      owner
      generation
      fn2-allocation-release
      fn2-fc
      fn2-fc-context
      fn2-b3
      fn2-fields
      fn2-pool
      fn2-digests)
 :hyps ((fn2-allocation-releasep fn2-allocation-release) (fn2-allocation-release-wfp fn2-allocation-release) (fn2-fcp fn2-fc) (fn2-fc-wfp fn2-fc) (fn2-fc-contextp fn2-fc-context) (fn2-fc-context-wfp fn2-fc-context) (fn2-b3p fn2-b3) (fn2-b3-wfp fn2-b3) (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool) (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests))
 :specs (("-FN2-FC-CONTEXT-TYPE" fn2-fc-contextp 3) ("-FN2-FC-CONTEXT-WFP" fn2-fc-context-wfp 3) ("-FN2-FC-CONTEXT-ROWS" fn2-fc-context-rows 3 :frame fn2-fc-context)))

(fn2-b3-preserves fn2-release-descriptor-step (slot gen
      kind
      owner
      generation
      fn2-allocation-release
      fn2-fc
      fn2-fc-context
      fn2-b3
      fn2-fields
      fn2-pool
      fn2-digests)
 :hyps ((fn2-allocation-releasep fn2-allocation-release) (fn2-allocation-release-wfp fn2-allocation-release) (fn2-fcp fn2-fc) (fn2-fc-wfp fn2-fc) (fn2-fc-contextp fn2-fc-context) (fn2-fc-context-wfp fn2-fc-context) (fn2-b3p fn2-b3) (fn2-b3-wfp fn2-b3) (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool) (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests))
 :specs (("-FN2-B3-TYPE" fn2-b3p 4) ("-FN2-B3-WFP" fn2-b3-wfp 4) ("-FN2-B3-ROWS" fn2-b3-rows 4 :frame fn2-b3)))

(fn2-fields-preserves fn2-release-descriptor-step (slot gen
      kind
      owner
      generation
      fn2-allocation-release
      fn2-fc
      fn2-fc-context
      fn2-b3
      fn2-fields
      fn2-pool
      fn2-digests)
 :hyps ((fn2-allocation-releasep fn2-allocation-release) (fn2-allocation-release-wfp fn2-allocation-release) (fn2-fcp fn2-fc) (fn2-fc-wfp fn2-fc) (fn2-fc-contextp fn2-fc-context) (fn2-fc-context-wfp fn2-fc-context) (fn2-b3p fn2-b3) (fn2-b3-wfp fn2-b3) (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool) (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests))
 :specs (("-FN2-FIELDS-TYPE" fn2-fieldsp 5) ("-FN2-FIELDS-WFP" fn2-fields-wfp 5) ("-FN2-FIELDS-ROWS" fn2-fields-rows 5 :frame fn2-fields)))

(fn2-pool-preserves fn2-release-descriptor-step (slot gen
      kind
      owner
      generation
      fn2-allocation-release
      fn2-fc
      fn2-fc-context
      fn2-b3
      fn2-fields
      fn2-pool
      fn2-digests)
 :hyps ((fn2-allocation-releasep fn2-allocation-release) (fn2-allocation-release-wfp fn2-allocation-release) (fn2-fcp fn2-fc) (fn2-fc-wfp fn2-fc) (fn2-fc-contextp fn2-fc-context) (fn2-fc-context-wfp fn2-fc-context) (fn2-b3p fn2-b3) (fn2-b3-wfp fn2-b3) (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool) (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests))
 :specs (("-FN2-POOL-TYPE" fn2-poolp 6) ("-FN2-POOL-WFP" fn2-pool-wfp 6) ("-FN2-POOL-ROWS" fn2-pool-rows 6 :frame fn2-pool)))

(fn2-digests-preserves fn2-release-descriptor-step (slot gen
      kind
      owner
      generation
      fn2-allocation-release
      fn2-fc
      fn2-fc-context
      fn2-b3
      fn2-fields
      fn2-pool
      fn2-digests)
 :hyps ((fn2-allocation-releasep fn2-allocation-release) (fn2-allocation-release-wfp fn2-allocation-release) (fn2-fcp fn2-fc) (fn2-fc-wfp fn2-fc) (fn2-fc-contextp fn2-fc-context) (fn2-fc-context-wfp fn2-fc-context) (fn2-b3p fn2-b3) (fn2-b3-wfp fn2-b3) (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool) (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests))
 :specs (("-FN2-DIGESTS-TYPE" fn2-digestsp 7) ("-FN2-DIGESTS-WFP" fn2-digests-wfp 7) ("-FN2-DIGESTS-ROWS" fn2-digests-rows 7 :frame fn2-digests)))

(fn2-digests-preserves fn2-release-hash-load (i hash fn2-allocation-release fn2-digests)
 :hyps ((fn2-allocation-releasep fn2-allocation-release) (fn2-allocation-release-wfp fn2-allocation-release)
        (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests) (natp i) (<= i 8) (fn2-digest-rowp hash fn2-digests))
 :specs (("-TYPE" fn2-digestsp 0) ("-WFP" fn2-digests-wfp 0) ("-ROWS" fn2-digests-rows 0 :frame fn2-digests)))
