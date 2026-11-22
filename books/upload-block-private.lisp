; Split U-byte reads from 32-byte pool writes; F-2 is never retained.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "upload-stream")
(local (include-book "std/lists/update-nth" :dir :system))
(local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))
(fn2-book-layer :d)

; ROW is the derived hash executor (F-2 for data, SOURCE for final root).
; PRIVATE is always SOURCE's declared FC result region, not B3 result57.
(defun fn2-upload-hash-private-children
 (row source ls lg off len kind id gen fn2-b3 fn2-digests fn2-pool)
 (declare (xargs :stobjs (fn2-b3 fn2-digests fn2-pool) :guard (fn2-pool-wfp fn2-pool)))
 (b* ((private (fn2-digest-slot (nfix source) *fn2-fc-result*))
      (result (fn2-digest-slot (nfix row) *fn2-b3-result*))
      ((unless (and (natp row) (natp source) (fn2-b3-ready source fn2-b3 fn2-digests)
        (fn2-b3-ready row fn2-b3 fn2-digests) (fn2-digest-rowp private fn2-digests)
        (fn2-digest-rowp result fn2-digests) (posp len) (<= len *fn2-commit-unit-bytes*)
        (unsigned-byte-p 32 off) (unsigned-byte-p 32 (+ off len))
        (eq (fn2-pool-workspace-code ls lg kind id gen fn2-pool) :ok)
        (eq (fn2-layout-range-code ls lg off (+ off len) nil kind id gen fn2-pool) :ok)))
       (mv :fault fn2-b3 fn2-digests))
      ((mv code fn2-b3 fn2-digests)
       (fn2-block-hash-into row ls lg off len kind id gen fn2-b3 fn2-digests fn2-pool))
      ((unless (and (eq code :ok) (fn2-digest-rowp private fn2-digests)
                    (fn2-digest-rowp result fn2-digests))) (mv :fault fn2-b3 fn2-digests))
      (fn2-digests (fn2-digest-copy private result fn2-digests)))
  (mv :ok fn2-b3 fn2-digests)))

(defun fn2-upload-cv-private-children (source ls lg block kind id gen fn2-digests fn2-pool)
 (declare (xargs :stobjs (fn2-digests fn2-pool) :guard (fn2-pool-wfp fn2-pool)))
 (let* ((private (fn2-digest-slot (nfix source) *fn2-fc-result*))
        (counter (* 4 (nfix block)))
        (off (+ (if (and (natp ls) (< ls (fn2-pool-rows fn2-pool)))
                     (fn2-pool-slot-base ls fn2-pool) 0) *fn2-upload-page-stage*)))
  (if (not (and (natp source) (natp block) (fn2-digest-rowp private fn2-digests)
       (unsigned-byte-p 54 counter) (<= (+ counter 4) (expt 2 54))
       (eq (fn2-pool-workspace-code ls lg kind id gen fn2-pool) :ok)
       (eq (fn2-layout-range-code ls lg *fn2-upload-page-stage*
             (+ *fn2-upload-page-stage* *fn2-commit-unit-bytes*) nil kind id gen fn2-pool) :ok)
       (natp off) (<= (+ off *fn2-commit-unit-bytes*) (fn2-pool-data-length fn2-pool))))
      (mv :fault fn2-digests)
   (let ((fn2-digests (fn2-b3-subtree-cv-into private off *fn2-commit-unit-bytes* counter fn2-digests fn2-pool)))
    (mv :ok fn2-digests)))))

(local (in-theory (disable fn2-b3-ready fn2-b3-rows fn2-digests-rows
                           fn2-digest-rowp fn2-digest-workspacep fn2-digest-slot
                           fn2-pool-workspace-code fn2-layout-range-code
                           fn2-b3-subtree-cv-into-by-definition)))

(fn2-fc-shape fn2-upload-hash-private-children-shape
 (fn2-upload-hash-private-children row source ls lg off len kind id gen fn2-b3 fn2-digests fn2-pool)
 (and (fn2-b3p fn2-b3) (fn2-b3-wfp fn2-b3) (fn2-digestsp fn2-digests)
      (fn2-digests-wfp fn2-digests) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
 ((fn2-b3 1) (fn2-digests 2)))
(fn2-fc-shape fn2-upload-cv-private-children-shape
 (fn2-upload-cv-private-children source ls lg block kind id gen fn2-digests fn2-pool)
 (and (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests)
      (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)) ((fn2-digests 1)))

; Generate the exact point observation for the concrete operation's returned
; digest carrier. The caller supplies the destination or excluded stripe.
(local
 (defun fn2-upload-frame-event (name stobj suffix observation hyps hints world)
  (declare (xargs :verify-guards nil))
  (let* ((args (getpropc name 'formals nil world))
         (outs (getpropc name 'stobjs-out nil world))
         (pos (position-eq stobj outs))
         (call (cons name args))
         (value (cond ((equal (len outs) 1) call)
                      ((equal pos 0) (list 'car call))
                      (t (list 'mv-nth pos call)))))
   (if (not (and (member-eq stobj args) pos))
       (er hard 'fn2-upload-frame-event "Missing ~x0 carrier for ~x1." stobj name)
     `(defthm ,(fn2-columns-sym name suffix)
        (implies (and ,@hyps)
                 ,(subst value 'output (subst stobj 'input observation)))
        :hints ,hints)))))

(local
 (defmacro fn2-upload-digest-frame (name hyps &rest hints)
  `(make-event (value (fn2-upload-frame-event ',name 'fn2-digests "-UPLOAD-DIGEST-FRAME"
                        '(equal (fn2-digest-word at i output) (fn2-digest-word at i input))
                        '((natp at) ,@hyps) ',hints (w state))))))

(local
 (defthm fn2-upload-nfix-natural
  (implies (natp x) (equal (nfix x) x))
  :hints (("Goal" :in-theory (enable nfix)))))

(local
 (defmacro fn2-upload-digest-dst-frame (name)
  `(fn2-upload-digest-frame ,name ((not (equal at (nfix dst))))
     ("Goal" :in-theory (e/d (,name fn2-digest-word nth-update-nth)
                             (nth update-nth nfix))))))

(local (fn2-upload-digest-dst-frame fn2-digest-copy))
(local (fn2-upload-digest-dst-frame fn2-digest-iv))
(local (fn2-upload-digest-dst-frame fn2-b3-parent-cv))
(local (fn2-upload-digest-dst-frame fn2-b3-parent-root))
(local (fn2-upload-digest-dst-frame fn2-b3-subtree-cv-into))
(local (fn2-upload-digest-dst-frame fn2-b3-output))
(local (fn2-upload-digest-frame fn2-b3-parent ((not (equal at (nfix dst))))
        ("Goal" :in-theory (enable fn2-b3-parent))))

(local
 (defun fn2-upload-outside-b3-p (at row)
  (declare (xargs :guard (and (natp at) (natp row))
                  :guard-hints (("Goal" :in-theory (enable fn2-digest-slot)))))
  (or (< at (fn2-digest-slot row 0))
      (< (fn2-digest-slot row *fn2-b3-result*) at))))

(local
 (defmacro fn2-upload-digest-stripe-frame (name &rest extra-hyps)
  `(fn2-upload-digest-frame ,name ((natp row) (fn2-upload-outside-b3-p at row) ,@extra-hyps)
     ("Goal" :in-theory (enable ,name fn2-digest-slot)))))

(local
 (fn2-upload-digest-frame fn2-b3-push
  ((natp row) (fn2-upload-outside-b3-p at row)
   (not (equal at (nfix src))) (< (nfix depth) 54))
  ("Goal" :induct (fn2-b3-push row n depth src fn2-digests fn2-b3)
           :in-theory (e/d (fn2-b3-push fn2-digest-slot)
                           (fn2-b3-parent floor)))))
(local
 (fn2-upload-digest-stripe-frame fn2-b3-init))
(local
 (fn2-upload-digest-stripe-frame fn2-b3-flush))
(local
 (fn2-upload-digest-stripe-frame fn2-b3-byte))
(local
 (fn2-upload-digest-frame fn2-b3-chunk-output-into ((natp row) (fn2-upload-outside-b3-p at row))
  ("Goal" :in-theory (e/d (fn2-b3-chunk-output-into fn2-digest-slot fn2-digest-word nth-update-nth)
                          (nth update-nth nfix)))))
(local
 (fn2-upload-digest-stripe-frame fn2-b3-bulk))
(local
 (fn2-upload-digest-stripe-frame fn2-b3-span))
(local
 (fn2-upload-digest-stripe-frame fn2-b3-feed))
(local
 (fn2-upload-digest-stripe-frame fn2-b3-fragment-into))
(local
 (fn2-upload-digest-stripe-frame fn2-b3-update))
(local
 (fn2-upload-digest-frame fn2-b3-fold ((not (equal at (nfix dst))))
  ("Goal" :induct (fn2-b3-fold dst row depth root fn2-digests fn2-b3)
           :in-theory (enable fn2-b3-fold))))
(local (fn2-upload-digest-frame fn2-b3-finish ((not (equal at (nfix dst))))
        ("Goal" :in-theory (enable fn2-b3-finish))))
(local (fn2-upload-digest-frame fn2-b3-finalize ((not (equal at (nfix dst))))
        ("Goal" :in-theory (enable fn2-b3-finalize))))
(local (fn2-upload-digest-stripe-frame fn2-block-hash-span))
(local (fn2-upload-digest-stripe-frame fn2-block-hash-into))

; The separate B3 carrier has scalar columns and a physically striped
; buffered-word array. Both observations follow its actual returned state.
(local
 (defmacro fn2-upload-b3-value-frame (name &optional extra-hyps)
  (let ((domain '((natp source) (natp row) (not (equal source row))))
        (hints `(("Goal" :in-theory (e/d (,name nth-update-nth) (nth update-nth nfix floor mod))))))
   `(make-event
     (value (list 'progn
      (fn2-upload-frame-event ',name 'fn2-b3 "-UPLOAD-B3-COLUMN-FRAME"
       '(equal (nth source (nth column output)) (nth source (nth column input)))
       '(,@domain (natp column) (< column *fn2-b3-rows*) ,@extra-hyps) ',hints (w state))
      (fn2-upload-frame-event ',name 'fn2-b3 "-UPLOAD-B3-WORD-VALUE-FRAME"
       '(equal (nth at (nth *fn2-b3-wordsi* output))
               (nth at (nth *fn2-b3-wordsi* input)))
       '((natp row) (natp at) (or (< at (* 16 row)) (<= (+ 16 (* 16 row)) at))
         ,@extra-hyps) ',hints (w state))))))))

(local
 (defthm fn2-upload-b3-byte-index-bound
  (and (natp (floor (mod x 64) 4)) (< (floor (mod x 64) 4) 16))
  :hints (("Goal" :cases ((rationalp x)) :in-theory (disable mod floor))
          ("Subgoal 1" :use ((:instance mod-bounds-1 (y 64))
                             (:instance floor-bounds-1 (x (mod x 64)) (y 4))))
          ("Subgoal 2" :in-theory (enable mod floor)))))

(local (fn2-upload-b3-value-frame fn2-b3-store ((natp i) (< i 16))))
(local (fn2-upload-b3-value-frame fn2-b3-init))
(local (fn2-upload-b3-value-frame fn2-b3-push))
(local (fn2-upload-b3-value-frame fn2-b3-flush))
(local (fn2-upload-b3-value-frame fn2-b3-byte))
(local (fn2-upload-b3-value-frame fn2-b3-pool-message ((natp i) (<= i 16))))
(local (fn2-upload-b3-value-frame fn2-b3-chunk-output-into))
(local (fn2-upload-b3-value-frame fn2-b3-bulk))
(local (fn2-upload-b3-value-frame fn2-b3-span))
(local (fn2-upload-b3-value-frame fn2-b3-feed))
(local (fn2-upload-b3-value-frame fn2-b3-fragment-into))
(local (fn2-upload-b3-value-frame fn2-b3-update))
(local (fn2-upload-b3-value-frame fn2-block-hash-span))
(local (fn2-upload-b3-value-frame fn2-block-hash-into))

(local
 (defthm fn2-upload-foreign-word-outside-b3-stripe
  (implies (and (natp source) (natp row) (not (equal source row)) (natp i) (< i 16))
           (or (< (+ i (* 16 source)) (* 16 row))
               (<= (+ 16 (* 16 row)) (+ i (* 16 source)))))
  :hints (("Goal" :cases ((< source row))))))

(local
 (defthm fn2-upload-digest-slot-natural
  (implies (and (natp row) (natp region))
           (natp (fn2-digest-slot row region)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn2-digest-slot)))))

(local
 (defthm fn2-upload-other-stripe-outside-b3
  (implies (and (natp source) (natp row) (not (equal source row))
                (natp region) (< region *fn2-digest-stride*))
           (fn2-upload-outside-b3-p (fn2-digest-slot source region) row))
  :hints (("Goal" :cases ((< source row))
                  :in-theory (enable fn2-upload-outside-b3-p fn2-digest-slot)))))

(local
 (defthm fn2-upload-low-region-distinct-from-private-result
  (implies (and (natp source) (natp region) (<= region *fn2-b3-result*))
           (not (equal (fn2-digest-slot source region)
                       (fn2-digest-slot source *fn2-fc-result*))))
  :hints (("Goal" :in-theory (enable fn2-digest-slot)))))

(defthm fn2-b3-update-preserves-digest-word-outside-workspace
 (implies (and (natp at) (natp row)
               (or (< at (fn2-digest-slot row 0))
                   (< (fn2-digest-slot row *fn2-b3-result*) at)))
          (equal (fn2-digest-word at i
                  (mv-nth 2 (fn2-b3-update row slot gen off len okind oslot ogen fn2-digests fn2-b3 fn2-pool)))
                 (fn2-digest-word at i fn2-digests)))
 :hints (("Goal" :use fn2-b3-update-upload-digest-frame
                 :in-theory (disable fn2-b3-update fn2-b3-update-upload-digest-frame))))

; Actual B3 update owns regions0..57, leaving the declared FC result125.
(defthm fn2-upload-b3-update-preserves-private-result
 (implies (and (fn2-b3-ready source fn2-b3 fn2-digests)
  (fn2-digestsp fn2-digests) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)
  (unsigned-byte-p 32 off) (unsigned-byte-p 32 len) (natp i) (< i 8))
  (equal (fn2-digest-word (fn2-digest-slot source *fn2-fc-result*) i
           (mv-nth 2 (fn2-b3-update source ls lg off len kind id gen fn2-digests fn2-b3 fn2-pool)))
         (fn2-digest-word (fn2-digest-slot source *fn2-fc-result*) i fn2-digests)))
 :hints (("Goal" :in-theory (enable fn2-digest-slot fn2-b3-ready))))
(defthm fn2-upload-hash-private-preserves-source-digest-context
 (implies (and (natp source) (natp row) (not (equal source row))
  (natp region) (<= region *fn2-b3-result*) (natp i) (< i 8)
  (fn2-b3p fn2-b3) (fn2-b3-wfp fn2-b3) (fn2-digestsp fn2-digests)
  (fn2-digests-wfp fn2-digests) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
  (equal (fn2-digest-word (fn2-digest-slot source region) i
           (mv-nth 2 (fn2-upload-hash-private-children row source ls lg off len kind id gen fn2-b3 fn2-digests fn2-pool)))
         (fn2-digest-word (fn2-digest-slot source region) i fn2-digests)))
 :hints (("Goal" :in-theory (e/d (fn2-upload-hash-private-children)
                                (fn2-upload-outside-b3-p)))))

(defthm fn2-upload-scratch-hash-preserves-other-digest-stripe
 (implies (and (natp source) (natp row) (not (equal source row))
  (natp region) (< region *fn2-digest-stride*) (natp i) (< i 8)
  (fn2-b3p fn2-b3) (fn2-b3-wfp fn2-b3) (fn2-digestsp fn2-digests)
  (fn2-digests-wfp fn2-digests) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
  (equal (fn2-digest-word (fn2-digest-slot source region) i
           (mv-nth 2 (fn2-block-hash-into row ls lg off len kind id gen fn2-b3 fn2-digests fn2-pool)))
         (fn2-digest-word (fn2-digest-slot source region) i fn2-digests)))
 :hints (("Goal" :in-theory (disable fn2-upload-outside-b3-p))))
(defthm fn2-upload-hash-private-preserves-source-b3-columns
 (implies (and (natp source) (natp row) (not (equal source row))
  (natp column) (< column *fn2-b3-rows*)
  (fn2-b3p fn2-b3) (fn2-b3-wfp fn2-b3) (fn2-digestsp fn2-digests)
  (fn2-digests-wfp fn2-digests) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
  (equal (nth source (nth column
           (mv-nth 1 (fn2-upload-hash-private-children row source ls lg off len kind id gen fn2-b3 fn2-digests fn2-pool))))
         (nth source (nth column fn2-b3))))
 :hints (("Goal" :in-theory (enable fn2-upload-hash-private-children))))
(defthm fn2-upload-hash-private-preserves-source-b3-words
 (implies (and (natp source) (natp row) (not (equal source row)) (natp i) (< i 16)
  (fn2-b3p fn2-b3) (fn2-b3-wfp fn2-b3) (fn2-digestsp fn2-digests)
  (fn2-digests-wfp fn2-digests) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
  (equal (nth (+ (* 16 source) i) (nth *fn2-b3-wordsi*
           (mv-nth 1 (fn2-upload-hash-private-children row source ls lg off len kind id gen fn2-b3 fn2-digests fn2-pool))))
         (nth (+ (* 16 source) i) (nth *fn2-b3-wordsi* fn2-b3))))
 :hints (("Goal" :cases ((< source row))
                 :use ((:instance fn2-block-hash-into-upload-b3-word-value-frame
                         (at (+ i (* 16 source))) (lslot ls) (lgen lg) (boff off)
                         (okind kind) (oslot id) (ogen gen)))
                 :in-theory (e/d (fn2-upload-hash-private-children)
                                 (fn2-block-hash-into-upload-b3-word-value-frame)))))

(defmacro fn2-upload-block-private-op-events ()
 '(progn
   (defun fn2-upload-private-source (id gen fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (if (and (eq (fn2-upload-snapshot-read-code id fn2-core) :ok)
             (posp gen) (unsigned-byte-p 60 gen) (equal (fn2-machine-generation id fn2-core) gen)
             (equal (fn2-upload-row-pending id fn2-core) 0)
             (fn2-upload-stream-page-ready-p id gen fn2-core))
        (mv :ok (fn2-upload-hasher id fn2-core) (fn2-upload-row-lslot id fn2-core)
            (fn2-upload-row-lgen id fn2-core))
      (mv :fault 0 0 0)))
   (defun fn2-upload-block-hash-keep (id gen fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (b* (((mv code source ls lg) (fn2-upload-private-source id gen fn2-core))
         ((unless (and (eq code :ok)
           (equal (fn2-upload-row-phase id fn2-core) *fn2-upload-state-stream-block*)
           (equal (fn2-upload-row-mstep id fn2-core) 0))) (mv :fault fn2-core))
         (len (fn2-upload-row-stream-stage-used id fn2-core)))
     (stobj-let ((fn2-b3 (fn2-core-b3 fn2-core)) (fn2-digests (fn2-core-digests fn2-core))
                 (fn2-pool (fn2-core-pool fn2-core))) (code fn2-b3 fn2-digests)
      (let ((row (fn2-b-block-read-row (fn2-b3-rows fn2-b3))))
       (if (< source row)
        (fn2-upload-hash-private-children row source ls lg *fn2-upload-page-stage* len *fn2-upload-kind* id gen
                                          fn2-b3 fn2-digests fn2-pool)
        (mv :fault fn2-b3 fn2-digests))) (mv code fn2-core))))
   (defun fn2-upload-block-cv-keep (id gen fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (b* (((mv code source ls lg) (fn2-upload-private-source id gen fn2-core))
         ((unless (and (eq code :ok)
           (equal (fn2-upload-row-phase id fn2-core) *fn2-upload-state-stream-block*)
           (equal (fn2-upload-row-mstep id fn2-core) 3)
           (equal (fn2-upload-row-stream-stage-used id fn2-core) *fn2-commit-unit-bytes*))) (mv :fault fn2-core))
         (block (floor (fn2-upload-row-pdone id fn2-core) *fn2-commit-unit-bytes*)))
     (stobj-let ((fn2-digests (fn2-core-digests fn2-core)) (fn2-pool (fn2-core-pool fn2-core)))
      (code fn2-digests)
      (fn2-upload-cv-private-children source ls lg
       block *fn2-upload-kind* id gen fn2-digests fn2-pool)
      (mv code fn2-core))))
   (defun fn2-upload-root-hash-keep (id gen fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (b* (((mv code source ls lg) (fn2-upload-private-source id gen fn2-core))
         (unit (if (eq code :ok) (fn2-upload-row-munit id fn2-core) 0))
         ((unless (and (eq code :ok)
           (equal (fn2-upload-row-phase id fn2-core) *fn2-upload-state-stream-root-write*)
           (equal (fn2-upload-row-mstep id fn2-core) 0)
           (natp unit) (< unit *fn2-commit-write-resources*))) (mv :fault fn2-core)))
     (stobj-let ((fn2-b3 (fn2-core-b3 fn2-core)) (fn2-digests (fn2-core-digests fn2-core))
                 (fn2-pool (fn2-core-pool fn2-core))) (code fn2-b3 fn2-digests)
      (fn2-upload-hash-private-children source source ls lg
       (+ *fn2-upload-page-manifest* (* unit *fn2-commit-unit-bytes*)) *fn2-commit-unit-bytes*
       *fn2-upload-kind* id gen fn2-b3 fn2-digests fn2-pool) (mv code fn2-core))))
   (defun fn2-upload-private-result-store (id gen fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (b* (((mv code source ls lg) (fn2-upload-private-source id gen fn2-core))
         ((unless (eq code :ok)) (mv :fault fn2-core))
         (phase (fn2-upload-row-phase id fn2-core)) (step (fn2-upload-row-mstep id fn2-core))
         (unit (fn2-upload-row-munit id fn2-core))
         (target (cond ((and (equal phase *fn2-upload-state-stream-block*) (equal step 1)) *fn2-upload-page-hash*)
                       ((and (equal phase *fn2-upload-state-stream-block*) (equal step 4)) (+ 32 *fn2-upload-page-hash*))
                       ((and (equal phase *fn2-upload-state-stream-root-write*) (equal step 1)
                             (natp unit) (< unit *fn2-commit-write-resources*))
                        (+ *fn2-upload-page-location-hashes* (* 32 unit))) (t nil)))
         ((unless (natp target)) (mv :fault fn2-core)))
     (stobj-let ((fn2-digests (fn2-core-digests fn2-core)) (fn2-pool (fn2-core-pool fn2-core))) (code fn2-pool)
      (let ((private (fn2-digest-slot source *fn2-fc-result*)))
       (if (and (fn2-digest-rowp private fn2-digests)
                (eq (fn2-layout-range-code ls lg target (+ target 32) t *fn2-upload-kind* id gen fn2-pool) :ok))
        (mv-let (code fn2-pool) (fn2-digest-store 32 private ls lg target *fn2-upload-kind* id gen fn2-digests fn2-pool)
         (mv (if (eq code :ok) :ok :fault) fn2-pool)) (mv :fault fn2-pool)))
      (mv code fn2-core))))
   (fn2-core-preserves fn2-upload-block-hash-keep (id gen fn2-core) :position 1 :rows nil)
   (fn2-core-preserves fn2-upload-block-cv-keep (id gen fn2-core) :position 1 :rows nil)
   (fn2-core-preserves fn2-upload-root-hash-keep (id gen fn2-core) :position 1 :rows nil)
   (fn2-core-preserves fn2-upload-private-result-store (id gen fn2-core) :position 1 :rows nil)
   (defcost fn2-upload-block-hash-keep :answers (:ok :fault) :faults (:fault)
    :bytes *fn2-commit-unit-bytes* :tables (fn2-core-b3 fn2-core-digests)
    :doc "Hash the actual staged block and keep words in private SOURCE FC125; no pool write.")
   (defcost fn2-upload-block-cv-keep :answers (:ok :fault) :faults (:fault)
    :bytes *fn2-commit-unit-bytes* :tables (fn2-core-digests)
    :doc "Read one full staged unit and retain its actual subtree CV in SOURCE FC125.")
   (defcost fn2-upload-root-hash-keep :answers (:ok :fault) :faults (:fault)
    :bytes *fn2-commit-unit-bytes* :tables (fn2-core-b3 fn2-core-digests)
    :doc "After SOURCE finalization reuse its context for one root unit; retain private result words.")
   (defcost fn2-upload-private-result-store :answers (:ok :fault) :faults (:fault)
    :bytes 32 :tables (fn2-core-pool)
    :doc "Store the retained private words at the actual phase/substep destination; no F-2 dependency.")))
