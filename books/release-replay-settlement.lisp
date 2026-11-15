; Private indexed target settlement shared by selected prefix inventory and
; chronological suffix RELEASE. Authentication and source-specific coverage
; belong to the actual D reader caller.
; This lower primitive cannot mint either authority and has no cost face.
; It keeps all three evidence claims after target FREE; only the exact new
; authenticated summary/Fence substitution may discharge those proof objects.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "release-evidence")
(include-book "checkpoint-owned-release")
(include-book "alloc-identity-index")
(fn2-book-layer :b)

(defconst *fn2-release-replay-settlement-children*
 '(fn2-allocation-release fn2-release-evidence fn2-release-evidence-candidates
   fn2-checkpoint-construction fn2-extents fn2-alloc-edges fn2-ops fn2-checkpoints))

(defmacro fn2-release-replay-settlement-function (name args &rest body)
 `(defun ,name (,@args ,@*fn2-release-replay-settlement-children*)
   (declare (xargs :stobjs ,*fn2-release-replay-settlement-children* :verify-guards nil
      :guard (and ,@(fn2-columns-carrier-hyps (pairlis$ *fn2-release-replay-settlement-children* nil)))))
   ,@body))

(fn2-release-replay-settlement-function fn2-release-target-settlement-code ()
 (b* (((unless (and (< 0 (fn2-allocation-release-rows fn2-allocation-release))
    (= (fn2-allocation-release-phase 0 fn2-allocation-release) *fn2-allocation-release-phase-replaying*)
    (= (fn2-allocation-release-read-pending 0 fn2-allocation-release) 0)
    (= (fn2-allocation-release-evidence-owned 0 fn2-allocation-release) 1)
    (= (fn2-allocation-release-candidate-bound 0 fn2-allocation-release) 0)
    (= (fn2-allocation-release-candidate 0 fn2-allocation-release) 0)
    (= (fn2-alloc-freeze-phase fn2-extents) 4)
    (= (fn2-alloc-epoch-begun fn2-extents) 0))) :state)
  (journal (fn2-allocation-release-journal 0 fn2-allocation-release))
  (batch (fn2-allocation-release-batch 0 fn2-allocation-release))
  (target (fn2-allocation-release-extent 0 fn2-allocation-release))
  (epoch (fn2-allocation-release-epoch 0 fn2-allocation-release))
  (allocation (fn2-allocation-release-allocation 0 fn2-allocation-release))
  (retirement (fn2-allocation-release-retirement 0 fn2-allocation-release))
  (cut (fn2-allocation-release-cut-commit 0 fn2-allocation-release))
  ((unless (and (posp (fn2-allocation-release-replay-generation 0 fn2-allocation-release))
    (posp retirement) (<= retirement cut)
    (< cut (fn2-allocation-release-installation-commit 0 fn2-allocation-release))
    (< (fn2-allocation-release-installation-commit 0 fn2-allocation-release) batch)
    (< (fn2-allocation-release-cut-event 0 fn2-allocation-release) (fn2-allocation-release-installation-event 0 fn2-allocation-release))
    (< (fn2-allocation-release-installation-event 0 fn2-allocation-release) (fn2-allocation-release-event 0 fn2-allocation-release)))) :record)
  ((unless (and (fn2-alloc-slotp target fn2-extents)
    (< journal (fn2-release-evidence-rows fn2-release-evidence))
    (= (fn2-release-evidence-phase journal fn2-release-evidence) *fn2-release-evidence-phase-persisted*)
    (fn2-release-evidence-row-matches journal fn2-allocation-release fn2-release-evidence)
    (fn2-release-evidence-row-owned-p journal
     (fn2-allocation-release-journal-epoch 0 fn2-allocation-release)
     (fn2-allocation-release-journal-allocation 0 fn2-allocation-release) batch
     fn2-release-evidence fn2-release-evidence-candidates fn2-extents fn2-alloc-edges fn2-ops fn2-checkpoints))) :evidence)
  ((unless (and (not (= target journal))
    (not (= target (fn2-allocation-release-installation-position 0 fn2-allocation-release)))
    (not (= target (floor (fn2-allocation-release-physical-unit 0 fn2-allocation-release) *fn2-storage-extent-units*)))
    (= (fn2-extents-state target fn2-extents) *fn2-extent-state-retire-pending*)
    (= (fn2-extents-retirement target fn2-extents) retirement))) :target)
  (code (fn2-alloc-release-under-cut-code target epoch allocation cut fn2-extents))
  ((unless (eq code :ok)) code))
  (fn2-checkpoint-owned-release-ledger-code target epoch allocation fn2-checkpoint-construction)))

(defmacro fn2-release-replay-settlement-mv (code next)
 `(mv ,code ,next fn2-allocation-release fn2-release-evidence fn2-checkpoint-construction fn2-extents))
(defmacro fn2-release-target-settlement-current-code ()
 `(fn2-release-target-settlement-code ,@*fn2-release-replay-settlement-children*))
(fn2-release-replay-settlement-function fn2-release-target-settlement-progress ()
 (b* ((code (fn2-release-target-settlement-current-code))
  ((unless (eq code :ok)) (fn2-release-replay-settlement-mv code 0))
  (kind (fn2-allocation-release-owner-kind 0 fn2-allocation-release))
  (owner (fn2-allocation-release-owner-slot 0 fn2-allocation-release))
  (ogen (fn2-allocation-release-owner-gen 0 fn2-allocation-release))
  ; The index belongs to the selected source's common generation, never its
  ; descriptor cut, checkpoint number, allocator epoch or transient row tag.
  (source (fn2-allocation-release-replay-generation 0 fn2-allocation-release))
  (target (fn2-allocation-release-extent 0 fn2-allocation-release))
  (epoch (fn2-allocation-release-epoch 0 fn2-allocation-release))
  (allocation (fn2-allocation-release-allocation 0 fn2-allocation-release))
  (cut (fn2-allocation-release-cut-commit 0 fn2-allocation-release))
  ((unless (fn2-alloc-identity-owner-p kind owner ogen source fn2-extents))
   (fn2-release-replay-settlement-mv :owner 0))
  (phase (fn2-alloc-identity-phase fn2-extents))
  ((when (= phase *fn2-alloc-identity-phase-idle*))
   (b* (((mv code fn2-extents)
          (fn2-alloc-identity-prepare-free kind owner ogen source target epoch allocation cut fn2-extents)))
    (fn2-release-replay-settlement-mv code 0)))
  ((unless (fn2-alloc-identity-free-pending-p kind owner ogen source target epoch allocation cut fn2-extents))
   (fn2-release-replay-settlement-mv :changed 0))
  ((when (= phase *fn2-alloc-identity-phase-probe*))
   (b* (((mv code fn2-extents) (fn2-alloc-identity-step kind owner ogen source fn2-extents)))
    (fn2-release-replay-settlement-mv (if (eq code :ready) :more code) 0)))
  ((unless (fn2-alloc-identity-free-ready-p kind owner ogen source target epoch allocation cut fn2-extents))
   (fn2-release-replay-settlement-mv :changed 0))
  ; Current-code above already preflights this exact construction row before
  ; the only allocator mutation. No yield or fallible check follows :OK.
  ((mv code fn2-extents) (fn2-alloc-identity-commit-free kind owner ogen source fn2-extents))
  ((unless (eq code :ok)) (fn2-release-replay-settlement-mv code 0))
  (journal (fn2-allocation-release-journal 0 fn2-allocation-release))
  (fn2-checkpoint-construction (fn2-checkpoint-owned-release-clear target fn2-checkpoint-construction))
  ; LIVE and every descriptor/J/self proof edge deliberately survive.
  (fn2-release-evidence (fn2-release-evidence-set-phase journal *fn2-release-evidence-phase-settled* fn2-release-evidence)))
  (fn2-release-replay-settlement-mv :settled 0)))

; Only the ordinary authenticated suffix reader consumes its original member
; cursor. A pending prefix inventory caller uses the common target kernel
; under its actual root4/selected-G queue contract, never fake RC offsets.
(fn2-release-replay-settlement-function fn2-release-replay-settlement-code ()
 (if (not (and (< 0 (fn2-allocation-release-rows fn2-allocation-release))
    (= (fn2-allocation-release-checker-stage 0 fn2-allocation-release) 8)
    (= (fn2-allocation-release-read-phase 0 fn2-allocation-release) *fn2-allocation-release-read-phase-loaded*)
    (= (fn2-allocation-release-read-purpose 0 fn2-allocation-release) *fn2-allocation-release-read-purpose-installation-records*)
    (= (fn2-allocation-release-replay-commit 0 fn2-allocation-release) (fn2-allocation-release-batch 0 fn2-allocation-release))
    (> (fn2-allocation-release-batch 0 fn2-allocation-release) (fn2-allocation-release-replay-base 0 fn2-allocation-release))
    (< (fn2-allocation-release-replay-roff 0 fn2-allocation-release) (fn2-allocation-release-replay-next 0 fn2-allocation-release))
    (<= (fn2-allocation-release-replay-next 0 fn2-allocation-release) (fn2-allocation-release-replay-rend 0 fn2-allocation-release))
    (<= (fn2-allocation-release-replay-rend 0 fn2-allocation-release) *fn2-commit-unit-bytes*)))
  :record (fn2-release-target-settlement-current-code)))
(defmacro fn2-release-replay-settlement-current-code ()
 `(fn2-release-replay-settlement-code ,@*fn2-release-replay-settlement-children*))
(defmacro fn2-release-target-settlement-current-progress ()
 `(fn2-release-target-settlement-progress ,@*fn2-release-replay-settlement-children*))
(fn2-release-replay-settlement-function fn2-release-replay-settlement-progress ()
 (b* ((code (fn2-release-replay-settlement-current-code))
      ((unless (eq code :ok)) (fn2-release-replay-settlement-mv code 0))
      ((mv code & fn2-allocation-release fn2-release-evidence fn2-checkpoint-construction fn2-extents)
        (fn2-release-target-settlement-current-progress))
      ((unless (eq code :settled)) (fn2-release-replay-settlement-mv code 0))
      (next (fn2-allocation-release-replay-next 0 fn2-allocation-release))
      (fn2-allocation-release (fn2-allocation-release-put 0
        (phase *fn2-allocation-release-phase-idle*) (evidence-owned 0)
        (read-phase *fn2-allocation-release-read-phase-idle*) (checker-stage 0))))
  (fn2-release-replay-settlement-mv :settled next)))

; The private transition carries every actual readonly input's TYPE and WFP.
; These are shape/frame obligations, not authentication or prefix authority.
(defmacro fn2-release-replay-settlement-contracts (name)
 (let* ((args *fn2-release-replay-settlement-children*)
        (hyps (fn2-columns-carrier-hyps (pairlis$ args nil))))
 `(progn
   (fn2-allocation-release-preserves ,name ,args
    :hyps ,hyps
    :specs (("-CONTROL-TYPE" fn2-allocation-releasep 2)
            ("-CONTROL-WFP" fn2-allocation-release-wfp 2)
            ("-CONTROL-ROWS" fn2-allocation-release-rows 2 :frame fn2-allocation-release)
            ("-EVIDENCE-TYPE" fn2-release-evidencep 3)
            ("-EVIDENCE-WFP" fn2-release-evidence-wfp 3)
            ("-EVIDENCE-ROWS" fn2-release-evidence-rows 3 :frame fn2-release-evidence)
            ("-CONSTRUCTION-TYPE" fn2-checkpoint-constructionp 4)
            ("-CONSTRUCTION-WFP" fn2-checkpoint-construction-wfp 4)
            ("-CONSTRUCTION-ROWS" fn2-checkpoint-construction-rows 4 :frame fn2-checkpoint-construction)
            ("-EXTENTS-TYPE" fn2-extentsp 5)
            ("-EXTENTS-WFP" fn2-extents-wfp 5)
            ("-EXTENTS-ROWS" fn2-extents-rows 5 :frame fn2-extents))))))
(fn2-release-replay-settlement-contracts fn2-release-target-settlement-progress)
(fn2-release-replay-settlement-contracts fn2-release-replay-settlement-progress)

; Exact refusal frames at the actual private entrypoints. The positive test
; also asserts that removing the non-OK premise changes the real index cursor.
(defmacro fn2-release-replay-settlement-refusal-frame (code-fn progress-fn name)
 (let ((children *fn2-release-replay-settlement-children*))
 `(defthm ,name
   (implies (and ,@(fn2-columns-carrier-hyps (pairlis$ children nil))
                 (not (equal (,code-fn ,@children) :ok)))
    (equal (,progress-fn ,@children)
           (mv (,code-fn ,@children) 0 fn2-allocation-release fn2-release-evidence fn2-checkpoint-construction fn2-extents)))
   :hints (("Goal" :in-theory (enable ,progress-fn)))
   :rule-classes nil)))
(fn2-release-replay-settlement-refusal-frame fn2-release-target-settlement-code fn2-release-target-settlement-progress
 fn2-release-target-settlement-refusal-frame-by-definition)
(fn2-release-replay-settlement-refusal-frame fn2-release-replay-settlement-code fn2-release-replay-settlement-progress
 fn2-release-replay-settlement-refusal-frame-by-definition)
(defmacro fn2-release-target-settlement-control-frame ()
 `(defthm fn2-release-target-settlement-control-frame-by-definition
   (implies (and ,@(fn2-columns-carrier-hyps (pairlis$ *fn2-release-replay-settlement-children* nil)))
    (equal (mv-nth 2 (fn2-release-target-settlement-progress ,@*fn2-release-replay-settlement-children*)) fn2-allocation-release))
   :hints (("Goal" :in-theory (enable fn2-release-target-settlement-progress)))
   :rule-classes nil))
(fn2-release-target-settlement-control-frame)
