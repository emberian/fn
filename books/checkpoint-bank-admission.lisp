; A bounded reservation of C directory ROW geometry, not physical extents or
; a durable publication promise. Created only while the actual snapshot is
; HELD, before any construction allocation or Write. It cannot mint APPLIED.
(in-package "ACL2")
(include-book "checkpoint-summary-state")
(include-book "c-snapshot")
(include-book "runs")
(fn2-book-layer :c)

(defcolumns fn2-checkpoint-bank-admission
 ((phase (:enum fn2-checkpoint-bank-admission-phase (:idle :scan :ready)))
  (token :u60) (owner-kind :u8) (owner-slot :u32) (owner-gen :u60)
  (cut-commit :u60) (cut-event :u60)
  (active-phase :u8) (active-tag :u60) (active-bank :bool) (bank :bool)
  (resident-limit :u32) (bank-capacity :u32) (cursor :u32)))

(defun fn2-checkpoint-bank-admission-current-p
 (token kind owner generation fn2-csnapshot fn2-checkpoint-summary
  fn2-run-installed fn2-checkpoint-bank-admission)
 (declare (xargs :stobjs (fn2-csnapshot fn2-checkpoint-summary
  fn2-run-installed fn2-checkpoint-bank-admission)
  :guard (and (fn2-csnapshot-wfp fn2-csnapshot)
   (fn2-checkpoint-summary-wfp fn2-checkpoint-summary)
   (fn2-run-installed-wfp fn2-run-installed)
   (fn2-checkpoint-bank-admission-wfp fn2-checkpoint-bank-admission))))
 (and (< 0 (fn2-checkpoint-bank-admission-rows fn2-checkpoint-bank-admission))
  (< 0 (fn2-checkpoint-summary-rows fn2-checkpoint-summary))
  (fn2-csnapshot-ownerp token kind owner generation fn2-csnapshot)
  (= (fn2-csnapshot-phase 0 fn2-csnapshot) *fn2-csnapshot-phase-held*)
  (fn2-run-installed-bank-geometry-p fn2-run-installed)
  (not (= (fn2-checkpoint-bank-admission-phase 0 fn2-checkpoint-bank-admission)
          *fn2-checkpoint-bank-admission-phase-idle*))
  (equal token (fn2-checkpoint-bank-admission-token 0 fn2-checkpoint-bank-admission))
  (equal kind (fn2-checkpoint-bank-admission-owner-kind 0 fn2-checkpoint-bank-admission))
  (equal owner (fn2-checkpoint-bank-admission-owner-slot 0 fn2-checkpoint-bank-admission))
  (equal generation (fn2-checkpoint-bank-admission-owner-gen 0 fn2-checkpoint-bank-admission))
  (= (fn2-csnapshot-cut-commit 0 fn2-csnapshot)
     (fn2-checkpoint-bank-admission-cut-commit 0 fn2-checkpoint-bank-admission))
  (= (fn2-csnapshot-cut-event 0 fn2-csnapshot)
     (fn2-checkpoint-bank-admission-cut-event 0 fn2-checkpoint-bank-admission))
  (= (fn2-checkpoint-summary-phase 0 fn2-checkpoint-summary)
     (fn2-checkpoint-bank-admission-active-phase 0 fn2-checkpoint-bank-admission))
  (= (fn2-checkpoint-summary-tag 0 fn2-checkpoint-summary)
     (fn2-checkpoint-bank-admission-active-tag 0 fn2-checkpoint-bank-admission))
  (= (fn2-checkpoint-summary-bank 0 fn2-checkpoint-summary)
     (fn2-checkpoint-bank-admission-active-bank 0 fn2-checkpoint-bank-admission))
  (= (fn2-run-installed-resident-limit fn2-run-installed)
     (fn2-checkpoint-bank-admission-resident-limit 0 fn2-checkpoint-bank-admission))
  (= (fn2-run-installed-bank-capacity fn2-run-installed)
     (fn2-checkpoint-bank-admission-bank-capacity 0 fn2-checkpoint-bank-admission))))

(defun fn2-checkpoint-bank-admission-begin
 (token kind owner generation fn2-csnapshot fn2-checkpoint-summary
  fn2-run-installed fn2-checkpoint-bank-admission)
 (declare (xargs :stobjs (fn2-csnapshot fn2-checkpoint-summary
  fn2-run-installed fn2-checkpoint-bank-admission)
  :guard (and (fn2-csnapshot-wfp fn2-csnapshot)
   (fn2-checkpoint-summary-wfp fn2-checkpoint-summary)
   (fn2-run-installed-wfp fn2-run-installed)
   (fn2-checkpoint-bank-admission-wfp fn2-checkpoint-bank-admission))))
 (b* (((unless (and (unsigned-byte-p 60 token) (posp token)
   (unsigned-byte-p 8 kind) (unsigned-byte-p 32 owner) (unsigned-byte-p 60 generation)
   (< 0 (fn2-checkpoint-bank-admission-rows fn2-checkpoint-bank-admission))
   (< 0 (fn2-checkpoint-summary-rows fn2-checkpoint-summary))
   (fn2-csnapshot-ownerp token kind owner generation fn2-csnapshot)
   (= (fn2-csnapshot-phase 0 fn2-csnapshot) *fn2-csnapshot-phase-held*)
   (fn2-run-installed-bank-geometry-p fn2-run-installed)
   (member-equal (fn2-checkpoint-summary-phase 0 fn2-checkpoint-summary)
    (list *fn2-checkpoint-summary-phase-idle* *fn2-checkpoint-summary-phase-applied*))))
   (mv :source fn2-checkpoint-bank-admission))
  ((when (fn2-checkpoint-bank-admission-current-p token kind owner generation
    fn2-csnapshot fn2-checkpoint-summary fn2-run-installed fn2-checkpoint-bank-admission))
   (mv :more fn2-checkpoint-bank-admission))
  ; A token is minted by actual snapshot admission. It cannot restart its own
  ; stale/changed continuation; a later snapshot may replace an expired one.
  ((unless (or (= (fn2-checkpoint-bank-admission-phase 0 fn2-checkpoint-bank-admission)
                  *fn2-checkpoint-bank-admission-phase-idle*)
               (not (equal token (fn2-checkpoint-bank-admission-token 0 fn2-checkpoint-bank-admission)))))
   (mv :state fn2-checkpoint-bank-admission))
  (active-phase (fn2-checkpoint-summary-phase 0 fn2-checkpoint-summary))
  (active-bank (fn2-checkpoint-summary-bank 0 fn2-checkpoint-summary))
  (bank (if (= active-phase *fn2-checkpoint-summary-phase-applied*) (- 1 active-bank) 0))
  (fn2-checkpoint-bank-admission (fn2-checkpoint-bank-admission-put 0
   (phase *fn2-checkpoint-bank-admission-phase-scan*)
   (token token) (owner-kind kind) (owner-slot owner) (owner-gen generation)
   (cut-commit (fn2-csnapshot-cut-commit 0 fn2-csnapshot))
   (cut-event (fn2-csnapshot-cut-event 0 fn2-csnapshot))
   (active-phase active-phase) (active-tag (fn2-checkpoint-summary-tag 0 fn2-checkpoint-summary))
   (active-bank active-bank) (bank bank)
   (resident-limit (fn2-run-installed-resident-limit fn2-run-installed))
   (bank-capacity (fn2-run-installed-bank-capacity fn2-run-installed)) (cursor 0))))
  (mv :more fn2-checkpoint-bank-admission)))

(fn2-checkpoint-bank-admission-preserves fn2-checkpoint-bank-admission-begin
 (token kind owner generation fn2-csnapshot fn2-checkpoint-summary
  fn2-run-installed fn2-checkpoint-bank-admission) :position 1 :raw-rows t)

(defun fn2-checkpoint-bank-admission-step
 (token kind owner generation fn2-csnapshot fn2-checkpoint-summary
  fn2-run-installed fn2-checkpoint-bank-admission)
 (declare (xargs :stobjs (fn2-csnapshot fn2-checkpoint-summary
  fn2-run-installed fn2-checkpoint-bank-admission)
  :guard (and (fn2-csnapshot-wfp fn2-csnapshot)
   (fn2-checkpoint-summary-wfp fn2-checkpoint-summary)
   (fn2-run-installed-wfp fn2-run-installed)
   (fn2-checkpoint-bank-admission-wfp fn2-checkpoint-bank-admission))))
 (b* (((unless (fn2-checkpoint-bank-admission-current-p token kind owner generation
   fn2-csnapshot fn2-checkpoint-summary fn2-run-installed fn2-checkpoint-bank-admission))
   (mv :source fn2-checkpoint-bank-admission))
  (i (fn2-checkpoint-bank-admission-cursor 0 fn2-checkpoint-bank-admission))
  (capacity (fn2-run-installed-bank-capacity fn2-run-installed))
  ((when (= i capacity))
   (let ((fn2-checkpoint-bank-admission (fn2-checkpoint-bank-admission-set-phase
     0 *fn2-checkpoint-bank-admission-phase-ready* fn2-checkpoint-bank-admission)))
    (mv :ready fn2-checkpoint-bank-admission)))
  ((unless (and (< i capacity) (unsigned-byte-p 32 (+ 1 i))
    (= (fn2-checkpoint-bank-admission-phase 0 fn2-checkpoint-bank-admission)
       *fn2-checkpoint-bank-admission-phase-scan*)))
   (mv :state fn2-checkpoint-bank-admission))
  (r (+ (fn2-run-installed-bank-start
    (fn2-checkpoint-bank-admission-bank 0 fn2-checkpoint-bank-admission) fn2-run-installed) i))
  ((unless (and (< r (fn2-run-installed-rows fn2-run-installed))
    (= (fn2-run-installed-state r fn2-run-installed) *fn2-run-installed-state-free*)
    (= (fn2-run-installed-physical r fn2-run-installed) 0)))
   (mv :resources fn2-checkpoint-bank-admission))
  (fn2-checkpoint-bank-admission (fn2-checkpoint-bank-admission-set-cursor 0 (+ 1 i) fn2-checkpoint-bank-admission)))
  (mv :more fn2-checkpoint-bank-admission)))

(fn2-checkpoint-bank-admission-preserves fn2-checkpoint-bank-admission-step
 (token kind owner generation fn2-csnapshot fn2-checkpoint-summary
  fn2-run-installed fn2-checkpoint-bank-admission) :position 1 :raw-rows t)

(defun fn2-checkpoint-bank-admission-ready-p
 (token kind owner generation fn2-csnapshot fn2-checkpoint-summary
  fn2-run-installed fn2-checkpoint-bank-admission)
 (declare (xargs :stobjs (fn2-csnapshot fn2-checkpoint-summary
  fn2-run-installed fn2-checkpoint-bank-admission)
  :guard (and (fn2-csnapshot-wfp fn2-csnapshot)
   (fn2-checkpoint-summary-wfp fn2-checkpoint-summary)
   (fn2-run-installed-wfp fn2-run-installed)
   (fn2-checkpoint-bank-admission-wfp fn2-checkpoint-bank-admission))))
 (and (fn2-checkpoint-bank-admission-current-p token kind owner generation
   fn2-csnapshot fn2-checkpoint-summary fn2-run-installed fn2-checkpoint-bank-admission)
  (= (fn2-checkpoint-bank-admission-phase 0 fn2-checkpoint-bank-admission)
     *fn2-checkpoint-bank-admission-phase-ready*)
  (= (fn2-checkpoint-bank-admission-cursor 0 fn2-checkpoint-bank-admission)
     (fn2-run-installed-bank-capacity fn2-run-installed))))
