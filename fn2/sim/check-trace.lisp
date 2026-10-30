; TRACE compares independent selection first, then the resulting projection.
(in-package "ACL2")
(include-book "../books/q1")

(defun fn2-trace-selections (records)
  (declare (xargs :verify-guards nil))
  (if (atom records) nil
    (let* ((r (car records)) (kind (fn2-trace-record-kind r))
           (visit (member-equal kind (list *fn2-trace-kind-machine* *fn2-trace-kind-service*))))
      (cons (list kind (and (= kind *fn2-trace-kind-machine*) (fn2-trace-record-machine r))
                  (and visit (fn2-trace-record-principal r))
                  (and visit (fn2-trace-record-position r)))
            (fn2-trace-selections (cdr records))))))
(defun fn2-trace-field-difference (fields actual expected)
  (declare (xargs :verify-guards nil))
  (if (atom fields) nil
    (if (equal (car actual) (car expected))
        (fn2-trace-field-difference (cdr fields) (cdr actual) (cdr expected))
      (list (car fields) (car actual) (car expected)))))
(defun fn2-trace-selection-difference (actual expected)
  (declare (xargs :verify-guards nil))
  (cond ((and (atom actual) (atom expected)) nil)
        ((or (atom actual) (atom expected)) (list :selection-count (len actual) (len expected)))
        (t (or (fn2-trace-field-difference '(:kind :machine :principal :position) (car actual) (car expected))
               (fn2-trace-selection-difference (cdr actual) (cdr expected))))))

(defun fn2-trace-classify (lost selection before after)
  (declare (xargs :guard t))
  (cond (selection (cons :selection selection))
        ((not (equal lost 0)) (list :state :trace-lost lost))
        ((or before after) (cons :state (or before after)))
        (t nil)))

; Both cores persist across turns; import only the common adapter boundary.
(defun fn2-check-trace-turn (profile cursor queues fn2-core fn2-ref-core)
  (declare (xargs :stobjs (fn2-core fn2-ref-core) :verify-guards nil))
  (b* ((fn2-ref-core (fn2-ref-import-boundary fn2-core fn2-ref-core))
       (lists (fn2-ref-lists (fn2-profile-p profile) cursor queues))
       (before (fn2-ref-difference fn2-core fn2-ref-core lists))
       ((mv rs ro rv ra lists fn2-ref-core) (fn2-ref-turn lists fn2-ref-core))
       ((mv status obs visits actions fn2-core) (fn2-turn fn2-core))
       ((mv records lost) (stobj-let ((fn2-trace (fn2-core-trace fn2-core)))
                           (records lost) (mv (fn2-trace-records fn2-trace) (fn2-trace-lost fn2-trace))
                           (mv records lost)))
       (selection (fn2-trace-selection-difference (fn2-trace-selections records) (fn2-ref-selections lists)))
       (difference (fn2-trace-classify lost selection before
                      (or (fn2-ref-difference fn2-core fn2-ref-core lists)
                          (fn2-trace-field-difference '(:status :observations :visits :actions)
                             (list status obs visits actions) (list rs ro rv ra)))))
       (verdict (if difference (list :fail :trace difference) :pass)))
    (progn$ (if difference (cw "TRACE DIFFERENCE ~x0~%" difference) nil)
            (mv verdict status obs visits actions (nth 1 lists) (nth 2 lists) fn2-core fn2-ref-core))))
(in-theory (disable fn2-check-trace-turn))
(assert-event
 (and (equal (fn2-trace-classify 0 '(:machine 7 8) '(:generation) nil) '(:selection :machine 7 8))
      (equal (fn2-trace-classify 0 nil nil '(:steps 3 4)) '(:state :steps 3 4))
      (equal (fn2-trace-classify 1 '(:machine 7 8) nil nil) '(:selection :machine 7 8))
      (equal (fn2-trace-classify 1 nil nil nil) '(:state :trace-lost 1))
      (equal (fn2-trace-selection-difference `((,*fn2-trace-kind-machine* 7 2 3))
                                             `((,*fn2-trace-kind-machine* 8 2 3))) '(:machine 7 8))
      (equal (fn2-trace-field-difference '(:bytes :steps) '(2 3) '(2 4)) '(:steps 3 4))))
;
; TRACE per case (DSL-METATHEORY 3.3-3.4, DM3). The same turn, stepped one
; transition at a time by the two loops themselves (fn2-concrete-loop and
; fn2-ref-loop with fuel 1, each continuing exactly when its own named stop
; condition is false), so the stepped turn equals fn2-turn and fn2-ref-turn.
; Before every transition the Q1 labeller names its case; after it, the G1
; square of that case is checked: both loops continue together, the five
; results agree, and the representation relation holds with the reference's
; work counters normalised (fn2-ref-loop writes its accumulators on exit,
; which is fn2-q1-normalize-reference-work). CASES counts checked transitions
; per label; CERTIFIED counts (:run K P) transitions after which the core has
; no stop reason, where the generated run entry asserted K's arm certificate
; non-vacuously (a refused certificate stops the core with :machine-contract).
(defun fn2-trace-tally (label tally)
  (declare (xargs :guard t))
  (let ((entry (assoc-equal label (if (alistp tally) tally nil))))
    (if entry
        (put-assoc-equal label (+ 1 (nfix (cdr entry))) (if (alistp tally) tally nil))
      (append (if (alistp tally) tally nil) (list (cons label 1))))))
(defun fn2-trace-lockstep (fuel h k a nobs nvisits nactions rh rk ra robs rvisits ractions
                                lists cases certified fn2-core fn2-ref-core)
  (declare (xargs :stobjs (fn2-core fn2-ref-core) :verify-guards nil :measure (nfix fuel)))
  (b* (((when (zp fuel))
        (mv nil cases certified nobs nvisits nactions robs rvisits ractions lists fn2-core fn2-ref-core))
       (rbytes (fn2-exec-turn-bytes fn2-ref-core)) (rsteps (fn2-exec-turn-steps fn2-ref-core))
       (cstop (fn2-concrete-loop-stop-p h k a nobs nvisits nactions fn2-core))
       (rstop (fn2-ref-loop-stop-p rh rk ra robs rvisits ractions rbytes rsteps lists fn2-ref-core))
       ((when (and cstop rstop))
        (mv nil cases certified nobs nvisits nactions robs rvisits ractions lists fn2-core fn2-ref-core))
       (label (fn2-q1-label lists fn2-core))
       ((when (or cstop rstop))
        (mv (list :continue label (if cstop :concrete-stops :reference-stops))
            cases certified nobs nvisits nactions robs rvisits ractions lists fn2-core fn2-ref-core))
       (bytes (fn2-exec-turn-bytes fn2-core)) (steps (fn2-exec-turn-steps fn2-core))
       ((mv & nobs1 nvisits1 nactions1 fn2-core)
        (fn2-concrete-loop 1 h k a nobs nvisits nactions fn2-core))
       ((mv & robs1 rvisits1 ractions1 lists fn2-ref-core)
        (fn2-ref-loop 1 rh rk ra robs rvisits ractions rbytes rsteps lists fn2-ref-core))
       (results (list (- nobs1 nobs) (- nvisits1 nvisits) (- nactions1 nactions)
                      (- (fn2-exec-turn-bytes fn2-core) bytes) (- (fn2-exec-turn-steps fn2-core) steps)))
       (rresults (list (- robs1 robs) (- rvisits1 rvisits) (- ractions1 ractions)
                       (- (fn2-exec-turn-bytes fn2-ref-core) rbytes)
                       (- (fn2-exec-turn-steps fn2-ref-core) rsteps)))
       (difference (or (and (not (equal results rresults)) (list :results results rresults))
                       (fn2-ref-difference fn2-core fn2-ref-core lists)))
       ((when difference)
        (mv (list :g1 label difference)
            cases certified nobs1 nvisits1 nactions1 robs1 rvisits1 ractions1 lists fn2-core fn2-ref-core))
       (certified (if (and (eq (car label) :run)
                           (equal (fn2-core-stop-reason fn2-core) *fn2-stop-reason-none*))
                      (fn2-trace-tally label certified) certified)))
    (fn2-trace-lockstep (- fuel 1) h k a nobs1 nvisits1 nactions1 rh rk ra robs1 rvisits1 ractions1
                        lists (fn2-trace-tally label cases) certified fn2-core fn2-ref-core)))
(in-theory (disable fn2-trace-lockstep))

; The same nine results as fn2-check-trace-turn, with the per-case tallies
; (CASES . CERTIFIED) before the stobjs. A G1 failure is a TRACE failure.
(defun fn2-check-trace-cases-turn (profile cursor queues fn2-core fn2-ref-core)
  (declare (xargs :stobjs (fn2-core fn2-ref-core) :verify-guards nil))
  (b* ((fn2-ref-core (fn2-ref-import-boundary fn2-core fn2-ref-core))
       (lists (fn2-ref-lists (fn2-profile-p profile) cursor queues))
       (before (fn2-ref-difference fn2-core fn2-ref-core lists))
       (h (fn2-exec-h fn2-core)) (k (fn2-exec-k fn2-core)) (a (fn2-exec-aturn fn2-core))
       (rh (fn2-exec-h fn2-ref-core)) (rk (fn2-exec-k fn2-ref-core)) (ra (fn2-exec-aturn fn2-ref-core))
       ; fn2-concrete-turn's and fn2-ref-turn's entries.
       (fn2-core (fn2-exec-set-turn-bytes 0 fn2-core))
       (fn2-core (fn2-exec-set-turn-steps 0 fn2-core))
       (fn2-ref-core (fn2-exec-set-turn-bytes 0 fn2-ref-core))
       (fn2-ref-core (fn2-exec-set-turn-steps 0 fn2-ref-core))
       ((mv failure cases certified obs visits actions robs rvisits ractions lists fn2-core fn2-ref-core)
        (fn2-trace-lockstep (+ h k) h k a 0 0 0 rh rk ra 0 0 0 (update-nth 4 nil lists)
                            nil nil fn2-core fn2-ref-core))
       ; Both loops' exits, with fuel 0: the status, and the reference's
       ; accumulated work written into its core.
       ((mv status obs visits actions fn2-core) (fn2-concrete-loop 0 h k a obs visits actions fn2-core))
       ((mv rs ro rv ra lists fn2-ref-core)
        (fn2-ref-loop 0 rh rk ra robs rvisits ractions (fn2-exec-turn-bytes fn2-ref-core)
                      (fn2-exec-turn-steps fn2-ref-core) lists fn2-ref-core))
       ((mv records lost) (stobj-let ((fn2-trace (fn2-core-trace fn2-core)))
                           (records lost) (mv (fn2-trace-records fn2-trace) (fn2-trace-lost fn2-trace))
                           (mv records lost)))
       (selection (fn2-trace-selection-difference (fn2-trace-selections records) (fn2-ref-selections lists)))
       (difference (if failure (list :q1 failure)
                     (fn2-trace-classify lost selection before
                        (or (fn2-ref-difference fn2-core fn2-ref-core lists)
                            (fn2-trace-field-difference '(:status :observations :visits :actions)
                               (list status obs visits actions) (list rs ro rv ra))))))
       (verdict (if difference (list :fail :trace difference) :pass)))
    (progn$ (if difference (cw "TRACE DIFFERENCE ~x0~%" difference) nil)
            (mv verdict status obs visits actions (nth 1 lists) (nth 2 lists) (cons cases certified)
                fn2-core fn2-ref-core))))
(in-theory (disable fn2-check-trace-cases-turn))

; The checker every Q1 case row names (:checker (:function fn2-q1-check-case
; :case C)): its evidence record from a run's tallies. RUN is
; (:revision R :profile P :domain D :turns N :transitions M :location L).
; A case the run never reached is recorded :unchecked with zero exercised:
; missing evidence is never a pass.
(defun fn2-q1-check-case (case tally run)
  (declare (xargs :verify-guards nil))
  (let ((n (nfix (cdr (assoc-equal case tally)))))
    (list :contract '(:g1 fn2-q1 :per-transition :enabled :results :relation)
          :revision (fn2-decl-get :revision run) :profile (fn2-decl-get :profile run)
          :domain (fn2-decl-get :domain run) :horizon (nfix (fn2-decl-get :turns run)) :unit :turns
          :reached (nfix (fn2-decl-get :transitions run)) :exercised n
          :verdict (if (posp n) :pass :unchecked) :location (fn2-decl-get :location run))))
; The run-time arm certificate's record for a K-P-BOUND row.
(defun fn2-arm-certificate-check (kind tally label run)
  (declare (xargs :verify-guards nil))
  (let ((n (nfix (cdr (assoc-equal label tally)))))
    (list :contract (list :run-time-certificate (fn2-columns-sym kind "-ARM-CHARGE-OK-P"))
          :revision (fn2-decl-get :revision run) :profile (fn2-decl-get :profile run)
          :domain (fn2-decl-get :domain run) :horizon (nfix (fn2-decl-get :turns run)) :unit :turns
          :reached (nfix (fn2-decl-get :transitions run)) :exercised n
          :verdict (if (posp n) :pass :unchecked) :location (fn2-decl-get :location run))))
