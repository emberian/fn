; Witnesses and teeth for books/owner-queued-work.lisp (lane owner-offlock,
; 2026-10-03).  The runs are the host's: host/native/owner.lisp
; fnn-owner-run-job starts at fn-oqw-start and calls fn-oqw-step after each
; phase's effect; fnn-owner-commit-pipeline consumes the job's end through
; fn-oqw-receipt on the time-bars ledger it issued the job under.
(in-package "ACL2")
(include-book "../../books/owner-queued-work")
(include-book "../../books/defkeystone")

; --- The batch job, every effect returned: five phases in order, :done.
(assert-event (equal (fn-oqw-start :batch) :intents))
(assert-event (equal (fn-oqw-trace :batch :intents '(:ok :ok :ok :ok :ok))
                     '(:intents :extend :append :fence :resolutions)))
(assert-event (equal (fn-oqw-final :batch :intents '(:ok :ok :ok :ok :ok)) :done))
; An intent frame uncertain: nothing after it runs (no append), :uncertain.
(assert-event (equal (fn-oqw-trace :batch :intents '(:uncertain :ok :ok)) '(:intents)))
(assert-event (equal (fn-oqw-final :batch :intents '(:uncertain :ok :ok)) :uncertain))
; A barrier fault: no resolution frame, :fault.
(assert-event (equal (fn-oqw-trace :batch :intents '(:ok :ok :ok :fault :ok))
                     '(:intents :extend :append :fence)))
(assert-event (equal (fn-oqw-final :batch :intents '(:ok :ok :ok :fault :ok)) :fault))
; A :frames job (a START that kept no member): its one phase, then :done.
(assert-event (equal (fn-oqw-trace :frames (fn-oqw-start :frames) '(:ok)) '(:intents)))
(assert-event (equal (fn-oqw-final :frames (fn-oqw-start :frames) '(:ok)) :done))
(assert-event (equal (fn-oqw-final :frames (fn-oqw-start :frames) '(:uncertain)) :uncertain))
; An unknown kind faults at its start; an unknown phase faults at its step.
(assert-event (equal (fn-oqw-start :nothing) :fault))
(assert-event (equal (fn-oqw-step :batch :elsewhere :ok) :fault))
; A terminal never moves.
(assert-event (equal (fn-oqw-step :batch :uncertain :ok) :uncertain))

; --- KEYSTONE fn-oqw-batch-effect-order, by conjunct.
(defun oqwt-k1 (words)
  (let ((trace (fn-oqw-trace :batch (fn-oqw-start :batch) words)))
    (list (member-equal :append trace)
          (and (equal (first words) :ok) (equal (second words) :ok))
          (member-equal :fence trace)
          (equal (third words) :ok)
          (member-equal :resolutions trace)
          (and (equal (first words) :ok) (equal (second words) :ok)
               (equal (third words) :ok) (equal (fourth words) :ok))
          (equal (fn-oqw-final :batch (fn-oqw-start :batch) words) :done)
          (and (fn-oqw-all-ok (take 5 words)) (<= 5 (len words)))
          (equal trace (fn-oqw-phases :batch)))))
; Positive: every antecedent holds and every conclusion.
(assert-event (equal (oqwt-k1 '(:ok :ok :ok :ok :ok))
                     (list '(:append :fence :resolutions) t '(:fence :resolutions) t
                           '(:resolutions) t t t t)))
; Removal of each antecedent: when the phase did not run, its conclusion
; need not hold (the extension failed: no append, and the first two words
; are not both :ok; the append failed: no fence, the third word is not
; :ok; the fence failed: no resolution, the fourth is not :ok; one effect
; short of five: not :done).
(assert-event (equal (oqwt-k1 '(:ok :uncertain))
                     (list nil nil nil nil nil nil nil nil nil)))
(assert-event (equal (oqwt-k1 '(:ok :ok :fault))
                     (list '(:append) t nil nil nil nil nil nil nil)))
(assert-event (equal (oqwt-k1 '(:ok :ok :ok :uncertain))
                     (list '(:append :fence) t '(:fence) t nil nil nil nil nil)))
(assert-event (equal (oqwt-k1 '(:ok :ok :ok :ok))
                     (list '(:append :fence) t '(:fence) t nil t nil nil nil)))
; MUTATION (labelled): a phase table with the append before the intents
; breaks the order -- the append runs with the intents' word not yet seen.
(defun oqwt-mutant-after (phase)
  (fn-oqw-after phase '(:append :intents :extend :fence :resolutions)))
(assert-event (equal (oqwt-mutant-after :append) :intents))

; --- fn-oqw-a-failed-effect-ends-the-job: positive (an uncertain fence
; and a faulted append, then a later :ok does not move them); removal of
; "not :ok" (an :ok continues to the next phase); removal of "not
; terminal" (a terminal answers itself, not :fault).
(assert-event (equal (fn-oqw-step :batch :fence :uncertain) :uncertain))
(assert-event (equal (fn-oqw-step :batch :uncertain :ok) :uncertain))
(assert-event (equal (fn-oqw-step :batch :append :eio) :fault))
(assert-event (equal (fn-oqw-step :batch :fault :ok) :fault))
(assert-event (equal (fn-oqw-step :batch :fence :ok) :resolutions))
(assert-event (equal (fn-oqw-step :batch :done :eio) :done))

; --- The receipt, reached: the ledger issued generation 1 for the job.
(defconst *oqwt-l* (caddr (fn-otb-issue (fn-otb-ledger-init))))
(assert-event (equal (fn-oqw-receipt *oqwt-l* 1 :done '(7 8)) (list :fenced '(7 8) '(1 nil nil))))
(assert-event (equal (car (fn-oqw-receipt *oqwt-l* 1 :uncertain '(7))) :failed))
(assert-event (equal (car (fn-oqw-receipt *oqwt-l* 1 :fault '(7))) :fault))
; A receipt naming an unfinished job (it ended in a phase) is a fault.
(assert-event (equal (car (fn-oqw-receipt *oqwt-l* 1 :fence '(7))) :fault))
; Stale and consumed answer no one and change nothing.
(assert-event (equal (fn-oqw-receipt *oqwt-l* 2 :done '(7)) (list :stale nil *oqwt-l*)))
(defconst *oqwt-done* (caddr (fn-oqw-receipt *oqwt-l* 1 :done '(7))))
(assert-event (equal (fn-oqw-receipt *oqwt-done* 1 :done '(7)) (list :consumed nil *oqwt-done*)))
; A late receipt after a stall's early answer: :fenced, but answers only
; the members not already told (7 told early; 8 answered now).
(defconst *oqwt-told* (cadr (fn-otb-answer-early *oqwt-l* '(7))))
(assert-event (equal (fn-oqw-receipt *oqwt-told* 1 :done '(7 8)) (list :fenced '(8) '(1 nil nil))))

; --- KEYSTONE fn-oqw-receipt-outcomes-are-distinct, by its hypotheses:
; :fenced needs open, the generation and :done -- remove each in turn and
; the outcome is not :fenced.
(assert-event (and (fn-otb-open *oqwt-l*) (equal 1 (fn-otb-gen *oqwt-l*))))
(assert-event (not (fn-otb-open *oqwt-done*)))
(assert-event (equal (car (fn-oqw-receipt *oqwt-done* 1 :done nil)) :consumed))
(assert-event (equal (car (fn-oqw-receipt *oqwt-l* 3 :done nil)) :stale))
(assert-event (equal (car (fn-oqw-receipt *oqwt-l* 1 :uncertain nil)) :failed))

; TEETH-62 BEGIN
; The three PRF owner-queued-work keystones with their teeth (TEETH CONTRACT v1).  The batch and receipt keystones state no antecedent outside their `let'; the receipt removals are mutations that drop one antecedent of an `iff' conjunct.
(defteeth fn-oqw-a-failed-effect-ends-the-job
  :claim (((not-terminal (not (fn-oqw-terminalp phase))) (not-ok (not (equal word :ok))))
          (and (equal (fn-oqw-step kind phase word)
                       (if (equal word :uncertain) :uncertain :fault))
                (fn-oqw-terminalp (fn-oqw-step kind phase word))
                (equal (fn-oqw-step kind (fn-oqw-step kind phase word) word2)
                       (fn-oqw-step kind phase word))))
  :subject fn-oqw-step
  :witness ((kind :batch) (phase :fence) (word :uncertain) (word2 :ok))
  :breaks ((not-terminal ((kind :batch) (phase :done) (word :eio) (word2 :ok)))
           (not-ok ((kind :batch) (phase :fence) (word :ok) (word2 :ok))))
  :mutations ((uncertain-as-fault
               (:conclusion (equal (fn-oqw-step kind phase word) :fault))
               ((kind :batch) (phase :fence) (word :uncertain) (word2 :ok))
               :fault "an uncertain effect collapsed to a fault")))

(defteeth fn-oqw-batch-effect-order
  :claim (() (let ((trace (fn-oqw-trace :batch (fn-oqw-start :batch) words))) (and (implies (member-equal :append trace)
                  (and (equal (first words) :ok)
                       (equal (second words) :ok)))
         (implies (member-equal :fence trace)
                  (equal (third words) :ok))
         (implies (member-equal :resolutions trace)
                  (and (equal (first words) :ok) (equal (second words) :ok)
                       (equal (third words) :ok) (equal (fourth words) :ok)))
         (iff (equal (fn-oqw-final :batch (fn-oqw-start :batch) words) :done)
              (and (fn-oqw-all-ok (take 5 words)) (<= 5 (len words))))
         (implies (equal (fn-oqw-final :batch (fn-oqw-start :batch) words) :done)
                  (equal trace (fn-oqw-phases :batch))))))
  :subject fn-oqw-final
  :witness ((words '(:ok :ok :ok :ok :ok)))
  :mutations ((fifth-effect-ignored
               (:conclusion (iff (equal (fn-oqw-final :batch (fn-oqw-start :batch) words) :done) (fn-oqw-all-ok (take 4 words))))
               ((words '(:ok :ok :ok :ok :uncertain)))
               :fault "the fifth effect left out of the success test")
              (failed-job-ran-every-phase
               (:conclusion (let ((trace (fn-oqw-trace :batch (fn-oqw-start :batch) words))) (equal trace (fn-oqw-phases :batch))))
               ((words '(:ok :ok :fault)))
               :fault "a job whose append failed claimed to have run every phase")))

(defteeth fn-oqw-receipt-outcomes-are-distinct
  :claim (() (let* ((r (fn-oqw-receipt l gen final cids))
         (outcome (car r))) (and (member-equal outcome '(:fenced :failed :fault :stale :consumed))
         (iff (equal outcome :fenced)
              (and (fn-otb-open l) (equal (nfix gen) (fn-otb-gen l))
                   (equal final :done)))
         (iff (equal outcome :failed)
              (and (fn-otb-open l) (equal (nfix gen) (fn-otb-gen l))
                   (equal final :uncertain)))
         (iff (equal outcome :fault)
              (and (fn-otb-open l) (equal (nfix gen) (fn-otb-gen l))
                   (not (equal final :done)) (not (equal final :uncertain))))
         (iff (equal outcome :stale) (not (equal (nfix gen) (fn-otb-gen l))))
         (implies (member-equal outcome '(:stale :consumed))
                  (and (null (cadr r)) (equal (caddr r) l)))
         (implies (member-equal outcome '(:fenced :failed :fault))
                  (and (equal (cdr r) (cdr (fn-otb-complete l gen cids)))
                       (not (fn-otb-open (caddr r))))))))
  :subject fn-oqw-receipt
  :witness ((l *oqwt-l*) (gen 1) (final :done) (cids '(7)))
  :mutations ((without-open
               (:conclusion (let* ((r (fn-oqw-receipt l gen final cids)) (outcome (car r))) (iff (equal outcome :fenced) (and (equal (nfix gen) (fn-otb-gen l)) (equal final :done)))))
               ((l *oqwt-done*) (gen 1) (final :done) (cids '(7)))
               :fault "a closed ledger counted as fenced: the open antecedent dropped")
              (without-generation
               (:conclusion (let* ((r (fn-oqw-receipt l gen final cids)) (outcome (car r))) (iff (equal outcome :fenced) (and (fn-otb-open l) (equal final :done)))))
               ((l *oqwt-l*) (gen 3) (final :done) (cids '(7)))
               :fault "a generation other than the ledger's counted as fenced")
              (without-done
               (:conclusion (let* ((r (fn-oqw-receipt l gen final cids)) (outcome (car r))) (iff (equal outcome :fenced) (and (fn-otb-open l) (equal (nfix gen) (fn-otb-gen l))))))
               ((l *oqwt-l*) (gen 1) (final :uncertain) (cids '(7)))
               :fault "an uncertain job counted as fenced: the :done antecedent dropped")
              (stale-by-final
               (:conclusion (let* ((r (fn-oqw-receipt l gen final cids)) (outcome (car r))) (iff (equal outcome :stale) (equal final :done))))
               ((l *oqwt-l*) (gen 1) (final :done) (cids '(7)))
               :fault "stale decided by the job's final phase, not the generation")))
