; Witnesses and teeth for books/owner-queued-work.lisp (lane owner-offlock,
; 2026-10-03).  The runs are the host's: host/native/owner.lisp
; fnn-owner-run-job starts at fn-oqw-start and calls fn-oqw-step after each
; phase's effect; fnn-owner-commit-pipeline consumes the job's end through
; fn-oqw-receipt on the time-bars ledger it issued the job under.
(in-package "ACL2")
(include-book "../../books/owner-queued-work")

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
