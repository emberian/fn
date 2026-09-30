; PRF-1057 teeth. Reached issued row; cancellation, new request, late
; completion, duplicate, error and stale identity, plus close's hypotheses.
(in-package "ACL2")
(include-book "../../books/page-read-ownership")

(defun piot-issue (next cid file eoff elen trailer)
  (declare (xargs :guard (and (natp next) (natp cid) (natp file)
                              (natp eoff) (natp elen) (natp trailer))))
  (mv-list 2 (fn-pio-issue next cid file eoff elen trailer)))
(defun piot-complete (r token verdict)
  (declare (xargs :guard t))
  (mv-list 2 (fn-pio-complete r token verdict)))

(defconst *piot-row* (nth 1 (piot-issue 0 7 11 4096 64 123)))
(defconst *piot-token* (fn-pio-token *piot-row*))
(defconst *piot-cancelled* (fn-pio-cancel *piot-row* *piot-token*))
(defconst *piot-new* (nth 1 (piot-issue 1 7 12 4096 64 456)))
(defconst *piot-settled* (nth 0 (piot-complete *piot-row* *piot-token* :ok)))

; KEYSTONE fn-pio-completion-publishes-only-the-issued-identity.
; REACHABLE POSITIVE: full antecedent and conclusion of literal theorem.
(assert-event
 (let ((r *piot-row*) (token *piot-token*) (verdict :ok))
   (and (equal (nth 1 (piot-complete r token verdict)) :publish)
        (fn-pio-rowp r) (equal token (fn-pio-token r))
        (eq (nth 6 r) :issued) (eq verdict :ok)
        (equal (fn-pio-token (nth 0 (piot-complete r token verdict))) token)
        (eq (nth 6 (nth 0 (piot-complete r token verdict))) :settled))))

; HYPOTHESIS-REMOVAL of publication antecedent: valid cancelled read,
; no publication and failure of the complete conclusion.
(assert-event
 (let ((r *piot-cancelled*) (token *piot-token*) (verdict :ok))
   (and (not (equal (nth 1 (piot-complete r token verdict)) :publish))
        (not (and (fn-pio-rowp r) (equal token (fn-pio-token r))
                  (eq (nth 6 r) :issued) (eq verdict :ok)
                  (equal (fn-pio-token (nth 0 (piot-complete r token verdict))) token)
                  (eq (nth 6 (nth 0 (piot-complete r token verdict))) :settled))))))

; KEYSTONE fn-pio-cancellation-retains-worker-ownership.
; REACHABLE POSITIVE: every retained hypothesis, complete conclusion.
(assert-event
 (and (not (eq (nth 6 *piot-row*) :settled))
      (equal (fn-pio-token *piot-cancelled*) *piot-token*)
      (not (eq (nth 6 *piot-cancelled*) :settled))))
; HYPOTHESIS-REMOVAL: settled is not resurrected by cancellation.
(assert-event
 (and (fn-pio-rowp *piot-settled*) (eq (nth 6 *piot-settled*) :settled)
      (eq (nth 6 (fn-pio-cancel *piot-settled* *piot-token*)) :settled)))

; KEYSTONE fn-pio-close-waits-for-every-worker.
; REACHABLE POSITIVE: close waits for a cancelled worker, even when CID 7
; is reused by request 1.
(assert-event
 (let ((r *piot-cancelled*) (file 11) (rows (list *piot-new* *piot-cancelled*)))
   (and (member-equal r rows) (fn-pio-rowp r) (equal (nth 2 r) file)
        (not (eq (nth 6 r) :settled)) (not (fn-pio-file-clear-p file rows)))))
; HYPOTHESIS-REMOVALS: membership, rowp (CORRUPTED-STATE), file, unsettled.
(assert-event
 (let ((r *piot-cancelled*) (file 11) (rows (list *piot-new*)))
   (and (not (member-equal r rows)) (fn-pio-rowp r) (equal (nth 2 r) file)
        (not (eq (nth 6 r) :settled)) (fn-pio-file-clear-p file rows))))
(assert-event
 (let* ((r '(0 7 11 4096 64 123 :bogus)) (file 11) (rows (list r)))
   (and (member-equal r rows) (not (fn-pio-rowp r)) (equal (nth 2 r) file)
        (not (eq (nth 6 r) :settled)) (fn-pio-file-clear-p file rows))))
(assert-event
 (let ((r *piot-cancelled*) (file 12) (rows (list *piot-cancelled*)))
   (and (member-equal r rows) (fn-pio-rowp r) (not (equal (nth 2 r) file))
        (not (eq (nth 6 r) :settled)) (fn-pio-file-clear-p file rows))))
(assert-event
 (let ((r *piot-settled*) (file 11) (rows (list *piot-settled*)))
   (and (member-equal r rows) (fn-pio-rowp r) (equal (nth 2 r) file)
        (eq (nth 6 r) :settled) (fn-pio-file-clear-p file rows))))

; Error settles with a named fault; cancelled success settles without cache
; publication; duplicate/stale neither release nor publish a second time.
(assert-event
 (and (equal (nth 1 (piot-complete *piot-row* *piot-token* :read)) '(:fault :read))
      (eq (nth 6 (nth 0 (piot-complete *piot-row* *piot-token* :read))) :settled)
      (equal (nth 1 (piot-complete *piot-cancelled* *piot-token* :ok)) :cancelled)
      (equal (nth 1 (piot-complete *piot-settled* *piot-token* :ok)) :stale)
      (equal (nth 0 (piot-complete *piot-settled* *piot-token* :ok)) *piot-settled*)
      (equal (nth 1 (piot-complete *piot-new* *piot-token* :ok)) :stale)
      (equal (nth 0 (piot-complete *piot-new* *piot-token* :ok)) *piot-new*)))

; Mutation: treating cancellation as settlement makes close incorrectly
; possible before the original worker completed.
(assert-event
 (let ((bad (append *piot-token* '(:settled))))
   (and (not (fn-pio-file-clear-p 11 (list *piot-cancelled*)))
        (fn-pio-file-clear-p 11 (list bad)))))

; The reaper's constant work quantum is independent of stored-data size.
(assert-event (equal (fn-pio-reap-work) 1))
(assert-event (and (equal (fn-pio-worker-death-step t) :settle)
                   (equal (fn-pio-worker-death-step nil) :rotate)))

(defun piot-file-issue (next) (mv-list 3 (fn-pio-file-issue next)))
(assert-event (and (equal (piot-file-issue nil) '(:issued 2 1))
                   (equal (piot-file-issue 2) '(:issued 3 2))
                   (equal (piot-file-issue 0) '(:invalid-file-identity 0 nil))
                   (equal (piot-file-issue :bad) '(:invalid-file-identity :bad nil))))

; KEYSTONE fn-pio-successive-file-issues-have-distinct-identities.
; Literal positive: include initial namespace and another carried allocator.
(assert-event
 (and (let* ((first (piot-file-issue nil)) (second (piot-file-issue (cadr first))))
        (and (eq (car first) :issued) (eq (car second) :issued)
             (posp (caddr first)) (posp (caddr second)) (< (caddr first) (caddr second))))
      (let* ((first (piot-file-issue 9)) (second (piot-file-issue (cadr first))))
        (and (eq (car first) :issued) (eq (car second) :issued)
             (posp (caddr first)) (posp (caddr second)) (< (caddr first) (caddr second))))))
; Hypothesis-removal, corrupted carried counter: omitted :issued is false;
; no other hypothesis remains, and the literal conclusion is false.
(assert-event
 (let* ((first (piot-file-issue 0)) (second (piot-file-issue (cadr first))))
   (and (not (eq (car first) :issued))
        (not (and (eq (car second) :issued)
                  (posp (caddr first)) (posp (caddr second))
                  (< (caddr first) (caddr second)))))))

; Resource-admission composition, literal positive/removal teeth.
(defun piot-prl-admit (ledger)
  (declare (xargs :guard t))
  (mv-list 3 (fn-prl-admit ledger 7 11 4096 64 123 '(400 0 0 1 1) '(100 0 0 1 0))))
(defconst *piot-funded-ledger*
  (mv-nth 1 (mv-list 2 (fn-prl-register (fn-prl-make '(10000 0 4 4 20)) 11 '(20 0 1 0 0)))))
; KEYSTONE fn-pio-admitted-resource-token-establishes-owned-read.
; REACHABLE POSITIVE: installed pool, reserved incarnation, whole conclusion.
(assert-event
 (let* ((ledger *piot-funded-ledger*) (answer (piot-prl-admit ledger))
        (token (nth 1 answer)) (row (fn-pio-own-admitted-token token)))
   (and (equal (nth 0 answer) :admitted)
        (fn-pio-rowp row) (equal (fn-pio-token row) token)
        (equal (nth 6 row) :issued) (equal (nth 0 row) (fn-prl-nth 2 ledger))
        (< (nth 0 row) (fn-prl-nth 2 (nth 2 answer))))))
; HYPOTHESIS-REMOVAL: no incarnation reservation -> refusal, no owned row.
(assert-event
 (let* ((ledger (fn-prl-make '(10000 0 4 4 20))) (answer (piot-prl-admit ledger))
        (token (nth 1 answer)) (row (fn-pio-own-admitted-token token)))
   (and (not (equal (nth 0 answer) :admitted))
        (not (and (fn-pio-rowp row) (equal (fn-pio-token row) token)
                  (equal (nth 6 row) :issued) (equal (nth 0 row) (fn-prl-nth 2 ledger))
                  (< (nth 0 row) (fn-prl-nth 2 (nth 2 answer))))))))
(defun piot-bounded-file-issue (next limit)
  (declare (xargs :guard t))
  (mv-list 3 (fn-pio-file-issue-with-limit next limit)))
; KEYSTONE fn-pio-bounded-file-issue-spends-a-fresh-representable-name.
; REACHABLE POSITIVE at initial and last admissible name.
(assert-event
 (and (let ((answer (piot-bounded-file-issue nil 2)))
        (and (equal (nth 0 answer) :issued) (posp (nth 2 answer))
             (<= (nth 2 answer) 2) (equal (nth 1 answer) (+ 1 (nth 2 answer)))))
      (let ((answer (piot-bounded-file-issue 2 2)))
        (and (equal (nth 0 answer) :issued) (posp (nth 2 answer))
             (<= (nth 2 answer) 2) (equal (nth 1 answer) (+ 1 (nth 2 answer)))))))
; HYPOTHESIS-REMOVAL: exhausted names cannot establish the whole conclusion.
(assert-event
 (let ((answer (piot-bounded-file-issue 3 2)))
   (and (not (equal (nth 0 answer) :issued))
        (equal answer '(:file-identities-exhausted 3 nil))
        (not (and (posp (nth 2 answer)) (<= (nth 2 answer) 2)
                  (equal (nth 1 answer) (+ 1 (nth 2 answer))))))))
; Corrupted counters and invalid profiles do not reset/reuse a name.
(assert-event
 (and (equal (piot-bounded-file-issue 0 2) '(:invalid-file-identity 0 nil))
      (equal (piot-bounded-file-issue nil 0) '(:invalid-file-identity nil nil))))
