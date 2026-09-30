; PRF-1080 literal teeth for persistent worker job incarnations.
(in-package "ACL2")
(include-book "../../books/page-read-executor")

(defun pxet-assign (w token) (declare (xargs :guard t)) (mv-list 2 (fn-pxe-assign w token)))
(defun pxet-acquire (ledger w token) (declare (xargs :guard t)) (mv-list 3 (fn-pxe-acquire ledger w token)))
(defun pxet-return (w token) (declare (xargs :guard t)) (mv-list 2 (fn-pxe-return w token)))
(defun pxet-commit (w io token ledger cachedp) (declare (xargs :guard t)) (mv-list 3 (fn-pxe-commit w io token ledger cachedp)))
(defun pxet-admit (ledger) (declare (xargs :guard t))
  (mv-list 3 (fn-prl-admit ledger 7 11 4096 64 123 '(400 0 0 1 1) '(0 0 0 1 0))))
(defun pxet-complete (r token) (declare (xargs :guard t)) (mv-list 2 (fn-pio-complete r token :ok)))
(defconst *pxet-reg* (nth 1 (mv-list 2 (fn-prl-register (fn-prl-make '(5000 0 4 2 10)) 11 '(20 0 1 0 0)))))
(defconst *pxet-first* (pxet-admit *pxet-reg*))
(defconst *pxet-token0* (nth 1 *pxet-first*))
(defconst *pxet-second* (pxet-admit (nth 2 *pxet-first*)))
(defconst *pxet-token1* (nth 1 *pxet-second*))
(defconst *pxet-ledger* (nth 2 *pxet-second*))
(defconst *pxet-new* (fn-pxe-new 0))
(defconst *pxet-acquired* (pxet-acquire *pxet-ledger* *pxet-new* *pxet-token0*))
(defconst *pxet-running* (nth 1 *pxet-acquired*))
(defconst *pxet-owned* (nth 2 *pxet-acquired*))
(defconst *pxet-returned* (nth 1 (pxet-return *pxet-running* *pxet-token0*)))
(defconst *pxet-io* (fn-pio-own-admitted-token *pxet-token0*))
(defconst *pxet-settled* (nth 0 (pxet-complete *pxet-io* *pxet-token0*)))
(defconst *pxet-committed* (pxet-commit *pxet-returned* *pxet-settled* *pxet-token0* *pxet-owned* nil))

; KEYSTONE fn-pxe-assignment-requires-idle-and-fresh-job.
; REACHABLE POSITIVE: exact antecedent and whole conclusion.
(assert-event
 (let* ((w *pxet-new*) (token *pxet-token0*) (answer (pxet-assign w token)))
   (and (equal (nth 0 answer) :assigned) (fn-pxe-rowp w) (equal (fn-prl-nth 2 w) :idle)
        (fn-pio-rowp (fn-pio-own-admitted-token token))
        (or (null (fn-prl-nth 1 w)) (< (fn-prl-nth 1 w) (fn-prl-nth 0 token)))
        (equal (fn-prl-nth 0 (nth 1 answer)) (fn-prl-nth 0 w))
        (equal (fn-prl-nth 2 (nth 1 answer)) :running)
        (equal (fn-prl-nth 3 (nth 1 answer)) token))))
; HYPOTHESIS-REMOVAL: busy worker cannot take a fresh next job.
(assert-event
 (let* ((w *pxet-running*) (token *pxet-token1*) (answer (pxet-assign w token)))
   (and (not (equal (nth 0 answer) :assigned))
        (not (and (fn-pxe-rowp w) (equal (fn-prl-nth 2 w) :idle)
                  (fn-pio-rowp (fn-pio-own-admitted-token token))
                  (or (null (fn-prl-nth 1 w)) (< (fn-prl-nth 1 w) (fn-prl-nth 0 token)))
                  (equal (fn-prl-nth 0 (nth 1 answer)) (fn-prl-nth 0 w))
                  (equal (fn-prl-nth 2 (nth 1 answer)) :running)
                  (equal (fn-prl-nth 3 (nth 1 answer)) token))))))

; KEYSTONE fn-pxe-acquired-token-cannot-own-a-second-worker.
; REACHABLE POSITIVE: charged token0 is actually assigned, second unchanged.
(assert-event
 (let* ((ledger *pxet-ledger*) (w *pxet-new*) (token *pxet-token0*) (other (fn-pxe-new 1))
        (first (pxet-acquire ledger w token)))
   (and (equal (nth 0 first) :assigned)
        (equal (pxet-acquire (nth 2 first) other token)
               (list :stale-job other (nth 2 first))))))
; HYPOTHESIS-REMOVAL: first worker busy; untouched token1 can use worker1.
(assert-event
 (let* ((ledger *pxet-owned*) (w *pxet-running*) (token *pxet-token1*) (other (fn-pxe-new 1))
        (first (pxet-acquire ledger w token)))
   (and (not (equal (nth 0 first) :assigned))
        (not (equal (pxet-acquire (nth 2 first) other token)
                    (list :stale-job other (nth 2 first)))))))

; KEYSTONE fn-pxe-commit-requires-returned-settled-exact-job.
; REACHABLE POSITIVE: worker relinquished result, I/O settled, binding exists.
(assert-event
 (let* ((w *pxet-returned*) (io *pxet-settled*) (token *pxet-token0*)
        (ledger *pxet-owned*) (cachedp nil) (answer (pxet-commit w io token ledger cachedp)))
   (and (equal (nth 0 answer) :committed) (fn-pxe-rowp w)
        (equal (fn-prl-nth 2 w) :returned) (equal token (fn-prl-nth 3 w))
        (fn-pio-rowp io) (equal (fn-prl-nth 6 io) :settled) (equal token (fn-pio-token io))
        (equal (nth 0 (mv-list 2 (fn-prl-settle ledger token cachedp))) :settled)
        (equal (fn-prl-nth 2 (nth 1 answer)) :idle)
        (equal (fn-prl-nth 0 (nth 1 answer)) (fn-prl-nth 0 w))
        (equal (nth 2 answer) (nth 1 (mv-list 2 (fn-prl-settle ledger token cachedp)))))))
; HYPOTHESIS-REMOVAL: a still-running worker cannot establish conclusion.
(assert-event
 (let* ((w *pxet-running*) (io *pxet-settled*) (token *pxet-token0*)
        (ledger *pxet-owned*) (answer (pxet-commit w io token ledger nil)))
   (and (not (equal (nth 0 answer) :committed))
        (not (and (fn-pxe-rowp w) (equal (fn-prl-nth 2 w) :returned)
                  (equal token (fn-prl-nth 3 w)) (fn-pio-rowp io)
                  (equal (fn-prl-nth 6 io) :settled) (equal token (fn-pio-token io))
                  (equal (nth 0 (mv-list 2 (fn-prl-settle ledger token nil))) :settled)
                  (equal (fn-prl-nth 2 (nth 1 answer)) :idle)
                  (equal (fn-prl-nth 0 (nth 1 answer)) (fn-prl-nth 0 w))
                  (equal (nth 2 answer) (nth 1 (mv-list 2 (fn-prl-settle ledger token nil)))))))))
; Cancel revokes publication, not physical job ownership or resource charge.
(assert-event
 (let ((cancelled (fn-pio-cancel *pxet-io* *pxet-token0*)))
   (and (equal (fn-prl-nth 6 cancelled) :cancelled)
        (equal (pxet-commit *pxet-returned* cancelled *pxet-token0* *pxet-owned* nil)
               (list :stale-job *pxet-returned* *pxet-owned*))
        (equal (pxet-assign *pxet-returned* *pxet-token1*) (list :worker-busy *pxet-returned*)))))
; Cached buffer persists; the execution slot returns without spent ID reuse.
(assert-event
 (let ((answer (pxet-commit *pxet-returned* *pxet-settled* *pxet-token0* *pxet-owned* t)))
   (and (equal (nth 0 answer) :committed)
        (equal (fn-prl-nth 1 (nth 2 answer)) '(820 0 1 1 2))
        (equal (fn-prl-nth 2 (nth 2 answer)) 2)
        (equal (fn-prl-nth 1 (cdr (fn-prl-binding *pxet-token0* (fn-prl-nth 3 (nth 2 answer))))) :cached)
        (null (fn-prl-nth 3 (cdr (fn-prl-binding *pxet-token0* (fn-prl-nth 3 (nth 2 answer)))))))))

(defconst *pxet-reused* (nth 1 (pxet-acquire (nth 2 *pxet-committed*) (nth 1 *pxet-committed*) *pxet-token1*)))
; KEYSTONE fn-pxe-stale-completion-cannot-return-a-reused-worker.
; REACHABLE POSITIVE: same slot0 reused by next exact token, late old return.
(assert-event
 (let ((w *pxet-reused*) (token *pxet-token0*))
   (and (not (equal token (fn-prl-nth 3 w)))
        (equal (nth 0 (pxet-return w token)) :stale-job)
        (equal (nth 1 (pxet-return w token)) w))))
; HYPOTHESIS-REMOVAL: matching token1 really returns, so full conclusion fails.
(assert-event
 (let ((w *pxet-reused*) (token *pxet-token1*))
   (and (equal token (fn-prl-nth 3 w))
        (not (and (equal (nth 0 (pxet-return w token)) :stale-job)
                  (equal (nth 1 (pxet-return w token)) w))))))
; A spent same token cannot be assigned even after this worker becomes idle.
(assert-event
 (equal (pxet-assign (nth 1 *pxet-committed*) *pxet-token0*)
        (list :stale-job (nth 1 *pxet-committed*))))
; Mutation: refund at cancellation allows an idle worker while old I/O lives.
(assert-event
 (let* ((cancelled (fn-pio-cancel *pxet-io* *pxet-token0*))
        (bad-worker (list 0 0 :idle nil)))
   (and (not (equal (fn-prl-nth 6 cancelled) :settled))
        (equal (nth 0 (pxet-commit *pxet-returned* cancelled *pxet-token0* *pxet-owned* nil)) :stale-job)
        (equal (nth 0 (pxet-assign bad-worker *pxet-token1*)) :assigned))))

; Nonzero permanent storage remains owned across the actual job lifecycle.
(assert-event
 (let* ((baseline '(1000 0 0 0 0))
        (ledger (fn-prl-build (fn-prl-nth 0 *pxet-ledger*)
                              (fn-prl-nth 1 *pxet-ledger*)
                              (fn-prl-nth 2 *pxet-ledger*)
                              (fn-prl-nth 3 *pxet-ledger*) baseline))
        (acquired (pxet-acquire ledger *pxet-new* *pxet-token0*))
        (returned (nth 1 (pxet-return (nth 1 acquired) *pxet-token0*)))
        (committed (pxet-commit returned *pxet-settled* *pxet-token0* (nth 2 acquired) nil)))
   (and (equal (nth 0 acquired) :assigned)
        (equal (fn-prl-nth 4 (nth 2 acquired)) baseline)
        (equal (nth 0 committed) :committed)
        (equal (fn-prl-nth 4 (nth 2 committed)) baseline)
        (equal (fn-prl-nth 1 (nth 2 committed)) '(420 0 1 1 2)))))

(assert-event (and (equal (fn-pxe-cache-mode t) :ready)
                   (equal (fn-pxe-cache-mode nil) :read-resources-unavailable)))
