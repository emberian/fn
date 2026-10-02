; Teeth for books/page-read-direct.lisp (lane cold-read-ownership).
; The reached run is GPT-6's native at the logic level: hold a cold read,
; disconnect (the request times out: cancel), retire its file generation
; (close must wait), reuse the worker set and the connection id for a new
; request on the next generation, then deliver the original completion --
; success, error and stale/duplicate variants.
(in-package "ACL2")
(include-book "../../books/page-read-direct")

(defun pirdt-admit (next cid file eoff elen trailer worker)
  (declare (xargs :guard t))
  (mv-list 5 (fn-pio-direct-admit next cid file eoff elen trailer worker)))
(defun pirdt-settle (row worker token verdict)
  (declare (xargs :guard t))
  (mv-list 3 (fn-pio-direct-settle row worker token verdict)))
(defun pirdt-return (w token)
  (declare (xargs :guard t))
  (mv-list 2 (fn-pxe-return w token)))

(assert-event (equal (fn-pio-direct-workers) 4))
(assert-event (and (eq (symbol-class 'fn-pio-direct-admit (w state)) :common-lisp-compliant)
                   (eq (symbol-class 'fn-pio-direct-settle (w state)) :common-lisp-compliant)
                   (eq (symbol-class 'fn-pxe-commit-direct (w state)) :common-lisp-compliant)))

; The run.  Request A (cid 7) on file incarnation 11, worker slot 0.
(defconst *pirdt-w0* (fn-pxe-new 0))
(defconst *pirdt-w1* (fn-pxe-new 1))
(defconst *pirdt-a* (pirdt-admit nil 7 11 4096 64 123 *pirdt-w0*))
(defconst *pirdt-ta* (nth 2 *pirdt-a*))
(defconst *pirdt-rowa* (nth 3 *pirdt-a*))
(defconst *pirdt-wa* (nth 4 *pirdt-a*))
; The client disconnects; the deadline passes: publication is revoked.
(defconst *pirdt-rowa-cancelled* (fn-pio-cancel *pirdt-rowa* *pirdt-ta*))
; Request B reuses cid 7, on the NEXT generation (file 12), on slot 1.
(defconst *pirdt-b* (pirdt-admit (nth 1 *pirdt-a*) 7 12 4096 64 456 *pirdt-w1*))
(defconst *pirdt-tb* (nth 2 *pirdt-b*))
(defconst *pirdt-rowb* (nth 3 *pirdt-b*))
; The original worker actually returns.
(defconst *pirdt-wa-returned* (nth 1 (pirdt-return *pirdt-wa* *pirdt-ta*)))

(assert-event (and (equal (nth 0 *pirdt-a*) :admitted) (equal (nth 1 *pirdt-a*) 1)
                   (equal *pirdt-ta* '(0 7 11 4096 64 123))
                   (equal (nth 0 *pirdt-b*) :admitted) (equal (nth 1 *pirdt-b*) 2)
                   (equal *pirdt-tb* '(1 7 12 4096 64 456))
                   (equal (nth 2 *pirdt-wa-returned*) :returned)))

; Retirement of generation 11 while A is held: close must wait, with or
; without the timeout, and B's row on 12 does not hold 11.
(assert-event
 (and (not (fn-pio-file-clear-p 11 (list *pirdt-rowb* *pirdt-rowa-cancelled*)))
      (not (fn-pio-file-clear-p 11 (list *pirdt-rowb* *pirdt-rowa*)))
      (fn-pio-file-clear-p 11 (list *pirdt-rowb*))))

;;; KEYSTONE fn-pio-direct-admit-binds-an-idle-worker-to-the-issued-identity.
; REACHABLE POSITIVE: request A's admission, complete antecedent/conclusion.
(assert-event
 (let ((next nil) (cid 7) (file 11) (eoff 4096) (elen 64) (trailer 123) (worker *pirdt-w0*))
   (let ((r (pirdt-admit next cid file eoff elen trailer worker)) (n 0))
     (and (equal (nth 0 r) :admitted)
          (fn-pxe-rowp worker) (equal (nth 2 worker) :idle)
          (equal (nth 2 r) (list n cid file eoff elen trailer))
          (fn-pio-rowp (nth 3 r)) (equal (fn-pio-token (nth 3 r)) (nth 2 r))
          (equal (nth 6 (nth 3 r)) :issued)
          (equal (nth 0 (nth 4 r)) (nth 0 worker))
          (equal (nth 2 (nth 4 r)) :running) (equal (nth 3 (nth 4 r)) (nth 2 r))
          (equal (nth 1 r) (+ 1 n))))))
; HYPOTHESIS-REMOVAL: the worker A occupies is offered again (busy): not
; admitted, and the conclusion fails (it is not idle, no row).
(assert-event
 (let ((r (pirdt-admit 1 8 11 0 64 123 *pirdt-wa*)))
   (and (not (equal (nth 0 r) :admitted))
        (equal (nth 0 r) :worker-busy)
        (not (equal (nth 2 *pirdt-wa*) :idle))
        (not (fn-pio-rowp (nth 3 r))))))
; Every worker busy (the host offers none): refused by name.  The companion
; theorem fn-pio-direct-admit-without-an-idle-worker-is-refused: counter,
; token, row and worker unchanged.
(assert-event
 (let ((r (pirdt-admit 2 9 11 0 64 123 nil)))
   (and (equal (nth 0 r) :read-resources-unavailable)
        (equal (nth 1 r) 2) (null (nth 2 r)) (null (nth 3 r)) (null (nth 4 r)))))
; An old job never re-enters a worker that ran a later one (fresh ids).
(assert-event
 (let* ((idle (list 0 5 :idle nil))
        (r (pirdt-admit 3 7 11 0 64 123 idle)))
   (and (equal (nth 0 r) :stale-job) (equal (nth 1 r) 3) (equal (nth 4 r) idle))))
; Not a file incarnation (0): refused, nothing issued.
(assert-event (equal (nth 0 (pirdt-admit nil 7 0 0 64 123 *pirdt-w0*)) :invalid-read-identity))

;;; KEYSTONE fn-pio-direct-settle-publishes-only-the-issued-identity.
; REACHABLE POSITIVE (success variant): A delivered before any timeout.
(assert-event
 (let* ((row *pirdt-rowa*) (worker *pirdt-wa-returned*) (token *pirdt-ta*) (verdict :ok)
        (r (pirdt-settle row worker token verdict)))
   (and (equal (nth 0 r) :publish)
        (fn-pio-rowp row) (equal token (fn-pio-token row))
        (equal (nth 6 row) :issued) (equal verdict :ok)
        (fn-pxe-rowp worker) (equal (nth 2 worker) :returned)
        (equal (nth 3 worker) token)
        (equal (fn-pio-token (nth 1 r)) token) (equal (nth 6 (nth 1 r)) :settled)
        (equal (nth 0 (nth 2 r)) (nth 0 worker)) (equal (nth 2 (nth 2 r)) :idle))))
; HYPOTHESIS-REMOVAL: the timed-out request (cancelled row): no publication,
; and the conclusion fails (the row was not :issued).
(assert-event
 (let ((r (pirdt-settle *pirdt-rowa-cancelled* *pirdt-wa-returned* *pirdt-ta* :ok)))
   (and (not (equal (nth 0 r) :publish))
        (not (equal (nth 6 *pirdt-rowa-cancelled*) :issued)))))

;;; KEYSTONE fn-pio-direct-settle-observes-every-outcome.
; REACHABLE POSITIVES, one per outcome, each the full conclusion.
(defun pirdt-observed-p (row worker token verdict)
  (declare (xargs :verify-guards nil))
  (let ((r (pirdt-settle row worker token verdict)))
    (and (not (equal (nth 0 r) :stale))
         (equal (nth 0 r)
                (cond ((not (equal verdict :ok)) (list :fault verdict))
                      ((equal (nth 6 row) :cancelled) :cancelled)
                      (t :publish)))
         (equal (fn-pio-token (nth 1 r)) token) (equal (nth 6 (nth 1 r)) :settled)
         (fn-pio-file-clear-p (nth 2 token) (list (nth 1 r)))
         (equal (nth 2 (nth 2 r)) :idle))))
; late success after the timeout: :cancelled, no insert, file 11 released
(assert-event
 (and (pirdt-observed-p *pirdt-rowa-cancelled* *pirdt-wa-returned* *pirdt-ta* :ok)
      (equal (nth 0 (pirdt-settle *pirdt-rowa-cancelled* *pirdt-wa-returned* *pirdt-ta* :ok))
             :cancelled)
      (fn-pio-file-clear-p
       11 (list *pirdt-rowb*
                (nth 1 (pirdt-settle *pirdt-rowa-cancelled* *pirdt-wa-returned* *pirdt-ta* :ok))))))
; late error after the timeout: a fault, not a timeout
(assert-event
 (and (pirdt-observed-p *pirdt-rowa-cancelled* *pirdt-wa-returned* *pirdt-ta* :read)
      (equal (nth 0 (pirdt-settle *pirdt-rowa-cancelled* *pirdt-wa-returned* *pirdt-ta* :read))
             '(:fault :read))))
; error and digest before any timeout
(assert-event
 (and (pirdt-observed-p *pirdt-rowa* *pirdt-wa-returned* *pirdt-ta* :error)
      (pirdt-observed-p *pirdt-rowa* *pirdt-wa-returned* *pirdt-ta* :digest)
      (pirdt-observed-p *pirdt-rowa* *pirdt-wa-returned* *pirdt-ta* :ok)))
; HYPOTHESIS-REMOVAL: a stale settlement (the worker never returned) is not
; observed: the conclusion fails (row not settled, worker not idle).
(assert-event
 (let ((r (pirdt-settle *pirdt-rowa-cancelled* *pirdt-wa* *pirdt-ta* :read)))
   (and (equal (nth 0 r) :stale)
        (not (equal (nth 6 (nth 1 r)) :settled))
        (not (equal (nth 2 (nth 2 r)) :idle))
        (not (fn-pio-file-clear-p 11 (list (nth 1 r)))))))

;;; KEYSTONE fn-pio-direct-settle-stale-changes-nothing.
; REACHABLE POSITIVES, one per disjunct of the hypothesis:
(defun pirdt-unchanged-p (row worker token verdict)
  (declare (xargs :guard t))
  (equal (pirdt-settle row worker token verdict) (list :stale row worker)))
; a foreign token: A's completion delivered to B's row (a reused cid on the
; next generation)
(assert-event (and (not (equal *pirdt-ta* (fn-pio-token *pirdt-rowb*)))
                   (pirdt-unchanged-p *pirdt-rowb* *pirdt-wa-returned* *pirdt-ta* :ok)))
; an already settled row
(assert-event
 (let ((settled (nth 1 (pirdt-settle *pirdt-rowa* *pirdt-wa-returned* *pirdt-ta* :ok))))
   (and (equal (nth 6 settled) :settled)
        (pirdt-unchanged-p settled *pirdt-wa-returned* *pirdt-ta* :ok))))
; the worker has not returned (a timeout is not evidence the worker stopped)
(assert-event (and (equal (nth 2 *pirdt-wa*) :running)
                   (pirdt-unchanged-p *pirdt-rowa-cancelled* *pirdt-wa* *pirdt-ta* :ok)))
; the worker returned another job
(assert-event
 (let ((other (list 0 1 :returned *pirdt-tb*)))
   (and (not (equal (nth 3 other) *pirdt-ta*))
        (pirdt-unchanged-p *pirdt-rowa* other *pirdt-ta* :ok))))
; CORRUPTED-STATE: not a row; not a worker row
(assert-event (pirdt-unchanged-p '(0 7 11) *pirdt-wa-returned* *pirdt-ta* :ok))
(assert-event (pirdt-unchanged-p *pirdt-rowa* '(0 0 :returned) *pirdt-ta* :ok))
; HYPOTHESIS-REMOVAL: every disjunct false (A's own returned job): the
; settlement is not stale, so the conclusion fails.
(assert-event
 (and (fn-pio-rowp *pirdt-rowa*) (equal *pirdt-ta* (fn-pio-token *pirdt-rowa*))
      (not (equal (nth 6 *pirdt-rowa*) :settled))
      (fn-pxe-rowp *pirdt-wa-returned*) (equal (nth 2 *pirdt-wa-returned*) :returned)
      (equal (nth 3 *pirdt-wa-returned*) *pirdt-ta*)
      (not (pirdt-unchanged-p *pirdt-rowa* *pirdt-wa-returned* *pirdt-ta* :ok))))

;;; KEYSTONE fn-pio-direct-settle-happens-once.
; REACHABLE POSITIVE: the duplicate delivery after each first outcome.
(defun pirdt-once-p (row worker token verdict verdict2)
  (declare (xargs :guard t))
  (let ((r (pirdt-settle row worker token verdict)))
    (and (not (equal (nth 0 r) :stale))
         (equal (pirdt-settle (nth 1 r) (nth 2 r) token verdict2)
                (list :stale (nth 1 r) (nth 2 r))))))
(assert-event
 (and (pirdt-once-p *pirdt-rowa* *pirdt-wa-returned* *pirdt-ta* :ok :ok)
      (pirdt-once-p *pirdt-rowa-cancelled* *pirdt-wa-returned* *pirdt-ta* :ok :ok)
      (pirdt-once-p *pirdt-rowa-cancelled* *pirdt-wa-returned* *pirdt-ta* :read :ok)
      (pirdt-once-p *pirdt-rowa* *pirdt-wa-returned* *pirdt-ta* :ok :error)))
; HYPOTHESIS-REMOVAL: from a stale first delivery (worker still running) the
; worker's actual return makes the second delivery NOT stale: the
; conclusion's shape fails there.
(assert-event
 (let ((r (pirdt-settle *pirdt-rowa-cancelled* *pirdt-wa* *pirdt-ta* :ok)))
   (and (equal (nth 0 r) :stale)
        (not (equal (nth 0 (pirdt-settle (nth 1 r) *pirdt-wa-returned* *pirdt-ta* :ok)) :stale)))))

;;; KEYSTONE fn-pio-direct-cancelled-read-still-pins-its-file.
; REACHABLE POSITIVE: A, with B's row beside it.
(assert-event
 (let ((r *pirdt-a*) (file 11) (rows (list *pirdt-rowb*)))
   (and (equal (nth 0 r) :admitted)
        (not (fn-pio-file-clear-p file (cons (nth 3 r) rows)))
        (not (fn-pio-file-clear-p file (cons (fn-pio-cancel (nth 3 r) (nth 2 r)) rows))))))
; HYPOTHESIS-REMOVAL: a refused admission pins nothing (no row): the
; conclusion fails.
(assert-event
 (let ((r (pirdt-admit 2 9 11 0 64 123 nil)) (file 11) (rows (list *pirdt-rowb*)))
   (and (not (equal (nth 0 r) :admitted))
        (fn-pio-file-clear-p file (cons (nth 3 r) rows)))))
