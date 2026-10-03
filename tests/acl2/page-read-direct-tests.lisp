; Teeth for books/page-read-direct.lisp (lane cold-read-ownership; re-expressed
; through def-holder by lane def-holder, 2026-10-03).
; The reached run is GPT-6's native at the logic level: hold a cold read,
; disconnect (the request times out: cancel), retire its file generation
; (close must wait), reuse the worker set and the connection id for a new
; request on the next generation, then deliver the original completion --
; success, error and stale/duplicate variants -- with the two tables (the
; issued alist and the holds table) threaded as the host threads them, and
; the close's one lookup agreeing with the walk it replaced.
(in-package "ACL2")
(include-book "../../books/page-read-direct")

(defun pirdt-admit (next cid file eoff elen trailer worker issued holds)
  (declare (xargs :guard (fn-hd-identp holds)))
  (mv-list 7 (fn-pio-direct-admit next cid file eoff elen trailer worker issued holds)))
(defun pirdt-settle (token worker verdict issued holds)
  (declare (xargs :guard (fn-hd-identp holds)))
  (mv-list 5 (fn-pio-direct-settle token worker verdict issued holds)))
(defun pirdt-return (w token)
  (declare (xargs :guard t))
  (mv-list 2 (fn-pxe-return w token)))

(assert-event (equal (fn-pio-direct-workers) 4))
(assert-event (and (eq (symbol-class 'fn-pio-direct-admit (w state)) :common-lisp-compliant)
                   (eq (symbol-class 'fn-pio-direct-settle (w state)) :common-lisp-compliant)
                   (eq (symbol-class 'fn-pio-direct-cancel (w state)) :common-lisp-compliant)
                   (eq (symbol-class 'fn-pio-direct-quiet-p (w state)) :common-lisp-compliant)
                   (eq (symbol-class 'fn-pxe-commit-direct (w state)) :common-lisp-compliant)))

; The declaration's generated names and rows, and the world walk.
(assert-event
 (and (getpropc 'fn-pio-file-holds-cold-read-acquire-holds 'theorem nil (w state))
      (getpropc 'fn-pio-file-holds-cold-read-release-drops 'theorem nil (w state))
      (getpropc 'fn-pio-file-holds-cold-read-acquire-keeps 'theorem nil (w state))
      (getpropc 'fn-pio-file-holds-table-run-carries 'theorem nil (w state))
      (equal *fn-pio-file-holds-cuts* '(:fn-pio-file-holds-decided :fn-pio-file-holds-released))
      (assoc-eq 'fn-pio-file-holds-cold-read-acquire-holds (table-alist 'fn-teeth-owed (w state)))))
(def-holder-check fn-pio-file-holds)

; The run.  Request A (cid 7) on file incarnation 11, worker slot 0, from
; the empty tables (fn-pio-direct-initial).
(defconst *pirdt-w0* (fn-pxe-new 0))
(defconst *pirdt-w1* (fn-pxe-new 1))
(defconst *pirdt-a* (pirdt-admit nil 7 11 4096 64 123 *pirdt-w0* nil nil))
(defconst *pirdt-ta* (nth 2 *pirdt-a*))
(defconst *pirdt-rowa* (nth 3 *pirdt-a*))
(defconst *pirdt-wa* (nth 4 *pirdt-a*))
(defconst *pirdt-i1* (nth 5 *pirdt-a*))
(defconst *pirdt-h1* (nth 6 *pirdt-a*))
; The client disconnects; the deadline passes: publication is revoked (the
; row cancelled in the issued table; the hold stands).
(defconst *pirdt-i1c* (fn-pio-direct-cancel *pirdt-ta* *pirdt-i1*))
; Request B reuses cid 7, on the NEXT generation (file 12), on slot 1.
(defconst *pirdt-b* (pirdt-admit (nth 1 *pirdt-a*) 7 12 4096 64 456 *pirdt-w1* *pirdt-i1c* *pirdt-h1*))
(defconst *pirdt-tb* (nth 2 *pirdt-b*))
(defconst *pirdt-rowb* (nth 3 *pirdt-b*))
(defconst *pirdt-i2* (nth 5 *pirdt-b*))
(defconst *pirdt-h2* (nth 6 *pirdt-b*))
; The original worker actually returns.
(defconst *pirdt-wa-returned* (nth 1 (pirdt-return *pirdt-wa* *pirdt-ta*)))

(assert-event (and (equal (nth 0 *pirdt-a*) :admitted) (equal (nth 1 *pirdt-a*) 1)
                   (equal *pirdt-ta* '(0 7 11 4096 64 123))
                   (equal *pirdt-i1* (list (cons *pirdt-ta* *pirdt-rowa*)))
                   (equal *pirdt-h1* '((11 (0 7 11 4096 64 123))))
                   (equal (nth 0 *pirdt-b*) :admitted) (equal (nth 1 *pirdt-b*) 2)
                   (equal *pirdt-tb* '(1 7 12 4096 64 456))
                   (equal *pirdt-h2* '((11 (0 7 11 4096 64 123)) (12 (1 7 12 4096 64 456))))
                   (equal (nth 6 (fn-pio-issued-row *pirdt-ta* *pirdt-i2*)) :cancelled)
                   (equal (nth 6 (fn-pio-issued-row *pirdt-tb* *pirdt-i2*)) :issued)
                   (equal (nth 2 *pirdt-wa-returned*) :returned)
                   (fn-pio-direct-okp *pirdt-i1* *pirdt-h1*)
                   (fn-pio-direct-okp *pirdt-i1c* *pirdt-h1*)
                   (fn-pio-direct-okp *pirdt-i2* *pirdt-h2*)))

; Retirement of generation 11 while A is held: close must wait, with or
; without the timeout, and B's row on 12 does not hold 11.  The lookup and
; the walk agree.
(assert-event
 (and (not (fn-pio-direct-quiet-p 11 *pirdt-h2*))
      (not (fn-pio-direct-quiet-p 12 *pirdt-h2*))
      (fn-pio-direct-quiet-p 13 *pirdt-h2*)
      (not (fn-pio-file-clear-p 11 (fn-pio-issued-rows *pirdt-i2*)))
      (not (fn-pio-file-clear-p 11 (fn-pio-issued-rows *pirdt-i1*)))
      (fn-pio-file-clear-p 11 (list *pirdt-rowb*))))

;;; KEYSTONE fn-pio-direct-admit-binds-an-idle-worker-to-the-issued-identity.
; REACHABLE POSITIVE: request A's admission, complete antecedent/conclusion.
(assert-event
 (let ((next nil) (cid 7) (file 11) (eoff 4096) (elen 64) (trailer 123) (worker *pirdt-w0*)
       (issued nil) (holds nil))
   (let ((r (pirdt-admit next cid file eoff elen trailer worker issued holds)) (n 0))
     (and (fn-hd-identp holds) (equal (nth 0 r) :admitted)
          (fn-pxe-rowp worker) (equal (nth 2 worker) :idle)
          (equal (nth 2 r) (list n cid file eoff elen trailer))
          (fn-pio-rowp (nth 3 r)) (equal (fn-pio-token (nth 3 r)) (nth 2 r))
          (equal (nth 6 (nth 3 r)) :issued)
          (equal (fn-pio-issued-row (nth 2 r) (nth 5 r)) (nth 3 r))
          (not (fn-pio-issued-row (nth 2 r) issued))
          (member-equal (nth 2 r) (fn-hd-tokens-of file (nth 6 r)))
          (not (member-equal (nth 2 r) (fn-hd-tokens-of file holds)))
          (equal (nth 0 (nth 4 r)) (nth 0 worker))
          (equal (nth 2 (nth 4 r)) :running) (equal (nth 3 (nth 4 r)) (nth 2 r))
          (equal (nth 1 r) (+ 1 n))))))
; HYPOTHESIS-REMOVAL: the worker A occupies is offered again (busy): not
; admitted, and the conclusion fails (it is not idle, no row, tables unchanged).
(assert-event
 (let ((r (pirdt-admit 1 8 11 0 64 123 *pirdt-wa* *pirdt-i1* *pirdt-h1*)))
   (and (not (equal (nth 0 r) :admitted))
        (equal (nth 0 r) :worker-busy)
        (not (equal (nth 2 *pirdt-wa*) :idle))
        (not (fn-pio-rowp (nth 3 r)))
        (equal (nth 5 r) *pirdt-i1*) (equal (nth 6 r) *pirdt-h1*))))
; Every worker busy (the host offers none): refused by name.  The companion
; theorem fn-pio-direct-admit-without-an-idle-worker-is-refused: counter,
; token, row, worker and both tables unchanged.
(assert-event
 (let ((r (pirdt-admit 2 9 11 0 64 123 nil *pirdt-i1* *pirdt-h1*)))
   (and (equal (nth 0 r) :read-resources-unavailable)
        (equal (nth 1 r) 2) (null (nth 2 r)) (null (nth 3 r)) (null (nth 4 r))
        (equal (nth 5 r) *pirdt-i1*) (equal (nth 6 r) *pirdt-h1*))))
; An old job never re-enters a worker that ran a later one (fresh ids).
(assert-event
 (let* ((idle (list 0 5 :idle nil))
        (r (pirdt-admit 3 7 11 0 64 123 idle *pirdt-i1* *pirdt-h1*)))
   (and (equal (nth 0 r) :stale-job) (equal (nth 1 r) 3) (equal (nth 4 r) idle))))
; Not a file incarnation (0): refused, nothing issued.
(assert-event (equal (nth 0 (pirdt-admit nil 7 0 0 64 123 *pirdt-w0* nil nil)) :invalid-read-identity))
; A token already issued (the counter handed back): :hold-refused, nothing
; issued, tables unchanged (distinct from every other word).
(assert-event
 (let ((r (pirdt-admit nil 7 11 4096 64 123 *pirdt-w1* *pirdt-i1* *pirdt-h1*)))
   (and (equal (nth 0 r) :hold-refused) (null (nth 2 r)) (null (nth 3 r))
        (equal (nth 4 r) *pirdt-w1*) (equal (nth 5 r) *pirdt-i1*) (equal (nth 6 r) *pirdt-h1*))))

;;; KEYSTONE fn-pio-direct-settle-publishes-only-the-issued-identity.
; REACHABLE POSITIVE (success variant): A delivered before any timeout.
(assert-event
 (let* ((token *pirdt-ta*) (worker *pirdt-wa-returned*) (verdict :ok)
        (issued *pirdt-i1*) (holds *pirdt-h1*)
        (row (fn-pio-issued-row token issued))
        (r (pirdt-settle token worker verdict issued holds)))
   (and (fn-pio-issuedp issued) (fn-hd-identp holds)
        (equal (nth 0 r) :publish)
        (fn-pio-rowp row) (equal token (fn-pio-token row))
        (equal (nth 6 row) :issued) (equal verdict :ok)
        (fn-pxe-rowp worker) (equal (nth 2 worker) :returned)
        (equal (nth 3 worker) token)
        (member-equal token (fn-hd-tokens-of 11 holds))
        (equal (fn-pio-token (nth 1 r)) token) (equal (nth 6 (nth 1 r)) :settled)
        (not (fn-pio-issued-row token (nth 3 r)))
        (not (member-equal token (fn-hd-tokens-of 11 (nth 4 r))))
        (equal (nth 0 (nth 2 r)) (nth 0 worker)) (equal (nth 2 (nth 2 r)) :idle))))
; HYPOTHESIS-REMOVAL: the timed-out request (cancelled row): no publication,
; and the conclusion fails (the row was not :issued).
(assert-event
 (let ((r (pirdt-settle *pirdt-ta* *pirdt-wa-returned* :ok *pirdt-i2* *pirdt-h2*)))
   (and (not (equal (nth 0 r) :publish))
        (not (equal (nth 6 (fn-pio-issued-row *pirdt-ta* *pirdt-i2*)) :issued)))))
; HYPOTHESIS-REMOVAL (fn-pio-issuedp): a table carrying the token twice keeps
; a row at the token after the settle: the conclusion fails.
(assert-event
 (let* ((twice (append *pirdt-i1* *pirdt-i1*))
        (r (pirdt-settle *pirdt-ta* *pirdt-wa-returned* :ok twice *pirdt-h1*)))
   (and (not (fn-pio-issuedp twice))
        (equal (nth 0 r) :publish)
        (fn-pio-issued-row *pirdt-ta* (nth 3 r)))))

;;; KEYSTONE fn-pio-direct-settle-observes-every-outcome.
; REACHABLE POSITIVES, one per outcome, each the full conclusion.
(defun pirdt-observed-p (token worker verdict issued holds)
  (declare (xargs :verify-guards nil))
  (let ((r (pirdt-settle token worker verdict issued holds))
        (row (fn-pio-issued-row token issued)))
    (and (fn-pio-issuedp issued) (fn-hd-identp holds)
         (not (member-equal (nth 0 r) '(:stale :unheld)))
         (equal (nth 0 r)
                (cond ((not (equal verdict :ok)) (list :fault verdict))
                      ((equal (nth 6 row) :cancelled) :cancelled)
                      (t :publish)))
         (equal (fn-pio-token (nth 1 r)) token) (equal (nth 6 (nth 1 r)) :settled)
         (not (fn-pio-issued-row token (nth 3 r)))
         (not (member-equal token (fn-hd-tokens-of (nth 2 token) (nth 4 r))))
         (equal (nth 2 (nth 2 r)) :idle))))
; late success after the timeout: :cancelled, no insert, file 11 released by
; A (B's hold on 12 stands), and the tables still agree
(assert-event
 (let ((r (pirdt-settle *pirdt-ta* *pirdt-wa-returned* :ok *pirdt-i2* *pirdt-h2*)))
   (and (pirdt-observed-p *pirdt-ta* *pirdt-wa-returned* :ok *pirdt-i2* *pirdt-h2*)
        (equal (nth 0 r) :cancelled)
        (fn-pio-direct-quiet-p 11 (nth 4 r))
        (not (fn-pio-direct-quiet-p 12 (nth 4 r)))
        (fn-pio-file-clear-p 11 (fn-pio-issued-rows (nth 3 r)))
        (fn-pio-direct-okp (nth 3 r) (nth 4 r)))))
; late error after the timeout: a fault, not a timeout
(assert-event
 (and (pirdt-observed-p *pirdt-ta* *pirdt-wa-returned* :read *pirdt-i2* *pirdt-h2*)
      (equal (nth 0 (pirdt-settle *pirdt-ta* *pirdt-wa-returned* :read *pirdt-i2* *pirdt-h2*))
             '(:fault :read))))
; error and digest before any timeout
(assert-event
 (and (pirdt-observed-p *pirdt-ta* *pirdt-wa-returned* :error *pirdt-i1* *pirdt-h1*)
      (pirdt-observed-p *pirdt-ta* *pirdt-wa-returned* :digest *pirdt-i1* *pirdt-h1*)
      (pirdt-observed-p *pirdt-ta* *pirdt-wa-returned* :ok *pirdt-i1* *pirdt-h1*)))
; HYPOTHESIS-REMOVAL: a stale settlement (the worker never returned) is not
; observed: the conclusion fails (the row stays, the worker is not idle, the
; file is not quiet).
(assert-event
 (let ((r (pirdt-settle *pirdt-ta* *pirdt-wa* :read *pirdt-i2* *pirdt-h2*)))
   (and (equal (nth 0 r) :stale)
        (fn-pio-issued-row *pirdt-ta* (nth 3 r))
        (not (equal (nth 2 (nth 2 r)) :idle))
        (not (fn-pio-direct-quiet-p 11 (nth 4 r))))))
; THE UNHELD OUTCOME (distinct from :stale): the row is issued but no hold
; carries its token: nothing changes; the host faults.
(assert-event
 (let ((r (pirdt-settle *pirdt-ta* *pirdt-wa-returned* :ok *pirdt-i1* nil)))
   (and (equal r (list :unheld *pirdt-rowa* *pirdt-wa-returned* *pirdt-i1* nil))
        (not (fn-pio-direct-okp *pirdt-i1* nil)))))

;;; KEYSTONE fn-pio-direct-settle-stale-changes-nothing.
; REACHABLE POSITIVES, one per disjunct of the hypothesis:
(defun pirdt-unchanged-p (token worker verdict issued holds)
  (declare (xargs :guard (fn-hd-identp holds)))
  (equal (pirdt-settle token worker verdict issued holds)
         (list :stale (fn-pio-issued-row token issued) worker issued holds)))
; a token the table does not hold: A's completion after A's row settled and
; left (a reused cid on the next generation is B's own token)
(assert-event
 (let ((after (nth 3 (pirdt-settle *pirdt-ta* *pirdt-wa-returned* :ok *pirdt-i1* *pirdt-h1*))))
   (and (not (fn-pio-issued-row *pirdt-ta* after))
        (pirdt-unchanged-p *pirdt-ta* *pirdt-wa-returned* :ok after nil))))
; the worker has not returned (a timeout is not evidence the worker stopped)
(assert-event (and (equal (nth 2 *pirdt-wa*) :running)
                   (pirdt-unchanged-p *pirdt-ta* *pirdt-wa* :ok *pirdt-i2* *pirdt-h2*)))
; the worker returned another job
(assert-event
 (let ((other (list 0 1 :returned *pirdt-tb*)))
   (and (not (equal (nth 3 other) *pirdt-ta*))
        (pirdt-unchanged-p *pirdt-ta* other :ok *pirdt-i1* *pirdt-h1*))))
; CORRUPTED-STATE: not a row at the token; not a worker row
(assert-event (pirdt-unchanged-p *pirdt-ta* *pirdt-wa-returned* :ok (list (cons *pirdt-ta* '(0 7 11))) *pirdt-h1*))
(assert-event (pirdt-unchanged-p *pirdt-ta* '(0 0 :returned) :ok *pirdt-i1* *pirdt-h1*))
; HYPOTHESIS-REMOVAL: every disjunct false (A's own returned job): the
; settlement is not stale, so the conclusion fails.
(assert-event
 (and (fn-pio-rowp (fn-pio-issued-row *pirdt-ta* *pirdt-i1*))
      (equal *pirdt-ta* (fn-pio-token (fn-pio-issued-row *pirdt-ta* *pirdt-i1*)))
      (not (equal (nth 6 (fn-pio-issued-row *pirdt-ta* *pirdt-i1*)) :settled))
      (fn-pxe-rowp *pirdt-wa-returned*) (equal (nth 2 *pirdt-wa-returned*) :returned)
      (equal (nth 3 *pirdt-wa-returned*) *pirdt-ta*)
      (not (pirdt-unchanged-p *pirdt-ta* *pirdt-wa-returned* :ok *pirdt-i1* *pirdt-h1*))))

;;; KEYSTONE fn-pio-direct-settle-happens-once (no hypothesis: the statement
;;; with fn-pio-issuedp was proved, then the weakened one, so there is no
;;; hypothesis-removal witness; the worker gates the second delivery).
; REACHABLE POSITIVES: the duplicate delivery after each first outcome,
; after a stale first delivery (the worker had not returned), and after an
; :unheld first delivery (the tables disagree: it repeats, never settles).
(defun pirdt-once-p (token worker verdict verdict2 issued holds)
  (declare (xargs :verify-guards nil))
  (let ((r (pirdt-settle token worker verdict issued holds)))
    (equal (pirdt-settle token (nth 2 r) verdict2 (nth 3 r) (nth 4 r))
           (list (if (equal (nth 0 r) :unheld) :unheld :stale)
                 (fn-pio-issued-row token (nth 3 r)) (nth 2 r) (nth 3 r) (nth 4 r)))))
(assert-event
 (and (pirdt-once-p *pirdt-ta* *pirdt-wa-returned* :ok :ok *pirdt-i1* *pirdt-h1*)
      (pirdt-once-p *pirdt-ta* *pirdt-wa-returned* :ok :ok *pirdt-i2* *pirdt-h2*)
      (pirdt-once-p *pirdt-ta* *pirdt-wa-returned* :read :ok *pirdt-i2* *pirdt-h2*)
      (pirdt-once-p *pirdt-ta* *pirdt-wa-returned* :ok :error *pirdt-i1* *pirdt-h1*)
      (equal (nth 0 (pirdt-settle *pirdt-ta* *pirdt-wa-returned* :ok *pirdt-i1* *pirdt-h1*)) :publish)
      (pirdt-once-p *pirdt-ta* *pirdt-wa* :ok :read *pirdt-i2* *pirdt-h2*)
      (equal (nth 0 (pirdt-settle *pirdt-ta* *pirdt-wa* :ok *pirdt-i2* *pirdt-h2*)) :stale)
      (pirdt-once-p *pirdt-ta* *pirdt-wa-returned* :ok :ok *pirdt-i1* nil)
      (equal (nth 0 (pirdt-settle *pirdt-ta* *pirdt-wa-returned* :ok *pirdt-i1* nil)) :unheld)))
; INTERVENING-RETURN SCENARIO (not a hypothesis removal: the second call is
; NOT on the first call's result).  A stale first delivery leaves the read
; owned; the worker's actual return in between is what lets the next
; delivery settle -- a timeout or an early delivery never spends the read.
(assert-event
 (let ((r (pirdt-settle *pirdt-ta* *pirdt-wa* :ok *pirdt-i2* *pirdt-h2*)))
   (and (equal (nth 0 r) :stale)
        (equal (nth 0 (pirdt-settle *pirdt-ta* *pirdt-wa-returned* :ok (nth 3 r) (nth 4 r)))
               :cancelled))))
; CORRUPTED-STATE: a table carrying the token twice still settles once: the
; second delivery finds the worker idle (the row that survives is unreachable
; through it).
(assert-event
 (let ((twice (append *pirdt-i1* *pirdt-i1*)))
   (and (not (fn-pio-issuedp twice))
        (pirdt-once-p *pirdt-ta* *pirdt-wa-returned* :ok :ok twice *pirdt-h1*)
        (fn-pio-issued-row *pirdt-ta* (nth 3 (pirdt-settle *pirdt-ta* *pirdt-wa-returned* :ok twice *pirdt-h1*))))))
; MUTATION: the conclusion fails for a call that is not the duplicate (the
; first delivery itself is not stale).
(assert-event
 (not (equal (pirdt-settle *pirdt-ta* *pirdt-wa-returned* :ok *pirdt-i1* *pirdt-h1*)
             (list :stale *pirdt-rowa* *pirdt-wa-returned* *pirdt-i1* *pirdt-h1*))))

;;; KEYSTONE fn-pio-direct-cancelled-read-still-pins-its-file.
; REACHABLE POSITIVE: A, with B's row beside it; the walk and the lookup.
(assert-event
 (let ((r *pirdt-a*) (file 11))
   (and (fn-hd-identp nil) (equal (nth 0 r) :admitted)
        (not (fn-pio-file-clear-p file (fn-pio-issued-rows (nth 5 r))))
        (not (fn-pio-file-clear-p file (fn-pio-issued-rows (fn-pio-direct-cancel (nth 2 r) (nth 5 r)))))
        (not (fn-pio-direct-quiet-p file (nth 6 r))))))
; HYPOTHESIS-REMOVAL: a refused admission pins nothing (no row, no hold):
; the conclusion fails.
(assert-event
 (let ((r (pirdt-admit 2 9 11 0 64 123 nil nil nil)) (file 11))
   (and (not (equal (nth 0 r) :admitted))
        (fn-pio-file-clear-p file (fn-pio-issued-rows (nth 5 r)))
        (fn-pio-direct-quiet-p file (nth 6 r)))))

;;; KEYSTONE fn-pio-direct-quiet-is-clear (the bridge: the close's one lookup
;;; is the walk it replaced, under the carried agreement).
; REACHABLE POSITIVES: both tables of the run, every file, both directions.
(defun pirdt-bridge-p (file issued holds)
  (declare (xargs :guard t))
  (and (fn-pio-direct-okp issued holds)
       (iff (fn-pio-direct-quiet-p file holds)
            (fn-pio-file-clear-p file (fn-pio-issued-rows issued)))))
(assert-event
 (and (pirdt-bridge-p 11 nil nil) (pirdt-bridge-p 11 *pirdt-i1* *pirdt-h1*)
      (pirdt-bridge-p 11 *pirdt-i1c* *pirdt-h1*) (pirdt-bridge-p 11 *pirdt-i2* *pirdt-h2*)
      (pirdt-bridge-p 12 *pirdt-i2* *pirdt-h2*) (pirdt-bridge-p 13 *pirdt-i2* *pirdt-h2*)
      (let ((r (pirdt-settle *pirdt-ta* *pirdt-wa-returned* :ok *pirdt-i2* *pirdt-h2*)))
        (and (pirdt-bridge-p 11 (nth 3 r) (nth 4 r)) (pirdt-bridge-p 12 (nth 3 r) (nth 4 r))))))
; HYPOTHESIS-REMOVAL (the agreement): a token held by no issued row makes 11
; not quiet while no row names it: the lookup and the walk disagree.
(assert-event
 (let ((holds '((11 ((9 9 11 0 0 0))))))
   (and (not (fn-pio-direct-okp nil holds))
        (not (fn-pio-direct-quiet-p 11 holds))
        (fn-pio-file-clear-p 11 (fn-pio-issued-rows nil)))))
; CORRUPTED-STATE: an issued row whose token holds nothing (the agreement
; broken the other way): the walk says held, the lookup says quiet.
(assert-event
 (and (not (fn-pio-direct-okp *pirdt-i1* nil))
      (not (fn-pio-file-clear-p 11 (fn-pio-issued-rows *pirdt-i1*)))
      (fn-pio-direct-quiet-p 11 nil)))
