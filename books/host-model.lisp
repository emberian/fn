; fn: the host model HM, a concurrent machine over the host's coordination
; state (lane host-model, 2026-10-03; decisions/whole-system-correctness-
; 2026-10-03.md section 3; decisions/host-into-acl2-2026-10-03.md; review
; lanedumps/host-model-review-1.md).  Prefix fn-hmc-.
;
; The theorems of this tree are each about ONE call of a pure function.  The
; host that calls them has threads, locks and I/O that completes late, and
; no theorem said what happens when those interleave.  This book is the
; machine over which that can be said.  Its state is the host's SHARED
; COORDINATION state as the existing books already model it, piece by piece:
;
;   ARPN     the arena readers' generation table   (books/arena-reader-pins.lisp)
;   OWNERS   the response plans' holds             (books/response-plan-pins.lisp)
;   ROWS     the issued cold reads                 (books/page-read-ownership.lisp)
;   WORKERS  the persistent cold workers           (books/page-read-executor.lisp)
;   NEXT     the read counter of fn-pio-direct-admit (books/page-read-direct.lisp)
;
; plus what the host's thin primitive layer holds and no book did: LOCKS
; (which actor holds which mutex), FDS (which fd number the OS binds to which
; file incarnation), REQS (the preads in flight, each with the fd and the
; incarnation it was issued against), READERS (the generation pins readers
; hold, one capability each), PASS (the reclaim pass's own pin), RESULTS
; (verdicts returned, not yet settled), LEASES (the window and discovery
; leases of the other two off-lock readers), RELEASED (retirements the table
; released, not yet closed), CLOSED (incarnations closed) and ENDED (a crash
; ended the run).
;
; THE LABELS.  A schedule is any list of labels; fn-hmc-run folds them.  A
; label whose precondition fails is a REFUSED no-op: the model refuses
; exactly what the generated code must refuse.  Two layers:
;
;   P, the primitives of the thin host layer, each an oracle step with a
;   named assumption (specs/failures.md A-PRIM-*):
;     (:acquire TID LOCK) (:release TID LOCK)        A-PRIM-MUTEX
;     (:fd-open TID INC FD)                           A-PRIM-FD: the OS binds FD
;                                                    to INC; a number closed
;                                                    earlier may be reused
;     (:io-begin TID KEY)                             A-PRIM-PREAD: the WORKER
;                                                    looks the fd up when it
;                                                    runs (after :issue, even
;                                                    after :cancel) and reads
;                                                    the incarnation bound then
;     (:io-complete KEY VERDICT)                      the device: any time, any
;                                                    order, after a cancel;
;                                                    VERDICT :ok :short :error
;                                                    :trailer :digest
;     (:crash)                                        ends the run (T1(c) is
;                                                    the recovery's)
;   C, the coordination steps, ACL2 functions of the books above, run by an
;   actor that HOLDS the named locks (the host's call sites are the quoted
;   realization table at the end; LOCK-CHECK reads it):
;     :owner+:extent  (:issue TID CID INC EOFF ELEN TRAILER)  fn-pio-direct-admit
;                     (:settle TID TOKEN)                     fn-pio-direct-settle
;                     (:close TID INC)                        fn-pio-file-clear-p,
;                                                             then the fd close
;     :extent         (:cancel TID TOKEN)                     fn-pio-cancel
;                     (:return TID TOKEN)                     fn-pxe-return
;                     (:window-acquire TID INC) (:window-release TID INC)
;                     (:discovery-acquire TID INC) (:discovery-release TID INC)
;     :owner+:pins    (:capture TID CID)                      fn-rpin-step :acquire
;                     (:pass-pin TID)                         fn-arpn-step :pin
;                     (:retire TID ITEMS) (:release-retired TID)  fn-arpn-step
;                     (:swap TID ITEMS)                       fn-arpn-step :retire
;     :pins           (:pin TID) (:unpin TID G)               fn-arpn-step
;                     (:drain TID CID)                        fn-rpin-step :release
;
; The pins lock is taken under the owner for :capture, :pass-pin, :retire,
; :release-retired and :swap (the host does: owner.lisp fnn-owner-response-
; pin, fnn-owner-maybe-publish-quantum, the reseat, the swap quantum); :pin,
; :unpin and :drain run off the owner.  :close holds owner and extent and
; rechecks fn-pio-file-clear-p under extent, as fnn-extent-close does; it is
; sound against a concurrent :pin only because every pin that could cover a
; released retirement is taken under the owner -- a REALIZATION obligation
; the table states and LOCK-CHECK checks, not a lock the model pretends the
; host holds.  An :unpin needs the reader's own capability (the READERS
; entry its :pin made): a thread cannot unpin what it did not pin, which is
; the generation-pin capability of the realization table.
;
; WHAT IS PROVED (every theorem over EVERY schedule from fn-hmc-init):
;   fn-hmc-run-keeps-invp (PRF-1242): the composed invariant.
;   fn-hmc-an-unsettled-read-keeps-its-incarnation-open (PRF-1243, T1(b).1):
;     retire, release, close and swap interleaved arbitrarily never close an
;     incarnation an issued or cancelled read, or a lease, names.
;   fn-hmc-a-request-in-flight-reads-its-own-incarnation (PRF-1243, T1(b).2):
;     the fd number a read in flight was issued against is still bound to
;     the incarnation its row (or lease) names.
;   fn-hmc-settle-publishes-only-its-own-token-once (PRF-1244, T1(b).3).
;   fn-hmc-release-postdates-every-live-pin (PRF-1244).
;   fn-hmc-a-held-response-refuses-the-swap: stated WITH its dependence on
;     the funded-pins conjunct and the pass having pinned first.
;   -by-definition: fn-hmc-close-is-refused-while-a-read-names-the-file,
;     fn-hmc-crash-ends-the-run (they restate the step; T1(b).1 is the claim).
;
; NOT MODELLED (named): fn-pgs-fill-realize (host/native/extent.lisp), a
; pread with no row and no lease -- it is no instance of any label here and
; is a counted LOCK-CHECK R3 baseline entry; the semantic owner state and its
; replies (T1(a)); the barrier ledger fn-otb; the reader view fn-ocvm; the
; crash as a cut of a byte program (T1(c)); liveness; a FOREIGN close of an
; fd number an incarnation holds (A-PRIM-FD: the host closes only fds it
; owns, a LOCK-CHECK rule).

(in-package "ACL2")
(include-book "page-read-direct")
(include-book "response-plan-pins")

; -----------------------------------------------------------------------------
; Row and worker accessors (never nth in a theorem: review S4), and guard-free
; list helpers (member-equal's guard wants a true list).

(defun fn-hmc-row-id (r) (declare (xargs :guard t)) (if (true-listp r) (nth 0 r) nil))
(defun fn-hmc-row-file (r) (declare (xargs :guard t)) (if (true-listp r) (nth 2 r) nil))
(defun fn-hmc-row-phase (r) (declare (xargs :guard t)) (if (true-listp r) (nth 6 r) nil))
(defun fn-hmc-row-settledp (r) (declare (xargs :guard t)) (eq (fn-hmc-row-phase r) :settled))
(defun fn-hmc-worker-slot (w) (declare (xargs :guard t)) (if (true-listp w) (nth 0 w) nil))
(defun fn-hmc-worker-phase (w) (declare (xargs :guard t)) (if (true-listp w) (nth 2 w) nil))
(defun fn-hmc-worker-token (w) (declare (xargs :guard t)) (if (true-listp w) (nth 3 w) nil))

(defun fn-hmc-memberp (x l)
  (declare (xargs :guard t))
  (cond ((atom l) nil)
        ((equal x (car l)) t)
        (t (fn-hmc-memberp x (cdr l)))))

(defun fn-hmc-remove1 (x l)
  (declare (xargs :guard t))
  (cond ((atom l) nil)
        ((equal x (car l)) (cdr l))
        (t (cons (car l) (fn-hmc-remove1 x (cdr l))))))

; -----------------------------------------------------------------------------
; The state.

(defconst *fn-hmc-field-index*
  '((:locks . 0) (:fds . 1) (:reqs . 2) (:arpn . 3) (:owners . 4) (:pass . 5)
    (:readers . 6) (:rows . 7) (:workers . 8) (:next . 9) (:results . 10)
    (:leases . 11) (:released . 12) (:closed . 13) (:ended . 14)))

(defconst *fn-hmc-fields* 15)

(defun fn-hmc-make (locks fds reqs arpn owners pass readers rows workers next results
                          leases released closed ended)
  (declare (xargs :guard t))
  (list locks fds reqs arpn owners pass readers rows workers next results
        leases released closed ended))

(defun fn-hmc-field (i st) (declare (xargs :guard (natp i))) (if (true-listp st) (nth i st) nil))
(defun fn-hmc-locks (st) (declare (xargs :guard t)) (fn-hmc-field 0 st))
(defun fn-hmc-fds (st) (declare (xargs :guard t)) (fn-hmc-field 1 st))
(defun fn-hmc-reqs (st) (declare (xargs :guard t)) (fn-hmc-field 2 st))
(defun fn-hmc-arpn (st) (declare (xargs :guard t)) (fn-hmc-field 3 st))
(defun fn-hmc-owners (st) (declare (xargs :guard t)) (fn-hmc-field 4 st))
(defun fn-hmc-pass (st) (declare (xargs :guard t)) (fn-hmc-field 5 st))
(defun fn-hmc-readers (st) (declare (xargs :guard t)) (fn-hmc-field 6 st))
(defun fn-hmc-rows (st) (declare (xargs :guard t)) (fn-hmc-field 7 st))
(defun fn-hmc-workers (st) (declare (xargs :guard t)) (fn-hmc-field 8 st))
(defun fn-hmc-next (st) (declare (xargs :guard t)) (fn-hmc-field 9 st))
(defun fn-hmc-results (st) (declare (xargs :guard t)) (fn-hmc-field 10 st))
(defun fn-hmc-leases (st) (declare (xargs :guard t)) (fn-hmc-field 11 st))
(defun fn-hmc-released (st) (declare (xargs :guard t)) (fn-hmc-field 12 st))
(defun fn-hmc-closed (st) (declare (xargs :guard t)) (fn-hmc-field 13 st))
(defun fn-hmc-ended (st) (declare (xargs :guard t)) (fn-hmc-field 14 st))

(defun fn-hmc-set (i v st)
  (declare (xargs :guard (natp i)))
  (update-nth i v (if (true-listp st) st nil)))

(defun fn-hmc-with-fn (st pairs)
  (declare (xargs :mode :program))
  (if (endp pairs)
      st
    (fn-hmc-with-fn (list 'fn-hmc-set (cdr (assoc-eq (car pairs) *fn-hmc-field-index*))
                          (cadr pairs) st)
                    (cddr pairs))))

; (fn-hmc-with ST :field VALUE ...): ST with those fields replaced.
(defmacro fn-hmc-with (st &rest pairs)
  (fn-hmc-with-fn st pairs))

(defun fn-hmc-workers-of-count (n acc)
  (declare (xargs :guard (and (natp n) (true-listp acc))))
  (if (zp n) acc (fn-hmc-workers-of-count (- n 1) (cons (fn-pxe-new (- n 1)) acc))))

(defun fn-hmc-init ()
  (declare (xargs :guard t))
  (fn-hmc-make nil nil nil (fn-arpn-initial) nil nil nil nil
               (fn-hmc-workers-of-count (fn-pio-direct-workers) nil)
               0 nil nil nil nil nil))

(defconst *fn-hmc-locks* '(:owner :extent :pins))

(defun fn-hmc-arg (i ev) (declare (xargs :guard (natp i))) (if (true-listp ev) (nth i ev) nil))

; -----------------------------------------------------------------------------
; Helpers over the fields.

(defun fn-hmc-holds-p (tid lock locks)
  (declare (xargs :guard t))
  (let ((e (and (alistp locks) (assoc-equal lock locks))))
    (and e (equal (cdr e) tid))))

(defun fn-hmc-lock-free-p (lock locks)
  (declare (xargs :guard t))
  (not (and (alistp locks) (assoc-equal lock locks))))

; FDS: ((FD . INC) ...).  Each fd once; an incarnation bound by at most one fd.
(defun fn-hmc-fd-inc (fd fds)
  (declare (xargs :guard t))
  (let ((e (and (alistp fds) (assoc-equal fd fds)))) (and e (cdr e))))

(defun fn-hmc-fd-of-inc (inc fds)
  (declare (xargs :guard t))
  (cond ((atom fds) nil)
        ((and (consp (car fds)) (equal (cdar fds) inc)) (caar fds))
        (t (fn-hmc-fd-of-inc inc (cdr fds)))))

(defun fn-hmc-fds-incs (fds)
  (declare (xargs :guard t))
  (cond ((atom fds) nil)
        ((consp (car fds)) (cons (cdar fds) (fn-hmc-fds-incs (cdr fds))))
        (t (fn-hmc-fds-incs (cdr fds)))))

(defthm fn-hmc-fds-incs-true-listp
  (true-listp (fn-hmc-fds-incs fds))
  :rule-classes (:rewrite :type-prescription))

(defun fn-hmc-boundp (inc fds)
  (declare (xargs :guard t))
  (and (member-equal inc (fn-hmc-fds-incs fds)) t))

(defun fn-hmc-unbind-inc (inc fds)
  (declare (xargs :guard t))
  (cond ((atom fds) nil)
        ((and (consp (car fds)) (equal (cdar fds) inc)) (fn-hmc-unbind-inc inc (cdr fds)))
        (t (cons (car fds) (fn-hmc-unbind-inc inc (cdr fds))))))

; ROWS: the issued table, one row per token; found by its token.
(defun fn-hmc-row-of (token rows)
  (declare (xargs :guard t))
  (cond ((atom rows) nil)
        ((and (true-listp (car rows)) (equal (fn-pio-token (car rows)) token)) (car rows))
        (t (fn-hmc-row-of token (cdr rows)))))

; Rows are keyed by their id (unique by the invariant): a put replaces the
; row of that id.
(defun fn-hmc-rows-remove (id rows)
  (declare (xargs :guard t))
  (cond ((atom rows) nil)
        ((equal (fn-hmc-row-id (car rows)) id) (fn-hmc-rows-remove id (cdr rows)))
        (t (cons (car rows) (fn-hmc-rows-remove id (cdr rows))))))

(defun fn-hmc-rows-put (row rows)
  (declare (xargs :guard t))
  (cons row (fn-hmc-rows-remove (fn-hmc-row-id row) rows)))

; WORKERS: one row per slot.
(defun fn-hmc-idle-worker (workers)
  (declare (xargs :guard t))
  (cond ((atom workers) nil)
        ((equal (fn-hmc-worker-phase (car workers)) :idle) (car workers))
        (t (fn-hmc-idle-worker (cdr workers)))))

(defun fn-hmc-worker-of (token workers)
  (declare (xargs :guard t))
  (cond ((atom workers) nil)
        ((and (not (equal (fn-hmc-worker-phase (car workers)) :idle))
              (equal (fn-hmc-worker-token (car workers)) token))
         (car workers))
        (t (fn-hmc-worker-of token (cdr workers)))))

(defun fn-hmc-workers-remove (slot workers)
  (declare (xargs :guard t))
  (cond ((atom workers) nil)
        ((equal (fn-hmc-worker-slot (car workers)) slot) (fn-hmc-workers-remove slot (cdr workers)))
        (t (cons (car workers) (fn-hmc-workers-remove slot (cdr workers))))))

(defun fn-hmc-workers-put (w workers)
  (declare (xargs :guard t))
  (cons w (fn-hmc-workers-remove (fn-hmc-worker-slot w) workers)))

; REQS: ((KEY FD INC) ...), KEY a row's token or a lease (:window INC) /
; (:discovery INC).
(defun fn-hmc-req-key (q) (declare (xargs :guard t)) (if (true-listp q) (nth 0 q) nil))
(defun fn-hmc-req-fd (q) (declare (xargs :guard t)) (if (true-listp q) (nth 1 q) nil))
(defun fn-hmc-req-inc (q) (declare (xargs :guard t)) (if (true-listp q) (nth 2 q) nil))

(defun fn-hmc-req-of (key reqs)
  (declare (xargs :guard t))
  (cond ((atom reqs) nil)
        ((equal (fn-hmc-req-key (car reqs)) key) (car reqs))
        (t (fn-hmc-req-of key (cdr reqs)))))

(defun fn-hmc-reqs-remove (key reqs)
  (declare (xargs :guard t))
  (cond ((atom reqs) nil)
        ((equal (fn-hmc-req-key (car reqs)) key) (fn-hmc-reqs-remove key (cdr reqs)))
        (t (cons (car reqs) (fn-hmc-reqs-remove key (cdr reqs))))))

; LEASES: ((KIND . INC) ...), several per incarnation.
(defun fn-hmc-lease-names-p (inc leases)
  (declare (xargs :guard t))
  (cond ((atom leases) nil)
        ((and (consp (car leases)) (equal (cdar leases) inc)) t)
        (t (fn-hmc-lease-names-p inc (cdr leases)))))

; RELEASED: the items of every retirement the table released, flat.
(defun fn-hmc-items-of (rel)
  (declare (xargs :guard t))
  (cond ((atom rel) nil)
        ((and (consp (car rel)) (true-listp (cdar rel)))
         (append (cdar rel) (fn-hmc-items-of (cdr rel))))
        (t (fn-hmc-items-of (cdr rel)))))

; READERS: ((TID . G) ...), one entry per generation pin a reader holds.
(defun fn-hmc-readers-at (g readers)
  (declare (xargs :guard t))
  (cond ((atom readers) 0)
        ((and (consp (car readers)) (equal (cdar readers) g))
         (+ 1 (fn-hmc-readers-at g (cdr readers))))
        (t (fn-hmc-readers-at g (cdr readers)))))

; The key a read in flight is issued under: the row's token, or the lease.
(defun fn-hmc-key-inc (key rows leases)
  (declare (xargs :guard t))
  (let ((row (fn-hmc-row-of key rows)))
    (cond ((and row (not (fn-hmc-row-settledp row))) (fn-hmc-row-file row))
          ((and (consp key) (member-eq (car key) '(:window :discovery))
                (consp (cdr key)) (null (cddr key))
                (fn-hmc-memberp (cons (car key) (cadr key)) leases))
           (cadr key))
          (t nil))))

; -----------------------------------------------------------------------------
; The steps, one function per label; each (mv ST' ANSWER), ANSWER :refused
; and ST' = ST when the label's precondition fails.

(defun fn-hmc-do-acquire (st ev)
  (declare (xargs :guard t))
  (let ((tid (fn-hmc-arg 1 ev)) (lock (fn-hmc-arg 2 ev)) (locks (fn-hmc-locks st)))
    (if (and (alistp locks) (member-eq lock *fn-hmc-locks*) (fn-hmc-lock-free-p lock locks))
        (mv (fn-hmc-with st :locks (cons (cons lock tid) locks)) :held)
      (mv st :refused))))

(defun fn-hmc-do-release (st ev)
  (declare (xargs :guard t))
  (let ((tid (fn-hmc-arg 1 ev)) (lock (fn-hmc-arg 2 ev)) (locks (fn-hmc-locks st)))
    (if (and (alistp locks) (fn-hmc-holds-p tid lock locks))
        (mv (fn-hmc-with st :locks (remove1-assoc-equal lock locks)) :released)
      (mv st :refused))))

(defun fn-hmc-do-fd-open (st ev)
  (declare (xargs :guard t))
  (let ((inc (fn-hmc-arg 2 ev)) (fd (fn-hmc-arg 3 ev)) (fds (fn-hmc-fds st))
        (closed (fn-hmc-closed st)))
    (if (and (natp inc) (natp fd) (alistp fds)
             (not (assoc-equal fd fds)) (not (fn-hmc-boundp inc fds))
             (not (fn-hmc-memberp inc closed)))
        (mv (fn-hmc-with st :fds (cons (cons fd inc) fds)) :bound)
      (mv st :refused))))

; The worker (or the lease holder) looks the fd up when it runs: the
; incarnation its key names must still be bound, and the read is recorded
; against the fd bound NOW.
(defun fn-hmc-do-io-begin (st ev)
  (declare (xargs :guard t))
  (let* ((key (fn-hmc-arg 2 ev)) (rows (fn-hmc-rows st)) (leases (fn-hmc-leases st))
         (fds (fn-hmc-fds st)) (reqs (fn-hmc-reqs st)) (workers (fn-hmc-workers st))
         (results (fn-hmc-results st))
         (inc (fn-hmc-key-inc key rows leases))
         (fd (and inc (fn-hmc-fd-of-inc inc fds))))
    (if (and inc fd (not (fn-hmc-req-of key reqs))
             (alistp results) (not (assoc-equal key results))
             (or (not (fn-hmc-row-of key rows))
                 (let ((w (fn-hmc-worker-of key workers)))
                   (and w (equal (fn-hmc-worker-phase w) :running)))))
        (mv (fn-hmc-with st :reqs (cons (list key fd inc) reqs)) :began)
      (mv st :refused))))

; The device: the bytes of the incarnation the request named reach the
; worker's private buffer, with its verdict.
(defun fn-hmc-do-io-complete (st ev)
  (declare (xargs :guard t))
  (let ((key (fn-hmc-arg 1 ev)) (verdict (fn-hmc-arg 2 ev))
        (reqs (fn-hmc-reqs st)) (results (fn-hmc-results st)))
    (if (and (fn-hmc-req-of key reqs)
             (member-eq verdict '(:ok :short :error :trailer :digest))
             (alistp results))
        (mv (fn-hmc-with st :reqs (fn-hmc-reqs-remove key reqs)
                         :results (cons (cons key verdict) results))
            :completed)
      (mv st :stale))))

(defun fn-hmc-do-crash (st)
  (declare (xargs :guard t))
  (mv (fn-hmc-make nil nil nil (fn-arpn-initial) nil nil nil nil nil
                   (if (natp (fn-hmc-next st)) (fn-hmc-next st) 0)
                   nil nil nil (fn-hmc-closed st) t)
      :crashed))

(defun fn-hmc-do-issue (st ev)
  (declare (xargs :guard t))
  (let* ((tid (fn-hmc-arg 1 ev)) (cid (fn-hmc-arg 2 ev)) (inc (fn-hmc-arg 3 ev))
         (eoff (fn-hmc-arg 4 ev)) (elen (fn-hmc-arg 5 ev)) (trailer (fn-hmc-arg 6 ev))
         (locks (fn-hmc-locks st)) (fds (fn-hmc-fds st)) (closed (fn-hmc-closed st))
         (rows (fn-hmc-rows st)) (workers (fn-hmc-workers st)) (next (fn-hmc-next st))
         (w (fn-hmc-idle-worker workers)))
    (if (and (fn-hmc-holds-p tid :owner locks) (fn-hmc-holds-p tid :extent locks)
             (fn-hmc-boundp inc fds) (not (fn-hmc-memberp inc closed)))
        (mv-let (word next1 token row w1)
          (fn-pio-direct-admit next cid inc eoff elen trailer w)
          (if (equal word :admitted)
              (mv (fn-hmc-with st :rows (fn-hmc-rows-put row rows)
                               :workers (fn-hmc-workers-put w1 workers)
                               :next next1)
                  (list :admitted token))
            (mv st word)))
      (mv st :refused))))

(defun fn-hmc-do-cancel (st ev)
  (declare (xargs :guard t))
  (let* ((tid (fn-hmc-arg 1 ev)) (token (fn-hmc-arg 2 ev))
         (locks (fn-hmc-locks st)) (rows (fn-hmc-rows st))
         (row (fn-hmc-row-of token rows)))
    (if (and (fn-hmc-holds-p tid :extent locks) row (not (fn-hmc-row-settledp row)))
        (mv (fn-hmc-with st :rows (fn-hmc-rows-put (fn-pio-cancel row token) rows)) :cancelled)
      (mv st :refused))))

(defun fn-hmc-do-return (st ev)
  (declare (xargs :guard t))
  (let* ((tid (fn-hmc-arg 1 ev)) (token (fn-hmc-arg 2 ev))
         (locks (fn-hmc-locks st)) (workers (fn-hmc-workers st)) (results (fn-hmc-results st))
         (w (fn-hmc-worker-of token workers)))
    (if (and (fn-hmc-holds-p tid :extent locks) w (alistp results) (assoc-equal token results))
        (mv-let (word w1) (fn-pxe-return w token)
          (if (equal word :returned)
              (mv (fn-hmc-with st :workers (fn-hmc-workers-put w1 workers)) :returned)
            (mv st word)))
      (mv st :refused))))

(defun fn-hmc-do-settle (st ev)
  (declare (xargs :guard t))
  (let* ((tid (fn-hmc-arg 1 ev)) (token (fn-hmc-arg 2 ev))
         (locks (fn-hmc-locks st)) (rows (fn-hmc-rows st)) (workers (fn-hmc-workers st))
         (results (fn-hmc-results st))
         (row (fn-hmc-row-of token rows)) (w (fn-hmc-worker-of token workers))
         (r (and (alistp results) (assoc-equal token results))))
    (if (and (fn-hmc-holds-p tid :owner locks) (fn-hmc-holds-p tid :extent locks) row w r)
        (mv-let (answer row1 w1) (fn-pio-direct-settle row w token (cdr r))
          (if (equal answer :stale)
              (mv st :stale)
            (mv (fn-hmc-with st :rows (fn-hmc-rows-put row1 rows)
                             :workers (fn-hmc-workers-put w1 workers)
                             :results (remove1-assoc-equal token results))
                answer)))
      (mv st :refused))))

(defun fn-hmc-do-lease-acquire (st ev kind)
  (declare (xargs :guard t))
  (let ((tid (fn-hmc-arg 1 ev)) (inc (fn-hmc-arg 2 ev)) (locks (fn-hmc-locks st))
        (fds (fn-hmc-fds st)) (closed (fn-hmc-closed st)) (leases (fn-hmc-leases st)))
    (if (and (fn-hmc-holds-p tid :extent locks) (fn-hmc-boundp inc fds)
             (not (fn-hmc-memberp inc closed)))
        (mv (fn-hmc-with st :leases (cons (cons kind inc) leases)) :leased)
      (mv st :refused))))

(defun fn-hmc-do-lease-release (st ev kind)
  (declare (xargs :guard t))
  (let ((tid (fn-hmc-arg 1 ev)) (inc (fn-hmc-arg 2 ev)) (locks (fn-hmc-locks st))
        (leases (fn-hmc-leases st)) (reqs (fn-hmc-reqs st)))
    (if (and (fn-hmc-holds-p tid :extent locks)
             (fn-hmc-memberp (cons kind inc) leases)
             (not (fn-hmc-req-of (list kind inc) reqs)))
        (mv (fn-hmc-with st :leases (fn-hmc-remove1 (cons kind inc) leases)) :released)
      (mv st :refused))))

(defun fn-hmc-do-pin (st ev)
  (declare (xargs :guard t))
  (let ((tid (fn-hmc-arg 1 ev)) (locks (fn-hmc-locks st)) (arpn (fn-hmc-arpn st))
        (readers (fn-hmc-readers st)))
    (if (and (fn-hmc-holds-p tid :pins locks) (fn-arpn-okp arpn))
        (mv-let (st1 g) (fn-arpn-step arpn '(:pin))
          (mv (fn-hmc-with st :arpn st1 :readers (cons (cons tid g) readers)) g))
      (mv st :refused))))

; The reclaim pass pins at its capture, under the owner, before it walks;
; the swap discounts exactly this pin.
(defun fn-hmc-do-pass-pin (st ev)
  (declare (xargs :guard t))
  (let ((tid (fn-hmc-arg 1 ev)) (locks (fn-hmc-locks st)) (arpn (fn-hmc-arpn st))
        (readers (fn-hmc-readers st)) (pass (fn-hmc-pass st)))
    (if (and (fn-hmc-holds-p tid :owner locks) (fn-hmc-holds-p tid :pins locks)
             (fn-arpn-okp arpn) (null pass))
        (mv-let (st1 g) (fn-arpn-step arpn '(:pin))
          (mv (fn-hmc-with st :arpn st1 :readers (cons (cons tid g) readers)
                           :pass (cons tid g))
              g))
      (mv st :refused))))

; A reader unpins what IT pinned (its READERS entry): the capability.
(defun fn-hmc-do-unpin (st ev)
  (declare (xargs :guard t))
  (let ((tid (fn-hmc-arg 1 ev)) (g (fn-hmc-arg 2 ev)) (locks (fn-hmc-locks st))
        (arpn (fn-hmc-arpn st)) (readers (fn-hmc-readers st)) (pass (fn-hmc-pass st)))
    (if (and (fn-hmc-holds-p tid :pins locks) (fn-arpn-okp arpn) (natp g)
             (fn-hmc-memberp (cons tid g) readers)
             (fn-arpn-held-p g (second arpn)))
        (mv-let (st1 ans) (fn-arpn-step arpn (list :unpin g))
          (if (equal ans :ok)
              (mv (fn-hmc-with st :arpn st1
                               :readers (fn-hmc-remove1 (cons tid g) readers)
                               :pass (if (equal pass (cons tid g)) nil pass))
                  :ok)
            (mv st :refused)))
      (mv st :refused))))

(defun fn-hmc-do-capture (st ev)
  (declare (xargs :guard t))
  (let ((tid (fn-hmc-arg 1 ev)) (cid (fn-hmc-arg 2 ev)) (locks (fn-hmc-locks st))
        (arpn (fn-hmc-arpn st)) (owners (fn-hmc-owners st)))
    (if (and (fn-hmc-holds-p tid :owner locks) (fn-hmc-holds-p tid :pins locks)
             (fn-arpn-okp arpn) (alistp owners) (natp cid))
        (mv-let (owners1 st1 ans) (fn-rpin-step owners arpn (list :acquire cid))
          (if (equal ans :acquired)
              (mv (fn-hmc-with st :arpn st1 :owners owners1) :acquired)
            (mv st ans)))
      (mv st :refused))))

(defun fn-hmc-do-drain (st ev)
  (declare (xargs :guard t))
  (let ((tid (fn-hmc-arg 1 ev)) (cid (fn-hmc-arg 2 ev)) (locks (fn-hmc-locks st))
        (arpn (fn-hmc-arpn st)) (owners (fn-hmc-owners st)))
    (if (and (fn-hmc-holds-p tid :pins locks) (fn-arpn-okp arpn) (alistp owners))
        (mv-let (owners1 st1 ans) (fn-rpin-step owners arpn (list :release cid))
          (if (equal ans :released)
              (mv (fn-hmc-with st :arpn st1 :owners owners1) :released)
            (mv st ans)))
      (mv st :refused))))

(defun fn-hmc-do-retire (st ev)
  (declare (xargs :guard t))
  (let ((tid (fn-hmc-arg 1 ev)) (items (fn-hmc-arg 2 ev)) (locks (fn-hmc-locks st))
        (arpn (fn-hmc-arpn st)))
    (if (and (fn-hmc-holds-p tid :owner locks) (fn-hmc-holds-p tid :pins locks)
             (fn-arpn-okp arpn) (true-listp items))
        (mv-let (st1 s) (fn-arpn-step arpn (list :retire items))
          (mv (fn-hmc-with st :arpn st1) s))
      (mv st :refused))))

(defun fn-hmc-do-release-retired (st ev)
  (declare (xargs :guard t))
  (let ((tid (fn-hmc-arg 1 ev)) (locks (fn-hmc-locks st)) (arpn (fn-hmc-arpn st))
        (released (fn-hmc-released st)))
    (if (and (fn-hmc-holds-p tid :owner locks) (fn-hmc-holds-p tid :pins locks)
             (fn-arpn-okp arpn) (true-listp released))
        (mv-let (st1 rel) (fn-arpn-step arpn '(:release))
          (mv (fn-hmc-with st :arpn st1 :released (append (fn-hmc-items-of rel) released))
              rel))
      (mv st :refused))))

; fn-orcp-swap-word's :readers test: (1- reader-count) <= 0 with the pass's
; own pin standing (owner.lisp fnn-owner-reclaim-pass).  The swap retires
; the old generation's items.
(defun fn-hmc-do-swap (st ev)
  (declare (xargs :guard t))
  (let ((tid (fn-hmc-arg 1 ev)) (items (fn-hmc-arg 2 ev)) (locks (fn-hmc-locks st))
        (arpn (fn-hmc-arpn st)) (pass (fn-hmc-pass st)))
    (if (and (fn-hmc-holds-p tid :owner locks) (fn-hmc-holds-p tid :pins locks)
             (fn-arpn-okp arpn) pass (<= (fn-arpn-count (second arpn)) 1)
             (true-listp items))
        (mv-let (st1 s) (fn-arpn-step arpn (list :retire items))
          (mv (fn-hmc-with st :arpn st1) (list :swapped s)))
      (mv st :refused))))

; fnn-extent-close: under owner and extent, the retirement released,
; fn-pio-file-clear-p rechecked, no lease (close-preview's :read-file-held);
; then the primitive close of the incarnation's fd.
(defun fn-hmc-do-close (st ev)
  (declare (xargs :guard t))
  (let ((tid (fn-hmc-arg 1 ev)) (inc (fn-hmc-arg 2 ev)) (locks (fn-hmc-locks st))
        (fds (fn-hmc-fds st)) (rows (fn-hmc-rows st)) (leases (fn-hmc-leases st))
        (released (fn-hmc-released st)) (closed (fn-hmc-closed st)))
    (if (and (fn-hmc-holds-p tid :owner locks) (fn-hmc-holds-p tid :extent locks)
             (fn-hmc-memberp inc released)
             (fn-pio-file-clear-p inc rows)
             (not (fn-hmc-lease-names-p inc leases))
             (fn-hmc-boundp inc fds))
        (mv (fn-hmc-with st :fds (fn-hmc-unbind-inc inc fds)
                         :released (fn-hmc-remove1 inc released)
                         :closed (cons inc closed))
            :closed)
      (mv st :refused))))

(defun fn-hmc-step (st ev)
  (declare (xargs :guard t))
  (if (fn-hmc-ended st)
      (mv st :refused)
    (case (fn-hmc-arg 0 ev)
      (:acquire (fn-hmc-do-acquire st ev))
      (:release (fn-hmc-do-release st ev))
      (:fd-open (fn-hmc-do-fd-open st ev))
      (:io-begin (fn-hmc-do-io-begin st ev))
      (:io-complete (fn-hmc-do-io-complete st ev))
      (:crash (fn-hmc-do-crash st))
      (:issue (fn-hmc-do-issue st ev))
      (:cancel (fn-hmc-do-cancel st ev))
      (:return (fn-hmc-do-return st ev))
      (:settle (fn-hmc-do-settle st ev))
      (:window-acquire (fn-hmc-do-lease-acquire st ev :window))
      (:window-release (fn-hmc-do-lease-release st ev :window))
      (:discovery-acquire (fn-hmc-do-lease-acquire st ev :discovery))
      (:discovery-release (fn-hmc-do-lease-release st ev :discovery))
      (:pin (fn-hmc-do-pin st ev))
      (:unpin (fn-hmc-do-unpin st ev))
      (:pass-pin (fn-hmc-do-pass-pin st ev))
      (:capture (fn-hmc-do-capture st ev))
      (:drain (fn-hmc-do-drain st ev))
      (:retire (fn-hmc-do-retire st ev))
      (:release-retired (fn-hmc-do-release-retired st ev))
      (:swap (fn-hmc-do-swap st ev))
      (:close (fn-hmc-do-close st ev))
      (otherwise (mv st :refused)))))

(defun fn-hmc-run (st sched)
  (declare (xargs :guard t))
  (if (consp sched)
      (mv-let (st1 ans) (fn-hmc-step st (car sched))
        (declare (ignore ans))
        (fn-hmc-run st1 (cdr sched)))
    st))

(defun fn-hmc-answer (st ev)
  (declare (xargs :guard t))
  (mv-let (st1 ans) (fn-hmc-step st ev) (declare (ignore st1)) ans))

(defun fn-hmc-next-state (st ev)
  (declare (xargs :guard t))
  (mv-let (st1 ans) (fn-hmc-step st ev) (declare (ignore ans)) st1))

; -----------------------------------------------------------------------------
; The invariant.

(defun fn-hmc-row-ids (rows)
  (declare (xargs :guard t))
  (cond ((atom rows) nil)
        (t (cons (fn-hmc-row-id (car rows)) (fn-hmc-row-ids (cdr rows))))))

(defun fn-hmc-rowsp (rows)
  (declare (xargs :guard t))
  (cond ((atom rows) (null rows))
        (t (and (fn-pio-rowp (car rows)) (fn-hmc-rowsp (cdr rows))))))

(defun fn-hmc-rows-below-p (rows next)
  (declare (xargs :guard t))
  (cond ((atom rows) t)
        (t (and (natp (fn-hmc-row-id (car rows))) (natp next)
                (< (fn-hmc-row-id (car rows)) next)
                (fn-hmc-rows-below-p (cdr rows) next)))))

; Every unsettled row names a bound, unclosed incarnation (T1(b).1's conjunct).
(defun fn-hmc-rows-open-p (rows fds closed)
  (declare (xargs :guard t))
  (cond ((atom rows) t)
        (t (and (or (fn-hmc-row-settledp (car rows))
                    (and (fn-hmc-boundp (fn-hmc-row-file (car rows)) fds)
                         (not (fn-hmc-memberp (fn-hmc-row-file (car rows)) closed))))
                (fn-hmc-rows-open-p (cdr rows) fds closed)))))

; Every lease names a bound, unclosed incarnation.
(defun fn-hmc-leases-open-p (leases fds closed)
  (declare (xargs :guard t))
  (cond ((atom leases) t)
        (t (and (consp (car leases))
                (member-eq (caar leases) '(:window :discovery))
                (fn-hmc-boundp (cdar leases) fds)
                (not (fn-hmc-memberp (cdar leases) closed))
                (fn-hmc-leases-open-p (cdr leases) fds closed)))))

(defun fn-hmc-worker-slots (workers)
  (declare (xargs :guard t))
  (cond ((atom workers) nil)
        (t (cons (fn-hmc-worker-slot (car workers)) (fn-hmc-worker-slots (cdr workers))))))

(defun fn-hmc-busy-tokens (workers)
  (declare (xargs :guard t))
  (cond ((atom workers) nil)
        ((equal (fn-hmc-worker-phase (car workers)) :idle) (fn-hmc-busy-tokens (cdr workers)))
        (t (cons (fn-hmc-worker-token (car workers)) (fn-hmc-busy-tokens (cdr workers))))))

; Every worker is a worker; a busy worker's token names an unsettled row.
(defun fn-hmc-workersp (workers rows)
  (declare (xargs :guard t))
  (cond ((atom workers) (null workers))
        (t (and (fn-pxe-rowp (car workers))
                (or (equal (fn-hmc-worker-phase (car workers)) :idle)
                    (let ((row (fn-hmc-row-of (fn-hmc-worker-token (car workers)) rows)))
                      (and row (not (fn-hmc-row-settledp row)))))
                (fn-hmc-workersp (cdr workers) rows)))))

; Every request in flight: its fd is bound to its incarnation, and its key
; names that incarnation (an unsettled row's file, or a live lease).
(defun fn-hmc-reqs-okp (reqs fds rows leases)
  (declare (xargs :guard t))
  (cond ((atom reqs) t)
        (t (and (true-listp (car reqs))
                (fn-hmc-req-inc (car reqs))
                (equal (fn-hmc-fd-inc (fn-hmc-req-fd (car reqs)) fds)
                       (fn-hmc-req-inc (car reqs)))
                (equal (fn-hmc-key-inc (fn-hmc-req-key (car reqs)) rows leases)
                       (fn-hmc-req-inc (car reqs)))
                (fn-hmc-reqs-okp (cdr reqs) fds rows leases)))))

; A verdict held for a key means no request of that key is in flight.
(defun fn-hmc-results-landed-p (results reqs)
  (declare (xargs :guard t))
  (cond ((atom results) t)
        (t (and (consp (car results))
                (not (fn-hmc-req-of (caar results) reqs))
                (fn-hmc-results-landed-p (cdr results) reqs)))))

; FDS: each fd once, each incarnation at most once; nothing bound is closed.
(defun fn-hmc-fdsp (fds closed)
  (declare (xargs :guard t))
  (and (alistp fds)
       (true-listp closed)
       (no-duplicatesp-equal (strip-cars fds))
       (no-duplicatesp-equal (fn-hmc-fds-incs fds))
       (not (intersectp-equal (fn-hmc-fds-incs fds) closed))))

; fn-arpn-pins-of answers a natural over a pins table (the fact is local to
; arena-reader-pins; restated here for the guards).
(defthm fn-hmc-pins-of-natp
  (implies (fn-arpn-pinsp pins)
           (natp (fn-arpn-pins-of h pins)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn-arpn-pinsp fn-arpn-pins-of))))

; The pins fund every hold: at each generation named by an owner or a
; reader, the table holds at least the owners there plus the readers there.
(defun fn-hmc-funded-at-p (gs owners readers pins)
  (declare (xargs :guard (fn-arpn-pinsp pins)))
  (cond ((atom gs) t)
        (t (and (natp (car gs))
                (<= (+ (fn-rpin-count-at (car gs) owners)
                       (fn-hmc-readers-at (car gs) readers))
                    (fn-arpn-pins-of (car gs) pins))
                (fn-hmc-funded-at-p (cdr gs) owners readers pins)))))

(defun fn-hmc-cdrs (xs)
  (declare (xargs :guard t))
  (cond ((atom xs) nil)
        ((consp (car xs)) (cons (cdar xs) (fn-hmc-cdrs (cdr xs))))
        (t (fn-hmc-cdrs (cdr xs)))))

(defun fn-hmc-pairsp (xs)
  (declare (xargs :guard t))
  (cond ((atom xs) (null xs))
        (t (and (consp (car xs)) (fn-hmc-pairsp (cdr xs))))))

(defun fn-hmc-invp (st)
  (declare (xargs :guard t))
  (let ((locks (fn-hmc-locks st)) (fds (fn-hmc-fds st)) (reqs (fn-hmc-reqs st))
        (arpn (fn-hmc-arpn st)) (owners (fn-hmc-owners st)) (pass (fn-hmc-pass st))
        (readers (fn-hmc-readers st))
        (rows (fn-hmc-rows st)) (workers (fn-hmc-workers st)) (next (fn-hmc-next st))
        (results (fn-hmc-results st)) (leases (fn-hmc-leases st))
        (released (fn-hmc-released st)) (closed (fn-hmc-closed st)))
    (and (true-listp st) (equal (len st) *fn-hmc-fields*)
         (alistp locks)
         (fn-hmc-fdsp fds closed)
         (fn-arpn-okp arpn)
         (fn-arpn-pinsp (second arpn))
         (alistp owners)
         (fn-hmc-pairsp readers)
         (fn-hmc-funded-at-p (append (fn-hmc-cdrs owners) (fn-hmc-cdrs readers))
                             owners readers (second arpn))
         (or (null pass) (fn-hmc-memberp pass readers))
         (fn-hmc-rowsp rows)
         (no-duplicatesp-equal (fn-hmc-row-ids rows))
         (natp next)
         (fn-hmc-rows-below-p rows next)
         (fn-hmc-rows-open-p rows fds closed)
         (fn-hmc-workersp workers rows)
         (no-duplicatesp-equal (fn-hmc-worker-slots workers))
         (no-duplicatesp-equal (fn-hmc-busy-tokens workers))
         (fn-hmc-reqs-okp reqs fds rows leases)
         (alistp results)
         (fn-hmc-results-landed-p results reqs)
         (fn-hmc-leases-open-p leases fds closed)
         (true-listp released)
         (true-listp closed)
         (or (not (fn-hmc-ended st))
             (and (null reqs) (null rows) (null workers) (null leases) (null fds)
                  (null readers) (null owners) (null pass))))))

; -----------------------------------------------------------------------------
; The realization: each label's host call sites today (read by LOCK-CHECK:
; tools/lock_discipline_check.py --emit-realization writes
; planning/host-realization.json from this constant and --check refuses
; drift).  Function names anchor every row; no line numbers.  "layer" P/C;
; for P the A-PRIM row; "enabled" the model's enabling predicate by name;
; "locks_held" from the check's table (O owner, E extent, A pins, G gate, R
; roster, C commit, K log kernel, ...); "requires_before" the ACL2 subjects
; that must dominate the primitive on every straight-line path; "capability"
; the typed borrow the site holds across its off-lock work.
(defconst *fn-hmc-realization*
  '((:label :acquire :layer "P" :assumption "A-PRIM-MUTEX" :enabled "fn-hmc-lock-free-p"
     :sites ((:function "fnn-owner-gated" :file "host/native/owner.lisp"
              :primitive "sb-thread:with-mutex" :core nil :locks_held ("G") :requires_before nil
              :capability nil)))
    (:label :release :layer "P" :assumption "A-PRIM-MUTEX" :enabled "fn-hmc-holds-p"
     :sites ((:function "fnn-owner-gated" :file "host/native/owner.lisp"
              :primitive "sb-thread:with-mutex" :core nil :locks_held ("O") :requires_before nil
              :capability nil)))
    (:label :fd-open :layer "P" :assumption "A-PRIM-FD" :enabled "fn-hmc-boundp"
     :sites ((:function "fnn-extent-register" :file "host/native/extent.lisp"
              :primitive "fnn-open" :core "fn-owner-page-file-issue" :locks_held ("E")
              :requires_before ("fn-owner-page-file-issue") :capability nil)))
    (:label :io-begin :layer "P" :assumption "A-PRIM-PREAD" :enabled "fn-hmc-key-inc"
     :sites ((:function "fnn-extent-prefetch" :file "host/native/extent.lisp"
              :primitive "fnn-extent-pread" :core nil :locks_held ()
              :requires_before ("fn-pio-direct-admit")
              :capability (:kind "issued-row" :acquire "fnn-extent-issue-direct"
                           :release_site "fnn-extent-direct-settle"))
             (:function "fnn-extent-window-run" :file "host/native/extent.lisp"
              :primitive "fnn-extent-window-pread" :core "fn-ews-begin" :locks_held ()
              :requires_before ("fn-owner-page-window-work-permittedp")
              :capability (:kind "window-lease" :acquire "fnn-extent-issue-window"
                           :release_site "fnn-extent-window-release"))
             (:function "fnn-extent-entry-fresh" :file "host/native/extent.lisp"
              :primitive "fnn-extent-read-entry" :core "fn-owner-page-read-discovery-admit"
              :locks_held ("E") :requires_before ("fn-owner-page-read-discovery-admit")
              :capability (:kind "file-pin" :acquire "fn-owner-page-read-discovery-admit"
                           :release_site "fnn-extent-discovery-release"))))
    (:label :io-complete :layer "P" :assumption "A-PRIM-PREAD" :enabled "fn-hmc-req-of"
     :sites ((:function "fnn-extent-executor-loop" :file "host/native/extent.lisp"
              :primitive nil :core nil :locks_held ("E") :requires_before nil :capability nil)))
    (:label :crash :layer "P" :assumption "A-CRASH-IMAGE" :enabled nil :sites nil)
    (:label :issue :layer "C" :enabled "fn-pio-direct-admit"
     :sites ((:function "fnn-extent-issue-direct" :file "host/native/extent.lisp"
              :primitive nil :core "fn-pio-direct-admit" :locks_held ("O" "E")
              :requires_before nil
              :capability (:kind "issued-row" :acquire "fnn-extent-issue-direct"
                           :release_site "fnn-extent-direct-settle"))
             (:function "fnn-extent-issue-read" :file "host/native/extent.lisp"
              :primitive nil :core "fn-owner-page-read-admit" :locks_held ("O" "E")
              :requires_before nil
              :capability (:kind "issued-row" :acquire "fnn-extent-issue-read"
                           :release_site "fnn-extent-complete-read"))))
    (:label :cancel :layer "C" :enabled "fn-pio-cancel"
     :sites ((:function "fnn-extent-cancel-read" :file "host/native/extent.lisp"
              :primitive nil :core "fn-pio-cancel" :locks_held ("E") :requires_before nil
              :capability nil)))
    (:label :return :layer "C" :enabled "fn-pxe-return"
     :sites ((:function "fnn-extent-executor-loop" :file "host/native/extent.lisp"
              :primitive nil :core "fn-pxe-return" :locks_held ("E") :requires_before nil
              :capability nil)))
    (:label :settle :layer "C" :enabled "fn-pio-direct-settle"
     :sites ((:function "fnn-extent-direct-settle" :file "host/native/extent.lisp"
              :primitive nil :core "fn-pio-direct-settle" :locks_held ("O" "E")
              :requires_before nil :capability nil)
             (:function "fnn-extent-complete-read" :file "host/native/extent.lisp"
              :primitive nil :core "fn-pio-complete" :locks_held ("O" "E")
              :requires_before nil :capability nil)))
    (:label :window-acquire :layer "C" :enabled "fn-hmc-boundp"
     :sites ((:function "fnn-extent-issue-window" :file "host/native/extent.lisp"
              :primitive nil :core "fn-owner-page-window-admit" :locks_held ("E")
              :requires_before nil
              :capability (:kind "window-lease" :acquire "fnn-extent-issue-window"
                           :release_site "fnn-extent-window-release"))))
    (:label :window-release :layer "C" :enabled "fn-hmc-memberp"
     :sites ((:function "fnn-extent-window-release" :file "host/native/extent.lisp"
              :primitive nil :core "fn-owner-page-window-release" :locks_held ("E")
              :requires_before nil :capability nil)))
    (:label :discovery-acquire :layer "C" :enabled "fn-hmc-boundp"
     :sites ((:function "fnn-extent-entry-fresh" :file "host/native/extent.lisp"
              :primitive nil :core "fn-owner-page-read-discovery-admit" :locks_held ("E")
              :requires_before nil
              :capability (:kind "file-pin" :acquire "fn-owner-page-read-discovery-admit"
                           :release_site "fnn-extent-discovery-release"))))
    (:label :discovery-release :layer "C" :enabled "fn-hmc-memberp"
     :sites ((:function "fnn-extent-discovery-release" :file "host/native/extent.lisp"
              :primitive nil :core "fn-owner-page-read-discovery-release" :locks_held ("E")
              :requires_before nil :capability nil)))
    (:label :pin :layer "C" :enabled "fn-arpn-step"
     :sites ((:function "fnn-arena-pin" :file "host/native/io.lisp"
              :primitive nil :core "fn-arpn-step" :locks_held ("O" "A") :requires_before nil
              :capability (:kind "generation-pin" :acquire "fnn-arena-pin"
                           :release_site "fnn-arena-unpin"))))
    (:label :unpin :layer "C" :enabled "fn-hmc-memberp"
     :sites ((:function "fnn-arena-unpin" :file "host/native/io.lisp"
              :primitive nil :core "fn-arpn-step" :locks_held ("A") :requires_before nil
              :capability nil)))
    (:label :pass-pin :layer "C" :enabled "fn-arpn-step"
     :sites ((:function "fnn-owner-reclaim-pass" :file "host/native/owner.lisp"
              :primitive nil :core "fn-arpn-step" :locks_held ("O" "A") :requires_before nil
              :capability (:kind "generation-pin" :acquire "fnn-arena-pin"
                           :release_site "fnn-arena-unpin"))))
    (:label :capture :layer "C" :enabled "fn-rpin-step"
     :sites ((:function "fnn-owner-response-pin" :file "host/native/owner.lisp"
              :primitive nil :core "fn-rpin-step" :locks_held ("O" "A") :requires_before nil
              :capability (:kind "response-pin" :acquire "fnn-owner-response-pin"
                           :release_site "fnn-owner-response-unpin"))))
    (:label :drain :layer "C" :enabled "fn-rpin-step"
     :sites ((:function "fnn-owner-response-unpin" :file "host/native/owner.lisp"
              :primitive nil :core "fn-rpin-step" :locks_held ("A") :requires_before nil
              :capability nil)))
    (:label :retire :layer "C" :enabled "fn-arpn-step"
     :sites ((:function "fnn-log-reseat-fenced" :file "host/native/io.lisp"
              :primitive nil :core "fn-arpn-step" :locks_held ("O" "A") :requires_before nil
              :capability nil)))
    (:label :release-retired :layer "C" :enabled "fn-arpn-step"
     :sites ((:function "fnn-owner-release-pending-extents-locked" :file "host/native/owner.lisp"
              :primitive nil :core "fn-arpn-step" :locks_held ("O" "A") :requires_before nil
              :capability nil)))
    (:label :swap :layer "C" :enabled "fn-arpn-count"
     :sites ((:function "fnn-owner-reclaim-pass" :file "host/native/owner.lisp"
              :primitive nil :core "fn-owner-orcp-swap-word" :locks_held ("O" "A")
              :requires_before ("fn-owner-orcp-swap-word") :capability nil)))
    (:label :close :layer "C" :enabled "fn-pio-file-clear-p"
     :sites ((:function "fnn-extent-close" :file "host/native/extent.lisp"
              :primitive "fnn-close" :core "fn-pio-file-clear-p" :locks_held ("O" "E")
              :requires_before ("fn-pio-file-clear-p" "fn-owner-page-read-close-preview")
              :capability nil)))))

; =============================================================================
; THE THEOREMS.

; The accessors over a made state.
(defthm fn-hmc-fields-of-make
  (let ((st (fn-hmc-make locks fds reqs arpn owners pass readers rows workers next results
                         leases released closed ended)))
    (and (equal (fn-hmc-locks st) locks) (equal (fn-hmc-fds st) fds)
         (equal (fn-hmc-reqs st) reqs) (equal (fn-hmc-arpn st) arpn)
         (equal (fn-hmc-owners st) owners) (equal (fn-hmc-pass st) pass)
         (equal (fn-hmc-readers st) readers) (equal (fn-hmc-rows st) rows)
         (equal (fn-hmc-workers st) workers) (equal (fn-hmc-next st) next)
         (equal (fn-hmc-results st) results) (equal (fn-hmc-leases st) leases)
         (equal (fn-hmc-released st) released) (equal (fn-hmc-closed st) closed)
         (equal (fn-hmc-ended st) ended)
         (true-listp st) (equal (len st) 15))))

; The accessors over a set field: the field set, every other one kept.
(defthm fn-hmc-field-of-set
  (implies (and (natp i) (natp j) (true-listp st) (equal (len st) 15) (< i 15) (< j 15))
           (equal (fn-hmc-field j (fn-hmc-set i v st))
                  (if (equal i j) v (fn-hmc-field j st)))))

(defthm fn-hmc-set-keeps-shape
  (implies (and (natp i) (< i 15) (true-listp st) (equal (len st) 15))
           (and (true-listp (fn-hmc-set i v st))
                (equal (len (fn-hmc-set i v st)) 15))))

(in-theory (disable fn-hmc-field fn-hmc-set fn-hmc-make))

; The row, worker and request accessors stay closed in every proof below
; (a goal keeps fn-hmc-row-id, never its car); these bridges are :use-only.
(defthm fn-hmc-row-accessors-are-nths
  (implies (true-listp r)
           (and (equal (fn-hmc-row-id r) (nth 0 r))
                (equal (fn-hmc-row-file r) (nth 2 r))
                (equal (fn-hmc-row-phase r) (nth 6 r))
                (equal (fn-hmc-row-settledp r) (eq (nth 6 r) :settled))))
  :rule-classes nil)

(defthm fn-hmc-worker-accessors-are-nths
  (implies (true-listp w)
           (and (equal (fn-hmc-worker-slot w) (nth 0 w))
                (equal (fn-hmc-worker-phase w) (nth 2 w))
                (equal (fn-hmc-worker-token w) (nth 3 w))))
  :rule-classes nil)

(in-theory (disable fn-hmc-row-id fn-hmc-row-file fn-hmc-row-phase fn-hmc-row-settledp
                    fn-hmc-worker-slot fn-hmc-worker-phase fn-hmc-worker-token
                    fn-hmc-req-key fn-hmc-req-fd fn-hmc-req-inc))

(defthm fn-hmc-req-accessors-of-make
  (and (equal (fn-hmc-req-key (list key fd inc)) key)
       (equal (fn-hmc-req-fd (list key fd inc)) fd)
       (equal (fn-hmc-req-inc (list key fd inc)) inc))
  :hints (("Goal" :in-theory (enable fn-hmc-req-key fn-hmc-req-fd fn-hmc-req-inc))))

; The initial state satisfies the invariant (by evaluation).
(defthm fn-hmc-init-invp
  (fn-hmc-invp (fn-hmc-init)))

; -----------------------------------------------------------------------------
; Preservation, one lemma per label.  Each opens the step and the invariant
; and leans on the component books' keystones.

(local (in-theory (disable fn-arpn-step fn-arpn-okp fn-rpin-step fn-pio-direct-admit
                           fn-pio-direct-settle fn-pio-cancel fn-pxe-return
                           fn-pio-file-clear-p fn-pio-rowp fn-pxe-rowp fn-pio-token
                           fn-arpn-pins-of fn-arpn-count fn-arpn-held-p fn-rpin-count-at)))

; ---- the primitives

(defthm fn-hmc-do-acquire-keeps-invp
  (implies (and (fn-hmc-invp st) (not (fn-hmc-ended st)))
           (fn-hmc-invp (mv-nth 0 (fn-hmc-do-acquire st ev)))))

(local
 (defthm fn-hmc-alistp-of-remove1-assoc-equal
   (implies (alistp l) (alistp (remove1-assoc-equal k l)))))

(defthm fn-hmc-do-release-keeps-invp
  (implies (and (fn-hmc-invp st) (not (fn-hmc-ended st)))
           (fn-hmc-invp (mv-nth 0 (fn-hmc-do-release st ev)))))

; An fd bound to a fresh number and an unbound, unclosed incarnation keeps
; every binding, every row open and every request consistent.
(local
 (defthm fn-hmc-boundp-of-cons
   (equal (fn-hmc-boundp inc (cons (cons fd inc2) fds))
          (or (equal inc inc2) (fn-hmc-boundp inc fds)))))

(local
 (defthm fn-hmc-rows-open-p-of-fd-cons
   (implies (fn-hmc-rows-open-p rows fds closed)
            (fn-hmc-rows-open-p rows (cons (cons fd inc) fds) closed))))

(local
 (defthm fn-hmc-leases-open-p-of-fd-cons
   (implies (fn-hmc-leases-open-p leases fds closed)
            (fn-hmc-leases-open-p leases (cons (cons fd inc) fds) closed))))

(local
 (defthm fn-hmc-memberp-is-member-equal
   (implies (true-listp l)
            (equal (fn-hmc-memberp x l) (and (member-equal x l) t)))))

(local
 (defthm fn-hmc-not-assoc-not-in-strip-cars
   (implies (and (alistp fds) (not (assoc-equal fd fds)))
            (not (member-equal fd (strip-cars fds))))))

(local
 (defthm fn-hmc-fd-inc-of-cons-other
   (implies (and (alistp fds) (not (assoc-equal fd fds)))
            (equal (fn-hmc-fd-inc fd2 (cons (cons fd inc) fds))
                   (if (equal fd2 fd) inc (fn-hmc-fd-inc fd2 fds))))))

(local
 (defthm fn-hmc-reqs-okp-fd-bound
   (implies (and (fn-hmc-reqs-okp reqs fds rows leases) (member-equal q reqs))
            (equal (fn-hmc-fd-inc (fn-hmc-req-fd q) fds) (fn-hmc-req-inc q)))))

(local
 (defthm fn-hmc-reqs-okp-of-fd-cons
   (implies (and (fn-hmc-reqs-okp reqs fds rows leases)
                 (alistp fds) (not (assoc-equal fd fds)))
            (fn-hmc-reqs-okp reqs (cons (cons fd inc) fds) rows leases))
   :hints (("Goal" :induct (fn-hmc-reqs-okp reqs fds rows leases)))))

(defthm fn-hmc-do-fd-open-keeps-invp
  (implies (and (fn-hmc-invp st) (not (fn-hmc-ended st)))
           (fn-hmc-invp (mv-nth 0 (fn-hmc-do-fd-open st ev)))))

; A request begun on a key that resolves to a bound incarnation is consistent.
(local
 (defthm fn-hmc-fd-of-inc-in-strip-cars
   (implies (fn-hmc-fd-of-inc inc fds)
            (member-equal (fn-hmc-fd-of-inc inc fds) (strip-cars fds)))))

(local
 (defthm fn-hmc-assoc-of-a-key-not-in-front
   (implies (and (alistp fds) (consp fds) (not (equal fd (caar fds))))
            (equal (assoc-equal fd fds) (assoc-equal fd (cdr fds))))))

(local
 (defthm fn-hmc-found-fd-is-not-an-absent-key
   (implies (and (alistp l) (not (assoc-equal k l)) k)
            (not (equal (fn-hmc-fd-of-inc inc l) k)))
   :hints (("Goal" :cases ((fn-hmc-fd-of-inc inc l))
            :use ((:instance fn-hmc-fd-of-inc-in-strip-cars (fds l))
                  (:instance fn-hmc-not-assoc-not-in-strip-cars (fds l) (fd k)))))))

(local
 (defthm fn-hmc-fd-inc-of-fd-of-inc
   (implies (and (alistp fds) (no-duplicatesp-equal (strip-cars fds))
                 (fn-hmc-fd-of-inc inc fds))
            (equal (fn-hmc-fd-inc (fn-hmc-fd-of-inc inc fds) fds) inc))
   :hints (("Goal" :induct (fn-hmc-fd-of-inc inc fds)
            :in-theory (enable fn-hmc-fd-inc)))))

(local
 (defthm fn-hmc-results-landed-p-of-reqs-cons
   (implies (and (fn-hmc-results-landed-p results reqs)
                 (not (assoc-equal key results)))
            (fn-hmc-results-landed-p results (cons (list key fd inc) reqs)))))

(local
 (defthm fn-hmc-req-of-is-assoc-like
   (implies (and (alistp results) (fn-hmc-results-landed-p results reqs)
                 (assoc-equal key results))
            (not (fn-hmc-req-of key reqs)))))

(defthm fn-hmc-do-io-begin-keeps-invp
  (implies (and (fn-hmc-invp st) (not (fn-hmc-ended st)))
           (fn-hmc-invp (mv-nth 0 (fn-hmc-do-io-begin st ev)))))

; A completion removes a request and lands its verdict.
(local
 (defthm fn-hmc-reqs-okp-of-remove
   (implies (fn-hmc-reqs-okp reqs fds rows leases)
            (fn-hmc-reqs-okp (fn-hmc-reqs-remove key reqs) fds rows leases))))

(local
 (defthm fn-hmc-req-of-after-remove
   (equal (fn-hmc-req-of key (fn-hmc-reqs-remove key2 reqs))
          (if (equal key key2) nil (fn-hmc-req-of key reqs)))))

(local
 (defthm fn-hmc-results-landed-p-of-reqs-remove
   (implies (fn-hmc-results-landed-p results reqs)
            (fn-hmc-results-landed-p results (fn-hmc-reqs-remove key reqs)))))

(defthm fn-hmc-do-io-complete-keeps-invp
  (implies (and (fn-hmc-invp st) (not (fn-hmc-ended st)))
           (fn-hmc-invp (mv-nth 0 (fn-hmc-do-io-complete st ev)))))

(defthm fn-hmc-do-crash-keeps-invp
  (implies (and (fn-hmc-invp st) (not (fn-hmc-ended st)))
           (fn-hmc-invp (mv-nth 0 (fn-hmc-do-crash st)))))

; ---- the leases

(local
 (defthm fn-hmc-leases-open-p-of-cons
   (implies (and (fn-hmc-leases-open-p leases fds closed)
                 (member-eq kind '(:window :discovery))
                 (fn-hmc-boundp inc fds) (not (fn-hmc-memberp inc closed)))
            (fn-hmc-leases-open-p (cons (cons kind inc) leases) fds closed))))

(local
 (defthm fn-hmc-lease-names-p-of-cons
   (equal (fn-hmc-lease-names-p inc (cons (cons kind inc2) leases))
          (or (equal inc inc2) (fn-hmc-lease-names-p inc leases)))))

(local
 (defthm fn-hmc-key-inc-of-lease-cons
   (implies (fn-hmc-key-inc key rows leases)
            (equal (fn-hmc-key-inc key rows (cons (cons kind inc) leases))
                   (fn-hmc-key-inc key rows leases)))))

(local
 (defthm fn-hmc-reqs-okp-of-lease-cons
   (implies (fn-hmc-reqs-okp reqs fds rows leases)
            (fn-hmc-reqs-okp reqs fds rows (cons (cons kind inc) leases)))))

(defthm fn-hmc-do-lease-acquire-keeps-invp
  (implies (and (fn-hmc-invp st) (not (fn-hmc-ended st)) (member-eq kind '(:window :discovery)))
           (fn-hmc-invp (mv-nth 0 (fn-hmc-do-lease-acquire st ev kind)))))

(local
 (defthm fn-hmc-leases-open-p-of-remove1
   (implies (fn-hmc-leases-open-p leases fds closed)
            (fn-hmc-leases-open-p (fn-hmc-remove1 x leases) fds closed))))

; Removing one lease keeps every request consistent: a request on a lease
; key of that incarnation is refused by the release itself; a request on a
; row key does not read the leases.
(local
 (defthm fn-hmc-memberp-of-remove1-other
   (implies (and (fn-hmc-memberp y leases) (not (equal y x)))
            (fn-hmc-memberp y (fn-hmc-remove1 x leases)))))

; A request whose key is not the released lease keeps its incarnation.
(local
 (defthm fn-hmc-key-inc-of-lease-remove1
   (implies (and (fn-hmc-key-inc key rows leases)
                 (not (equal key (list (car x) (cdr x)))))
            (equal (fn-hmc-key-inc key rows (fn-hmc-remove1 x leases))
                   (fn-hmc-key-inc key rows leases)))))

(local
 (defthm fn-hmc-reqs-okp-of-lease-remove1
   (implies (and (fn-hmc-reqs-okp reqs fds rows leases)
                 (not (fn-hmc-req-of (list (car x) (cdr x)) reqs)))
            (fn-hmc-reqs-okp reqs fds rows (fn-hmc-remove1 x leases)))
   :hints (("Goal" :induct (fn-hmc-reqs-okp reqs fds rows leases)))))

(defthm fn-hmc-do-lease-release-keeps-invp
  (implies (and (fn-hmc-invp st) (not (fn-hmc-ended st)) (member-eq kind '(:window :discovery)))
           (fn-hmc-invp (mv-nth 0 (fn-hmc-do-lease-release st ev kind)))))

; ---- the generation table: retire, release, swap change no pin

; In a proof (mv-nth 0 x) is (car x) and (mv-nth 1 x) is (cadr x): the
; component books' keystones are restated in that form.
(local
 (defthm fn-hmc-arpn-okp-of-car-step
   (implies (fn-arpn-okp st)
            (fn-arpn-okp (car (fn-arpn-step st ev))))
   :hints (("Goal" :use fn-arpn-step-preserves-okp :in-theory (enable mv-nth)))))

(local
 (defthm fn-hmc-arpn-retire-keeps-pins
   (implies (fn-arpn-okp st)
            (equal (cadr (car (fn-arpn-step st (list :retire items))))
                   (cadr st)))
   :hints (("Goal" :in-theory (enable fn-arpn-step fn-arpn-okp)))))

(local
 (defthm fn-hmc-arpn-release-keeps-pins
   (implies (fn-arpn-okp st)
            (equal (cadr (car (fn-arpn-step st '(:release))))
                   (cadr st)))
   :hints (("Goal" :in-theory (enable fn-arpn-step fn-arpn-okp)))))

(local
 (defthm fn-hmc-arpn-okp-pinsp
   (implies (fn-arpn-okp st) (fn-arpn-pinsp (cadr st)))
   :hints (("Goal" :in-theory (enable fn-arpn-okp)))))

(defthm fn-hmc-do-retire-keeps-invp
  (implies (and (fn-hmc-invp st) (not (fn-hmc-ended st)))
           (fn-hmc-invp (mv-nth 0 (fn-hmc-do-retire st ev)))))

(local
 (defthm fn-hmc-items-of-true-listp
   (true-listp (fn-hmc-items-of rel))))

(defthm fn-hmc-do-release-retired-keeps-invp
  (implies (and (fn-hmc-invp st) (not (fn-hmc-ended st)))
           (fn-hmc-invp (mv-nth 0 (fn-hmc-do-release-retired st ev)))))

(defthm fn-hmc-do-swap-keeps-invp
  (implies (and (fn-hmc-invp st) (not (fn-hmc-ended st)))
           (fn-hmc-invp (mv-nth 0 (fn-hmc-do-swap st ev)))))

; ---- the rows: helpers over rows-put (rows keyed by id)

(local
 (defthm fn-hmc-row-ids-of-rows-remove
   (equal (fn-hmc-row-ids (fn-hmc-rows-remove id rows))
          (remove-equal id (fn-hmc-row-ids rows)))))

(local
 (defthm fn-hmc-member-of-remove-equal-early
   (implies (member-equal x (remove-equal y l)) (member-equal x l))))

(local
 (defthm fn-hmc-no-dup-of-remove-equal
   (implies (no-duplicatesp-equal l)
            (no-duplicatesp-equal (remove-equal x l)))))

(local
 (defthm fn-hmc-not-member-of-remove-equal
   (not (member-equal x (remove-equal x l)))))

(local
 (defthm fn-hmc-no-dup-row-ids-of-rows-put
   (implies (no-duplicatesp-equal (fn-hmc-row-ids rows))
            (no-duplicatesp-equal (fn-hmc-row-ids (fn-hmc-rows-put row rows))))))

(local
 (defthm fn-hmc-rowsp-of-rows-remove
   (implies (fn-hmc-rowsp rows) (fn-hmc-rowsp (fn-hmc-rows-remove id rows)))))

(local
 (defthm fn-hmc-rowsp-of-rows-put
   (implies (and (fn-hmc-rowsp rows) (fn-pio-rowp row))
            (fn-hmc-rowsp (fn-hmc-rows-put row rows)))))

(local
 (defthm fn-hmc-rowsp-member
   (implies (and (fn-hmc-rowsp rows) (member-equal r rows))
            (fn-pio-rowp r))))

(local
 (defthm fn-hmc-pio-rowp-true-listp
   (implies (fn-pio-rowp r) (and (true-listp r) (equal (len r) 7)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-pio-rowp)))))

(local
 (defthm fn-hmc-pxe-rowp-true-listp
   (implies (fn-pxe-rowp w) (and (true-listp w) (equal (len w) 4)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-pxe-rowp)))))

(local
 (defthm fn-hmc-row-of-is-a-member
   (implies (fn-hmc-row-of key rows)
            (member-equal (fn-hmc-row-of key rows) rows))))

(local
 (defthm fn-hmc-row-of-has-the-token
   (implies (fn-hmc-row-of key rows)
            (equal (fn-pio-token (fn-hmc-row-of key rows)) key))))

(local
 (defthm fn-hmc-row-of-is-a-true-list
   (implies (fn-hmc-row-of key rows)
            (true-listp (fn-hmc-row-of key rows)))))

(local
 (defthm fn-hmc-car-of-token
   (implies (true-listp r)
            (equal (car (fn-pio-token r)) (fn-hmc-row-id r)))
   :hints (("Goal" :in-theory (enable fn-pio-token fn-hmc-row-id)))))

(local
 (defthm fn-hmc-member-row-id
   (implies (member-equal r rows)
            (member-equal (fn-hmc-row-id r) (fn-hmc-row-ids rows)))))

(local
 (defthm fn-hmc-rowsp-member-true-listp
   (implies (and (fn-hmc-rowsp rows) (member-equal r rows))
            (true-listp r))))

(local
 (defthm fn-hmc-pio-rowp-shape
   (implies (fn-pio-rowp r)
            (and (consp r) (natp (fn-hmc-row-id r)) (natp (fn-hmc-row-file r))))
   :hints (("Goal" :in-theory (enable fn-pio-rowp fn-hmc-row-id fn-hmc-row-file)))))

(local
 (defthm fn-hmc-rowsp-member-shape
   (implies (and (fn-hmc-rowsp rows) (member-equal r rows))
            (and (consp r) (natp (fn-hmc-row-id r))))))

; Two members of a list of distinct ids with the same id are the same row.
(local
 (defthm fn-hmc-same-id-same-row
   (implies (and (fn-hmc-rowsp rows) (no-duplicatesp-equal (fn-hmc-row-ids rows))
                 (member-equal r1 rows) (member-equal r2 rows)
                 (equal (fn-hmc-row-id r1) (fn-hmc-row-id r2)))
            (equal r1 r2))
   :rule-classes nil
   :hints (("Goal" :induct (fn-hmc-rowsp rows)))))

; ... so two tokens found in the rows with the same id are the same token.
(local
 (defthm fn-hmc-same-id-same-token
   (implies (and (fn-hmc-rowsp rows) (no-duplicatesp-equal (fn-hmc-row-ids rows))
                 (fn-hmc-row-of k1 rows) (fn-hmc-row-of k2 rows)
                 (equal (nth 0 k1) (nth 0 k2)))
            (equal k1 k2))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn-hmc-same-id-same-row
                                    (r1 (fn-hmc-row-of k1 rows)) (r2 (fn-hmc-row-of k2 rows)))
                         (:instance fn-hmc-row-of-has-the-token (key k1))
                         (:instance fn-hmc-row-of-has-the-token (key k2))
                         (:instance fn-hmc-car-of-token (r (fn-hmc-row-of k1 rows)))
                         (:instance fn-hmc-car-of-token (r (fn-hmc-row-of k2 rows))))
            :do-not-induct t))))

; A removal by id drops exactly the rows of that id: looking a token up in
; the remainder answers nil for that id and the old row otherwise.
(local
 (defthm fn-hmc-row-of-rows-remove
   (implies (fn-hmc-rowsp rows)
            (equal (fn-hmc-row-of key (fn-hmc-rows-remove id rows))
                   (if (equal (nth 0 key) id) nil (fn-hmc-row-of key rows))))
   :hints (("Goal" :induct (fn-hmc-rows-remove id rows)))))

(local
 (defthm fn-hmc-row-of-rows-put
   (implies (and (fn-hmc-rowsp rows) (true-listp row))
            (equal (fn-hmc-row-of key (fn-hmc-rows-put row rows))
                   (cond ((equal key (fn-pio-token row)) row)
                         ((equal (nth 0 key) (fn-hmc-row-id row)) nil)
                         (t (fn-hmc-row-of key rows)))))))

; With both the looked-up token and the put row present, the put row is
; found only under its own token (the other case needs two rows of one id).
(local
 (defthm fn-hmc-row-of-rows-put-when-present
   (implies (and (fn-hmc-rowsp rows) (no-duplicatesp-equal (fn-hmc-row-ids rows))
                 (fn-pio-rowp row)
                 (fn-hmc-row-of key rows)
                 (fn-hmc-row-of (fn-pio-token row) rows))
            (equal (fn-hmc-row-of key (fn-hmc-rows-put row rows))
                   (if (equal key (fn-pio-token row)) row (fn-hmc-row-of key rows))))
   :hints (("Goal" :use ((:instance fn-hmc-same-id-same-token (k1 key) (k2 (fn-pio-token row))))
            :do-not-induct t))))

; A key no row of ROWS answers (a lease key) is not answered after a put of
; a real row either: the put row's token is a list of naturals.
(local
 (defthm fn-hmc-row-of-rows-put-when-absent
   (implies (and (fn-hmc-rowsp rows) (fn-pio-rowp row)
                 (not (fn-hmc-row-of key rows))
                 (not (natp (nth 0 key))))
            (not (fn-hmc-row-of key (fn-hmc-rows-put row rows))))
   :hints (("Goal" :do-not-induct t))))

(local
 (defthm fn-hmc-rows-open-p-member
   (implies (and (fn-hmc-rows-open-p rows fds closed) (member-equal r rows)
                 (not (fn-hmc-row-settledp r)))
            (and (fn-hmc-boundp (fn-hmc-row-file r) fds)
                 (not (fn-hmc-memberp (fn-hmc-row-file r) closed))))))

(local
 (defthm fn-hmc-rows-open-p-of-rows-remove
   (implies (fn-hmc-rows-open-p rows fds closed)
            (fn-hmc-rows-open-p (fn-hmc-rows-remove id rows) fds closed))))

(local
 (defthm fn-hmc-rows-open-p-of-rows-put
   (implies (and (fn-hmc-rows-open-p rows fds closed)
                 (or (fn-hmc-row-settledp row)
                     (and (fn-hmc-boundp (fn-hmc-row-file row) fds)
                          (not (fn-hmc-memberp (fn-hmc-row-file row) closed)))))
            (fn-hmc-rows-open-p (fn-hmc-rows-put row rows) fds closed))))

(local
 (defthm fn-hmc-rows-below-p-of-rows-remove
   (implies (fn-hmc-rows-below-p rows next)
            (fn-hmc-rows-below-p (fn-hmc-rows-remove id rows) next))))

(local
 (defthm fn-hmc-rows-below-p-of-rows-put
   (implies (and (fn-hmc-rows-below-p rows next) (natp next)
                 (natp (fn-hmc-row-id row)) (< (fn-hmc-row-id row) next))
            (fn-hmc-rows-below-p (fn-hmc-rows-put row rows) next))))

(local
 (defthm fn-hmc-rows-below-p-member
   (implies (and (fn-hmc-rows-below-p rows next) (member-equal r rows))
            (and (natp (fn-hmc-row-id r)) (natp next) (< (fn-hmc-row-id r) next)))))

(local (in-theory (disable fn-hmc-rows-put fn-hmc-rows-remove)))

; fn-pio-cancel keeps the token, the id and the file, and settles nothing.
(local
 (defthm fn-hmc-cancel-keeps-identity
   (and (equal (fn-hmc-row-id (fn-pio-cancel r tok)) (fn-hmc-row-id r))
        (equal (fn-hmc-row-file (fn-pio-cancel r tok)) (fn-hmc-row-file r))
        (equal (fn-hmc-row-settledp (fn-pio-cancel r tok)) (fn-hmc-row-settledp r))
        (implies (true-listp r) (true-listp (fn-pio-cancel r tok)))
        (implies (true-listp r)
                 (equal (fn-pio-token (fn-pio-cancel r tok)) (fn-pio-token r))))
   :hints (("Goal" :in-theory (enable fn-pio-cancel fn-pio-token fn-pio-rowp
                                      fn-hmc-row-id fn-hmc-row-file fn-hmc-row-phase
                                      fn-hmc-row-settledp)))))

; A put of an unsettled row that replaces a row of the same token (the
; cancel) keeps every worker's and every request's row.
(local
 (defthm fn-hmc-workersp-of-rows-put-same-token
   (implies (and (fn-hmc-rowsp rows) (no-duplicatesp-equal (fn-hmc-row-ids rows))
                 (fn-hmc-workersp workers rows)
                 (fn-pio-rowp row) (not (fn-hmc-row-settledp row))
                 (fn-hmc-row-of (fn-pio-token row) rows))
            (fn-hmc-workersp workers (fn-hmc-rows-put row rows)))
   :hints (("Goal" :induct (fn-hmc-workersp workers rows)
            :in-theory (disable fn-hmc-row-of-rows-put)))))

(local
 (defthm fn-hmc-key-inc-of-rows-put-same-token
   (implies (and (fn-hmc-rowsp rows) (no-duplicatesp-equal (fn-hmc-row-ids rows))
                 (fn-pio-rowp row) (not (fn-hmc-row-settledp row))
                 (fn-hmc-row-of (fn-pio-token row) rows)
                 (not (fn-hmc-row-settledp (fn-hmc-row-of (fn-pio-token row) rows)))
                 (equal (fn-hmc-row-file row)
                        (fn-hmc-row-file (fn-hmc-row-of (fn-pio-token row) rows)))
                 (fn-hmc-key-inc key rows leases))
            (equal (fn-hmc-key-inc key (fn-hmc-rows-put row rows) leases)
                   (fn-hmc-key-inc key rows leases)))
   :hints (("Goal" :in-theory (e/d (fn-hmc-key-inc) (fn-hmc-row-of-rows-put))
            :do-not-induct t
            :cases ((fn-hmc-row-of key rows))))))

(local
 (defthm fn-hmc-reqs-okp-of-rows-put-same-token
   (implies (and (fn-hmc-rowsp rows) (no-duplicatesp-equal (fn-hmc-row-ids rows))
                 (fn-hmc-reqs-okp reqs fds rows leases)
                 (fn-pio-rowp row) (not (fn-hmc-row-settledp row))
                 (fn-hmc-row-of (fn-pio-token row) rows)
                 (not (fn-hmc-row-settledp (fn-hmc-row-of (fn-pio-token row) rows)))
                 (equal (fn-hmc-row-file row)
                        (fn-hmc-row-file (fn-hmc-row-of (fn-pio-token row) rows))))
            (fn-hmc-reqs-okp reqs fds (fn-hmc-rows-put row rows) leases))
   :hints (("Goal" :induct (fn-hmc-reqs-okp reqs fds rows leases)
            :in-theory (disable fn-hmc-key-inc fn-hmc-row-of-rows-put)))))

(defthm fn-hmc-do-cancel-keeps-invp
  (implies (and (fn-hmc-invp st) (not (fn-hmc-ended st)))
           (fn-hmc-invp (mv-nth 0 (fn-hmc-do-cancel st ev)))))

; ---- the generation pins: funding under pin, unpin, capture, drain

; The arena table's events, opened: a pin adds one at the current
; generation; an unpin of a held generation removes one there.
(local
 (defthm fn-hmc-arpn-pin-form
   (implies (fn-arpn-okp st)
            (and (equal (cadr (fn-arpn-step st '(:pin))) (car st))
                 (equal (car (car (fn-arpn-step st '(:pin)))) (car st))
                 (equal (cadr (car (fn-arpn-step st '(:pin))))
                        (fn-arpn-pin-at (car st) (cadr st)))))
   :hints (("Goal" :in-theory (enable fn-arpn-step fn-arpn-okp)))))

(local
 (defthm fn-hmc-arpn-unpin-form
   (implies (and (fn-arpn-okp st) (natp g) (fn-arpn-held-p g (cadr st)))
            (and (equal (cadr (fn-arpn-step st (list :unpin g))) :ok)
                 (equal (car (car (fn-arpn-step st (list :unpin g)))) (car st))
                 (equal (cadr (car (fn-arpn-step st (list :unpin g))))
                        (fn-arpn-unpin-at g (cadr st)))))
   :hints (("Goal" :in-theory (enable fn-arpn-step fn-arpn-okp)))))

; Response holds, opened: a fresh acquire adds (cid . cur) and pins; a
; release of a held response removes it and unpins its generation.
(local
 (defthm fn-hmc-rpin-acquire-form
   (implies (and (fn-arpn-okp st) (natp cid) (not (fn-rpin-owner cid owners)))
            (and (equal (caddr (fn-rpin-step owners st (list :acquire cid))) :acquired)
                 (equal (car (fn-rpin-step owners st (list :acquire cid)))
                        (cons (cons cid (car st)) owners))
                 (equal (cadr (fn-rpin-step owners st (list :acquire cid)))
                        (car (fn-arpn-step st '(:pin))))))
   :hints (("Goal" :in-theory (enable fn-rpin-step)))))

(local
 (defthm fn-hmc-rpin-release-form
   (implies (and (fn-arpn-okp st) (fn-rpin-owner cid owners)
                 (natp (cdr (fn-rpin-owner cid owners)))
                 (fn-arpn-held-p (cdr (fn-rpin-owner cid owners)) (cadr st)))
            (and (equal (caddr (fn-rpin-step owners st (list :release cid))) :released)
                 (equal (car (fn-rpin-step owners st (list :release cid)))
                        (fn-rpin-remove cid owners))
                 (equal (cadr (fn-rpin-step owners st (list :release cid)))
                        (car (fn-arpn-step st (list :unpin (cdr (fn-rpin-owner cid owners))))))))
   :hints (("Goal" :in-theory (enable fn-rpin-step)))))

; The funding predicate pointwise, and its universal consequence: once it
; holds over every generation an owner or a reader names, it holds at every
; generation (the others have no holds).
(defun fn-hmc-funded-g-p (g owners readers pins)
  (declare (xargs :guard (fn-arpn-pinsp pins)))
  (<= (+ (fn-rpin-count-at g owners) (fn-hmc-readers-at g readers))
      (fn-arpn-pins-of g pins)))

(local
 (defthm fn-hmc-funded-at-p-member
   (implies (and (fn-hmc-funded-at-p gs owners readers pins) (member-equal g gs))
            (fn-hmc-funded-g-p g owners readers pins))))

(local
 (defthm fn-hmc-count-at-zero-when-absent
   (implies (not (member-equal g (fn-hmc-cdrs owners)))
            (equal (fn-rpin-count-at g owners) 0))
   :hints (("Goal" :in-theory (enable fn-rpin-count-at)))))

(local
 (defthm fn-hmc-readers-at-zero-when-absent
   (implies (not (member-equal g (fn-hmc-cdrs readers)))
            (equal (fn-hmc-readers-at g readers) 0))))

(local
 (defthm fn-hmc-funded-at-p-of-append
   (equal (fn-hmc-funded-at-p (append a b) owners readers pins)
          (and (fn-hmc-funded-at-p a owners readers pins)
               (fn-hmc-funded-at-p b owners readers pins)))))

(local
 (defthm fn-hmc-funded-universal
   (implies (and (fn-arpn-pinsp pins)
                 (fn-hmc-funded-at-p (append (fn-hmc-cdrs owners) (fn-hmc-cdrs readers))
                                     owners readers pins))
            (fn-hmc-funded-g-p g owners readers pins))
   :hints (("Goal" :cases ((member-equal g (fn-hmc-cdrs owners))
                           (member-equal g (fn-hmc-cdrs readers)))
            :in-theory (disable fn-hmc-funded-at-p-of-append)
            :use ((:instance fn-hmc-funded-at-p-member
                             (gs (append (fn-hmc-cdrs owners) (fn-hmc-cdrs readers)))))))))

(defun fn-hmc-nat-listp (xs)
  (declare (xargs :guard t))
  (cond ((atom xs) t)
        (t (and (natp (car xs)) (fn-hmc-nat-listp (cdr xs))))))

(local
 (defthm fn-hmc-funded-at-p-nat-listp
   (implies (fn-hmc-funded-at-p gs owners readers pins)
            (fn-hmc-nat-listp gs))))

(local
 (defthm fn-hmc-nat-listp-of-append
   (equal (fn-hmc-nat-listp (append a b))
          (and (fn-hmc-nat-listp a) (fn-hmc-nat-listp b)))))

; The counts under the four table edits.
(local
 (defthm fn-hmc-readers-at-of-cons
   (equal (fn-hmc-readers-at g (cons (cons tid g2) readers))
          (+ (if (equal g g2) 1 0) (fn-hmc-readers-at g readers)))))

(local
 (defthm fn-hmc-count-at-of-cons
   (equal (fn-rpin-count-at g (cons (cons cid g2) owners))
          (+ (if (equal g g2) 1 0) (fn-rpin-count-at g owners)))
   :hints (("Goal" :in-theory (enable fn-rpin-count-at)))))

(local
 (defthm fn-hmc-readers-at-of-remove1
   (implies (fn-hmc-memberp (cons tid g2) readers)
            (equal (fn-hmc-readers-at g (fn-hmc-remove1 (cons tid g2) readers))
                   (- (fn-hmc-readers-at g readers) (if (equal g g2) 1 0))))))

(local
 (defthm fn-hmc-readers-at-natp
   (natp (fn-hmc-readers-at g readers))
   :rule-classes :type-prescription))

(local
 (defthm fn-hmc-count-at-natp
   (natp (fn-rpin-count-at g owners))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable fn-rpin-count-at)))))

(local
 (defthm fn-hmc-count-at-of-rpin-remove
   (implies (and (alistp owners) (fn-rpin-owner cid owners))
            (equal (fn-rpin-count-at g (fn-rpin-remove cid owners))
                   (- (fn-rpin-count-at g owners)
                      (if (equal g (cdr (fn-rpin-owner cid owners))) 1 0))))
   :hints (("Goal" :in-theory (enable fn-rpin-count-at fn-rpin-remove fn-rpin-owner)))))

(local
 (defthm fn-hmc-owner-counts-at-its-generation
   (implies (and (alistp owners) (fn-rpin-owner cid owners))
            (< 0 (fn-rpin-count-at (cdr (fn-rpin-owner cid owners)) owners)))
   :hints (("Goal" :in-theory (enable fn-rpin-count-at fn-rpin-owner)))))

; A funded table stays funded through each edit, at every generation.
(local
 (defthm fn-hmc-funded-g-p-after-pin
   (implies (and (fn-arpn-pinsp pins) (fn-hmc-funded-g-p g owners readers pins))
            (fn-hmc-funded-g-p g owners (cons (cons tid g2) readers)
                               (fn-arpn-pin-at g2 pins)))))

(local
 (defthm fn-hmc-funded-g-p-after-capture
   (implies (and (fn-arpn-pinsp pins) (fn-hmc-funded-g-p g owners readers pins))
            (fn-hmc-funded-g-p g (cons (cons cid g2) owners) readers
                               (fn-arpn-pin-at g2 pins)))))

(local
 (defthm fn-hmc-funded-g-p-after-unpin
   (implies (and (fn-arpn-pinsp pins) (fn-hmc-funded-g-p g owners readers pins)
                 (fn-hmc-memberp (cons tid g2) readers))
            (fn-hmc-funded-g-p g owners (fn-hmc-remove1 (cons tid g2) readers)
                               (fn-arpn-unpin-at g2 pins)))))

(local
 (defthm fn-hmc-funded-g-p-after-drain
   (implies (and (fn-arpn-pinsp pins) (alistp owners)
                 (fn-hmc-funded-g-p g owners readers pins)
                 (fn-rpin-owner cid owners))
            (fn-hmc-funded-g-p g (fn-rpin-remove cid owners) readers
                               (fn-arpn-unpin-at (cdr (fn-rpin-owner cid owners)) pins)))))

; ... so funded-at-p holds over any list of naturals after the edit, from
; the universal fact before it.
(local
 (defthm fn-hmc-funded-at-p-after-pin
   (implies (and (fn-arpn-pinsp pins) (fn-hmc-nat-listp gs)
                 (fn-hmc-funded-at-p (append (fn-hmc-cdrs owners) (fn-hmc-cdrs readers))
                                     owners readers pins))
            (fn-hmc-funded-at-p gs owners (cons (cons tid g2) readers)
                                (fn-arpn-pin-at g2 pins)))
   :hints (("Goal" :induct (fn-hmc-nat-listp gs)
            :in-theory (disable fn-hmc-funded-g-p fn-hmc-funded-at-p-of-append)))))

(local
 (defthm fn-hmc-funded-at-p-after-capture
   (implies (and (fn-arpn-pinsp pins) (fn-hmc-nat-listp gs)
                 (fn-hmc-funded-at-p (append (fn-hmc-cdrs owners) (fn-hmc-cdrs readers))
                                     owners readers pins))
            (fn-hmc-funded-at-p gs (cons (cons cid g2) owners) readers
                                (fn-arpn-pin-at g2 pins)))
   :hints (("Goal" :induct (fn-hmc-nat-listp gs)
            :in-theory (disable fn-hmc-funded-g-p fn-hmc-funded-at-p-of-append)))))

(local
 (defthm fn-hmc-funded-at-p-after-unpin
   (implies (and (fn-arpn-pinsp pins) (fn-hmc-nat-listp gs)
                 (fn-hmc-memberp (cons tid g2) readers)
                 (fn-hmc-funded-at-p (append (fn-hmc-cdrs owners) (fn-hmc-cdrs readers))
                                     owners readers pins))
            (fn-hmc-funded-at-p gs owners (fn-hmc-remove1 (cons tid g2) readers)
                                (fn-arpn-unpin-at g2 pins)))
   :hints (("Goal" :induct (fn-hmc-nat-listp gs)
            :in-theory (disable fn-hmc-funded-g-p fn-hmc-funded-at-p-of-append)))))

(local
 (defthm fn-hmc-funded-at-p-after-drain
   (implies (and (fn-arpn-pinsp pins) (fn-hmc-nat-listp gs) (alistp owners)
                 (fn-rpin-owner cid owners)
                 (fn-hmc-funded-at-p (append (fn-hmc-cdrs owners) (fn-hmc-cdrs readers))
                                     owners readers pins))
            (fn-hmc-funded-at-p gs (fn-rpin-remove cid owners) readers
                                (fn-arpn-unpin-at (cdr (fn-rpin-owner cid owners)) pins)))
   :hints (("Goal" :induct (fn-hmc-nat-listp gs)
            :in-theory (disable fn-hmc-funded-g-p fn-hmc-funded-at-p-of-append)))))

(local
 (defthm fn-hmc-cdrs-of-cons
   (equal (fn-hmc-cdrs (cons (cons a g) xs)) (cons g (fn-hmc-cdrs xs)))))

(local
 (defthm fn-hmc-cdrs-of-remove1-nat-listp
   (implies (fn-hmc-nat-listp (fn-hmc-cdrs xs))
            (fn-hmc-nat-listp (fn-hmc-cdrs (fn-hmc-remove1 x xs))))))

(local
 (defthm fn-hmc-cdrs-of-rpin-remove-nat-listp
   (implies (fn-hmc-nat-listp (fn-hmc-cdrs owners))
            (fn-hmc-nat-listp (fn-hmc-cdrs (fn-rpin-remove cid owners))))
   :hints (("Goal" :in-theory (enable fn-rpin-remove)))))

(local
 (defthm fn-hmc-pairsp-of-remove1
   (implies (fn-hmc-pairsp xs) (fn-hmc-pairsp (fn-hmc-remove1 x xs)))))

(local
 (defthm fn-hmc-alistp-of-rpin-remove
   (implies (alistp owners) (alistp (fn-rpin-remove cid owners)))
   :hints (("Goal" :in-theory (enable fn-rpin-remove)))))

(local
 (defthm fn-hmc-arpn-okp-of-pin-form
   (implies (fn-arpn-okp st)
            (fn-arpn-okp (list (car st) (fn-arpn-pin-at (car st) (cadr st)) (caddr st))))
   :hints (("Goal" :use ((:instance fn-hmc-arpn-okp-of-car-step (ev '(:pin))))
            :in-theory (disable fn-hmc-arpn-okp-of-car-step)))))

(local
 (defthm fn-hmc-arpn-okp-of-unpin-form
   (implies (and (fn-arpn-okp st) (natp g) (fn-arpn-held-p g (cadr st)))
            (fn-arpn-okp (list (car st) (fn-arpn-unpin-at g (cadr st)) (caddr st))))
   :hints (("Goal" :use ((:instance fn-hmc-arpn-okp-of-car-step (ev (list :unpin g))))
            :in-theory (disable fn-hmc-arpn-okp-of-car-step)))))

(local
 (defthm fn-hmc-arpn-okp-car-natp
   (implies (fn-arpn-okp st) (natp (car st)))
   :hints (("Goal" :in-theory (enable fn-arpn-okp)))))

(defthm fn-hmc-do-pin-keeps-invp
  (implies (and (fn-hmc-invp st) (not (fn-hmc-ended st)))
           (fn-hmc-invp (mv-nth 0 (fn-hmc-do-pin st ev)))))

(defthm fn-hmc-do-pass-pin-keeps-invp
  (implies (and (fn-hmc-invp st) (not (fn-hmc-ended st)))
           (fn-hmc-invp (mv-nth 0 (fn-hmc-do-pass-pin st ev)))))

(defthm fn-hmc-do-unpin-keeps-invp
  (implies (and (fn-hmc-invp st) (not (fn-hmc-ended st)))
           (fn-hmc-invp (mv-nth 0 (fn-hmc-do-unpin st ev)))))

(defthm fn-hmc-do-capture-keeps-invp
  (implies (and (fn-hmc-invp st) (not (fn-hmc-ended st)))
           (fn-hmc-invp (mv-nth 0 (fn-hmc-do-capture st ev)))))

(local
 (defthm fn-hmc-rpin-owner-generation-natp
   (implies (and (alistp owners) (fn-hmc-nat-listp (fn-hmc-cdrs owners))
                 (fn-rpin-owner cid owners))
            (natp (cdr (fn-rpin-owner cid owners))))
   :hints (("Goal" :in-theory (enable fn-rpin-owner)))))

(local
 (defthm fn-hmc-rpin-owner-generation-held
   (implies (and (alistp owners) (fn-arpn-pinsp pins) (fn-rpin-owner cid owners)
                 (fn-hmc-funded-at-p (append (fn-hmc-cdrs owners) (fn-hmc-cdrs readers))
                                     owners readers pins))
            (fn-arpn-held-p (cdr (fn-rpin-owner cid owners)) pins))
   :hints (("Goal" :in-theory (enable fn-arpn-held-p)
            :use ((:instance fn-hmc-funded-universal (g (cdr (fn-rpin-owner cid owners)))))))))

(defthm fn-hmc-do-drain-keeps-invp
  (implies (and (fn-hmc-invp st) (not (fn-hmc-ended st)))
           (fn-hmc-invp (mv-nth 0 (fn-hmc-do-drain st ev)))))
