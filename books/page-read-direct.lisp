; fn: the unfunded cold line's issued reads (lane cold-read-ownership,
; 2026-10-01; Codex r31 F1/F2; GPT-6's first fallible-I/O row: "every
; completion of an issued page read preserves request/generation identity
; and resource ownership, including error, cancellation and late delivery").
;
; Until the funded pool is installed from the profile (design 2026-10-01
; section 4 stage 6), the page-read pool runs in its :offline context
; (host/page-read-host.lisp fn-owner-page-read-direct-mode).  The served cold
; line used to spawn one thread per miss whose pread held nothing retirement
; honoured.  It now reuses the pool's ownership layer without the ledger:
;
;   * an fn-pio row (books/page-read-ownership.lisp) per issued read, kept in
;     the host's issued table (host/native/extent.lisp *fnn-extent-issued*),
;     names the file INCARNATION (a process-local id never reused) and the
;     whole extent identity; fnn-extent-close closes a file only when
;     fn-pio-file-clear-p finds no unsettled row naming it, so the row is the
;     read's pin on its file generation until the I/O actually completes;
;   * the read runs on one of a fixed set of persistent workers (fn-pxe rows,
;     books/page-read-executor.lisp); admission needs an idle worker, so a
;     stalled disk occupies at most every worker and the next miss is refused
;     by name (:read-resources-unavailable, the owner's 403 "cold read
;     resources unavailable; try again later": books/owner-resource-line.lisp),
;     never given a new thread;
;   * a timeout cancels the row (fn-pio-cancel: publication revoked, the
;     worker keeps the row and the file); only the worker's actual return
;     lets the owner settle (fn-pio-direct-settle), and a fault it reports is
;     a fault even after the line was answered.
;
; fn-pio-direct-admit and fn-pio-direct-settle are the two transitions the
; host calls (host/native/extent.lisp fnn-extent-issue-direct and
; fnn-extent-direct-settle).
(in-package "ACL2")
(include-book "page-read-executor")
(include-book "profile-limits") ; the worker count is a row there

(local
 (defthm fn-pird-ledger-nth-unfolds
   (implies (natp n) (equal (fn-prl-nth n x) (nth n x)))
   :hints (("Goal" :induct (fn-prl-nth n x) :in-theory (enable fn-prl-nth nth)))))

; The persistent workers of the unfunded cold line (a work bound: how many
; reads may be in flight at once, never a bound on stored data).
(defconst *fn-pio-direct-workers* (fn-profile-limit :cold-workers))

(defun fn-pio-direct-workers ()
  (declare (xargs :guard t))
  *fn-pio-direct-workers*)

; NEXT is the direct read counter (NIL before the first read); the host keeps
; it as it keeps the file counter, advanced only here.  WORKER is the idle
; worker row the host offers, NIL when every worker is busy.
; Answer: (mv WORD NEXT1 TOKEN ROW WORKER1).
(defun fn-pio-direct-admit (next cid file eoff elen trailer worker)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (enable fn-pio-issue fn-pio-token)))))
  (let ((n (if (null next) 0 next)))
    (cond ((not (and (natp n) (natp cid) (posp file)
                     (natp eoff) (natp elen) (natp trailer)))
           (mv :invalid-read-identity next nil nil worker))
          ((null worker) (mv :read-resources-unavailable next nil nil worker))
          (t (mv-let (next1 row) (fn-pio-issue n cid file eoff elen trailer)
               (let ((token (fn-pio-token row)))
                 (mv-let (word w1) (fn-pxe-assign worker token)
                   (if (equal word :assigned)
                       (mv :admitted next1 token row w1)
                     (mv word next nil nil worker)))))))))

; The ledger-free commit: the worker returned THIS job and its I/O row is
; settled under the same token.
(defun fn-pxe-commit-direct (w io token)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (enable fn-pio-rowp fn-prl-nth)))))
  (if (and (fn-pxe-rowp w) (equal (fn-prl-nth 2 w) :returned)
           (equal token (fn-prl-nth 3 w))
           (fn-pio-rowp io) (equal (fn-prl-nth 6 io) :settled)
           (equal token (fn-pio-token io)))
      (mv :committed (list (fn-prl-nth 0 w) (fn-prl-nth 1 w) :idle nil))
    (mv :stale-job w)))

; The owner's settlement of one returned read, under owner -> extent.
; Answer: (mv ANSWER ROW1 WORKER1), ANSWER :publish, :cancelled,
; (:fault VERDICT) or :stale.  Anything but :stale settles the row (the file
; pin is released) and idles the worker; :stale changes neither.
(defun fn-pio-direct-settle (row worker token verdict)
  (declare (xargs :guard t))
  (mv-let (row1 answer) (fn-pio-complete row token verdict)
    (if (equal answer :stale)
        (mv :stale row worker)
      (mv-let (word w1) (fn-pxe-commit-direct worker row1 token)
        (if (equal word :committed)
            (mv answer row1 w1)
          (mv :stale row worker))))))

;; The row and worker shapes the settlement theorems open, as lemmas, so
;; no theorem below opens fn-pio-rowp or fn-pxe-rowp itself.
(local
 (defthm fn-pird-settled-row-keeps-its-token
   (implies (fn-pio-rowp r)
            (and (equal (fn-pio-token (append (fn-pio-token r) (list x))) (fn-pio-token r))
                 (equal (nth 6 (append (fn-pio-token r) (list x))) x)))
   :hints (("Goal" :in-theory (enable fn-pio-rowp fn-pio-token)))))

(local
 (defthm fn-pird-row-phase-is-one-of-three
   (implies (and (fn-pio-rowp r) (not (equal (nth 6 r) :settled))
                 (not (equal (nth 6 r) :cancelled)))
            (equal (nth 6 r) :issued))
   :hints (("Goal" :in-theory (enable fn-pio-rowp)))))

(local
 (defthm fn-pird-settled-row-is-a-row
   (implies (fn-pio-rowp r)
            (fn-pio-rowp (append (fn-pio-token r) (list :settled))))
   :hints (("Goal" :in-theory (enable fn-pio-rowp fn-pio-token)))))

(local
 (defthm fn-pird-settled-row-clears-its-file
   (implies (fn-pio-rowp r)
            (fn-pio-file-clear-p (nth 2 (fn-pio-token r))
                                 (list (append (fn-pio-token r) (list :settled)))))
   :hints (("Goal" :in-theory (enable fn-pio-rowp fn-pio-token fn-pio-file-clear-p)))))

(local (in-theory (enable fn-pio-direct-settle fn-pio-complete fn-pxe-commit-direct)))

; KEYSTONE.  Admission binds an idle worker to exactly the issued identity:
; the token names the request, the file incarnation and the whole extent;
; the row is :issued for that token; the worker runs that token; the counter
; advances.  No idle worker -> refused by name, nothing issued.
(defthm fn-pio-direct-admit-binds-an-idle-worker-to-the-issued-identity
  (implies (equal (mv-nth 0 (fn-pio-direct-admit next cid file eoff elen trailer worker))
                  :admitted)
           (let ((n (if (null next) 0 next))
                 (token (mv-nth 2 (fn-pio-direct-admit next cid file eoff elen trailer worker)))
                 (row (mv-nth 3 (fn-pio-direct-admit next cid file eoff elen trailer worker)))
                 (w1 (mv-nth 4 (fn-pio-direct-admit next cid file eoff elen trailer worker))))
             (and (fn-pxe-rowp worker) (equal (nth 2 worker) :idle)
                  (equal token (list n cid file eoff elen trailer))
                  (fn-pio-rowp row) (equal (fn-pio-token row) token)
                  (equal (nth 6 row) :issued)
                  (equal (nth 0 w1) (nth 0 worker))
                  (equal (nth 2 w1) :running) (equal (nth 3 w1) token)
                  (equal (mv-nth 1 (fn-pio-direct-admit next cid file eoff elen trailer worker))
                         (+ 1 n)))))
  :hints (("Goal" :in-theory (enable fn-pio-direct-admit fn-pio-issue fn-pio-token fn-pio-rowp
                                     fn-pxe-assign fn-pxe-rowp)))
  :rule-classes nil)

(defthm fn-pio-direct-admit-without-an-idle-worker-is-refused
  (implies (not (equal (mv-nth 0 (fn-pio-direct-admit next cid file eoff elen trailer worker))
                       :admitted))
           (and (equal (mv-nth 1 (fn-pio-direct-admit next cid file eoff elen trailer worker)) next)
                (equal (mv-nth 2 (fn-pio-direct-admit next cid file eoff elen trailer worker)) nil)
                (equal (mv-nth 3 (fn-pio-direct-admit next cid file eoff elen trailer worker)) nil)
                (equal (mv-nth 4 (fn-pio-direct-admit next cid file eoff elen trailer worker)) worker)))
  :hints (("Goal" :in-theory (enable fn-pio-direct-admit fn-pxe-assign)))
  :rule-classes nil)

; KEYSTONE.  Publication only for the issued identity, never after a timeout:
; the row was :issued (not cancelled) for exactly TOKEN, the read verified,
; the worker had returned exactly that job; the row is settled and the
; worker idle in the same slot.
(defthm fn-pio-direct-settle-publishes-only-the-issued-identity
  (implies (equal (mv-nth 0 (fn-pio-direct-settle row worker token verdict)) :publish)
           (let ((row1 (mv-nth 1 (fn-pio-direct-settle row worker token verdict)))
                 (w1 (mv-nth 2 (fn-pio-direct-settle row worker token verdict))))
             (and (fn-pio-rowp row) (equal token (fn-pio-token row))
                  (equal (nth 6 row) :issued) (equal verdict :ok)
                  (fn-pxe-rowp worker) (equal (nth 2 worker) :returned)
                  (equal (nth 3 worker) token)
                  (equal (fn-pio-token row1) token) (equal (nth 6 row1) :settled)
                  (equal (nth 0 w1) (nth 0 worker)) (equal (nth 2 w1) :idle))))
  :rule-classes nil)

; KEYSTONE.  Every non-stale settlement names its outcome by the observation:
; a failed read is a fault whether or not its request timed out (an error is
; never a timeout and is always observed); a verified read whose request
; timed out is :cancelled (no insert); the row settles, releasing the file.
(defthm fn-pio-direct-settle-observes-every-outcome
  (implies (not (equal (mv-nth 0 (fn-pio-direct-settle row worker token verdict)) :stale))
           (let ((answer (mv-nth 0 (fn-pio-direct-settle row worker token verdict)))
                 (row1 (mv-nth 1 (fn-pio-direct-settle row worker token verdict)))
                 (w1 (mv-nth 2 (fn-pio-direct-settle row worker token verdict))))
             (and (equal answer
                         (cond ((not (equal verdict :ok)) (list :fault verdict))
                               ((equal (nth 6 row) :cancelled) :cancelled)
                               (t :publish)))
                  (equal (fn-pio-token row1) token) (equal (nth 6 row1) :settled)
                  (fn-pio-file-clear-p (nth 2 token) (list row1))
                  (equal (nth 2 w1) :idle))))
  :rule-classes nil)

; KEYSTONE.  A late, duplicate or foreign completion changes nothing: a
; token that is not the row's (another request, a reused worker's next job,
; another file generation), a row already settled, or a worker that has not
; returned this job -- the row (so the file pin) and the worker stay as they
; were, and nothing is published.
(defthm fn-pio-direct-settle-stale-changes-nothing
  (implies (or (not (fn-pio-rowp row)) (not (equal token (fn-pio-token row)))
               (equal (nth 6 row) :settled)
               (not (fn-pxe-rowp worker)) (not (equal (nth 2 worker) :returned))
               (not (equal (nth 3 worker) token)))
           (equal (mv-list 3 (fn-pio-direct-settle row worker token verdict))
                  (list :stale row worker)))
  :rule-classes nil)

; KEYSTONE.  Settlement happens once: whatever the first delivery did, a
; second delivery of any completion for the same token to its result is
; stale, so nothing publishes or releases twice.  (Proved first with the
; hypothesis that the first delivery was not stale; the weakened statement
; was then proved, so the hypothesis is gone: a stale first delivery returns
; its inputs, and staleness does not depend on the verdict.)
(defthm fn-pio-direct-settle-happens-once
  (let ((row1 (mv-nth 1 (fn-pio-direct-settle row worker token verdict)))
        (w1 (mv-nth 2 (fn-pio-direct-settle row worker token verdict))))
    (equal (mv-list 3 (fn-pio-direct-settle row1 w1 token verdict2))
           (list :stale row1 w1)))
  :rule-classes nil)

; KEYSTONE.  The pin outlives the timeout: an admitted read's row, cancelled
; or not, keeps its file from closing until a non-stale settlement.
(defthm fn-pio-direct-cancelled-read-still-pins-its-file
  (implies (equal (mv-nth 0 (fn-pio-direct-admit next cid file eoff elen trailer worker))
                  :admitted)
           (let* ((token (mv-nth 2 (fn-pio-direct-admit next cid file eoff elen trailer worker)))
                  (row (mv-nth 3 (fn-pio-direct-admit next cid file eoff elen trailer worker))))
             (and (not (fn-pio-file-clear-p file (cons row rows)))
                  (not (fn-pio-file-clear-p file (cons (fn-pio-cancel row token) rows))))))
  :hints (("Goal" :in-theory (enable fn-pio-direct-admit fn-pio-issue fn-pio-token fn-pio-rowp
                                     fn-pio-cancel fn-pio-file-clear-p fn-pxe-assign)))
  :rule-classes nil)

(in-theory (disable fn-pio-direct-admit fn-pxe-commit-direct fn-pio-direct-settle))
