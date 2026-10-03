; fn: the unfunded cold line's issued reads (lane cold-read-ownership,
; 2026-10-01; Codex r31 F1/F2; GPT-6's first fallible-I/O row: "every
; completion of an issued page read preserves request/generation identity
; and resource ownership, including error, cancellation and late delivery").
; Re-expressed through def-holder (lane def-holder, 2026-10-03): the file
; incarnation a read pins is a declared resource, held by the read's token.
;
; Until the funded pool is installed from the profile (design 2026-10-01
; section 4 stage 6), the page-read pool runs in its :offline context
; (host/page-read-host.lisp fn-owner-page-read-direct-mode).  The served cold
; line used to spawn one thread per miss whose pread held nothing retirement
; honoured.  It now reuses the pool's ownership layer without the ledger:
;
;   * an fn-pio row (books/page-read-ownership.lisp) per issued read, in the
;     ISSUED table this book threads (an alist TOKEN -> ROW the host keeps as
;     ACL2 returns it, host/native/extent.lisp *fnn-extent-issued*; at most
;     the worker count long), names the file INCARNATION (a process-local id
;     never reused) and the whole extent identity;
;   * the HOLDS table (books/def-holder.lisp fn-hd-ident-step: a token per
;     holder) counts, per file, the tokens of the reads that pin it: the
;     admit holds the file for the read's token, the settlement drops it,
;     and fnn-extent-close asks whether a file is QUIET (no token) -- one
;     lookup, never a walk of the issued rows.  KEYSTONE
;     fn-pio-direct-quiet-is-clear: under the carried agreement of the two
;     tables a file is quiet exactly when no issued row names it (the walk
;     fn-pio-file-clear-p the host used to run), so the row is still the
;     read's pin on its file generation until the I/O actually completes;
;   * the read runs on one of a fixed set of persistent workers (fn-pxe rows,
;     books/page-read-executor.lisp); admission needs an idle worker, so a
;     stalled disk occupies at most every worker and the next miss is refused
;     by name (:read-resources-unavailable, the owner's 403 "cold read
;     resources unavailable; try again later": books/owner-resource-line.lisp),
;     never given a new thread;
;   * a timeout cancels the row (fn-pio-direct-cancel: publication revoked,
;     the worker keeps the row, the file and the hold); only the worker's
;     actual return lets the owner settle (fn-pio-direct-settle), and a fault
;     it reports is a fault even after the line was answered.
;
; fn-pio-direct-admit, fn-pio-direct-cancel, fn-pio-direct-settle and
; fn-pio-direct-quiet-p are the four entries the host calls
; (host/native/extent.lisp fnn-extent-issue-direct, fnn-extent-cancel-read,
; fnn-extent-direct-settle, fnn-extent-close).  Uncertain, refused and
; accepted stay distinct: :stale (a late, duplicate or foreign completion),
; :unheld (the tables disagree: the row is issued but no hold carries its
; token -- an invariant breach the host faults on, never a silent settle),
; :hold-refused (a token already held or issued: nothing is issued).
(in-package "ACL2")
(include-book "page-read-executor")
(include-book "profile-limits") ; the worker count is a row there
(include-book "def-holder")     ; the holds table

; Exported by books/def-holder.lisp (redundant here once that book carries
; them): a key that is not a natural is refused whatever the verb; a key's
; tokens have no duplicates, so a dropped token is not among the rest.
(defthm fn-hd-ident-step-refuses-a-bad-key
  (implies (not (natp (cadr ev)))
           (equal (mv-list 2 (fn-hd-ident-step table ev)) (list table :refused)))
  :hints (("Goal" :in-theory (enable fn-hd-ident-step))))

(defthm fn-hd-tokens-of-shape
  (implies (fn-hd-identp table)
           (and (true-listp (fn-hd-tokens-of k table))
                (no-duplicatesp-equal (fn-hd-tokens-of k table))))
  :hints (("Goal" :induct (fn-hd-identp table)
           :in-theory (enable fn-hd-identp fn-hd-tokens-of fn-hd-ident-row))))

(defthm fn-hd-no-member-of-remove1-of-no-dups
  (implies (no-duplicatesp-equal x)
           (not (member-equal a (remove1-equal a x)))))

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

; ---------------------------------------------------------------------------
; The two tables.

(defun fn-pio-issued-row (token issued)
  (declare (xargs :guard t))
  (cond ((atom issued) nil)
        ((and (consp (car issued)) (equal (caar issued) token)) (cdar issued))
        (t (fn-pio-issued-row token (cdr issued)))))

(local
 (defthm fn-pird-rowp-true-listp
   (implies (fn-pio-rowp r) (true-listp r))
   :hints (("Goal" :in-theory (enable fn-pio-rowp)))
   :rule-classes (:rewrite :forward-chaining)))

; ISSUED: an alist TOKEN -> ROW, each row's token its key, no token twice,
; no row :settled (a settled row leaves the table).
(defun fn-pio-issuedp (issued)
  (declare (xargs :guard t))
  (if (atom issued)
      (null issued)
    (and (consp (car issued))
         (fn-pio-rowp (cdar issued))
         (equal (caar issued) (fn-pio-token (cdar issued)))
         (not (equal (nth 6 (cdar issued)) :settled))
         (not (fn-pio-issued-row (caar issued) (cdr issued)))
         (fn-pio-issuedp (cdr issued)))))

(defun fn-pio-issued-remove (token issued)
  (declare (xargs :guard t))
  (cond ((atom issued) nil)
        ((and (consp (car issued)) (equal (caar issued) token)) (cdr issued))
        (t (cons (car issued) (fn-pio-issued-remove token (cdr issued))))))

(defun fn-pio-issued-put (token row issued)
  (declare (xargs :guard t))
  (cond ((atom issued) (list (cons token row)))
        ((and (consp (car issued)) (equal (caar issued) token)) (cons (cons token row) (cdr issued)))
        (t (cons (car issued) (fn-pio-issued-put token row (cdr issued))))))

(defun fn-pio-issued-rows (issued)
  (declare (xargs :guard t))
  (cond ((atom issued) nil)
        ((consp (car issued)) (cons (cdar issued) (fn-pio-issued-rows (cdr issued))))
        (t (fn-pio-issued-rows (cdr issued)))))

; The file a token names (its third element; guard t: a token of another
; shape names no file).
(defun fn-pio-token-file (token)
  (declare (xargs :guard t))
  (and (consp token) (consp (cdr token)) (consp (cddr token)) (car (cddr token))))

; The agreement of the two tables: every issued row's token holds its file,
; and every token holding a file is an issued row's naming that file.
; Membership with guard t (the holds table's token list is a true list
; under fn-hd-identp, which a walker over an arbitrary value cannot assume).
(defun fn-pio-token-member (token tokens)
  (declare (xargs :guard t))
  (cond ((atom tokens) nil)
        ((equal (car tokens) token) t)
        (t (fn-pio-token-member token (cdr tokens)))))

(defthm fn-pio-token-member-is-member
  (iff (fn-pio-token-member token tokens) (member-equal token tokens)))

(defun fn-pio-issued-in-holds-p (issued holds)
  (declare (xargs :guard t))
  (cond ((atom issued) t)
        ((consp (car issued))
         (and (fn-pio-token-member (caar issued)
                                   (fn-hd-tokens-of (fn-pio-token-file (caar issued)) holds))
              (fn-pio-issued-in-holds-p (cdr issued) holds)))
        (t (fn-pio-issued-in-holds-p (cdr issued) holds))))

(defun fn-pio-tokens-in-issued-p (file tokens issued)
  (declare (xargs :guard t))
  (cond ((atom tokens) t)
        (t (and (equal (fn-pio-token-file (car tokens)) file)
                (fn-pio-issued-row (car tokens) issued)
                (fn-pio-tokens-in-issued-p file (cdr tokens) issued)))))

(defun fn-pio-holds-in-issued-p (holds issued)
  (declare (xargs :guard t))
  (cond ((atom holds) t)
        ((consp (car holds))
         (and (fn-pio-tokens-in-issued-p (caar holds) (cdar holds) issued)
              (fn-pio-holds-in-issued-p (cdr holds) issued)))
        (t (fn-pio-holds-in-issued-p (cdr holds) issued))))

(defun fn-pio-direct-okp (issued holds)
  (declare (xargs :guard t))
  (and (fn-pio-issuedp issued)
       (fn-hd-identp holds)
       (fn-pio-issued-in-holds-p issued holds)
       (fn-pio-holds-in-issued-p holds issued)))

; ---------------------------------------------------------------------------
; The entries.

; NEXT is the direct read counter (NIL before the first read); the host keeps
; it as it keeps the file counter, advanced only here.  WORKER is the idle
; worker row the host offers, NIL when every worker is busy.
; Answer: (mv WORD NEXT1 TOKEN ROW WORKER1 ISSUED1 HOLDS1).
(defun fn-pio-direct-admit (next cid file eoff elen trailer worker issued holds)
  (declare (xargs :guard (fn-hd-identp holds)
                  :guard-hints (("Goal" :in-theory (enable fn-pio-issue fn-pio-token)))))
  (let ((n (if (null next) 0 next)))
    (cond ((not (and (natp n) (natp cid) (posp file)
                     (natp eoff) (natp elen) (natp trailer)))
           (mv :invalid-read-identity next nil nil worker issued holds))
          ((null worker) (mv :read-resources-unavailable next nil nil worker issued holds))
          (t (mv-let (next1 row) (fn-pio-issue n cid file eoff elen trailer)
               (let ((token (fn-pio-token row)))
                 (mv-let (word w1) (fn-pxe-assign worker token)
                   (if (not (equal word :assigned))
                       (mv word next nil nil worker issued holds)
                     (mv-let (holds1 held) (fn-hd-ident-step holds (list :hold file token))
                       (if (or (not (equal held :held)) (fn-pio-issued-row token issued))
                           (mv :hold-refused next nil nil worker issued holds)
                         (mv :admitted next1 token row w1
                             (fn-pio-issued-put token row issued) holds1)))))))))))

; The timeout: the row's publication revoked; the worker, the file and the
; hold are kept (host/native/extent.lisp fnn-extent-cancel-read).
(defun fn-pio-direct-cancel (token issued)
  (declare (xargs :guard t))
  (let ((row (fn-pio-issued-row token issued)))
    (if row
        (fn-pio-issued-put token (fn-pio-cancel row token) issued)
      issued)))

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
; Answer: (mv ANSWER ROW1 WORKER1 ISSUED1 HOLDS1), ANSWER :publish,
; :cancelled, (:fault VERDICT), :stale or :unheld.  Anything but :stale and
; :unheld settles the row (removed from ISSUED: the file pin is released),
; drops the token's hold and idles the worker; :stale changes nothing;
; :unheld (the row is issued but no hold carries its token) changes nothing
; and is an invariant breach the host faults on.
(defun fn-pio-direct-settle (token worker verdict issued holds)
  (declare (xargs :guard (fn-hd-identp holds)))
  (let ((row (fn-pio-issued-row token issued)))
    (mv-let (row1 answer) (fn-pio-complete row token verdict)
      (if (equal answer :stale)
          (mv :stale row worker issued holds)
        (mv-let (word w1) (fn-pxe-commit-direct worker row1 token)
          (if (not (equal word :committed))
              (mv :stale row worker issued holds)
            (mv-let (holds1 dropped)
              (fn-hd-ident-step holds (list :drop (nth 2 token) token))
              (if (not (equal dropped :dropped))
                  (mv :unheld row worker issued holds)
                (mv answer row1 w1 (fn-pio-issued-remove token issued) holds1)))))))))

; The close's question: is FILE held by no read?  One lookup.
(defun fn-pio-direct-quiet-p (file holds)
  (declare (xargs :guard t))
  (atom (fn-hd-tokens-of file holds)))

(defun fn-pio-direct-initial ()
  (declare (xargs :guard t))
  (mv nil nil))

; ---------------------------------------------------------------------------
; The declaration: the file incarnation is the resource, the read its holder.

; What the two callees never answer (their words are fixed sets): the
; branches the entries relay a callee's word through are then never the
; entries' own words.
(local
 (defthm fn-pird-assign-words
   (and (not (equal (mv-nth 0 (fn-pxe-assign w token)) :admitted))
        (not (equal (mv-nth 0 (fn-pxe-assign w token)) :hold-refused))
        (not (equal (car (fn-pxe-assign w token)) :admitted))
        (not (equal (car (fn-pxe-assign w token)) :hold-refused)))
   :hints (("Goal" :in-theory (enable fn-pxe-assign)))))

(local
 (defthm fn-pird-complete-words
   (and (not (equal (mv-nth 1 (fn-pio-complete r token verdict)) :unheld))
        (not (equal (mv-nth 1 (fn-pio-complete r token verdict)) :publish-refused))
        (iff (equal (mv-nth 1 (fn-pio-complete r token verdict)) :stale)
             (not (and (fn-pio-rowp r) (equal token (fn-pio-token r))
                       (not (equal (nth 6 r) :settled))))))
   :hints (("Goal" :in-theory (enable fn-pio-complete)))))

; A row's token names the row's file, a natural.
(local
 (defthm fn-pird-token-file-of-token
   (implies (fn-pio-rowp r)
            (and (equal (fn-pio-token-file (fn-pio-token r)) (nth 2 r))
                 (natp (nth 2 (fn-pio-token r)))
                 (natp (nth 2 r))))
   :hints (("Goal" :in-theory (enable fn-pio-rowp fn-pio-token)))))

; A put row is among the rows; a row naming an unsettled file keeps the
; file from being clear.
(local
 (defthm fn-pird-put-row-is-a-row-of-put
   (member-equal row (fn-pio-issued-rows (fn-pio-issued-put tok row issued)))
   :hints (("Goal" :induct (fn-pio-issued-put tok row issued)))))

(local
 (defthm fn-pird-named-row-not-clear
   (implies (and (member-equal row rows) (fn-pio-rowp row)
                 (equal (nth 2 row) file) (not (equal (nth 6 row) :settled)))
            (not (fn-pio-file-clear-p file rows)))
   :hints (("Goal" :in-theory (enable fn-pio-file-clear-p)))))

; The issued table after a put: the row at that token, the others as they were.
(local
 (defthm fn-pird-issued-row-of-put
   (equal (fn-pio-issued-row tok (fn-pio-issued-put tok2 row issued))
          (if (equal tok tok2) row (fn-pio-issued-row tok issued)))
   :hints (("Goal" :induct (fn-pio-issued-put tok2 row issued)))))

(local
 (defthm fn-pird-admit-holds-lemma
   (implies (fn-hd-identp holds)
            (equal (mv-nth 6 (fn-pio-direct-admit next cid file eoff elen trailer worker issued holds))
                   (if (equal (mv-nth 0 (fn-pio-direct-admit next cid file eoff elen trailer worker issued holds))
                              :admitted)
                       (mv-nth 0 (fn-hd-ident-step
                                  holds (list :hold file (list (if (null next) 0 next) cid file eoff elen trailer))))
                     holds)))
   :hints (("Goal" :in-theory (e/d (fn-pio-issue fn-pio-token) (fn-hd-ident-step fn-pxe-assign fn-pio-issued-row))))
   :rule-classes nil))

(local
 (defthm fn-pird-settle-drops-lemma
   (implies (fn-hd-identp holds)
            (equal (mv-nth 4 (fn-pio-direct-settle token worker verdict issued holds))
                   (if (not (member-equal (mv-nth 0 (fn-pio-direct-settle token worker verdict issued holds))
                                          '(:stale :unheld)))
                       (mv-nth 0 (fn-hd-ident-step holds (list :drop (nth 2 token) token)))
                     holds)))
   :hints (("Goal" :in-theory (disable fn-hd-ident-step fn-pio-complete fn-pxe-commit-direct fn-pio-issued-row)))
   :rule-classes nil))

(def-holder fn-pio-file-holds
  :shape :identified
  :key "a durable file incarnation (fn-pio-file-issue: a process-local id never reused), held by the token of each cold read issued against it until that read's actual completion settles"
  :holders ((cold-read
             :acquire (fn-pio-direct-admit fn-pird-admit-holds-lemma
                       :table 8 :result (mv-nth 6 _)
                       :key file
                       :token (list (if (null next) 0 next) cid file eoff elen trailer)
                       :ok (equal (mv-nth 0 _) :admitted))
             :release (fn-pio-direct-settle fn-pird-settle-drops-lemma
                       :table 4 :result (mv-nth 4 _)
                       :key (nth 2 token)
                       :token token
                       :ok (not (member-equal (mv-nth 0 _) '(:stale :unheld)))))
            (cold-worker :root t :in (fnn-extent-prefetch fnn-extent-executor-job)
                         :status (:excluded "the worker takes the descriptor under the extent lock and preads off it; fnn-extent-close asks fn-pio-direct-quiet-p first, so no descriptor closes under a pread (the read's token holds the file until the worker's actual return settles it)"))
            (history-image :root t :in (fnn-state-checkpoint-adopt-image fn-pgs-fill-realize fnn-owner-release-extents)
                           :status (:excluded "the history image's file id (*fnn-extent-image-id*, registered at the open) is preread off the lock by fn-pgs-fill-realize for the process's life and is never retired: fnn-owner-release-extents faults by name before retiring anything if that id is among the dropped or the previous checkpoint (c05 finding F1: a checked exclusion in place of a docstring)")))
  :effect (:process-local "the tables are host memory (host/native/extent.lisp *fnn-extent-issued*, *fnn-extent-file-holds*), both empty at fnn-extent-direct-start (fn-pio-direct-initial); a death between :fn-pio-file-holds-decided (the settlement answered) and :fn-pio-file-holds-released (the row removed, the worker idled) loses the process; descriptors are not durable state")
  :complete-by "fn-pio-direct-admit and fn-pio-direct-settle are the only functions of the world that call fn-hd-ident-step on this table (def-holder-check's walk); fn-pio-direct-cancel and fn-pio-direct-quiet-p read it; the host's sites are fnn-extent-issue-direct, fnn-extent-cancel-read, fnn-extent-direct-settle, fnn-extent-close (tools/holder_check.py)")

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

(local (in-theory (enable fn-pio-direct-settle fn-pio-complete fn-pxe-commit-direct)))

; The admitted branch, once: when the admit answers :admitted, every value
; it returns in terms of the callees' (so the keystones below open nothing
; of the admit itself).
(local
 (defthm fn-pird-admitted-shape
   (implies (equal (mv-nth 0 (fn-pio-direct-admit next cid file eoff elen trailer worker issued holds))
                   :admitted)
            (let* ((n (if (null next) 0 next))
                   (token (list n cid file eoff elen trailer))
                   (row (list n cid file eoff elen trailer :issued)))
              (and (natp n) (natp cid) (posp file) (natp eoff) (natp elen) (natp trailer)
                   worker
                   (equal (mv-nth 0 (fn-pxe-assign worker token)) :assigned)
                   (equal (mv-nth 1 (fn-hd-ident-step holds (list :hold file token))) :held)
                   (not (fn-pio-issued-row token issued))
                   (equal (mv-nth 1 (fn-pio-direct-admit next cid file eoff elen trailer worker issued holds))
                          (+ 1 n))
                   (equal (mv-nth 2 (fn-pio-direct-admit next cid file eoff elen trailer worker issued holds))
                          token)
                   (equal (mv-nth 3 (fn-pio-direct-admit next cid file eoff elen trailer worker issued holds))
                          row)
                   (equal (mv-nth 4 (fn-pio-direct-admit next cid file eoff elen trailer worker issued holds))
                          (mv-nth 1 (fn-pxe-assign worker token)))
                   (equal (mv-nth 5 (fn-pio-direct-admit next cid file eoff elen trailer worker issued holds))
                          (fn-pio-issued-put token row issued))
                   (equal (mv-nth 6 (fn-pio-direct-admit next cid file eoff elen trailer worker issued holds))
                          (mv-nth 0 (fn-hd-ident-step holds (list :hold file token)))))))
   :hints (("Goal" :in-theory (e/d (fn-pio-direct-admit fn-pio-issue fn-pio-token)
                                   (fn-hd-ident-step fn-pxe-assign fn-pio-issued-row
                                    fn-pio-issued-put))))
   :rule-classes nil))

; The row the admit issues is a row with that token.
(local
 (defthm fn-pird-issued-row-shape
   (implies (and (natp n) (natp cid) (posp file) (natp eoff) (natp elen) (natp trailer))
            (and (fn-pio-rowp (list n cid file eoff elen trailer :issued))
                 (fn-pio-rowp (list n cid file eoff elen trailer :cancelled))
                 (equal (fn-pio-token (list n cid file eoff elen trailer :issued))
                        (list n cid file eoff elen trailer))))
   :hints (("Goal" :in-theory (enable fn-pio-rowp fn-pio-token)))))

; KEYSTONE.  Admission binds an idle worker to exactly the issued identity:
; the token names the request, the file incarnation and the whole extent;
; the row is :issued for that token and is the issued table's row at that
; token; the worker runs that token; the file is held by the token; the
; counter advances.  No idle worker -> refused by name, nothing issued.
(defthm fn-pio-direct-admit-binds-an-idle-worker-to-the-issued-identity
  (implies (and (fn-hd-identp holds)
                (equal (mv-nth 0 (fn-pio-direct-admit next cid file eoff elen trailer worker issued holds))
                       :admitted))
           (let ((n (if (null next) 0 next))
                 (token (mv-nth 2 (fn-pio-direct-admit next cid file eoff elen trailer worker issued holds)))
                 (row (mv-nth 3 (fn-pio-direct-admit next cid file eoff elen trailer worker issued holds)))
                 (w1 (mv-nth 4 (fn-pio-direct-admit next cid file eoff elen trailer worker issued holds)))
                 (issued1 (mv-nth 5 (fn-pio-direct-admit next cid file eoff elen trailer worker issued holds)))
                 (holds1 (mv-nth 6 (fn-pio-direct-admit next cid file eoff elen trailer worker issued holds))))
             (and (fn-pxe-rowp worker) (equal (nth 2 worker) :idle)
                  (equal token (list n cid file eoff elen trailer))
                  (fn-pio-rowp row) (equal (fn-pio-token row) token)
                  (equal (nth 6 row) :issued)
                  (equal (fn-pio-issued-row token issued1) row)
                  (not (fn-pio-issued-row token issued))
                  (member-equal token (fn-hd-tokens-of file holds1))
                  (not (member-equal token (fn-hd-tokens-of file holds)))
                  (equal (nth 0 w1) (nth 0 worker))
                  (equal (nth 2 w1) :running) (equal (nth 3 w1) token)
                  (equal (mv-nth 1 (fn-pio-direct-admit next cid file eoff elen trailer worker issued holds))
                         (+ 1 n)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-pxe-assign fn-pxe-rowp fn-pird-issued-row-of-put)
                           (fn-pio-direct-admit fn-hd-ident-step fn-pio-issued-row fn-pio-issued-put
                            fn-hd-ident-hold-adds-exactly-its-token
                            fn-hd-ident-duplicate-hold-is-refused fn-pio-rowp fn-pio-token mv-nth))
           :use ((:instance fn-pird-admitted-shape)
                 (:instance fn-pird-issued-row-shape (n (if (null next) 0 next)))
                 (:instance fn-hd-ident-hold-adds-exactly-its-token
                            (table holds) (k file) (h file)
                            (tok (list (if (null next) 0 next) cid file eoff elen trailer)))
                 (:instance fn-hd-ident-duplicate-hold-is-refused
                            (table holds) (k file)
                            (tok (list (if (null next) 0 next) cid file eoff elen trailer))))))
  :rule-classes nil)

(defthm fn-pio-direct-admit-without-an-idle-worker-is-refused
  (implies (not (equal (mv-nth 0 (fn-pio-direct-admit next cid file eoff elen trailer worker issued holds))
                       :admitted))
           (and (equal (mv-nth 1 (fn-pio-direct-admit next cid file eoff elen trailer worker issued holds)) next)
                (equal (mv-nth 2 (fn-pio-direct-admit next cid file eoff elen trailer worker issued holds)) nil)
                (equal (mv-nth 3 (fn-pio-direct-admit next cid file eoff elen trailer worker issued holds)) nil)
                (equal (mv-nth 4 (fn-pio-direct-admit next cid file eoff elen trailer worker issued holds)) worker)
                (equal (mv-nth 5 (fn-pio-direct-admit next cid file eoff elen trailer worker issued holds)) issued)
                (equal (mv-nth 6 (fn-pio-direct-admit next cid file eoff elen trailer worker issued holds)) holds)))
  :hints (("Goal" :in-theory (e/d (fn-pio-direct-admit fn-pxe-assign) (fn-hd-ident-step))))
  :rule-classes nil)

; A removed token is gone (the table carries no token twice).
(local
 (defthm fn-pird-issued-row-of-remove
   (equal (fn-pio-issued-row token (fn-pio-issued-remove token issued))
          (if (fn-pio-issuedp issued) nil (fn-pio-issued-row token (fn-pio-issued-remove token issued))))
   :hints (("Goal" :induct (fn-pio-issued-remove token issued)))
   :rule-classes nil))

(local
 (defthm fn-pird-issued-row-of-remove-under-issuedp
   (implies (fn-pio-issuedp issued)
            (not (fn-pio-issued-row token (fn-pio-issued-remove token issued))))
   :hints (("Goal" :induct (fn-pio-issued-remove token issued)))))

; KEYSTONE.  Publication only for the issued identity, never after a timeout:
; the issued table's row at TOKEN was :issued (not cancelled) for exactly
; TOKEN, the read verified, the worker had returned exactly that job, the
; token held its file; the row is settled and gone from the table (the
; table carries no token twice: fn-pio-issuedp, part of the carried
; agreement), the hold dropped, the worker idle in the same slot.
(defthm fn-pio-direct-settle-publishes-only-the-issued-identity
  (implies (and (fn-pio-issuedp issued) (fn-hd-identp holds)
                (equal (mv-nth 0 (fn-pio-direct-settle token worker verdict issued holds)) :publish))
           (let ((row (fn-pio-issued-row token issued))
                 (row1 (mv-nth 1 (fn-pio-direct-settle token worker verdict issued holds)))
                 (w1 (mv-nth 2 (fn-pio-direct-settle token worker verdict issued holds)))
                 (issued1 (mv-nth 3 (fn-pio-direct-settle token worker verdict issued holds)))
                 (holds1 (mv-nth 4 (fn-pio-direct-settle token worker verdict issued holds))))
             (and (fn-pio-rowp row) (equal token (fn-pio-token row))
                  (equal (nth 6 row) :issued) (equal verdict :ok)
                  (fn-pxe-rowp worker) (equal (nth 2 worker) :returned)
                  (equal (nth 3 worker) token)
                  (member-equal token (fn-hd-tokens-of (nth 2 token) holds))
                  (equal (fn-pio-token row1) token) (equal (nth 6 row1) :settled)
                  (not (fn-pio-issued-row token issued1))
                  (not (member-equal token (fn-hd-tokens-of (nth 2 token) holds1)))
                  (equal (nth 0 w1) (nth 0 worker)) (equal (nth 2 w1) :idle))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-hd-ident-step fn-hd-ident-drop-removes-exactly-its-token
                               fn-hd-ident-drop-of-absent-token-is-refused
                               fn-pio-issued-row fn-pio-issued-remove fn-pio-issued-put mv-nth)
           :use ((:instance fn-hd-ident-drop-removes-exactly-its-token
                            (table holds) (k (nth 2 token)) (h (nth 2 token)) (tok token))
                 (:instance fn-hd-ident-drop-of-absent-token-is-refused
                            (table holds) (k (nth 2 token)) (tok token))
                 (:instance fn-hd-ident-step-refuses-a-bad-key
                            (table holds) (ev (list :drop (nth 2 token) token)))
                 (:instance fn-pird-token-file-of-token
                            (r (fn-pio-issued-row token issued))))))
  :rule-classes nil)

; KEYSTONE.  Every settlement that is neither stale nor unheld names its
; outcome by the observation: a failed read is a fault whether or not its
; request timed out (an error is never a timeout and is always observed); a
; verified read whose request timed out is :cancelled (no insert); the row
; settles and leaves the table, the hold is dropped: the file is released by
; this read.
(defthm fn-pio-direct-settle-observes-every-outcome
  (implies (and (fn-pio-issuedp issued) (fn-hd-identp holds)
                (not (member-equal (mv-nth 0 (fn-pio-direct-settle token worker verdict issued holds))
                                   '(:stale :unheld))))
           (let ((answer (mv-nth 0 (fn-pio-direct-settle token worker verdict issued holds)))
                 (row (fn-pio-issued-row token issued))
                 (row1 (mv-nth 1 (fn-pio-direct-settle token worker verdict issued holds)))
                 (w1 (mv-nth 2 (fn-pio-direct-settle token worker verdict issued holds)))
                 (issued1 (mv-nth 3 (fn-pio-direct-settle token worker verdict issued holds)))
                 (holds1 (mv-nth 4 (fn-pio-direct-settle token worker verdict issued holds))))
             (and (equal answer
                         (cond ((not (equal verdict :ok)) (list :fault verdict))
                               ((equal (nth 6 row) :cancelled) :cancelled)
                               (t :publish)))
                  (equal (fn-pio-token row1) token) (equal (nth 6 row1) :settled)
                  (not (fn-pio-issued-row token issued1))
                  (not (member-equal token (fn-hd-tokens-of (nth 2 token) holds1)))
                  (equal (nth 2 w1) :idle))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-hd-ident-step fn-hd-ident-drop-removes-exactly-its-token
                               fn-hd-ident-drop-of-absent-token-is-refused
                               fn-pio-issued-row fn-pio-issued-remove fn-pio-issued-put mv-nth)
           :use ((:instance fn-hd-ident-drop-removes-exactly-its-token
                            (table holds) (k (nth 2 token)) (h (nth 2 token)) (tok token))
                 (:instance fn-hd-ident-drop-of-absent-token-is-refused
                            (table holds) (k (nth 2 token)) (tok token))
                 (:instance fn-hd-ident-step-refuses-a-bad-key
                            (table holds) (ev (list :drop (nth 2 token) token)))
                 (:instance fn-pird-token-file-of-token
                            (r (fn-pio-issued-row token issued))))))
  :rule-classes nil)

; KEYSTONE.  A late, duplicate or foreign completion changes nothing: a
; token the issued table does not hold (another request, a reused worker's
; next job, another file generation, a row already settled and gone), or a
; worker that has not returned this job -- the tables (so the file pin) and
; the worker stay as they were, and nothing is published.
(defthm fn-pio-direct-settle-stale-changes-nothing
  (implies (or (not (fn-pio-rowp (fn-pio-issued-row token issued)))
               (not (equal token (fn-pio-token (fn-pio-issued-row token issued))))
               (equal (nth 6 (fn-pio-issued-row token issued)) :settled)
               (not (fn-pxe-rowp worker)) (not (equal (nth 2 worker) :returned))
               (not (equal (nth 3 worker) token)))
           (equal (mv-list 5 (fn-pio-direct-settle token worker verdict issued holds))
                  (list :stale (fn-pio-issued-row token issued) worker issued holds)))
  :hints (("Goal" :in-theory (disable fn-hd-ident-step)))
  :rule-classes nil)

; KEYSTONE.  Settlement happens once: whatever the first delivery did, a
; second delivery of any completion for the same token to its result is
; stale -- or, after an :unheld first delivery (the tables disagree: an
; invariant breach the host faults on), :unheld again -- so nothing
; publishes or releases twice.  No hypothesis: the worker gates the second
; delivery (a committed worker is idle, an uncommitted one unchanged), so a
; malformed issued table changes nothing here; the statement with
; (fn-pio-issuedp issued) was proved first, then the weakened one.
(defthm fn-pio-direct-settle-happens-once
  (let ((w1 (mv-nth 2 (fn-pio-direct-settle token worker verdict issued holds)))
        (issued1 (mv-nth 3 (fn-pio-direct-settle token worker verdict issued holds)))
        (holds1 (mv-nth 4 (fn-pio-direct-settle token worker verdict issued holds))))
    (equal (mv-list 5 (fn-pio-direct-settle token w1 verdict2 issued1 holds1))
           (list (if (equal (mv-nth 0 (fn-pio-direct-settle token worker verdict issued holds))
                            :unheld)
                     :unheld
                   :stale)
                 (fn-pio-issued-row token issued1) w1 issued1 holds1)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-hd-ident-step fn-pio-issued-row fn-pio-issued-remove
                               fn-pio-issued-put mv-nth)))
  :rule-classes nil)

; KEYSTONE.  The pin outlives the timeout: an admitted read's row, cancelled
; or not, keeps its file from closing until a non-stale settlement -- in the
; issued table (the walk) and in the holds table (the lookup the close asks).
(defthm fn-pio-direct-cancelled-read-still-pins-its-file
  (implies (and (fn-hd-identp holds)
                (equal (mv-nth 0 (fn-pio-direct-admit next cid file eoff elen trailer worker issued holds))
                       :admitted))
           (let* ((token (mv-nth 2 (fn-pio-direct-admit next cid file eoff elen trailer worker issued holds)))
                  (issued1 (mv-nth 5 (fn-pio-direct-admit next cid file eoff elen trailer worker issued holds)))
                  (holds1 (mv-nth 6 (fn-pio-direct-admit next cid file eoff elen trailer worker issued holds))))
             (and (not (fn-pio-file-clear-p file (fn-pio-issued-rows issued1)))
                  (not (fn-pio-file-clear-p file (fn-pio-issued-rows (fn-pio-direct-cancel token issued1))))
                  (not (fn-pio-direct-quiet-p file holds1)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-pio-direct-cancel fn-pio-direct-quiet-p fn-pio-cancel
                            fn-pird-issued-row-of-put)
                           (fn-pio-direct-admit fn-hd-ident-step fn-hd-ident-hold-adds-exactly-its-token
                            fn-pio-issued-row fn-pio-issued-put fn-pio-issued-rows fn-pio-rowp
                            fn-pio-token fn-pio-file-clear-p fn-pird-named-row-not-clear mv-nth))
           :use ((:instance fn-pird-admitted-shape)
                 (:instance fn-pird-issued-row-shape (n (if (null next) 0 next)))
                 (:instance fn-hd-ident-hold-adds-exactly-its-token
                            (table holds) (k file) (h file)
                            (tok (list (if (null next) 0 next) cid file eoff elen trailer)))
                 (:instance fn-pird-named-row-not-clear
                            (row (list (if (null next) 0 next) cid file eoff elen trailer :issued))
                            (rows (fn-pio-issued-rows
                                   (fn-pio-issued-put (list (if (null next) 0 next) cid file eoff elen trailer)
                                                      (list (if (null next) 0 next) cid file eoff elen trailer :issued)
                                                      issued))))
                 (:instance fn-pird-named-row-not-clear
                            (row (list (if (null next) 0 next) cid file eoff elen trailer :cancelled))
                            (rows (fn-pio-issued-rows
                                   (fn-pio-issued-put (list (if (null next) 0 next) cid file eoff elen trailer)
                                                      (list (if (null next) 0 next) cid file eoff elen trailer :cancelled)
                                                      (fn-pio-issued-put (list (if (null next) 0 next) cid file eoff elen trailer)
                                                                         (list (if (null next) 0 next) cid file eoff elen trailer :issued)
                                                                         issued))))))))
  :rule-classes nil)

; ---------------------------------------------------------------------------
; The bridge: the lookup is the walk.

(local
 (defthm fn-pird-issued-in-holds-member
   (implies (and (fn-pio-issued-in-holds-p issued holds)
                 (member-equal row (fn-pio-issued-rows issued))
                 (fn-pio-issuedp issued))
            (member-equal (fn-pio-token row) (fn-hd-tokens-of (fn-pio-token-file (fn-pio-token row)) holds)))
   :hints (("Goal" :induct (fn-pio-issued-rows issued)
            :in-theory (enable fn-pio-token)))))

(local
 (defun fn-pird-witness (file rows)
   (cond ((atom rows) nil)
         ((and (fn-pio-rowp (car rows)) (equal (nth 2 (car rows)) file)
               (not (equal (nth 6 (car rows)) :settled)))
          (car rows))
         (t (fn-pird-witness file (cdr rows))))))

(local
 (defthm fn-pird-rows-not-clear-has-row
   (implies (not (fn-pio-file-clear-p file rows))
            (let ((row (fn-pird-witness file rows)))
              (and (member-equal row rows) (fn-pio-rowp row)
                   (equal (nth 2 row) file) (not (equal (nth 6 row) :settled)))))
   :hints (("Goal" :in-theory (enable fn-pio-file-clear-p)))))

(local
 (defthm fn-pird-tokens-in-issued-first
   (implies (and (fn-pio-tokens-in-issued-p file tokens issued) (consp tokens))
            (and (fn-pio-issued-row (car tokens) issued)
                 (equal (fn-pio-token-file (car tokens)) file)))))

(local
 (defthm fn-pird-holds-in-issued-tokens
   (implies (and (fn-pio-holds-in-issued-p holds issued) (fn-hd-identp holds))
            (fn-pio-tokens-in-issued-p file (fn-hd-tokens-of file holds) issued))
   :hints (("Goal" :induct (fn-pio-holds-in-issued-p holds issued)
            :in-theory (enable fn-hd-identp fn-hd-tokens-of fn-hd-ident-row)))))

(local
 (defthm fn-pird-issued-row-is-a-row-naming
   (implies (and (fn-pio-issuedp issued) (fn-pio-issued-row token issued))
            (and (member-equal (fn-pio-issued-row token issued) (fn-pio-issued-rows issued))
                 (fn-pio-rowp (fn-pio-issued-row token issued))
                 (equal (fn-pio-token (fn-pio-issued-row token issued)) token)))
   :hints (("Goal" :induct (fn-pio-issued-row token issued)))))

(local
 (defthm fn-pird-issued-rows-never-settled
   ; the host removes a settled row: an issued row is :issued or :cancelled
   (implies (and (fn-pio-issuedp issued) (member-equal row (fn-pio-issued-rows issued)))
            (and (fn-pio-rowp row) (not (equal (nth 6 row) :settled))))
   :hints (("Goal" :induct (fn-pio-issued-rows issued)))))

(local
 (defthm fn-pird-clear-when-no-token
   (implies (and (fn-pio-issuedp issued)
                 (fn-pio-issued-in-holds-p issued holds)
                 (not (consp (fn-hd-tokens-of file holds))))
            (fn-pio-file-clear-p file (fn-pio-issued-rows issued)))
   :hints (("Goal" :do-not-induct t
            :in-theory (disable fn-pio-file-clear-p fn-hd-tokens-of fn-pio-issued-rows
                                fn-pio-issuedp fn-pio-issued-in-holds-p fn-pio-token-file
                                fn-pird-rows-not-clear-has-row fn-pird-issued-in-holds-member
                                fn-pird-token-file-of-token fn-pird-witness)
            :use ((:instance fn-pird-rows-not-clear-has-row (rows (fn-pio-issued-rows issued)))
                  (:instance fn-pird-issued-in-holds-member
                             (row (fn-pird-witness file (fn-pio-issued-rows issued))))
                  (:instance fn-pird-token-file-of-token
                             (r (fn-pird-witness file (fn-pio-issued-rows issued)))))))))

(local
 (defthm fn-pird-not-clear-when-token
   (implies (and (fn-pio-issuedp issued) (fn-hd-identp holds)
                 (fn-pio-holds-in-issued-p holds issued)
                 (consp (fn-hd-tokens-of file holds)))
            (not (fn-pio-file-clear-p file (fn-pio-issued-rows issued))))
   :hints (("Goal" :do-not-induct t
            :in-theory (disable fn-pio-file-clear-p fn-hd-tokens-of fn-hd-identp
                                fn-pio-issued-row fn-pio-issued-rows fn-pio-tokens-in-issued-p
                                fn-pird-named-row-not-clear fn-pird-issued-row-is-a-row-naming
                                fn-pird-tokens-in-issued-first)
            :use ((:instance fn-pird-holds-in-issued-tokens)
                  (:instance fn-pird-tokens-in-issued-first (tokens (fn-hd-tokens-of file holds)))
                  (:instance fn-pird-issued-row-is-a-row-naming (token (car (fn-hd-tokens-of file holds))))
                  (:instance fn-pird-token-file-of-token
                             (r (fn-pio-issued-row (car (fn-hd-tokens-of file holds)) issued)))
                  (:instance fn-pird-issued-rows-never-settled
                             (row (fn-pio-issued-row (car (fn-hd-tokens-of file holds)) issued)))
                  (:instance fn-pird-named-row-not-clear
                             (row (fn-pio-issued-row (car (fn-hd-tokens-of file holds)) issued))
                             (rows (fn-pio-issued-rows issued))))))))

; KEYSTONE.  Under the agreement of the two tables (established empty by
; fn-pio-direct-initial, kept by every entry), a file is quiet in the holds
; table exactly when no issued row names it: the one lookup
; fnn-extent-close asks is the walk it used to run.  Rows the issued table
; holds are never :settled (a settled row leaves it), so "no issued row
; names the file" is "no unsettled row names it".
(defthm fn-pio-direct-quiet-is-clear
  (implies (fn-pio-direct-okp issued holds)
           (iff (fn-pio-direct-quiet-p file holds)
                (fn-pio-file-clear-p file (fn-pio-issued-rows issued))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-pio-direct-okp fn-pio-direct-quiet-p)
                           (fn-pio-file-clear-p fn-hd-tokens-of fn-hd-identp fn-pio-issuedp
                            fn-pio-issued-in-holds-p fn-pio-holds-in-issued-p fn-pio-issued-rows
                            fn-pird-clear-when-no-token fn-pird-not-clear-when-token))
           :use ((:instance fn-pird-clear-when-no-token)
                 (:instance fn-pird-not-clear-when-token))))
  :rule-classes nil)

(in-theory (disable fn-pio-direct-admit fn-pxe-commit-direct fn-pio-direct-settle
                    fn-pio-direct-cancel fn-pio-direct-quiet-p fn-pio-direct-okp))
