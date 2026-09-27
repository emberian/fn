; fn: content reclamation over the record log (lane log-recovery, PKT-750;
; design planning/design-2026-09-27-storage-log.md section 6; STO-014,
; STO-017).
;
; On a format-9 store `store reclaim' is a checkpoint of the REWRITTEN history
; followed by the drop: the decision (fn-lgr-decide) is the reclaiming pack's
; (books/store-reclaim-pack.lisp fn-rclp-decide) over the same per-article
; context -- STO-014's decision over every holder, fn-rclp-ctx, untouched --
; without the pack's observation and link limits: every article record the
; context releases becomes its tombstone (fn-rclp-events), and nothing else
; changes.  The host (host/native/checkpoint.lisp fnn-command-reclaim) replays
; the rewritten history into the store node, publishes its state checkpoint
; with the log rotated, and drops the segments the checkpoint covers
; (books/store-log-segments.lisp, T8): the payload octets the released
; articles held leave the disk with those segments, and the open reads the
; checkpoint of the rewritten history.  A process death before the
; checkpoint's install reopens the history as it was (the rerun reclaims
; again); from the install on it reopens the rewritten history, and a rerun
; rewrites nothing more (fn-rclp-events-idempotent,
; fn-rclp-a-reclaimed-event-stays-reclaimed).
(in-package "ACL2")
(include-book "store-reclaim-stream")

;   (:refused :profile)             the profile is not admitted
;   (:none COUNTS)                  nothing to rewrite
;   (:dry-run MSGIDS FREED COUNTS)  what a run would reclaim; nothing written
;   (:reclaim MSGIDS FREED RECORDS COUNTS)
;                                   RECORDS: the rewritten history
; COUNTS read the articles through the arena (books/store-reclaim-holders.lisp
; fn-rcl-store-counts-arena; lane matrix-reds-reclaim): the arena is only read.
(defun fn-lgr-decide (profile rule now s records dry fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (let* ((counts (fn-rcl-store-counts-arena rule now s fn-arena))
         (ctx (fn-rclp-ctx rule now s))
         (msgids (fn-rclp-rewritten-msgids records ctx)))
    (cond ((not (fn-bs-profile-admittedp profile)) (list :refused :profile))
          ((atom msgids) (list :none counts))
          (dry (list :dry-run msgids (fn-rclp-freed records ctx) counts))
          (t (list :reclaim msgids (fn-rclp-freed records ctx)
                   (fn-rclp-events records ctx) counts)))))

; KEYSTONE: the decision writes the rewrite and nothing else.  When the verb
; reclaims, the history it checkpoints is exactly fn-rclp-events of the
; committed history under the store's context (so every theorem of
; books/store-reclaim-pack.lisp about that list -- a held article is never
; touched, a reclaimed event stays reclaimed, a rerun rewrites nothing -- is a
; theorem about what the log's checkpoint holds), the dry run writes nothing,
; and a reclaim happens only when some article is rewritten.
(defthm fn-lgr-decide-checkpoints-the-rewrite
  (let ((d (fn-lgr-decide profile rule now s records dry fn-arena)))
    (implies (equal (car d) :reclaim)
             (and (not dry)
                  (fn-bs-profile-admittedp profile)
                  (consp (fn-rclp-rewritten-msgids records (fn-rclp-ctx rule now s)))
                  (equal (nth 3 d) (fn-rclp-events records (fn-rclp-ctx rule now s)))
                  (equal (nth 1 d) (fn-rclp-rewritten-msgids records (fn-rclp-ctx rule now s))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-lgr-decide car-cons cdr-cons nth-0-cons nth-add1)
                                             (theory 'minimal-theory)))))

; -----------------------------------------------------------------------------
; The streamed decision (what the host calls; D27, compact-arena's fold).
;
; The host (host/native/checkpoint.lisp fnn-log-reclaim-steps) hands ACL2 one
; record's octets at a time: the fold step (books/store-reclaim-stream.lisp
; fn-rcls-step, through host/checkpoint-host.lisp fn-store-reclaim-step) and
; the record's rewrite (fn-rclp-event, through fn-store-log-reclaim-event),
; keeping the rewrites as octet vectors; then fn-lgr-decide-stream over the
; fold.  No list of the history is ever built in ACL2.
;   (:refused :profile) | (:none COUNTS) | (:dry-run MSGIDS FREED COUNTS)
;   | (:reclaim MSGIDS FREED COUNTS)   -- the rewritten history is the host's
;                                         per-record rewrites, in order
(defun fn-lgr-decide-stream (profile rule now s acc dry fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (let ((counts (fn-rcl-store-counts-arena rule now s fn-arena))
        (msgids (rev (nth 1 acc)))
        (freed (nth 2 acc)))
    (cond ((not (fn-bs-profile-admittedp profile)) (list :refused :profile))
          ((atom msgids) (list :none counts))
          (dry (list :dry-run msgids freed counts))
          (t (list :reclaim msgids freed counts)))))

; The per-record rewrites the host collects are the rewritten history.
(defthm fn-lgr-rewrites-are-the-events
  (equal (fn-rclp-events records ctx)
         (if (consp records)
             (cons (fn-rclp-event (car records) ctx) (fn-rclp-events (cdr records) ctx))
           records))
  ;; The definition's own body: one expansion, nothing else (in the batch's
  ;; union world the default theory ran past 300 s here).
  :hints (("Goal" :expand ((fn-rclp-events records ctx))
                  :in-theory (theory 'minimal-theory)))
  :rule-classes nil)

; KEYSTONE: over the fold of the history from fn-rcls-init under the store's
; context, the streamed decision is the whole-history decision without its
; RECORDS element, which is the list of the per-record rewrites (so
; fn-lgr-decide-checkpoints-the-rewrite is about what the host checkpoints).
(defthm fn-lgr-decide-stream-is-lgr-decide
  (implies (and (true-listp records)
                (equal acc (fn-rcls-fold records (fn-rclp-ctx rule now s) (fn-rcls-init))))
           (equal (fn-lgr-decide profile rule now s records dry fn-arena)
                  (let ((d (fn-lgr-decide-stream profile rule now s acc dry fn-arena)))
                    (if (equal (car d) :reclaim)
                        (list :reclaim (nth 1 d) (nth 2 d)
                              (fn-rclp-events records (fn-rclp-ctx rule now s)) (nth 3 d))
                      d))))
  :hints (("Goal" :use ((:instance fn-rcls-fold-of-init (ctx (fn-rclp-ctx rule now s))))
                  :in-theory (e/d (fn-lgr-decide fn-lgr-decide-stream)
                                  (fn-rcls-fold fn-rclp-events fn-rclp-freed
                                   fn-rclp-rewritten-msgids fn-rcl-store-counts-arena
                                   fn-rclp-ctx fn-bs-profile-admittedp)))))
