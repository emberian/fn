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
(include-book "store-reclaim-pack")

;   (:refused :profile)             the profile is not admitted
;   (:none COUNTS)                  nothing to rewrite
;   (:dry-run MSGIDS FREED COUNTS)  what a run would reclaim; nothing written
;   (:reclaim MSGIDS FREED RECORDS COUNTS)
;                                   RECORDS: the rewritten history
(defun fn-lgr-decide (profile rule now s records dry)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((counts (fn-rcl-store-counts rule now s))
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
  (let ((d (fn-lgr-decide profile rule now s records dry)))
    (implies (equal (car d) :reclaim)
             (and (not dry)
                  (fn-bs-profile-admittedp profile)
                  (consp (fn-rclp-rewritten-msgids records (fn-rclp-ctx rule now s)))
                  (equal (nth 3 d) (fn-rclp-events records (fn-rclp-ctx rule now s)))
                  (equal (nth 1 d) (fn-rclp-rewritten-msgids records (fn-rclp-ctx rule now s))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-lgr-decide car-cons cdr-cons nth-0-cons nth-add1)
                                             (theory 'minimal-theory)))))
