; B1 abstract sealed-batch log.  This is a test/checker specification, not a
; served representation or a disk format.  The quarry is fn-lgk-relp's
; completed/fenced/acknowledged separation and fn-lg-crash-verdictp's prefix
; relation.  FNLG framing, files, inodes and its single pending write do not
; carry: several batches may have outstanding writes here.
(in-package "ACL2")
(include-book "crash-model")
(include-book "assumptions-integrity")
(include-book "owed")

; One trace names one history incarnation. Batch numbers are unbounded logical
; naturals, not resident counters. A sealed batch is
; (number predecessor records dependency-set), with genesis predecessor 0.
; Dependency identities are abstract; :batch-writes-complete supplies the exact
; set whose writes (and all batch writes) completed. B3 must refine that event.
(defun fn2-lm-at (n x)
  (declare (xargs :guard t))
  (fn2-cm-at n x))

(defun fn2-lm-batch (number predecessor records dependencies)
  (declare (xargs :guard t))
  (list number predecessor records dependencies))

(defun fn2-lm-batchp (x)
  (declare (xargs :guard t :verify-guards nil))
  (and (true-listp x) (equal (len x) 4)
       (posp (fn2-lm-at 0 x)) (natp (fn2-lm-at 1 x))
       (true-listp (fn2-lm-at 2 x)) (true-listp (fn2-lm-at 3 x))
       (no-duplicatesp-equal (fn2-lm-at 3 x))))

(defun fn2-lm-prefixp (a b)
  (declare (xargs :guard t))
  (if (consp a)
      (and (consp b) (equal (car a) (car b))
           (fn2-lm-prefixp (cdr a) (cdr b)))
    (null a)))

; State: submitted, completed IDs, fenced IDs, acknowledged IDs, crashed,
; corrupt required IDs, bad-tail ID, rollback frontier (nil means absent),
; presented witnesses (name . frontier), complete-survivor IDs, valid.
(defun fn2-lm-initial ()
  (declare (xargs :guard t))
  (list nil nil nil nil nil nil nil nil nil nil t))

(defun fn2-lm-all-through-p (n ids)
  (declare (xargs :guard (natp n) :measure (nfix n)
                  :verify-guards nil))
  (if (zp n) t
    (and (member-equal n ids) (fn2-lm-all-through-p (- n 1) ids))))

(defun fn2-lm-knownp (n s)
  (declare (xargs :guard t :verify-guards nil))
  (and (posp n) (<= n (len (fn2-lm-at 0 s)))))

(defun fn2-lm-event-allowedp (event s)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((tag (fn2-lm-at 0 event))
         (arg (fn2-lm-at 1 event))
         (history (fn2-lm-at 0 s))
         (n (len history))
         (crashed (fn2-lm-at 4 s)))
    (and (true-listp event)
         (case tag
           (:submit-batch
            (and (equal (len event) 2) (not crashed) (fn2-lm-batchp arg)
                 (equal (fn2-lm-at 0 arg) (+ 1 n))
                 (equal (fn2-lm-at 1 arg) n)))
           (:batch-writes-complete
            (and (equal (len event) 3) (not crashed) (fn2-lm-knownp arg s)
                 (not (member-equal arg (fn2-lm-at 1 s)))
                 (true-listp (fn2-lm-at 2 event))
                 (no-duplicatesp-equal (fn2-lm-at 2 event))
                 (subsetp-equal (fn2-lm-at 2 event)
                               (fn2-lm-at 3 (fn2-lm-at (- arg 1) history)))
                 (subsetp-equal (fn2-lm-at 3 (fn2-lm-at (- arg 1) history))
                               (fn2-lm-at 2 event))))
           (:fence-ok
            (and (equal (len event) 2) (not crashed)
                 (member-equal arg (fn2-lm-at 1 s))
                 (not (member-equal arg (fn2-lm-at 2 s)))))
           (:acknowledge
            (and (equal (len event) 2) (not crashed) (fn2-lm-knownp arg s)
                 (fn2-lm-all-through-p arg (fn2-lm-at 2 s))
                 (not (member-equal arg (fn2-lm-at 3 s)))))
           (:crash (equal (len event) 1))
           (:corrupt-required
            (and (equal (len event) 2) (member-equal arg (fn2-lm-at 2 s))
                 (not (member-equal arg (fn2-lm-at 5 s)))))
           (:bad-tail
            (and (equal (len event) 2) crashed (posp n) (equal arg n)))
           (:rollback
            (and (equal (len event) 2) crashed (natp arg) (< arg n)))
           (:present-frontier
            (and (equal (len event) 3) crashed (symbolp arg) arg
                 (member-equal (fn2-lm-at 2 event) (fn2-lm-at 2 s))))
           (:survives
            (and (equal (len event) 2) crashed (fn2-lm-knownp arg s)
                 (not (member-equal arg (fn2-lm-at 5 s)))))
           (otherwise nil)))))

(defun fn2-lm-step (event s)
  (declare (xargs :guard t :verify-guards nil))
  (let ((tag (fn2-lm-at 0 event)) (arg (fn2-lm-at 1 event)))
    (if (or (not (fn2-lm-at 10 s)) (not (fn2-lm-event-allowedp event s)))
        (update-nth 10 nil s)
      (case tag
        (:submit-batch (update-nth 0 (append (fn2-lm-at 0 s) (list arg)) s))
        (:batch-writes-complete (update-nth 1 (cons arg (fn2-lm-at 1 s)) s))
        (:fence-ok (update-nth 2 (cons arg (fn2-lm-at 2 s)) s))
        (:acknowledge (update-nth 3 (cons arg (fn2-lm-at 3 s)) s))
        ; A second crash during read-only recovery changes no durable history.
        ; Surviving witnesses and complete-batch observations must be presented
        ; again. A physical corruption/rollback is not undone by another crash.
        (:crash (update-nth 4 t (update-nth 8 nil (update-nth 9 nil s))))
        (:corrupt-required (update-nth 5 (cons arg (fn2-lm-at 5 s)) s))
        (:bad-tail (update-nth 6 arg s))
        (:rollback (update-nth 7 arg s))
        (:present-frontier
         (update-nth 8 (cons (cons arg (fn2-lm-at 2 event)) (fn2-lm-at 8 s)) s))
        (:survives (update-nth 9 (cons arg (fn2-lm-at 9 s)) s))
        (otherwise s)))))

(defun fn2-lm-run (trace s)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp trace) (fn2-lm-run (cdr trace) (fn2-lm-step (car trace) s))
    (if (null trace) s (update-nth 10 nil s))))

(defun fn2-lm-trace-state (trace)
  (declare (xargs :guard t :verify-guards nil))
  (fn2-lm-run trace (fn2-lm-initial)))

(defun fn2-lm-acknowledged-in-historyp (acked history)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp acked)
      (and (posp (car acked)) (<= (car acked) (len history))
           (fn2-lm-acknowledged-in-historyp (cdr acked) history))
    (null acked)))

(defun fn2-lm-corruption-beforep (n corrupt)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp corrupt)
      (or (<= (nfix (car corrupt)) (nfix n))
          (fn2-lm-corruption-beforep n (cdr corrupt)))
    nil))

(defun fn2-lm-protected-acks-p (acked corrupt recovered)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp acked)
      (and (or (fn2-lm-corruption-beforep (car acked) corrupt)
               (<= (nfix (car acked)) (len recovered)))
           (fn2-lm-protected-acks-p (cdr acked) corrupt recovered))
    t))

(defun fn2-lm-recovered-completep (history completed survived corrupt)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp history)
      (let ((n (fn2-lm-at 0 (car history))))
        (and (or (member-equal n completed) (member-equal n survived))
             (not (member-equal n corrupt))
             (fn2-lm-recovered-completep (cdr history) completed survived corrupt)))
    (null history)))

; Return the actual presented name, not a manufactured boolean "anchor".
; The trace's incarnation scopes the witness; a future persisted receipt must
; also bind that incarnation and the exact batch head in its refinement.
(defun fn2-lm-conflicting-witness (witnesses recovered)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp witnesses)
      (if (< (len recovered) (nfix (cdar witnesses)))
          (caar witnesses)
        (fn2-lm-conflicting-witness (cdr witnesses) recovered))
    nil))

(defun fn2-lm-no-destructionp (s)
  (declare (xargs :guard t :verify-guards nil))
  (and (not (consp (fn2-lm-at 5 s))) (null (fn2-lm-at 7 s))
       (not (member-equal (fn2-lm-at 6 s) (fn2-lm-at 3 s)))))

; Non-executable checksum premise for B5's refinement statement: the profile
; selection alone must never stand in for the named integrity assumption.
(defun-nx fn2-lm-integrity-premise (profile expected observed)
  (and (fn2-cm-integrity-evidence profile)
       (fn2-a-integrity-evidence expected observed)))

; The executable profile bit is the assumption parameter, not evidence that
; any checksum is cryptographically sound. B5's checksum refinement must use
; fn2-lm-integrity-premise, reusing fn2-a-integrity-evidence from layer A; this model
; neither attaches a fabricated implementation nor claims a collision bound.
;
; HISTORY and RECOVERY call this exact interface:
; (fn2-lm-recovery-allowedp trace profile classification recovered-history).
; :damaged/:unknown histories are the verified prefix for diagnosis, never a
; permission to resume service. Complete unacknowledged batches may be adopted.
; :survives witnesses a complete batch that landed without a write completion.
; An unexplained bad final batch is :unknown under broad/lying profiles.
; No independent witness => no rollback-detection claim, even if several local
; superblock copies agree on the older image. Fail-slow is latency and absent
; from this timeless safety model (papers table row 19).
(defun fn2-lm-recovery-allowedp (trace profile classification recovered-history)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((s (fn2-lm-trace-state trace))
         (corrupt (fn2-lm-at 5 s))
         (bad-tail (fn2-lm-at 6 s))
         (rollback (fn2-lm-at 7 s))
         (crash-only (eq (fn2-cm-profile-kind profile) :crash-only))
         (honest (fn2-cm-persistence-fence profile))
         (detected-corruption (and (fn2-cm-integrity-evidence profile) (consp corrupt)))
         (witness (and (fn2-cm-independent-frontier profile)
                       (fn2-lm-conflicting-witness (fn2-lm-at 8 s) recovered-history)))
         (damage (or detected-corruption witness)))
    (and (fn2-cm-profilep profile)
         (fn2-lm-at 10 s) (fn2-lm-at 4 s)
         (fn2-lm-prefixp recovered-history (fn2-lm-at 0 s))
         (fn2-lm-recovered-completep recovered-history (fn2-lm-at 1 s)
                                     (fn2-lm-at 9 s) corrupt)
         ; The device model spends the unit budget. One damaged shared
         ; dependency may affect many batches, so batch count is not a second
         ; unit budget. A zero budget still rules out any corruption event.
         (or (null corrupt) (< 0 (nfix (fn2-cm-corruption-budget profile))))
         (or (not crash-only) (and (null corrupt) (null rollback)))
         (or (null rollback) (equal (len recovered-history) rollback))
         (or (not honest) rollback
             (fn2-lm-protected-acks-p (fn2-lm-at 3 s)
                                      (if bad-tail (cons bad-tail corrupt) corrupt)
                                      recovered-history))
         (or (null bad-tail) (< (len recovered-history) bad-tail))
         (cond (damage (if (member-eq classification '(:damaged :unknown)) t nil))
               ; Destruction the named assumptions do not let recovery detect:
               ; no detection claim either way, but a recovery that does notice
               ; it (by other evidence) must not be refused for saying so.
               ((or (consp corrupt) rollback)
                (if (member-eq classification '(:intact :damaged :unknown)) t nil))
               ((and bad-tail (not crash-only)) (eq classification :unknown))
               (bad-tail
                (and (eq classification :torn-tail)
                     (fn2-lm-acknowledged-in-historyp (fn2-lm-at 3 s) recovered-history)))
               (t (eq classification :intact))))))

(defun fn2-lm-durable-ack-hyps (trace profile classification recovered-history)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn2-cm-persistence-fence profile)
       (fn2-lm-no-destructionp (fn2-lm-trace-state trace))
       (fn2-lm-recovery-allowedp trace profile classification recovered-history)))

(defthm-owed fn2-lm-durable-acknowledgement
  (trace profile classification recovered-history)
  (implies (fn2-lm-durable-ack-hyps trace profile classification recovered-history)
           (fn2-lm-acknowledged-in-historyp
            (fn2-lm-at 3 (fn2-lm-trace-state trace)) recovered-history))
  :teeth "log-model-unit: two acknowledged batches survive, including repeated recovery crashes; dropping honest fences permits a shorter intact history; actual corruption removes the no-destruction premise and permits a damaged prefix."
  :doc "B1 specification obligation for HISTORY/RECOVERY; not a proof of B3 commit or B5 recovery.")
