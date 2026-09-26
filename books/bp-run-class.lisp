; The outcome class of one BP verb's run, and its exit code (PRF-131 part 1).
;
; A BP verb (bp send, bp receive, bp-service, bp-contact tick, bp-node,
; bp-app, bp-obligation) meets four different adverse facts, and an operator
; or agent must ask a different question after each (mandate 4
; "Uncertainty", 9's joins; specs/host.md "BP run classes"):
;
;   :failed     ACL2 requeued a job whose transfer never had a connection
;               (the (:forward-refused W A G :failed) effect of the durable
;               :requeued record): nothing left the node; the job is queued.
;   :uncertain  (class :interrupted) a connection existed and was lost, so the peer may or may
;               not hold the bundle ((:forward-refused W A G :uncertain), a
;               TCPCL session whose transfer failed after it was
;               established), or ACL2 could not decide an article's
;               lifetime: connection-local; the job stays and is re-offered
;               under its own identity.
;   :fenced     a publication (FNBS record, Store handoff, restart replay)
;               whose outcome is unknown: a recovery event.  The owner fences
;               and is never retried optimistically.
;   :refused    a known refusal before an effect.
;
; The host observes each fact where it happens and records it here with
; fn-bprc-note (the word it passes is ACL2's own: the reason of a
; :forward-refused effect through fn-bprc-transfer-evidence, or a session
; outcome through fn-bprc-session-evidence).  The class and the exit code are
; computed here; the host renders the code.

(in-package "ACL2")

(defconst *fn-bprc-classes* '(:accepted :refused :interrupted :fenced :not-connected))

; The evidence record: (refused failed uncertain fenced), four counts.
(defun fn-bprc-empty ()
  (declare (xargs :guard t))
  (list 0 0 0 0))

(defun fn-bprc-countsp (c)
  (declare (xargs :guard t))
  (and (true-listp c) (equal (len c) 4)
       (natp (nth 0 c)) (natp (nth 1 c)) (natp (nth 2 c)) (natp (nth 3 c))))

; Record one observation.  :accepted and NIL record nothing; a word that is
; not evidence is recorded as a fence (fail closed), as is an invalid record.
(defun fn-bprc-note (c word)
  (declare (xargs :guard t))
  (if (not (fn-bprc-countsp c))
      (list 0 0 0 1)
    (let ((r (nth 0 c)) (f (nth 1 c)) (u (nth 2 c)) (x (nth 3 c)))
      (case word
        ((nil :accepted) c)
        (:refused (list (+ 1 r) f u x))
        (:failed (list r (+ 1 f) u x))
        (:uncertain (list r f (+ 1 u) x))
        (otherwise (list r f u (+ 1 x)))))))

; The class.  A fence dominates everything (nothing masks a recovery event);
; then a connection lost after it existed (:interrupted); then a refusal;
; then a connection that never existed; otherwise the run was accepted.
(defun fn-bprc-class (c)
  (declare (xargs :guard t))
  (cond ((not (fn-bprc-countsp c)) :fenced)
        ((< 0 (nth 3 c)) :fenced)
        ((< 0 (nth 2 c)) :interrupted)
        ((< 0 (nth 0 c)) :refused)
        ((< 0 (nth 1 c)) :not-connected)
        (t :accepted)))

; specs/host.md "CLI exit codes" and "BP run classes".  A fence keeps the
; code every fn command gives an unknown publication outcome, 3: recovery is
; required before further mutation.  A connection lost after it existed is 6
; and a connection that never existed 7: neither asks for recovery.
(defun fn-bprc-exit-code (class)
  (declare (xargs :guard t))
  (case class
    (:accepted 0)
    (:refused 1)
    (:interrupted 6)
    (:not-connected 7)
    (otherwise 3)))

(defun fn-bprc-run-exit-code (c)
  (declare (xargs :guard t))
  (fn-bprc-exit-code (fn-bprc-class c)))

; The word the host records for ACL2's (:forward-refused W A G REASON)
; effect: its reason, which fn-bpn-forward-result-step wrote into the durable
; :requeued record.  Any other reason is a fence.
(defun fn-bprc-transfer-evidence (reason)
  (declare (xargs :guard t))
  (case reason
    (:refused :refused)
    (:failed :failed)
    (:uncertain :uncertain)
    (otherwise :fenced)))

; The word the host records for one effect ACL2 emitted: the reason of a
; (:forward-refused W A G REASON) effect, and nothing for any other effect.
(defun fn-bprc-effect-evidence (effect)
  (declare (xargs :guard t))
  (if (and (consp effect) (eq (car effect) :forward-refused)
           (true-listp effect) (equal (len effect) 5))
      (fn-bprc-transfer-evidence (nth 4 effect))
    nil))

; The host's fold over one effect list (fnn-bps-drive-effects records each
; effect's word in order).
(defun fn-bprc-note-effects (c effects)
  (declare (xargs :guard t))
  (if (atom effects)
      c
    (fn-bprc-note-effects (fn-bprc-note c (fn-bprc-effect-evidence (car effects)))
                          (cdr effects))))

; The word the host records for a TCPCL session (host/native/tcpcl.lisp):
; OUTCOME is the connection's outcome word, FENCED whether a Store or FNBS
; publication inside its delivery callback was uncertain.
(defun fn-bprc-session-evidence (outcome fenced)
  (declare (xargs :guard t))
  (cond (fenced :fenced)
        ((member-eq outcome '(nil :accepted)) nil)
        ((eq outcome :refused) :refused)
        ((eq outcome :uncertain) :uncertain)
        (t :fenced)))

; The word the host records for the classification of one publication
; program (books/journal-publish through fnn-immutable-publish-effect, or a
; generation selection): an ambiguous publication is a fence.  :durable and
; :refused record nothing here; the machine answers them with effects the
; host records in turn.
(defun fn-bprc-publication-evidence (outcome)
  (declare (xargs :guard t))
  (if (eq outcome :uncertain) :fenced nil))

; -----------------------------------------------------------------------------
; Theorems.

(defthm fn-bprc-countsp-of-note
  (fn-bprc-countsp (fn-bprc-note c word)))

(defthm fn-bprc-class-is-a-class
  (member-equal (fn-bprc-class c) *fn-bprc-classes*))

; Keystone 1: the five classes answer five different exit codes, so each
; question an operator must ask has its own code.
(defthm fn-bprc-exit-code-separates-the-classes
  (implies (and (member-equal c1 *fn-bprc-classes*)
                (member-equal c2 *fn-bprc-classes*)
                (not (equal c1 c2)))
           (not (equal (fn-bprc-exit-code c1) (fn-bprc-exit-code c2)))))

; Keystone 2: a fence is never masked.  Whatever was recorded before, and
; whatever is recorded after, the run is :fenced once a fence is recorded.
(defun fn-bprc-note-all (c words)
  (declare (xargs :guard (true-listp words)))
  (if (endp words) c (fn-bprc-note-all (fn-bprc-note c (car words)) (cdr words))))

(defthm fn-bprc-note-keeps-a-fence
  (implies (and (fn-bprc-countsp c) (< 0 (nth 3 c)))
           (and (fn-bprc-countsp (fn-bprc-note c word))
                (< 0 (nth 3 (fn-bprc-note c word))))))

(defthm fn-bprc-note-all-keeps-a-fence
  (implies (and (fn-bprc-countsp c) (< 0 (nth 3 c)))
           (and (fn-bprc-countsp (fn-bprc-note-all c words))
                (< 0 (nth 3 (fn-bprc-note-all c words)))))
  :hints (("Goal" :induct (fn-bprc-note-all c words)
           :in-theory (disable fn-bprc-note fn-bprc-countsp))))

(defthm fn-bprc-note-fenced-is-a-fence
  (and (fn-bprc-countsp (fn-bprc-note c :fenced))
       (< 0 (nth 3 (fn-bprc-note c :fenced)))))

(defthm fn-bprc-fence-is-never-masked
  (equal (fn-bprc-class (fn-bprc-note-all (fn-bprc-note c :fenced) later))
         :fenced)
  :hints (("Goal" :use ((:instance fn-bprc-note-all-keeps-a-fence
                                   (c (fn-bprc-note c :fenced)) (words later)))
           :in-theory (disable fn-bprc-note-all-keeps-a-fence fn-bprc-note
                               fn-bprc-note-all fn-bprc-countsp))))

; Keystone 3: connection-local evidence never fences.  From an empty record,
; words that are :failed, :uncertain, :refused or :accepted never make the
; run :fenced, and a lost connection is never reported as a connection that
; did not exist.
(defun fn-bprc-connection-local-wordsp (words)
  (declare (xargs :guard t))
  (if (atom words)
      (null words)
    (and (member-eq (car words) '(nil :accepted :refused :failed :uncertain))
         (fn-bprc-connection-local-wordsp (cdr words)))))

(defthm fn-bprc-connection-local-words-keep-no-fence
  (implies (and (fn-bprc-countsp c) (equal (nth 3 c) 0)
                (fn-bprc-connection-local-wordsp words))
           (and (fn-bprc-countsp (fn-bprc-note-all c words))
                (equal (nth 3 (fn-bprc-note-all c words)) 0)))
  :hints (("Goal" :induct (fn-bprc-note-all c words))))

(defthm fn-bprc-connection-local-never-fences
  (implies (fn-bprc-connection-local-wordsp words)
           (not (equal (fn-bprc-class (fn-bprc-note-all (fn-bprc-empty) words))
                       :fenced)))
  :hints (("Goal" :use ((:instance fn-bprc-connection-local-words-keep-no-fence
                                   (c (fn-bprc-empty))))
           :in-theory (disable fn-bprc-connection-local-words-keep-no-fence))))

; The transfer class of a job result's outcome: what the run answers when
; that one result is all it saw.
(defun fn-bprc-transfer-class (outcome)
  (declare (xargs :guard t))
  (case outcome
    (:accepted :accepted)
    (:refused :refused)
    (:uncertain :interrupted)
    (otherwise :not-connected)))
