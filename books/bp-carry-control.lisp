; fn: the operator's control of BP carry (lane operations, PKT-869, 2026-09-28).
;
; Carrying a POSTed article over BP is a forwarding obligation in the FNWF
; workflow journal (books/bp-workflow.lisp: a work, enqueued, undertaken
; against the Store's pin, requested attempt by attempt; books/bp-release:
; released only by the receipt's evidence, D13).  The operator had no verbs
; over it (fitness 2026-09-28: workflow-init, workflow-enqueue,
; bp-obligation undertake and request per article, none documented).  This
; book is the control half: one FNWF record kind, durable operator events
; the carry control journal replays (its own application journal domain,
; :carry, framed by books/bp-carry-frame.lisp: not FNWF kinds, whose book has
; some 1,100 dependents), folded over the workflow image the FNWF journal
; replayed, and never in the work records:
;
;   (:carry "pause" WORK "-")     no request is formed for WORK ("*": every work)
;   (:carry "resume" WORK "-")    the pause ends ("*": every pause)
;   (:carry "drop" WORK REASON)   WORK is carried no more, for REASON, final.
;
; A drop stops the carrying; it does not release the Store's pin.  The pin
; is the obligation's, and books/retention.lisp releases it only with the
; evidence it was undertaken against (fn-retain-matching-releasep): the
; receipt's.  An operator's abandonment of the pin itself is a different
; evidence kind, a decision the register does not hold (the lane's record).
;
; KEYSTONE fn-bpcc-gate-refuses-a-held-work: the request gate (host/
; workflow-host.lisp fn-workflow-request-plan, the `bp-obligation request'
; and `carry' paths) refuses by name every request for a paused or dropped
; work, and is the request plan itself for any other
; (fn-bpcc-gate-is-the-plan-otherwise).  fn-bpcc-drop-is-final: no record
; undoes a drop.
(in-package "ACL2")
(include-book "bp-release")

; The overlay: (ALL PAUSED DROPPED): ALL t while "*" is paused, PAUSED the
; work ids paused one by one, DROPPED ((WORK . REASON) ...), newest first.
(defun fn-bpcc-initial () (declare (xargs :guard t)) (list nil nil nil))
(defun fn-bpcc-all (c) (declare (xargs :guard t)) (and (consp c) (car c) t))
(defun fn-bpcc-paused (c)
  (declare (xargs :guard t))
  (if (and (consp c) (consp (cdr c))) (cadr c) nil))
(defun fn-bpcc-dropped (c)
  (declare (xargs :guard t))
  (if (and (consp c) (consp (cdr c)) (consp (cddr c))) (caddr c) nil))

(defun fn-bpcc-kindp (kind)
  (declare (xargs :guard t))
  (equal kind :carry))

(defun fn-bpcc-verb (record) (declare (xargs :guard t)) (fn-ag-car (fn-ag-cdr record)))
(defun fn-bpcc-record-work (record)
  (declare (xargs :guard t)) (fn-ag-car (fn-ag-cdr (fn-ag-cdr record))))
(defun fn-bpcc-record-reason (record)
  (declare (xargs :guard t)) (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr record)))))

(defun fn-bpcc-recordp (record)
  (declare (xargs :guard t))
  (and (true-listp record)
       (equal (len record) 4)
       (fn-bpcc-kindp (car record))
       (member-equal (fn-bpcc-verb record) '("pause" "resume" "drop"))
       (fn-bp-journal-textp (fn-bpcc-record-work record))
       (fn-bp-journal-textp (fn-bpcc-record-reason record))
       t))

(defun fn-bpcc-drop-entry (c work-id)
  (declare (xargs :guard t))
  (assoc-equal work-id (if (alistp (fn-bpcc-dropped c)) (fn-bpcc-dropped c) nil)))

(defun fn-bpcc-dropped-reason (c work-id)
  (declare (xargs :guard t))
  (let ((hit (fn-bpcc-drop-entry c work-id)))
    (if (consp hit) (cdr hit) nil)))

; A work's hold: :dropped, :paused, or nil.
(defun fn-bpcc-work-state (c work-id)
  (declare (xargs :guard t))
  (cond ((consp (fn-bpcc-drop-entry c work-id)) :dropped)
        ((or (fn-bpcc-all c)
             (member-equal work-id (true-list-fix (fn-bpcc-paused c))))
         :paused)
        (t nil)))

(defun fn-bpcc-workp (bp work-id)
  (declare (xargs :guard t))
  (consp (fn-bp-find-work work-id (fn-bp-state-works bp))))

; Why a control record is refused, or nil when it is admitted.  BP is the
; workflow image the record would join.
(defun fn-bpcc-refusal (bp c record)
  (declare (xargs :guard t))
  (if (not (fn-bpcc-recordp record))
      :malformed
    (let ((kind (fn-bpcc-verb record)) (w (fn-bpcc-record-work record)))
      (cond ((equal kind "pause")
             (cond ((equal w "*") (if (fn-bpcc-all c) :already-paused nil))
                   ((not (fn-bpcc-workp bp w)) :unknown-work)
                   ((equal (fn-bpcc-work-state c w) :dropped) :dropped)
                   ((equal (fn-bpcc-work-state c w) :paused) :already-paused)
                   (t nil)))
            ((equal kind "resume")
             (cond ((equal w "*")
                    (if (or (fn-bpcc-all c) (consp (fn-bpcc-paused c))) nil :not-paused))
                   ((not (fn-bpcc-workp bp w)) :unknown-work)
                   ((equal (fn-bpcc-work-state c w) :dropped) :dropped)
                   ((member-equal w (true-list-fix (fn-bpcc-paused c))) nil)
                   (t :not-paused)))
            (t
             (cond ((equal w "*") :unknown-work)
                   ((not (fn-bpcc-workp bp w)) :unknown-work)
                   ((equal (fn-bpcc-work-state c w) :dropped) :already-dropped)
                   (t nil)))))))

(defun fn-bpcc-admissiblep (bp c record)
  (declare (xargs :guard t))
  (null (fn-bpcc-refusal bp c record)))

(defun fn-bpcc-remove (w xs)
  (declare (xargs :guard t))
  (remove-equal w (true-list-fix xs)))

(defun fn-bpcc-apply (c record)
  (declare (xargs :guard t))
  (let ((kind (fn-bpcc-verb record)) (w (fn-bpcc-record-work record))
        (all (fn-bpcc-all c)) (paused (true-list-fix (fn-bpcc-paused c)))
        (dropped (if (alistp (fn-bpcc-dropped c)) (fn-bpcc-dropped c) nil)))
    (cond ((equal kind "pause")
           (if (equal w "*") (list t paused dropped)
             (list all (cons w paused) dropped)))
          ((equal kind "resume")
           (if (equal w "*") (list nil nil dropped)
             (list all (fn-bpcc-remove w paused) dropped)))
          ((equal kind "drop")
           (list all (fn-bpcc-remove w paused)
                 (cons (cons w (fn-bpcc-record-reason record)) dropped)))
          (t (list all paused dropped)))))

; The request gate: PLAN is books/bp-request-plan.lisp fn-bprq-plan's answer
; for WORK-ID; a held work's request is refused by name instead.
(defun fn-bpcc-request-gate (c work-id plan)
  (declare (xargs :guard t))
  (let ((hold (fn-bpcc-work-state c work-id)))
    (cond ((equal hold :dropped) (list :refused :carry-dropped))
          ((equal hold :paused) (list :refused :carry-paused))
          (t plan))))

; The carry journal's replay (host/workflow-host.lisp
; fn-workflow-carry-install): its :config record first, then each control
; record admitted against the workflow image BP and applied; anything else
; is a fault, never a skipped record.  (OKP . STATE).
(defun fn-bpcc-replay-records (bp c records)
  (declare (xargs :guard t :measure (acl2-count records)
                  :hints (("Goal" :in-theory (disable fn-bpcc-admissiblep fn-bpcc-apply)))
                  :guard-hints (("Goal" :in-theory (disable fn-bpcc-admissiblep
                                                            fn-bpcc-apply)))))
  (if (consp records)
      (if (fn-bpcc-admissiblep bp c (car records))
          (fn-bpcc-replay-records bp (fn-bpcc-apply c (car records)) (cdr records))
        (cons nil c))
    (cons t c)))

(defun fn-bpcc-configp (record)
  (declare (xargs :guard t))
  (and (true-listp record) (equal (len record) 2) (equal (car record) :config)
       (fn-bp-journal-textp (cadr record))))

; The carry journal's first record (host/native/bp-obligation.lisp publishes
; it before the first control).
(defun fn-bpcc-journal-config ()
  (declare (xargs :guard t))
  (list :config "fn-carry-1"))

(defun fn-bpcc-replay (bp records)
  (declare (xargs :guard t))
  (cond ((atom records) (cons t (fn-bpcc-initial)))
        ((fn-bpcc-configp (car records))
         (fn-bpcc-replay-records bp (fn-bpcc-initial) (cdr records)))
        (t (cons nil (fn-bpcc-initial)))))

; KEYSTONE.
(defthm fn-bpcc-gate-refuses-a-held-work
  (implies (fn-bpcc-work-state c work-id)
           (and (equal (car (fn-bpcc-request-gate c work-id plan)) :refused)
                (not (equal (car (fn-bpcc-request-gate c work-id plan)) :request)))))

(defthm fn-bpcc-gate-is-the-plan-otherwise
  (implies (not (fn-bpcc-work-state c work-id))
           (equal (fn-bpcc-request-gate c work-id plan) plan)))

(local (defthm fn-bpcc-alistp-of-dropped-apply
  (alistp (fn-bpcc-dropped (fn-bpcc-apply c record)))))

(local (defthm fn-bpcc-assoc-of-cons-other
  (implies (not (equal a w))
           (equal (assoc-equal w (cons (cons a r) al)) (assoc-equal w al)))))

(defthm fn-bpcc-drop-is-final
  (implies (equal (fn-bpcc-work-state c w) :dropped)
           (equal (fn-bpcc-work-state (fn-bpcc-apply c record) w) :dropped)))

; A drop admitted for W holds W dropped with its reason.
(defthm fn-bpcc-admitted-drop-drops
  (implies (and (fn-bpcc-admissiblep bp c record)
                (equal (fn-bpcc-verb record) "drop"))
           (and (equal (fn-bpcc-work-state (fn-bpcc-apply c record)
                                           (fn-bpcc-record-work record))
                       :dropped)
                (equal (fn-bpcc-dropped-reason (fn-bpcc-apply c record)
                                               (fn-bpcc-record-work record))
                       (fn-bpcc-record-reason record)))))

; ---------------------------------------------------------------------------
; The operator's reports (`fn operator CONFIG carry list|inspect'), rendered
; here.  PINNED is the list of the work ids whose Store pin stands
; (host/bp-release-owner-host.lisp fn-owner-workflow-forward-pinnedp, over
; the Store the verb opened).

(defun fn-bpcc-text (x)
  (declare (xargs :guard t))
  (if (stringp x) (fn-record-string-octets x) (fn-record-string-octets "-")))

(defun fn-bpcc-word (x)
  (declare (xargs :guard t))
  (if (symbolp x) (fn-record-string-octets (string-downcase (symbol-name x)))
    (fn-record-string-octets "-")))

(defun fn-bpcc-work-line (bp c pinned work)
  (declare (xargs :guard t))
  (let* ((id (fn-bp-work-id work))
         (hold (fn-bpcc-work-state c id))
         (attempt (fn-bp-work-attempt work)))
    (append (fn-record-string-octets "carry ") (fn-bpcc-text id)
            (fn-record-string-octets " message-id=") (fn-bpcc-text (fn-bp-work-msgid work))
            (fn-record-string-octets " peer=") (fn-bpcc-text (fn-bp-work-peer-eid work))
            (fn-record-string-octets " status=")
            (fn-bpcc-word (fn-bp-work-status id (fn-bp-state-works bp)))
            (fn-record-string-octets " pinned=")
            (fn-record-string-octets (if (member-equal id (true-list-fix pinned)) "yes" "no"))
            (fn-record-string-octets " hold=")
            (fn-record-string-octets (cond ((equal hold :dropped) "dropped")
                                           ((equal hold :paused) "paused")
                                           (t "none")))
            (if (consp attempt)
                (append (fn-record-string-octets " attempt=") (fn-bpcc-text (fn-bp-attempt-id attempt))
                        (fn-record-string-octets " transport=")
                        (fn-bpcc-word (fn-bp-attempt-status attempt)))
              nil)
            (if (equal hold :dropped)
                (append (fn-record-string-octets " reason=")
                        (fn-bpcc-text (fn-bpcc-dropped-reason c id)))
              nil)
            (list 10))))

(defun fn-bpcc-list-report-loop (bp c pinned works acc)
  (declare (xargs :guard (true-listp acc)))
  (if (consp works)
      (fn-bpcc-list-report-loop bp c pinned (cdr works)
                                (revappend (fn-bpcc-work-line bp c pinned (car works)) acc))
    (revappend acc nil)))

(defun fn-bpcc-list-report (bp c pinned)
  (declare (xargs :guard t))
  (fn-bpcc-list-report-loop bp c pinned (fn-bp-state-works bp) nil))

(defun fn-bpcc-inspect-report (bp c pinned work-id)
  (declare (xargs :guard t))
  (let ((work (fn-bp-find-work work-id (fn-bp-state-works bp))))
    (if (consp work) (fn-bpcc-work-line bp c pinned work) nil)))
