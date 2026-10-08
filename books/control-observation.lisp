; Local client observation policy; never a durable acceptance decision.
; Props (statement first; implementation and proof obligations below):
; S1 (control-receipt): Every control verb (FNCT kind, and the declared verb within an administrative kind) is declared :bounded (work bounded by the request; the reply deadline applies) or :store-sized (answers :requested with a receipt). The declaration is total over the kind table, checked by evaluation.
; S2 (control-receipt): An admitted :store-sized verb replies :requested with a receipt, never its completion, and never waits on its work: the owner answers in the quantum accepting the request.
; S3 (control-receipt, keystone): For every receipt the owner issues there is exactly one completion status observed through status: its state goes :requested to exactly one terminal word, never back and never twice. State this over the owner step the host calls, with a positive witness of the whole antecedent and conclusion and a hypothesis-removal witness refusing a second completion. Eventual completion requires the owner to continue executing and receive a work outcome; process death and recovery must retain an honest unresolved outcome.
; S4 (control-receipt): The client reply deadline covers only the acknowledgement for :store-sized verbs. Subsequent status observation uses an ACL2-named wait policy bounding each observation, with no fixed ceiling on store-sized work.
; S3a (C8, statement first): Over the actual fn-nco-owner-step, in every reachable owner state each requested receipt has exactly one pending producer job naming it, and every pending producer job names exactly one requested receipt. Acceptance creates both atomically; only that job's terminal outcome leaves requested and consumes the job, mapping to exactly one terminal status. The host executes the job held by that state, not an untracked copy of its request.
; S3b (C8, statement first): Over fn-nco-wire-step, the status entry the host calls, a status query for a receipt the owner does not hold (after death/restart or for an unissued serial) answers the distinct word receipt-unknown, never requested and never a terminal word. The ACL2 client decision maps receipt-unknown to uncertain, exit 3, and stops polling. Persistence across process death is not claimed beyond this observation contract.
(in-package "ACL2")

(defconst *fn-nco-reply-grace-seconds* 10)
(defconst *fn-nco-observation-octets-per-second* 65536)

(defun fn-nco-reply-seconds (request-octets)
  (declare (xargs :guard (natp request-octets)))
  (+ *fn-nco-reply-grace-seconds*
     (ceiling request-octets *fn-nco-observation-octets-per-second*)))


; The existing handler-kind table now also declares the work class. Kinds
; 15/16 are reserved legacy status codes (bounded refusal here). Admin kinds carry a
; declared verb, rather than inferring its work from the frame's size.
; Columns: kind, handler (:store/:read/nil), work class.
(defconst *fn-nco-kind-table*
  '((1 nil :bounded) (2 nil :bounded) (3 nil :bounded)
    (4 :store :bounded) (5 :store :bounded) (6 :store :bounded)
    (7 :store :bounded) (8 :store :bounded) (9 :store :bounded)
    (10 :store :bounded) (11 :store :bounded) (12 :store :bounded)
    (13 nil :bounded) (14 :store :bounded)
    (15 nil :bounded) (16 nil :bounded)
    (17 nil :bounded) (18 nil :bounded) (19 :read :bounded)
    (20 nil :bounded) (21 nil :bounded) (22 nil :bounded)
    (23 nil :bounded) (24 :read :bounded) (25 nil :bounded)
    (26 :read :bounded) (27 nil :bounded)))

(defun fn-nco-handler-kinds (rows handler)
  (declare (xargs :guard (alistp rows)))
  (if (endp rows) nil
    (if (and (consp (cdar rows)) (equal (cadar rows) handler))
        (cons (caar rows) (fn-nco-handler-kinds (cdr rows) handler))
      (fn-nco-handler-kinds (cdr rows) handler))))

; Octet argv, the native admin codec's existing representation. These
; aliases all run the same compaction/publication producer.
(defconst *fn-nco-store-verbs*
  '((((114 101 99 108 97 105 109) (114 101 113 117 101 115 116)) :request-reclaim :store-sized)
    (((114 101 99 108 97 105 109) (114 101 99 111 114 100 101 100)) :request-reclaim-recorded :store-sized)
    (((114 101 99 108 97 105 109) (100 114 121 45 114 117 110)) :request-reclaim-dry-run :store-sized)
    (((99 111 109 112 97 99 116 105 111 110) (114 101 113 117 101 115 116)) :request-compaction :store-sized)))

; Native-admin consumes this same declaration for its plan. There is no
; second maintenance-verb parser beside the work-class declaration.
(defun fn-nco-store-plan-kind (argv)
  (declare (xargs :guard t))
  (cadr (assoc-equal argv *fn-nco-store-verbs*)))

(defun fn-nco-work-class (kind argv)
  (declare (xargs :guard t))
  (if (and (member-equal kind '(3 17))
           (fn-nco-store-plan-kind argv))
      (caddr (assoc-equal argv *fn-nco-store-verbs*))
    (caddr (assoc-equal kind *fn-nco-kind-table*))))

(defun fn-nco-classes (rows)
  (declare (xargs :guard (alistp rows)))
  (if (endp rows) nil
    (cons (fn-nco-work-class (caar rows) nil) (fn-nco-classes (cdr rows)))))

; S1, evaluation over every assigned kind, including the consumer/identity
; kinds; requests 3/17 additionally dispatch the verb declaration above.
(defthm fn-nco-kind-table-total
  (and (equal (fn-nco-classes *fn-nco-kind-table*)
              '(:bounded :bounded :bounded :bounded :bounded :bounded
                :bounded :bounded :bounded :bounded :bounded :bounded
                :bounded :bounded :bounded :bounded :bounded :bounded
                :bounded :bounded :bounded :bounded :bounded :bounded :bounded
                :bounded :bounded))
       (equal (fn-nco-handler-kinds *fn-nco-kind-table* :store)
              '(4 5 6 7 8 9 10 11 12 14))
       (equal (fn-nco-handler-kinds *fn-nco-kind-table* :read) '(19 24 26)))
  :rule-classes nil)

; Policy bounds a status exchange and the delay before another exchange,
; never the number of exchanges or the work's lifetime (D27).
(defun fn-nco-wait-seconds () (declare (xargs :guard t)) 1/10)
(defun fn-nco-epoch-octets () (declare (xargs :guard t)) 16)

(defun fn-nco-at (n x)
  (declare (xargs :guard (natp n)))
  (if (atom x) nil (if (zp n) (car x) (fn-nco-at (1- n) (cdr x)))))

(defun fn-nco-terminalp (word)
  (declare (xargs :guard t))
  (and (member-eq word '(:accepted :refused :uncertain :fault)) t))

; One process-local maintenance receipt slot. Like the publication slot it
; has a serial and a retained outcome; a second issue is refused until the
; client releases an observed terminal receipt. Status reads do not consume
; it. The epoch is fresh host entropy, not evidence of durable acceptance.
; State: (epoch serial receipt phase status reason jobs). Jobs is empty or
; the single (receipt argv) producer, retained until its terminal outcome.
(defun fn-nco-initial (epoch)
  (declare (xargs :guard t))
  (list epoch 0 nil :idle nil nil nil))

(defun fn-nco-receipt (epoch serial)
  (declare (xargs :guard t))
  (list epoch (nfix serial)))

(defun fn-nco-pending-job (st)
  (declare (xargs :guard t))
  (fn-nco-at 0 (fn-nco-at 6 st)))

; A bijection, not just a count: the one job names this requested receipt
; and carries its declared producer's argv. No job survives completion.
(defun fn-nco-no-orphanp (st)
  (declare (xargs :guard t))
  (let ((job (fn-nco-pending-job st)))
    (if (eq (fn-nco-at 3 st) :requested)
        (and (consp (fn-nco-at 2 st))
             (equal (fn-nco-at 6 st)
                    (list (list (fn-nco-at 2 st) (fn-nco-at 1 job))))
             (eq (fn-nco-work-class 17 (fn-nco-at 1 job)) :store-sized))
      (not (fn-nco-at 6 st)))))

; Owner entry called under its control quantum. Result: (word next-state).
; Completion names the exact issued receipt. Unknown observations, duplicate
; completions and releases before completion leave the state unchanged.
(defun fn-nco-owner-step (st event)
  (declare (xargs :guard t))
  (let ((op (fn-nco-at 0 event)) (receipt (fn-nco-at 1 event))
        (phase (fn-nco-at 3 st)))
    (cond
     ((and (eq op :request) (eq phase :idle)
           (eq (fn-nco-work-class 17 receipt) :store-sized))
      (let* ((serial (+ 1 (nfix (fn-nco-at 1 st))))
             (token (fn-nco-receipt (fn-nco-at 0 st) serial)))
        (list :requested
              (list (fn-nco-at 0 st) serial token :requested nil nil
                    (list (list token receipt))))))
     ((and (eq op :complete) (eq phase :requested)
           (equal receipt (fn-nco-at 2 st))
           (fn-nco-terminalp (fn-nco-at 2 event)))
      (list :completed
            (list (fn-nco-at 0 st) (fn-nco-at 1 st) receipt
                  :completed (fn-nco-at 2 event) (fn-nco-at 3 event) nil)))
     ((and (eq op :release) (eq phase :completed)
           (equal receipt (fn-nco-at 2 st)))
      (list :released (list (fn-nco-at 0 st) (fn-nco-at 1 st) nil :idle nil nil nil)))
     (t (list :refused st)))))

; S2: issuance contains no work outcome and always returns the receipt in
; requested phase. No producer is called by this transition.
(defthm fn-nco-issued-receipt-is-requested
  (implies (equal (car (fn-nco-owner-step st event)) :requested)
           (let ((next (cadr (fn-nco-owner-step st event))))
             (and (equal (fn-nco-at 3 next) :requested)
                  (consp (fn-nco-at 2 next))
                  (not (fn-nco-at 4 next)) (not (fn-nco-at 5 next))))))

(defthm fn-nco-terminal-never-changes-without-release
  (implies (and (equal (fn-nco-at 3 st) :completed)
                (not (equal (fn-nco-at 0 event) :release)))
           (equal (fn-nco-owner-step st event) (list :refused st))))

; S3 safety and conditional progress: a matching terminal observation
; completes its requested receipt once. Status is this retained outcome;
; a second completion, even with a different terminal word, is refused.
; Liveness needs the producer to return an observation. Process death is
; uncertain, not a claimed completion (same scope as publication lifecycle).
(defthm fn-nco-receipt-completes-exactly-once
  (implies (and (equal (fn-nco-at 3 st) :requested)
                (equal token (fn-nco-at 2 st))
                (fn-nco-terminalp outcome))
           (let* ((r (fn-nco-owner-step st (list :complete token outcome reason)))
                  (next (cadr r)))
             (and (equal (car r) :completed)
                  (equal (fn-nco-at 3 next) :completed)
                  (equal (fn-nco-at 4 next) outcome)
                  (equal (fn-nco-at 5 next) reason)
                  (equal (fn-nco-owner-step next (list :complete token other why))
                         (list :refused next)))))
  :rule-classes nil)

(defthm fn-nco-completion-positive-witness
  (let* ((issued (cadr (fn-nco-owner-step (fn-nco-initial "epoch")
                        (list :request (caar *fn-nco-store-verbs*)))))
         (token (fn-nco-at 2 issued))
         (r (fn-nco-owner-step issued (list :complete token :accepted :installed))))
    (and (equal (fn-nco-at 3 issued) :requested)
         (equal token (fn-nco-at 2 issued))
         (fn-nco-terminalp :accepted)
         (equal (car r) :completed)
         (equal (fn-nco-at 4 (cadr r)) :accepted)
         (equal (fn-nco-at 5 (cadr r)) :installed)
         (equal (fn-nco-owner-step (cadr r) (list :complete token :refused :failed))
                (list :refused (cadr r)))))
  :rule-classes nil)

(defthm fn-nco-completion-needs-requested-witness
  (let* ((st '("epoch" 1 ("epoch" 1) :completed :accepted :installed))
         (token (fn-nco-at 2 st)))
    (and (equal token (fn-nco-at 2 st)) (fn-nco-terminalp :refused)
         (not (equal (fn-nco-at 3 st) :requested))
         (equal (fn-nco-owner-step st (list :complete token :refused :failed))
                (list :refused st))))
  :rule-classes nil)

; S4: work size and progress are deliberately not inputs to the deadline.
(defthm fn-nco-store-sized-deadline-by-definition
  (implies (equal (fn-nco-work-class kind argv) :store-sized)
           (equal (fn-nco-reply-seconds request-octets)
                  (+ *fn-nco-reply-grace-seconds*
                     (ceiling request-octets *fn-nco-observation-octets-per-second*)))))

(defun fn-nco-publication-word (target durable inflight requested deferred)
  (declare (xargs :guard t))
  (cond ((<= (nfix target) (nfix durable)) :compacted)
        ((natp inflight) :requested)
        (deferred :blocked)
        (requested :requested)
        (t :blocked)))

(local
 (defthm fn-nco-explode-characters
   (implies (and (natp n) (character-listp acc))
            (character-listp (explode-nonnegative-integer n 10 acc)))))

(defun fn-nco-token-text (token)
  (declare (xargs :guard t))
  (concatenate 'string
               (if (stringp (fn-nco-at 0 token)) (fn-nco-at 0 token) "")
               "-"
               (coerce (explode-nonnegative-integer
                        (nfix (fn-nco-at 1 token)) 10 nil) 'string)))


; A retry retains an earlier deferral until it publishes. That old word
; must not terminate the receipt for an attempt still in flight.
(defthm fn-nco-inflight-publication-keeps-observing
  (implies (and (< (nfix durable) (nfix target)) (natp inflight))
           (equal (fn-nco-publication-word target durable inflight requested deferred)
                  :requested)))


; Carried shape, used by proofs rather than revalidated on the served path.
(defun fn-nco-statep (st)
  (declare (xargs :guard t))
  (and (true-listp st) (equal (len st) 7)
       (fn-nco-no-orphanp st)
       (stringp (fn-nco-at 0 st)) (natp (fn-nco-at 1 st))
       (if (eq (fn-nco-at 3 st) :idle)
           (and (not (fn-nco-at 2 st)) (not (fn-nco-at 4 st)) (not (fn-nco-at 5 st)))
         (and (equal (fn-nco-at 2 st)
                     (fn-nco-receipt (fn-nco-at 0 st) (fn-nco-at 1 st)))
              (or (and (eq (fn-nco-at 3 st) :requested)
                       (not (fn-nco-at 4 st)) (not (fn-nco-at 5 st)))
                  (and (eq (fn-nco-at 3 st) :completed)
                       (fn-nco-terminalp (fn-nco-at 4 st))))))))

(defthm fn-nco-initial-state
  (implies (stringp epoch) (fn-nco-statep (fn-nco-initial epoch))))

(defthm fn-nco-owner-step-preserves-state
  (implies (fn-nco-statep st)
           (fn-nco-statep (cadr (fn-nco-owner-step st event)))))

(defthm fn-nco-new-receipt-advances-serial
  (implies (equal (car (fn-nco-owner-step st event)) :requested)
           (< (nfix (fn-nco-at 1 st))
              (fn-nco-at 1 (cadr (fn-nco-owner-step st event))))))

(defthm fn-nco-old-receipt-cannot-complete-new-work
  (implies (and (fn-nco-statep st)
                (< (nfix serial) (fn-nco-at 1 st)))
           (equal (fn-nco-owner-step
                   st (list :complete (fn-nco-receipt epoch serial) outcome reason))
                  (list :refused st))))

; S3a: initial and preserved over the actual owner entry. Repeated steps
; therefore cannot leave a requested receipt without its unique producer.
(defthm fn-nco-initial-has-no-orphan
  (fn-nco-no-orphanp (fn-nco-initial epoch)))

(defthm fn-nco-owner-step-has-no-orphan
  (implies (fn-nco-no-orphanp st)
           (fn-nco-no-orphanp (cadr (fn-nco-owner-step st event)))))

(defun fn-nco-owner-run (st events)
  (declare (xargs :guard (true-listp events)))
  (if (endp events) st
    (fn-nco-owner-run (cadr (fn-nco-owner-step st (car events))) (cdr events))))

(defthm fn-nco-owner-run-has-no-orphan
  (implies (fn-nco-no-orphanp st)
           (fn-nco-no-orphanp (fn-nco-owner-run st events)))
  :hints (("Goal" :in-theory (disable fn-nco-no-orphanp fn-nco-owner-step))))

(defthm fn-nco-reachable-receipts-have-one-job
  (fn-nco-no-orphanp (fn-nco-owner-run (fn-nco-initial epoch) events))
  :hints (("Goal" :use ((:instance fn-nco-owner-run-has-no-orphan
                                  (st (fn-nco-initial epoch))))
           :in-theory (disable fn-nco-no-orphanp fn-nco-owner-run fn-nco-initial))))

; The job is removed only by its outcome, atomically with completion.
(defthm fn-nco-only-job-outcome-leaves-requested
  (implies (and (fn-nco-no-orphanp st)
                (equal (fn-nco-at 3 st) :requested)
                (not (equal (fn-nco-at 3 (cadr (fn-nco-owner-step st event)))
                            :requested)))
           (and (equal (fn-nco-at 0 event) :complete)
                (equal (fn-nco-at 1 event) (fn-nco-at 0 (fn-nco-pending-job st)))
                (fn-nco-terminalp (fn-nco-at 2 event))
                (equal (car (fn-nco-owner-step st event)) :completed)
                (not (fn-nco-at 6 (cadr (fn-nco-owner-step st event)))))))
