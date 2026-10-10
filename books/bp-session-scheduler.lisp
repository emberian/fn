; Listener generation plus admitted retained sessions; installation stays the
; existing single-writer machine. Its old scalar session consumer is separate.
(in-package "ACL2")
(include-book "bp-node-listener-control")
(include-book "resource-bp-session")
(include-book "def-loop")
(defun fn-bpsg-livep (row fn-resource-ledger)
 (declare (xargs :stobjs fn-resource-ledger :guard t :verify-guards nil))
 (and (fn-rl-wfp fn-resource-ledger) (true-listp row) (equal (len row) 6)
      (equal (first row) :bp-session-grant) (natp (second row)) (natp (third row))
      (< (second row) (fn-rl-count fn-resource-ledger))
      (equal (fn-rl-phasesi (second row) fn-resource-ledger) 1)
      (equal (fn-rl-gensi (second row) fn-resource-ledger) (third row))))
(verify-guards fn-bpsg-livep :hints (("Goal" :in-theory (enable fn-rl-wfp))))
(defun fn-bpsched-accept-plan (st index row fn-resource-ledger)
 (declare (xargs :stobjs fn-resource-ledger :guard t))
 (and (fn-bpsg-livep row fn-resource-ledger)
      (equal (fourth row) :incoming)
      (not (fifth row)) (not (sixth row))
      (equal (fn-bplc-phase st) :stable)
      (natp index) (< index (len (fn-bplc-ports st)))
      (list :accept (fn-bplc-generation st) (fn-ncfg-nth index (fn-bplc-ports st)))))
(def-loop fn-bpsched-remove (key xs)
  :shape :map :over xs :elt x
  :keep (not (equal key (fn-ag-car x)))
  :body x)
(defun fn-bpsched-session-view (rows)
 (declare (xargs :guard t))
 (and (consp rows)
      (list :accept (fn-ncfg-nth 1 (car rows)) (fn-ncfg-nth 2 (car rows)) rows)))
(defun fn-bpsched-listener-step (st event)
 (declare (xargs :guard t))
 (let ((rows (fn-ncfg-nth 3 (fn-bplc-session st))))
  (case (fn-ag-car event)
   (:retained-accepted
    (let ((plan (fn-ncfg-nth 2 event)))
     (fn-bplc-with-session st
      (fn-bpsched-session-view
       (fn-ag-append rows (list (list (fn-ncfg-nth 1 event)
                          (fn-ncfg-nth 1 plan) (fn-ncfg-nth 2 plan))))))))
   (:retained-closed
    (fn-bplc-with-session st
     (fn-bpsched-session-view (fn-bpsched-remove (fn-ncfg-nth 1 event) rows))))
   (otherwise (fn-bplc-step st event)))))
; The node loop's local service for this pass.  CUSTODY-UNRELEASED: some
; retained session accepted an inbound transfer (its final XFER_ACK queued,
; fn-tcl-delivery-plan-progress-p) and that session's own turn has not yet
; written the ACK and run its progress.  Dispatch hands accepted custody to
; the application, and an application fence ends every session: dispatching
; first lost the owed ACK, so the sender saw an interrupted transfer for a
; custody this node holds (CONVERGE-2 row 22, test_bp_node_native).  The
; session's own progress turn, which follows the actual ACK write
; (host/native/tcpcl.lisp fnn-tcl-turn-local), dispatches it instead.
(defun fn-bpsched-service (phase custody-unreleased)
 (declare (xargs :guard t))
 (let ((service (nth (mod (nfix phase) 8)
                     '(:fragment :dispatch :expiry :outbox :forward :receipt :report :rotation))))
  (if (and custody-unreleased (equal service :dispatch)) :custody-wait service)))

; KEYSTONE: no dispatch while an accepted custody's ACK may still be owed.
(defthm fn-bpsched-no-dispatch-before-acknowledged-custody-is-released
 (implies custody-unreleased
          (not (equal (fn-bpsched-service phase custody-unreleased) :dispatch))))

; ... and otherwise the rotation is unchanged: every pass still reaches
; dispatch once custody is released (no starvation by this rule).
(defthm fn-bpsched-service-without-unreleased-custody-is-the-rotation
 (equal (fn-bpsched-service phase nil)
        (nth (mod (nfix phase) 8)
             '(:fragment :dispatch :expiry :outbox :forward :receipt :report :rotation))))

; Teeth: the rule bites at the dispatch phase and only there.
(defthm fn-bpsched-custody-wait-teeth
 (and (equal (fn-bpsched-service 1 t) :custody-wait)
      (equal (fn-bpsched-service 1 nil) :dispatch)
      (equal (fn-bpsched-service 0 t) :fragment))
 :rule-classes nil)
(defun fn-bpsched-next (phase)
 (declare (xargs :guard t)) (mod (+ 1 (nfix phase)) 8))

(defun fn-bpsched-next-slot (slot count)
 (declare (xargs :guard t))
 (if (and (natp slot) (natp count) (<= 2 slot) (< (+ 1 slot) count))
  (+ 1 slot) 2))

(defun fn-bpsched-listener-index (cursor count)
 (declare (xargs :guard t))
 (if (posp count) (mod (nfix cursor) count) 0))
(defun fn-bpsched-deadline (now grant)
 (declare (xargs :guard (true-listp grant))) (+ (nfix now) (nfix (seventh grant))))
(defun fn-bpsched-timeout-p (now deadline)
 (declare (xargs :guard t)) (and (natp deadline) (<= deadline (nfix now))))
(defun fn-bpsched-forward-entry (plan busy)
 (declare (xargs :guard (true-listp busy)))
 (if (consp plan)
  (if (member-equal (fn-ag-car (car plan)) busy)
   (fn-bpsched-forward-entry (cdr plan) busy) (car plan)) nil))

; A completed bounded input/source/output action prepays one slot sweep without
; an artificial sleep at every empty slot. Idle/local polling does not do so.
; This is scheduling cadence, not a resource return or overall latency bound.
(defun fn-bpsched-work-credit (status action previous slots)
 (declare (xargs :guard t))
 (if (and (eq status :work) (member-eq action '(:source :buffer :encode :write)))
  (nfix slots) (if (zp (nfix previous)) 0 (1- (nfix previous)))))
(defun fn-bpsched-idle-p (credit)
 (declare (xargs :guard t)) (zp (nfix credit)))

; ---------------------------------------------------------------------------
; The rotation drain (FILL-BP-FRAGMENT-NODE-10MIB).  The serve rotates its
; journal at a :rotation turn only when the session bank holds nothing,
; because no retained operation may cross an owner reopen
; (host/native/bp-node.lisp, the :rotation arm).  Whether the rotation is due
; is ACL2's fn-bpnrd-serve-rotation-due-p.  Measured at image d8fb738b3 on
; SCN-077, with four senders: over 14,853 :rotation turns between 1,000 and
; 1,311 records, ACL2's conjuncts held at every turn, and the bank held one or
; two sessions at every turn but the last.  The rotation was therefore
; starved until the sender stopped.  So while a rotation is due, the loop
; admits no new inbound session (host/native/bp-session.lisp
; fnn-bp-session-loop, ADMIT): the bank drains, and the next :rotation turn
; takes the rotation.  DECLINED means the last due turn's in-place recovery
; did not rotate (the open-time decision fn-bpnrd-due-rotation-event
; refused).  Admission then stays open, so a refused rotation never closes
; the listener.
(defun fn-bpsched-admit-p (due declined)
 (declare (xargs :guard t))
 (or (not due) (if declined t nil)))

(defthm fn-bpsched-refused-rotation-keeps-admission-open
 (and (fn-bpsched-admit-p due t)
      (fn-bpsched-admit-p nil declined)
      (iff (fn-bpsched-admit-p due declined) (or (not due) declined))))

; One pass of fnn-bp-session-loop, reduced to the bank's count, in the loop's
; order.  First a readable connection is accepted, when admission is open.
; Then the slot turn may end DEPARTED sessions.  Then the pass's service runs.
(defun fn-bpsched-bank-after (held due declined arrival departed)
 (declare (xargs :guard t))
 (nfix (- (+ (nfix held) (if (and arrival (fn-bpsched-admit-p due declined)) 1 0))
          (nfix departed))))

; Whether a due rotation is taken within PASSES.  Each pass is
; (ARRIVAL DEPARTED CUSTODY-UNRELEASED).  A pass whose service is :rotation
; and whose bank is empty takes the rotation.
(defun fn-bpsched-rotates-within (phase held due declined passes)
 (declare (xargs :guard t :measure (acl2-count passes)))
 (if (atom passes) nil
  (let* ((pass (car passes))
         (held (fn-bpsched-bank-after held due declined
                                      (fn-ncfg-nth 0 pass) (fn-ncfg-nth 1 pass))))
   (or (and due
            (equal (fn-bpsched-service phase (fn-ncfg-nth 2 pass)) :rotation)
            (zerop held))
       (fn-bpsched-rotates-within (fn-bpsched-next phase) held due declined (cdr passes))))))

; The sessions that end in the first K passes.
(defun fn-bpsched-departed (k passes)
 (declare (xargs :guard t :measure (acl2-count passes)))
 (if (or (not (posp k)) (atom passes)) 0
  (+ (nfix (fn-ncfg-nth 1 (car passes)))
     (fn-bpsched-departed (1- k) (cdr passes)))))

(local (include-book "arithmetic-5/top" :dir :system))

(local
 (defthm fn-bpsched-service-rotation-iff
  (equal (equal (fn-bpsched-service phase c) :rotation)
         (equal (mod (nfix phase) 8) 7))
  :hints (("Goal" :in-theory (enable fn-bpsched-service)
           :cases ((equal (mod (nfix phase) 8) 0) (equal (mod (nfix phase) 8) 1)
                   (equal (mod (nfix phase) 8) 2) (equal (mod (nfix phase) 8) 3)
                   (equal (mod (nfix phase) 8) 4) (equal (mod (nfix phase) 8) 5)
                   (equal (mod (nfix phase) 8) 6) (equal (mod (nfix phase) 8) 7))))))
(local
 (defthm fn-bpsched-bank-after-drained
  (implies (and due (zerop (nfix held)))
           (equal (fn-bpsched-bank-after held due nil arrival departed) 0))))
(local
 (defun fn-bpsched-to-rotation (phase)
  (mod (- 7 (mod (nfix phase) 8)) 8)))
(local
 (defthm fn-bpsched-to-rotation-next
  (implies (not (equal (mod (nfix phase) 8) 7))
           (equal (fn-bpsched-to-rotation (fn-bpsched-next phase))
                  (1- (fn-bpsched-to-rotation phase))))))
(local
 (defthm fn-bpsched-to-rotation-zero
  (equal (equal (fn-bpsched-to-rotation phase) 0) (equal (mod (nfix phase) 8) 7))))
(local
 (defthm fn-bpsched-to-rotation-bound
  (<= (fn-bpsched-to-rotation phase) 7) :rule-classes :linear))
(local
 (defthm fn-bpsched-drained-bank-rotates
  (implies (and due (zerop (nfix held))
                (< (fn-bpsched-to-rotation phase) (len passes)))
           (fn-bpsched-rotates-within phase held due nil passes))
  :hints (("Goal" :in-theory (disable fn-bpsched-to-rotation fn-bpsched-next
                                      fn-bpsched-bank-after fn-bpsched-service)))))

; While a rotation is due and has not been refused, the bank never grows.
(defthm fn-bpsched-due-rotation-drain-never-grows-the-bank
 (implies (and due (not declined))
          (<= (fn-bpsched-bank-after held due declined arrival departed) (nfix held)))
 :rule-classes :linear)

(local
 (defthm fn-bpsched-drain-step-within-departures
  (implies (and due (<= (nfix held) (+ (nfix d) x)) (natp x))
           (<= (fn-bpsched-bank-after held due nil a d) x))
  :rule-classes nil))
(local
 (defun fn-bpsched-drain-induction (k phase held due passes)
  (declare (xargs :measure (acl2-count passes)))
  (if (or (not (posp k)) (atom passes)) (list phase held due)
   (fn-bpsched-drain-induction
    (1- k) (fn-bpsched-next phase)
    (fn-bpsched-bank-after held due nil (fn-ncfg-nth 0 (car passes)) (fn-ncfg-nth 1 (car passes)))
    due (cdr passes)))))
(local
 (defthm fn-bpsched-departed-natp
  (natp (fn-bpsched-departed k passes)) :rule-classes :type-prescription))

; KEYSTONE (fairness of the due rotation).  Suppose a rotation is due and has
; not been refused, and the sessions that end in the first K passes cover the
; bank.  Then the rotation is taken within K + 8 passes, whatever arrives,
; whatever the custody flags are, and from any phase.  Arrivals cannot starve
; it.
(defthm fn-bpsched-due-rotation-is-taken-once-the-bank-drains
 (implies (and due
               (<= (nfix held) (fn-bpsched-departed k passes))
               (<= (+ (nfix k) 8) (len passes)))
          (fn-bpsched-rotates-within phase held due nil passes))
 :hints (("Goal" :induct (fn-bpsched-drain-induction k phase held due passes)
          :in-theory (disable fn-bpsched-to-rotation fn-bpsched-next
                              fn-bpsched-bank-after fn-bpsched-service))
         ("Subgoal *1/3" :use ((:instance fn-bpsched-drained-bank-rotates)))
         ("Subgoal *1/1" :use ((:instance fn-bpsched-drained-bank-rotates)))
         ("Subgoal *1/2" :use ((:instance fn-bpsched-drain-step-within-departures
                                (d (fn-ncfg-nth 1 (car passes)))
                                (a (fn-ncfg-nth 0 (car passes)))
                                (x (fn-bpsched-departed (1- k) (cdr passes))))))))

; Witnesses.  Satisfiable: one session is held, it ends in the first pass,
; and a new connection arrives at every pass, as with SCN-077's senders.
; Under the drain the rotation is taken (the premise holds, with K = 1).
; Teeth: under the same arrivals with admission left open (the rule before
; this one), the bank holds one session at every turn and the rotation is
; never taken.  The window is tight: an empty bank at phase 0 needs all 8
; passes.
(defthm fn-bpsched-due-rotation-drain-witnesses
 (let ((passes (make-list 64 :initial-element '(t 1 nil))))
  (and (<= 1 (fn-bpsched-departed 1 passes))
       (fn-bpsched-rotates-within 0 1 t nil passes)
       (not (fn-bpsched-rotates-within 0 1 t t passes))
       (fn-bpsched-rotates-within 0 0 t nil (take 8 passes))
       (not (fn-bpsched-rotates-within 0 0 t nil (take 7 passes)))))
 :rule-classes nil)
