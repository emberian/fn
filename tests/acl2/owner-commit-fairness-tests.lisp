; Witnesses and teeth for books/owner-commit-fairness.lisp (lane
; durability-bugs, 2026-09-28).  Every state is REACHED from fn-otm-init
; through the host's entries: the gate's pick (fn-otm-next,
; fnn-owner-gate-pick), the committer's wake (fn-otm-committer-wake,
; fnn-owner-commit-wake) and its events (fn-otm-commit-event,
; fnn-owner-commit-event).
(in-package "ACL2")
(include-book "../../books/owner-commit-fairness")

(defun ocft-class (s w) (mv-let (c s2) (fn-otm-next s w) (declare (ignore s2)) c))
(defun ocft-pick (s w) (mv-let (c s2) (fn-otm-next s w) (declare (ignore c)) s2))
(defun ocft-event (s e) (mv-let (a s2) (fn-otm-commit-event s e) (declare (ignore a)) s2))
(defun ocft-quantum (s w events)
  (mv-let (stopped seals s2) (fn-ocf-events (ocft-pick s w) events)
    (declare (ignore stopped seals))
    s2))

; Waiting counts, by slot (control reader poster transit commit inspect).
(defconst *ocft-commit* '(0 0 0 0 1 0))
(defconst *ocft-rc* '(0 3 0 0 1 0))        ; readers and the committer
(defconst *ocft-crc* '(1 3 0 0 1 0))       ; a control request too
(defconst *ocft-cr* '(1 3 0 0 0 0))

; --- The reached state: a batch in flight with the next batch open behind
; it, the moment a control request arrives.
(defconst *ocft-s1* (ocft-quantum (fn-otm-init) *ocft-commit* '(:started)))
(assert-event (equal (fn-otm-phase *ocft-s1*) :staged))
; No control waits yet: the committer prepares the next batch.
(assert-event (equal (fn-otm-committer-wake *ocft-s1* nil t *ocft-rc*) :start-next))
(defconst *ocft-open* (ocft-quantum *ocft-s1* *ocft-rc* '(:next-started)))
(assert-event (and (equal (fn-otm-phase *ocft-open*) :staged) (fn-otm-open-next *ocft-open*)))
; Now a control request waits: no further START-NEXT (the rule).
(assert-event (equal (fn-otm-committer-wake *ocft-open* nil t *ocft-crc*) :wait))
(assert-event (equal (fn-otm-committer-wake *ocft-open* t t *ocft-crc*) :collect))

; --- Reached positive witness of the keystone.  The barrier returns; the
; COMPLETE seals the open batch; a reader reads during its barrier; its
; COMPLETE leaves flight; the next pick is the control request's.
(defconst *ocft-walk*
  (list (list *ocft-crc* '(:fenced :completed))
        (list *ocft-cr* nil)
        (list *ocft-crc* '(:fenced :completed))
        (list *ocft-crc* nil)))
; The antecedent, clause by clause: control waits at every pick ...
(assert-event (fn-ocf-okp *ocft-open* *ocft-walk*))
; ... the picks are the COMPLETE, a reader in flight, the COMPLETE, control.
(assert-event (equal (ocft-class *ocft-open* *ocft-crc*) :commit))
(defconst *ocft-w1* (ocft-quantum *ocft-open* *ocft-crc* '(:fenced :completed)))
(assert-event (and (equal (fn-otm-phase *ocft-w1*) :staged) (not (fn-otm-open-next *ocft-w1*))))
;; The pass budget: one :commit quantum ran in flight while control waited,
;; so a START-NEXT is still allowed (*fn-ocp-pass-bound* = 4) ...
(assert-event (equal (fn-ocp-passes (fn-otm-ocp *ocft-w1*)) 1))
(assert-event (equal (fn-otm-committer-wake *ocft-w1* nil t *ocft-crc*) :start-next))
(assert-event (equal (ocft-class *ocft-w1* *ocft-cr*) :reader))
(defconst *ocft-w2* (ocft-pick *ocft-w1* *ocft-cr*))
(assert-event (equal (ocft-class *ocft-w2* *ocft-crc*) :commit))
(defconst *ocft-w3* (ocft-quantum *ocft-w2* *ocft-crc* '(:fenced :completed)))
(assert-event (equal (fn-otm-phase *ocft-w3*) :idle))
(assert-event (equal (ocft-class *ocft-w3* *ocft-crc*) :control))
; The conclusion: two counted quanta (the two COMPLETEs), one seal (the open
; batch's), both within the keystone's bound.
(assert-event (equal (fn-ocf-delay *ocft-open* *ocft-walk*) 2))
(assert-event (equal (fn-ocf-seals *ocft-open* *ocft-walk*) 1))
(assert-event (and (<= (fn-ocf-delay *ocft-open* *ocft-walk*) 22)
                   (<= (fn-ocf-seals *ocft-open* *ocft-walk*) 6)))

; --- The starvation counterexample: the policy BEFORE this lane (the wake
; ignored the waiting control request).  Under it the committer prepares a
; next batch behind every barrier and the control request is never admitted:
; the walk below is the old okp's (every clause but the wake's), the pipeline
; never leaves flight, and the counts grow with the walk's length.
(defun ocft-old-quantum-okp (s events)
  ;; fn-ocf-quantum-okp with the pre-lane wake (no BLOCKED argument).
  (if (fn-ocs-in-flight-p (fn-otm-phase s))
      (or (equal events '(:next-none)) (equal events '(:next-uncertain))
          (and (equal events '(:next-started))
               (equal (fn-ocp-wake (fn-otm-phase s) (fn-otm-open-next s) nil t nil)
                      :start-next))
          (equal events '(:fenced :completed)) (equal events '(:failed :completed)))
    (or (equal events '(:started)) (equal events '(:started-none))
        (equal events '(:started-uncertain)))))

(defun ocft-old-okp (s items)
  (declare (xargs :measure (len items)))
  (if (consp items)
      (let ((w (fn-ocf-item-w (car items))))
        (mv-let (class picked) (fn-otm-next s w)
          (mv-let (c stopped seals s2) (fn-ocf-step s (car items))
            (declare (ignore c seals))
            (and (posp (fn-osch-waits 0 w))
                 (implies (eq class :commit)
                          (ocft-old-quantum-okp picked (fn-ocf-item-events (car items))))
                 (or (eq class :control) stopped (ocft-old-okp s2 (cdr items)))))))
    t))

(defun ocft-unfair (n)
  (if (zp n)
      nil
    (list* (list *ocft-crc* '(:next-started))
           (list *ocft-crc* '(:fenced :completed))
           (ocft-unfair (- n 1)))))

(defconst *ocft-starve* (ocft-unfair 12))
(assert-event (ocft-old-okp *ocft-w1* *ocft-starve*))
(assert-event (not (fn-ocf-okp *ocft-w1* *ocft-starve*)))
(assert-event (equal (fn-ocf-seals *ocft-w1* *ocft-starve*) 12))
(assert-event (equal (fn-ocf-delay *ocft-w1* *ocft-starve*) 24))
(assert-event (not (<= (fn-ocf-delay *ocft-w1* *ocft-starve*) 22)))
(assert-event (not (<= (fn-ocf-seals *ocft-w1* *ocft-starve*) 6)))

; --- Hypothesis removal: control does NOT wait at the picks.  Every other
; clause holds (the wake is :start-next at each START-NEXT, the shapes are
; the host's), and the conclusion fails: without a waiter nothing stops the
; pipeline, which is the point.
(defun ocft-busy (n)
  (if (zp n)
      nil
    (list* (list *ocft-rc* '(:next-started)) (list *ocft-rc* '(:fenced :completed))
           (ocft-busy (- n 1)))))
(defconst *ocft-nocontrol* (ocft-busy 7))
(assert-event (not (posp (fn-osch-waits 0 *ocft-rc*))))
(assert-event (equal (fn-otm-committer-wake *ocft-w1* nil t *ocft-rc*) :start-next))
(assert-event (not (fn-ocf-okp *ocft-w1* *ocft-nocontrol*)))
(assert-event (equal (fn-ocf-seals *ocft-w1* *ocft-nocontrol*) 7))
(assert-event (not (<= (fn-ocf-seals *ocft-w1* *ocft-nocontrol*) 6)))

; --- Hypothesis removal: a :commit quantum outside the host's shapes (a
; START that seals, completes and starts again inside one quantum).  Control
; waits at every pick; the commit pick is due (four readers were served
; while it waited, before the control request arrived); the conclusion's
; seal count fails.
(defconst *ocft-due*
  (ocft-pick (ocft-pick (ocft-pick (ocft-pick (fn-otm-init) *ocft-rc*) *ocft-rc*)
                        *ocft-rc*)
             *ocft-rc*))
(assert-event (equal (fn-ocm-skipped (fn-ocf-ocm *ocft-due*)) 4))
(assert-event (equal (ocft-class *ocft-due* *ocft-crc*) :commit))
(defconst *ocft-bad-shape*
  (list (list *ocft-crc* '(:started :fenced :completed :started :fenced :completed :started :fenced :completed :started :fenced :completed :started :fenced :completed :started :fenced :completed :started))))
(assert-event (posp (fn-osch-waits 0 *ocft-crc*)))
(assert-event (not (fn-ocf-quantum-okp (ocft-pick *ocft-due* *ocft-crc*) *ocft-crc*
                                       '(:started :fenced :completed :started :fenced :completed :started :fenced :completed :started :fenced :completed :started :fenced :completed :started :fenced :completed :started))))
(assert-event (not (fn-ocf-okp *ocft-due* *ocft-bad-shape*)))
(assert-event (equal (fn-ocf-seals *ocft-due* *ocft-bad-shape*) 7))
(assert-event (not (<= (fn-ocf-seals *ocft-due* *ocft-bad-shape*) 6)))
; The same due START in the host's shape: one seal, then the control pick
; after its COMPLETE.
(defconst *ocft-good-shape*
  (list (list *ocft-crc* '(:started)) (list *ocft-crc* '(:fenced :completed))
        (list *ocft-crc* nil)))
(assert-event (fn-ocf-okp *ocft-due* *ocft-good-shape*))
(assert-event (equal (fn-ocf-seals *ocft-due* *ocft-good-shape*) 1))
(assert-event (equal (fn-ocf-delay *ocft-due* *ocft-good-shape*) 2))

;; --- The budget spent: from *ocft-w1* (one pass) the committer still
; prepares a batch behind the barrier while control waits; each START-NEXT
; and COMPLETE is a :commit quantum in flight that counts a pass; at four the
; wake stops the pipeline, the batches complete, the owner leaves flight and
; control is admitted.
(defconst *ocft-budget-walk*
  (list (list *ocft-crc* '(:next-started)) (list *ocft-crc* '(:fenced :completed))
        (list *ocft-crc* '(:fenced :completed)) (list *ocft-crc* nil)))
(assert-event (fn-ocf-okp *ocft-w1* *ocft-budget-walk*))
(assert-event (equal (fn-ocf-seals *ocft-w1* *ocft-budget-walk*) 1))
(assert-event (equal (fn-ocf-delay *ocft-w1* *ocft-budget-walk*) 3))
(defconst *ocft-b3* (ocft-quantum (ocft-quantum *ocft-w1* *ocft-crc* '(:next-started))
                                  *ocft-crc* '(:fenced :completed)))
(assert-event (equal (fn-ocp-passes (fn-otm-ocp *ocft-b3*)) 3))
(assert-event (equal (fn-otm-phase *ocft-b3*) :staged))
(defconst *ocft-b4* (ocft-pick *ocft-b3* *ocft-crc*))
(assert-event (equal (fn-ocp-passes (fn-otm-ocp *ocft-b4*)) 4))
(assert-event (equal (fn-otm-committer-wake *ocft-b4* nil t *ocft-crc*) :wait))
; A START-NEXT at the fourth pass is outside the hypothesis (its wake is :wait).
(assert-event (not (fn-ocf-okp *ocft-b3* (list (list *ocft-crc* '(:next-started))))))
