; Ground run of the held commit over the owner's scheduler value
; (books/owner-time-held.lisp, ruling 19).
(in-package "ACL2")
(include-book "../../books/owner-time-held")

(defun oth-s (s e)
  (declare (xargs :guard t))
  (mv-let (a s2) (fn-otm-held-event s e) (declare (ignore a)) s2))
(defun oth-a (s e)
  (declare (xargs :guard t))
  (mv-let (a s2) (fn-otm-held-event s e) (declare (ignore s2)) a))
(defun oth-next (s w)
  (declare (xargs :guard t))
  (mv-let (c s2) (fn-otm-next s w) (declare (ignore c)) s2))

(defconst *oth-w0* '(0 0 0 0 0 0))

; Quantum 1: START captured a batch for a caller holding its submission.
(defconst *oth-s1* (oth-s (fn-otm-init) :started-held))
(assert-event (equal (oth-a (fn-otm-init) :started-held) :sync))
(assert-event (and (fn-otm-held *oth-s1*) (equal (fn-otm-phase-of *oth-s1*) :staged)))

; Between the quanta the gate's entries keep the slot, the committer waits
; (even with a returned sync and queued members) and the caller collects
; only once the sync returned.
(assert-event (fn-otm-held (oth-next *oth-s1* *oth-w0*)))
(assert-event (equal (fn-otm-held-committer-wake *oth-s1* t t *oth-w0*) :wait))
(assert-event (equal (fn-otm-held-caller-wake *oth-s1* nil) :wait))
(assert-event (equal (fn-otm-held-caller-wake *oth-s1* t) :collect))

; Teeth: the same value without the slot wakes the committer to collect.
(assert-event (equal (fn-otm-committer-wake *oth-s1* t t *oth-w0*) :collect))

; Quantum 2: fenced, COMPLETE, then the held submission; the slot clears.
(defconst *oth-s2* (oth-s *oth-s1* :fenced))
(assert-event (equal (oth-a *oth-s1* :fenced) :complete))
(assert-event (equal (oth-a *oth-s2* :completed) :submit))
(assert-event (not (fn-otm-held (oth-s *oth-s2* :completed))))
(assert-event (equal (fn-otm-phase-of (oth-s *oth-s2* :completed)) :idle))

; A failed sync stops and takes no submission.
(assert-event (equal (oth-a *oth-s1* :failed) :stop))
(assert-event (equal (oth-a (oth-s *oth-s1* :failed)
                                                  :completed)
                     :none))
