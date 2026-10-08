; Ground witnesses and teeth for books/owner-time-reconfig.lisp (the gate's
; hold for a phased live reconfiguration).
(in-package "ACL2")
(include-book "../../books/owner-time-reconfig")

(defmacro otr-word (form) `(mv-let (w s) ,form (declare (ignore s)) w))
(defmacro otr-state (form) `(mv-let (w s) ,form (declare (ignore w)) s))

(defconst *otr-held* (mv-let (word s) (fn-otm-hold-begin (fn-otm-init))
                       (declare (ignore word)) s))
(assert-event (equal (otr-word (fn-otm-hold-begin (fn-otm-init))) :held))
(assert-event (fn-otm-holdp *otr-held*))
; H4: a second reconfiguration asking for the hold is :busy.
(assert-event (equal (otr-word (fn-otm-hold-begin *otr-held*)) :busy))

; H1 with teeth: a waiting control quantum (slot 0) is picked without the
; hold and not under it; a waiting reader is picked under it.
(assert-event (equal (otr-word (fn-otm-next (fn-otm-init) '(1 0 0 0 0 0))) :control))
(assert-event (equal (otr-word (fn-otm-hold-next *otr-held* '(1 0 0 0 0 0))) nil))
(assert-event (equal (otr-word (fn-otm-hold-next *otr-held* '(1 1 0 0 0 0))) :reader))
(assert-event (equal (otr-word (fn-otm-hold-next *otr-held* '(1 0 1 1 1 0))) :commit))
(assert-event (fn-otm-holdp (otr-state (fn-otm-hold-next *otr-held* '(1 1 0 0 0 0)))))

; H3 with teeth: an idle owner without the hold lets the committer start;
; under the hold it may not, and a START event faults.
(assert-event (fn-otm-committer-may-start (fn-otm-init)))
(assert-event (not (fn-otm-committer-may-start *otr-held*)))
(assert-event (equal (otr-word (fn-otm-held-event *otr-held* :started)) :fault))
(assert-event (not (equal (otr-word (fn-otm-held-event (fn-otm-init) :started)) :fault)))

; H4: the end releases the hold; an end without one faults.
(assert-event (equal (otr-word (fn-otm-hold-end *otr-held*)) :released))
(assert-event (not (fn-otm-held (otr-state (fn-otm-hold-end *otr-held*)))))
(assert-event (equal (otr-word (fn-otm-hold-end (fn-otm-init))) :fault))
