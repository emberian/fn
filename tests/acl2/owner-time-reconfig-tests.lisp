; Ground witnesses and teeth for books/owner-time-reconfig.lisp (the gate's
; hold for a phased live reconfiguration).
(in-package "ACL2")
(include-book "../../books/owner-time-reconfig")
(include-book "../../books/defkeystone")

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

; RULING19-MODEL-AWAITS-HOST: model admission, not a host-lock claim.
(defteeth fn-otm-hold-admits-only-inspect-commit-and-reader
  :claim (((held (fn-otm-holdp s)))
          (and (member-equal (mv-nth 0 (fn-otm-hold-next s w)) '(:inspect :commit :reader nil))
               (fn-otm-holdp (mv-nth 1 (fn-otm-hold-next s w)))))
  :witness ((s *otr-held*) (w '(1 1 0 0 0 0)))
  :breaks ((held ((s (fn-otm-init)) (w '(1 0 0 0 0 0)))))
  :mutations ((control-during-hold
               (:conclusion (equal (mv-nth 0 (fn-otm-hold-next s w)) :control))
               ((s *otr-held*) (w '(1 0 0 0 0 0)))
               :fault "a waiting control quantum runs while reconfiguration holds")))

(defteeth fn-otm-hold-stops-the-committer
  :claim (((held (fn-otm-holdp s)))
          (and (not (fn-otm-committer-may-start s))
               (equal (fn-otm-held-committer-wake s returned queued w) :wait)
               (equal (mv-nth 0 (fn-otm-held-event s event)) :fault)))
  :witness ((s *otr-held*) (returned t) (queued t)
            (w '(1 0 0 0 0 0)) (event :started))
  :breaks ((held ((s (fn-otm-init)))))
  :mutations ((committer-collects
               (:conclusion (equal (fn-otm-held-committer-wake s returned queued w) :collect))
               ((s *otr-held*) (returned t) (queued t)
                (w '(1 0 0 0 0 0)) (event :started))
               :fault "a returned sync wakes the committer despite the reconfiguration hold")))

; H4 is unconditional: its branch conditions belong to the conclusion.
(defteeth fn-otm-hold-begin-and-end
  :claim (()
          (and (iff (equal (mv-nth 0 (fn-otm-hold-begin s)) :held)
                    (and (not (fn-otm-held s)) (not (fn-ocs-in-flight-p (fn-otm-phase-of s)))))
               (implies (equal (mv-nth 0 (fn-otm-hold-begin s)) :held)
                        (fn-otm-holdp (mv-nth 1 (fn-otm-hold-begin s))))
               (implies (not (equal (mv-nth 0 (fn-otm-hold-begin s)) :held))
                        (and (equal (mv-nth 0 (fn-otm-hold-begin s)) :busy)
                             (equal (mv-nth 1 (fn-otm-hold-begin s)) s)))
               (implies (fn-otm-holdp s)
                        (and (equal (mv-nth 0 (fn-otm-hold-end s)) :released)
                             (not (fn-otm-held (mv-nth 1 (fn-otm-hold-end s))))
                             (not (fn-ocs-in-flight-p (fn-otm-phase-of (mv-nth 1 (fn-otm-hold-end s)))))))))
  :witness ((s *otr-held*))
  :breaks ()
  :mutations ((reentrant-hold
               (:conclusion (equal (mv-nth 0 (fn-otm-hold-begin s)) :held))
               ((s *otr-held*))
               :fault "a second reconfiguration acquires an already held slot")
              (busy-clears-hold
               (:conclusion (not (fn-otm-held (mv-nth 1 (fn-otm-hold-begin s)))))
               ((s *otr-held*))
               :fault "a busy begin clears the first reconfiguration's hold")
              (end-keeps-hold
               (:conclusion (fn-otm-held (mv-nth 1 (fn-otm-hold-end s))))
               ((s *otr-held*))
               :fault "ending a reconfiguration leaks its hold")))

; The successful-begin branch cannot coincide with the busy/end witness.
(assert-event
 (let ((s (fn-otm-init)))
   (and (not (fn-otm-held s))
        (not (fn-ocs-in-flight-p (fn-otm-phase-of s)))
        (equal (otr-word (fn-otm-hold-begin s)) :held)
        (fn-otm-holdp (otr-state (fn-otm-hold-begin s))))))

(defteeth-check)
