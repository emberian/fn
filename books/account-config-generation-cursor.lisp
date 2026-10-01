; Actual one-entry generation projection preparation for typed C adoption.
; A differing entry requests the general bounded rebuild; no row is skipped.
(in-package "ACL2")
(include-book "config")
(include-book "consumer-position-fields")

(defun fn-acg-state (phase rows old-generation new-generation)
 (declare (xargs :guard t))
 (list :account-config-generation phase rows old-generation new-generation))

(defun fn-acg-begin (rows old-generation new-generation)
 (declare (xargs :guard t))
 (fn-acg-state :scan rows old-generation new-generation))

(defun fn-acg-tick (s)
 (declare (xargs :guard t))
 (let ((rows (fn-cp-nth 2 s)) (old (fn-cp-nth 3 s)) (new (fn-cp-nth 4 s)))
  (case (fn-cp-nth 1 s)
   (:scan
    (if (consp rows)
        (if (equal (fn-cfg-entry-livep (car rows) old)
                   (fn-cfg-entry-livep (car rows) new))
            (list :yield (fn-acg-state :scan (cdr rows) old new))
          (list :rebuild s))
      (list :ready (fn-acg-state :ready nil old new))))
   (:ready (list :ready s))
   (otherwise '(:refused :configuration-generation-phase)))))

; Proof-only complete observation of the actual per-cell predicate.
(defun fn-acg-rows-samep (rows old new)
 (declare (xargs :guard t))
 (if (consp rows)
     (and (equal (fn-cfg-entry-livep (car rows) old)
                 (fn-cfg-entry-livep (car rows) new))
          (fn-acg-rows-samep (cdr rows) old new))
   t))

(defun fn-acg-reachablep (s)
 (declare (xargs :guard t))
 (and (true-listp s) (equal (len s) 5)
      (eq (fn-cp-nth 0 s) :account-config-generation)
      (true-listp (fn-cp-nth 2 s))
      (or (eq (fn-cp-nth 1 s) :scan)
          (and (eq (fn-cp-nth 1 s) :ready) (null (fn-cp-nth 2 s))))))

(defun fn-acg-requirement (s)
 (declare (xargs :guard t))
 (fn-acg-rows-samep (fn-cp-nth 2 s) (fn-cp-nth 3 s) (fn-cp-nth 4 s)))

(defun fn-acg-rank (s)
 (declare (xargs :guard t))
 (if (eq (fn-cp-nth 1 s) :scan) (1+ (len (fn-cp-nth 2 s))) 0))

(defthm fn-acg-begin-establishes-complete-requirement
 (implies (true-listp rows)
          (and (fn-acg-reachablep (fn-acg-begin rows old new))
               (equal (fn-acg-requirement (fn-acg-begin rows old new))
                      (fn-acg-rows-samep rows old new))))
 :hints (("Goal" :in-theory (enable fn-acg-state fn-acg-begin fn-acg-reachablep
                                     fn-acg-requirement fn-cp-nth))))

(defthm fn-acg-tick-preserves-complete-requirement
 (implies (fn-acg-reachablep s)
          (and (fn-acg-reachablep (fn-cp-nth 1 (fn-acg-tick s)))
               (equal (fn-acg-requirement (fn-cp-nth 1 (fn-acg-tick s)))
                      (fn-acg-requirement s))))
 :hints (("Goal" :in-theory (e/d (fn-acg-state fn-acg-tick fn-acg-reachablep
                                  fn-acg-requirement fn-acg-rows-samep fn-cp-nth)
                                 (fn-cfg-entry-livep)))))

(defthm fn-acg-ready-requires-complete-generation-agreement
 (implies (and (fn-acg-reachablep s)
               (equal (fn-cp-nth 0 (fn-acg-tick s)) :ready))
          (fn-acg-requirement s))
 :hints (("Goal" :in-theory (e/d (fn-acg-state fn-acg-tick fn-acg-reachablep
                                  fn-acg-requirement fn-acg-rows-samep fn-cp-nth)
                                 (fn-cfg-entry-livep)))))

(defthm fn-acg-tick-makes-progress
 (implies (and (not (equal (fn-cp-nth 1 s) :ready))
               (member-eq (fn-cp-nth 0 (fn-acg-tick s)) '(:yield :ready)))
          (< (fn-acg-rank (fn-cp-nth 1 (fn-acg-tick s))) (fn-acg-rank s)))
 :hints (("Goal" :in-theory (e/d (fn-acg-state fn-acg-tick fn-acg-reachablep
                                  fn-acg-rank fn-cp-nth)
                                 (fn-cfg-entry-livep)))))

(in-theory (disable fn-acg-state fn-acg-begin fn-acg-tick fn-acg-rows-samep
                    fn-acg-reachablep fn-acg-requirement fn-acg-rank))
