(in-package "ACL2")
(include-book "../../books/account-config-generation-cursor")

(defconst *acgt-live* (fn-cfg-group-make "live" 1 nil nil 0 1))
(defconst *acgt-retired* (fn-cfg-group-make "retired" 1 nil 3 0 1))
(defconst *acgt-arriving* (fn-cfg-group-make "arriving" 6 nil nil 0 1))
(defconst *acgt-retiring* (fn-cfg-group-make "retiring" 1 nil 6 0 1))

(assert-event
 (let* ((rows (list *acgt-live* *acgt-retired*)) (s (fn-acg-begin rows 5 6))
        (one (fn-acg-tick s)) (next (fn-cp-nth 1 one)))
  (and (true-listp rows) (fn-acg-reachablep s)
       (equal (fn-acg-requirement s) (fn-acg-rows-samep rows 5 6))
       (fn-acg-requirement s) (equal (fn-cp-nth 0 one) :yield)
       (fn-acg-reachablep next) (equal (fn-acg-requirement next) (fn-acg-requirement s))
       (not (equal (fn-cp-nth 1 s) :ready))
       (member-eq (fn-cp-nth 0 one) '(:yield :ready))
       (< (fn-acg-rank next) (fn-acg-rank s)))))

(assert-event
 (let ((s (fn-acg-begin nil 5 6)))
  (and (fn-acg-reachablep s) (equal (fn-cp-nth 0 (fn-acg-tick s)) :ready)
       (fn-acg-requirement s))))

; A new/retiring row requests a rebuild and retains the EXACT unresolved row.
(assert-event
 (let ((s (fn-acg-begin (list *acgt-arriving*) 5 6)))
  (and (fn-acg-reachablep s) (not (fn-acg-requirement s))
       (equal (fn-acg-tick s) (list :rebuild s)))))

(assert-event
 (let ((s (fn-acg-begin (list *acgt-retiring*) 5 6)))
  (and (fn-acg-reachablep s) (not (fn-acg-requirement s))
       (equal (fn-acg-tick s) (list :rebuild s)))))

; Literal hypothesis removals, separately corrupted-state model data.
(assert-event
 (let ((rows (cons *acgt-live* :bad-tail)))
  (and (not (true-listp rows))
       (not (and (fn-acg-reachablep (fn-acg-begin rows 5 6))
                 (equal (fn-acg-requirement (fn-acg-begin rows 5 6))
                        (fn-acg-rows-samep rows 5 6)))))))

(assert-event
 (let ((s (fn-acg-state :ready (list *acgt-arriving*) 5 6)))
  (and (not (fn-acg-reachablep s))
       (not (and (fn-acg-reachablep (fn-cp-nth 1 (fn-acg-tick s)))
                 (equal (fn-acg-requirement (fn-cp-nth 1 (fn-acg-tick s)))
                        (fn-acg-requirement s)))))))

(assert-event
 (let ((s (fn-acg-state :ready (list *acgt-arriving*) 5 6)))
  (and (not (fn-acg-reachablep s))
       (equal (fn-cp-nth 0 (fn-acg-tick s)) :ready)
       (not (fn-acg-requirement s)))))

(assert-event
 (let ((s (fn-acg-begin (list *acgt-arriving*) 5 6)))
  (and (fn-acg-reachablep s)
       (not (equal (fn-cp-nth 0 (fn-acg-tick s)) :ready))
       (not (fn-acg-requirement s)))))

(assert-event
 (let ((s (fn-acg-state :ready nil 5 6)))
  (and (equal (fn-cp-nth 1 s) :ready)
       (member-eq (fn-cp-nth 0 (fn-acg-tick s)) '(:yield :ready))
       (not (< (fn-acg-rank (fn-cp-nth 1 (fn-acg-tick s))) (fn-acg-rank s))))))

(assert-event
 (let ((s (fn-acg-begin (list *acgt-arriving*) 5 6)))
  (and (not (equal (fn-cp-nth 1 s) :ready))
       (not (member-eq (fn-cp-nth 0 (fn-acg-tick s)) '(:yield :ready)))
       (not (< (fn-acg-rank (fn-cp-nth 1 (fn-acg-tick s))) (fn-acg-rank s))))))
